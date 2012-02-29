/* -*- mode: C; c-file-style: "gnu"; indent-tabs-mode: nil; -*-
 *
 * Copyright (C) 2007-2010 David Zeuthen <zeuthen@gmail.com>
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA  02110-1301  USA
 *
 */

#include "config.h"
#include <glib/gi18n-lib.h>

#define _GNU_SOURCE
#include <string.h>

/* TODO:
 *
 *  - instead of parsing /var/lib/iscsi, we should probably run the
 *    command 'iscsadm -m node -P 1' and parse the output
 *
 *  - need to somehow get reliable change notifications when
 *    iscsiadm's database has changed
 *
 *  - there is currently no way to get/set properties for each
 *    connection/path - this is really needed especially for
 *    e.g. setting up authentication
 *
 *  - there is no way to add/remove targets and add/remove paths -
 *    this should use a discovery mechanism
 *
 *  - should we expose node.discovery_address, node.discovery_port and
 *    node.discovery_type somehow so the UI can group targets
 *    discovered from a SendTargets server... ugh..
 *
 *  - apparently we don't get any uevent when the state sysfs
 *    attribute changes on an iscsi_connection - TODO: file a bug and
 *    poll until this is fixed
 */

#include <stdio.h>
#include <mntent.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <sys/wait.h>
#include <unistd.h>

#include <string.h>
#include <stdlib.h>

#include <gudev/gudev.h>

#include "udisksdaemon.h"
#include "udisksprovider.h"
#include "udisksmount.h"
#include "udisksmountmonitor.h"
#include "udisksiscsiprovider.h"
#include "udiskslinuxprovider.h"
#include "udisksdaemonutil.h"
#include "udiskslogging.h"

/**
 * SECTION:udisksiscsiprovider
 * @title: UDisksiSCSIProvider
 * @short_description: Provides UDisksiSCSITarget from the open-iscsi database
 *
 * This provider provides #UDisksiSCSITarget objects for iSCSI targets
 * defined in the open-iscsi database. Additionally, this information
 * is tied together with information to sysfs in order to convey the
 * connection state of each iSCSI target.
 */

/* ---------------------------------------------------------------------------------------------------- */

static void load_and_process_iscsi (UDisksiSCSIProvider *provider);

static void request_reload (UDisksiSCSIProvider *provider);

static void         connections_init      (UDisksiSCSIProvider *provider);
static void         connections_finalize  (UDisksiSCSIProvider *provider);
static const gchar *connections_get_state (UDisksiSCSIProvider *provider,
                                           const gchar         *target_name,
                                           gint                 tpgt,
                                           const gchar         *portal_address,
                                           gint                 portal_port,
                                           const gchar         *iface_name,
                                           gint                *out_tpgt);

/* ---------------------------------------------------------------------------------------------------- */

static void
diff_sorted_lists (GList *list1,
                   GList *list2,
                   GCompareFunc compare,
                   GList **added,
                   GList **removed)
{
  int order;

  *added = *removed = NULL;

  while (list1 != NULL && list2 != NULL)
    {
      order = (*compare) (list1->data, list2->data);
      if (order < 0)
        {
          *removed = g_list_prepend (*removed, list1->data);
          list1 = list1->next;
        }
      else if (order > 0)
        {
          *added = g_list_prepend (*added, list2->data);
          list2 = list2->next;
        }
      else
        { /* same item */
          list1 = list1->next;
          list2 = list2->next;
        }
    }

  while (list1 != NULL)
    {
      *removed = g_list_prepend (*removed, list1->data);
      list1 = list1->next;
    }
  while (list2 != NULL)
    {
      *added = g_list_prepend (*added, list2->data);
      list2 = list2->next;
    }
}

/* ---------------------------------------------------------------------------------------------------- */

static gchar *
util_compute_object_path (const gchar *base,
                          const gchar *path)
{
  const gchar *basename;
  GString *s;
  guint n;

  g_return_val_if_fail (path != NULL, NULL);

  basename = strrchr (path, '/');
  if (basename != NULL)
    basename++;
  else
    basename = path;

  s = g_string_new (base);
  for (n = 0; basename[n] != '\0'; n++)
    {
      gint c = basename[n];

      /* D-Bus spec sez:
       *
       * Each element must only contain the ASCII characters "[A-Z][a-z][0-9]_"
       */
      if ((c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z') || (c >= '0' && c <= '9'))
        {
          g_string_append_c (s, c);
        }
      else
        {
          /* Escape bytes not in [A-Z][a-z][0-9] as _<hex-with-two-digits> */
          g_string_append_printf (s, "_%02x", c);
        }
    }

  return g_string_free (s, FALSE);
}

/* ---------------------------------------------------------------------------------------------------- */

typedef struct
{
  gchar *name;

  GVariant *settings;
  GVariant *secret_settings;
} iSCSIIface;

static void
iscsi_iface_free (iSCSIIface *iface)
{
  g_free (iface->name);
  if (iface->settings != NULL)
    g_variant_unref (iface->settings);
  if (iface->secret_settings != NULL)
    g_variant_unref (iface->secret_settings);
  g_free (iface);
}

static gint
iscsi_iface_compare (const iSCSIIface *a,
                     const iSCSIIface *b)
{
  return g_strcmp0 (a->name, b->name);
}

typedef struct
{
  gchar *address;
  gint port;
  gint tpgt;
  GList *ifaces;
} iSCSIPortal;

static void
iscsi_portal_free (iSCSIPortal *portal)
{
  g_free (portal->address);
  g_list_foreach (portal->ifaces, (GFunc) iscsi_iface_free, NULL);
  g_list_free (portal->ifaces);
  g_free (portal);
}

static gint
iscsi_portal_compare (const iSCSIPortal *a,
                      const iSCSIPortal *b)
{
  gint ret;
  GList *l;
  GList *j;

  ret = g_strcmp0 (a->address, b->address);
  if (ret != 0)
    goto out;
  ret = a->port - b->port;
  if (ret != 0)
    goto out;
  ret = a->tpgt - b->tpgt;
  if (ret != 0)
    goto out;
  ret = g_list_length (a->ifaces) - g_list_length (b->ifaces);
  if (ret != 0)
    goto out;
  for (l = a->ifaces, j = b->ifaces; l != NULL; l = l->next, j = j->next)
    {
      iSCSIIface *ia = l->data;
      iSCSIIface *ib = j->data;
      ret = iscsi_iface_compare (ia, ib);
      if (ret != 0)
        goto out;
    }
  ret = 0;
 out:
  return ret;
}

typedef struct
{
  volatile gint ref_count;

  gchar *target_name;

  gchar *object_path;
  UDisksObjectSkeleton *object;
  UDisksiSCSITarget *iface;

  gchar *source_object_path;

  GList *portals;
} iSCSITarget;

static iSCSITarget *
iscsi_target_ref (iSCSITarget *target)
{
  g_atomic_int_inc (&target->ref_count);
  return target;
}

static void
iscsi_target_unref (iSCSITarget *target)
{
  if (g_atomic_int_dec_and_test (&target->ref_count))
    {
      g_free (target->target_name);

      g_free (target->object_path);
      if (target->object != NULL)
        g_object_unref (target->object);
      if (target->iface != NULL)
        g_object_unref (target->iface);

      g_free (target->source_object_path);

      g_list_foreach (target->portals, (GFunc) iscsi_portal_free, NULL);
      g_list_free (target->portals);

      g_free (target);
    }
}

/* on purpose, this does not take portals/ifaces into account */
static gint
iscsi_target_compare (const iSCSITarget *a,
                      const iSCSITarget *b)
{
  gint ret;

  ret = g_strcmp0 (a->target_name, b->target_name);
  if (ret != 0)
    goto out;

 out:
  return ret;
}

typedef struct
{
  volatile gint ref_count;

  const gchar *mechanism;

  gchar *object_path;
  UDisksObjectSkeleton *object;
  UDisksiSCSISource *iface;

  gchar *discovery_address;
} iSCSISource;

static iSCSISource *
iscsi_source_ref (iSCSISource *source)
{
  g_atomic_int_inc (&source->ref_count);
  return source;
}

static void
iscsi_source_unref (iSCSISource *source)
{
  if (g_atomic_int_dec_and_test (&source->ref_count))
    {
      g_free (source->object_path);
      if (source->object != NULL)
        g_object_unref (source->object);
      if (source->iface != NULL)
        g_object_unref (source->iface);

      g_free (source->discovery_address);

      g_free (source);
    }
}

/* on purpose, this does not take targets/portals/ifaces into account */
static gint
iscsi_source_compare (const iSCSISource *a,
                      const iSCSISource *b)
{
  gint ret;

  ret = g_strcmp0 (a->mechanism, b->mechanism);
  if (ret != 0)
    goto out;

  ret = g_strcmp0 (a->discovery_address, b->discovery_address);
  if (ret != 0)
    goto out;

 out:
  return ret;
}

static void
iscsi_source_compute_object_path (iSCSISource *source)
{
  g_assert (source->object_path == NULL);
  if (g_strcmp0 (source->mechanism, "static") == 0)
    {
      source->object_path = g_strdup ("/org/freedesktop/UDisks2/iSCSI/static");
    }
  else if (g_strcmp0 (source->mechanism, "sendtargets") == 0)
    {
      source->object_path = util_compute_object_path ("/org/freedesktop/UDisks2/iSCSI/sendtargets/", source->discovery_address);
    }
  else if (g_strcmp0 (source->mechanism, "firmware") == 0)
    {
      source->object_path = g_strdup ("/org/freedesktop/UDisks2/iSCSI/firmware");
    }
  else
    {
      g_error ("TODO: support '%s'", source->mechanism);
    }
}

/* ---------------------------------------------------------------------------------------------------- */

typedef struct _UDisksiSCSIProviderClass   UDisksiSCSIProviderClass;

/**
 * UDisksiSCSIProvider:
 *
 * The #UDisksiSCSIProvider structure contains only private data and
 * should only be accessed using the provided API.
 */
struct _UDisksiSCSIProvider
{
  UDisksProvider parent_instance;

  UDisksDaemon *daemon;
  GUdevClient *udev_client;

  GFileMonitor *file_monitor;
  guint cool_off_timeout_id;

  GHashTable *sysfs_to_connection;
  GHashTable *id_to_connection;
  GHashTable *id_without_tpgt_to_connection;

  GList *targets;
  GList *sources;
};

struct _UDisksiSCSIProviderClass
{
  UDisksProviderClass parent_class;
};

static void
on_file_monitor_changed (GFileMonitor     *monitor,
                         GFile            *file,
                         GFile            *other_file,
                         GFileMonitorEvent event_type,
                         gpointer          user_data);

G_DEFINE_TYPE (UDisksiSCSIProvider, udisks_iscsi_provider, UDISKS_TYPE_PROVIDER);

static void
udisks_iscsi_provider_finalize (GObject *object)
{
  UDisksiSCSIProvider *provider = UDISKS_ISCSI_PROVIDER (object);
  GList *l;

  if (provider->cool_off_timeout_id != 0)
    g_source_remove (provider->cool_off_timeout_id);

  if (provider->file_monitor == NULL)
    {
      g_signal_handlers_disconnect_by_func (provider->file_monitor,
                                            G_CALLBACK (on_file_monitor_changed),
                                            provider);
      g_object_unref (provider->file_monitor);
    }

  for (l = provider->targets; l != NULL; l = l->next)
    {
      iSCSITarget *target = l->data;
      g_assert (target->object_path != NULL);
      g_dbus_object_manager_server_unexport (udisks_daemon_get_object_manager (udisks_provider_get_daemon (UDISKS_PROVIDER (provider))),
                                             target->object_path);
      iscsi_target_unref (target);
    }
  g_list_free (provider->targets);

  for (l = provider->sources; l != NULL; l = l->next)
    {
      iSCSISource *source = l->data;
      g_dbus_object_manager_server_unexport (udisks_daemon_get_object_manager (udisks_provider_get_daemon (UDISKS_PROVIDER (provider))),
                                             source->object_path);
      iscsi_source_unref (source);
    }
  g_list_free (provider->sources);

  connections_finalize (provider);
  g_object_unref (provider->udev_client);

  if (G_OBJECT_CLASS (udisks_iscsi_provider_parent_class)->finalize != NULL)
    G_OBJECT_CLASS (udisks_iscsi_provider_parent_class)->finalize (object);
}

static void
udisks_iscsi_provider_init (UDisksiSCSIProvider *provider)
{
}

/* ---------------------------------------------------------------------------------------------------- */

static void
udisks_iscsi_provider_start (UDisksProvider *_provider)
{
  UDisksiSCSIProvider *provider = UDISKS_ISCSI_PROVIDER (_provider);
  GFile *file;
  GError *error;
  const gchar *nodes_dir_name;
  const gchar *subsystems[] = {"iscsi_connection",
                               "iscsi_session",
                               "scsi",
                               NULL};

  if (UDISKS_PROVIDER_CLASS (udisks_iscsi_provider_parent_class)->start != NULL)
    UDISKS_PROVIDER_CLASS (udisks_iscsi_provider_parent_class)->start (_provider);

  provider->daemon = udisks_provider_get_daemon (UDISKS_PROVIDER (provider));
  provider->udev_client = g_udev_client_new (subsystems);

  /* TODO: this doesn't catch all changes but it's good enough for now */
  nodes_dir_name = "/var/lib/iscsi/nodes";
  file = g_file_new_for_path ("/var/lib/iscsi/nodes");
  error = NULL;
  provider->file_monitor = g_file_monitor_directory (file,
                                                     G_FILE_MONITOR_NONE,
                                                     NULL,
                                                     &error);
  if (provider->file_monitor == NULL)
    {
      udisks_warning ("Error monitoring dir %s: %s",
                      nodes_dir_name,
                      error->message);
      g_error_free (error);
    }
  else
    {
      g_file_monitor_set_rate_limit (provider->file_monitor, 50 /* msec */);
      g_signal_connect (provider->file_monitor,
                        "changed",
                        G_CALLBACK (on_file_monitor_changed),
                        provider);
    }
  g_object_unref (file);

  connections_init (provider);

  load_and_process_iscsi (provider);
}


static void
udisks_iscsi_provider_class_init (UDisksiSCSIProviderClass *klass)
{
  GObjectClass *gobject_class;
  UDisksProviderClass *provider_class;

  gobject_class = G_OBJECT_CLASS (klass);
  gobject_class->finalize     = udisks_iscsi_provider_finalize;

  provider_class        = UDISKS_PROVIDER_CLASS (klass);
  provider_class->start = udisks_iscsi_provider_start;
}

/**
 * udisks_iscsi_provider_new:
 * @daemon: A #UDisksDaemon.
 *
 * Create a new provider object for iSCSI targets on the system.
 *
 * Returns: A #UDisksiSCSIProvider object. Free with g_object_unref().
 */
UDisksiSCSIProvider *
udisks_iscsi_provider_new (UDisksDaemon *daemon)
{
  g_return_val_if_fail (UDISKS_IS_DAEMON (daemon), NULL);
  return UDISKS_ISCSI_PROVIDER (g_object_new (UDISKS_TYPE_ISCSI_PROVIDER,
                                              "daemon", daemon,
                                              NULL));
}

/* ---------------------------------------------------------------------------------------------------- */

/* returns a new floating GVariant */
static GVariant *
portals_and_ifaces_to_gvariant (UDisksiSCSIProvider *provider,
                                iSCSITarget         *target)
{
  GVariantBuilder connections_builder;
  GList *l, *ll;

  target->portals = g_list_sort (target->portals, (GCompareFunc) iscsi_portal_compare);

  g_variant_builder_init (&connections_builder, G_VARIANT_TYPE ("a(siisa{ss}sa{sv})"));
  for (l = target->portals; l != NULL; l = l->next)
    {
      iSCSIPortal *portal = l->data;
      portal->ifaces = g_list_sort (portal->ifaces, (GCompareFunc) iscsi_iface_compare);
      for (ll = portal->ifaces; ll != NULL; ll = ll->next)
        {
          iSCSIIface *iface = ll->data;
          const gchar *state;
          gint connection_tpgt;

          state = connections_get_state (provider,
                                         target->target_name,
                                         portal->tpgt,
                                         portal->address,
                                         portal->port,
                                         iface->name,
                                         &connection_tpgt);

          g_variant_builder_add (&connections_builder, "(siis@a{ss}sa{sv})",
                                 portal->address,
                                 portal->port,
                                 portal->tpgt != -1 ? portal->tpgt : connection_tpgt,
                                 iface->name,
                                 iface->settings,
                                 state,
                                 NULL); /* expansion */
        }
    }
  return g_variant_builder_end (&connections_builder);
}

/* ---------------------------------------------------------------------------------------------------- */

/* runs in dedicated thread */
static gboolean
on_iscsi_target_handle_login_logout (UDisksiSCSITarget     *iface,
                                     GDBusMethodInvocation *invocation,
                                     const gchar           *host,
                                     gint                   port,
                                     gint                   tpgt,
                                     const gchar           *iface_name,
                                     GVariant              *options,
                                     UDisksiSCSIProvider   *provider,
                                     gboolean               is_login)
{
  gint exit_status;
  gchar *error_message = NULL;
  GString *command_line = NULL;
  UDisksObject *object = NULL;
  GError *error;
  gchar *s;

  error = NULL;
  object = udisks_daemon_util_dup_object (iface, &error);
  if (object == NULL)
    {
      g_dbus_method_invocation_take_error (invocation, error);
      goto out;
    }

  /* TODO: we want nicer authentication message */
  if (!udisks_daemon_util_check_authorization_sync (provider->daemon,
                                                    object,
                                                    "org.freedesktop.udisks2.iscsi-initiator.login-logout",
                                                    options,
                                                    is_login ?
                                                      N_("Authentication is required to login to a remote iSCSI target") :
                                                      N_("Authentication is required to logout from a remote iSCSI target"),
                                                    invocation))
    goto out;

  command_line = g_string_new ("iscsiadm --mode node");

  s = g_strescape (udisks_iscsi_target_get_name (iface), NULL);
  g_string_append_printf (command_line, " --target \"%s\"", s);
  g_free (s);
  if (strlen (host) > 0)
    {
      s = g_strescape (host, NULL);
      if (port == 0)
        port = 3260;
      g_string_append_printf (command_line, " --portal \"%s\":%d", s, port);
      g_free (s);
    }
  if (strlen (iface_name) > 0)
    {
      s = g_strescape (iface_name, NULL);
      g_string_append_printf (command_line, " --interface \"%s\"", s);
      g_free (s);
    }

  if (is_login)
    g_string_append (command_line, " --login");
  else
    g_string_append (command_line, " --logout");

  if (!udisks_daemon_launch_spawned_job_sync (provider->daemon,
                                              object,
                                              NULL,  /* GCancellable */
                                              0,     /* uid_t run_as_uid */
                                              0,     /* uid_t run_as_euid */
                                              &exit_status,
                                              &error_message,
                                              NULL,  /* input_string */
                                              "%s",
                                              command_line->str))
    {
      g_dbus_method_invocation_return_error (invocation,
                                             UDISKS_ERROR,
                                             UDISKS_ERROR_FAILED,
                                             "iscsiadm(8) failed with: %s",
                                             error_message);
    }
  else
    {
      /* sometimes iscsiadm returns 0 when it fails but stderr is set...
       *
       * TODO: file a bug against iscsi-initiator-utils
       */
      if (error_message != NULL && strlen (error_message) > 0)
        {
          g_dbus_method_invocation_return_error (invocation,
                                                 UDISKS_ERROR,
                                                 UDISKS_ERROR_FAILED,
                                                 "iscsiadm(8) failed with: %s",
                                                 error_message);
        }
      else
        {
          g_dbus_method_invocation_return_value (invocation, NULL);
        }
    }

 out:
  g_clear_object (&object);
  if (command_line != NULL)
    g_string_free (command_line, TRUE);
  g_free (error_message);
  return TRUE; /* call was handled */
}

static gboolean
on_iscsi_target_handle_login (UDisksiSCSITarget     *iface,
                              GDBusMethodInvocation *invocation,
                              const gchar           *host,
                              gint                   port,
                              gint                   tpgt,
                              const gchar           *iface_name,
                              GVariant              *options,
                              gpointer               user_data)
{
  UDisksiSCSIProvider *provider = UDISKS_ISCSI_PROVIDER (user_data);
  return on_iscsi_target_handle_login_logout (iface, invocation, host, port, tpgt, iface_name, options, provider, TRUE);
}

static gboolean
on_iscsi_target_handle_logout (UDisksiSCSITarget     *iface,
                               GDBusMethodInvocation *invocation,
                               const gchar           *host,
                               gint                   port,
                               gint                   tpgt,
                               const gchar           *iface_name,
                               GVariant              *options,
                               gpointer               user_data)
{
  UDisksiSCSIProvider *provider = UDISKS_ISCSI_PROVIDER (user_data);
  return on_iscsi_target_handle_login_logout (iface, invocation, host, port, tpgt, iface_name, options, provider, FALSE);
}

/* ---------------------------------------------------------------------------------------------------- */

/* TODO: this can be done a lot smarter... */
static iSCSIIface *
find_iface (UDisksiSCSIProvider  *provider,
            UDisksiSCSITarget    *target_iface,
            const gchar           *host,
            gint                   port,
            gint                   tpgt,
            const gchar           *iface_name)
{
  GList *l, *ll, *lll;
  iSCSIIface *ret = NULL;

  for (l = provider->targets; l != NULL; l = l->next)
    {
      iSCSITarget *target = l->data;

      if (target->iface != target_iface)
        continue;

      for (ll = target->portals; ll != NULL; ll = ll->next)
        {
          iSCSIPortal *portal = ll->data;

          if (!(g_strcmp0 (portal->address, host) == 0 &&
                portal->port == port &&
                portal->tpgt == tpgt))
            continue;

          for (lll = portal->ifaces; lll != NULL; lll = lll->next)
            {
              iSCSIIface *iface = lll->data;

              if (g_strcmp0 (iface->name, iface_name) == 0)
                {
                  ret = iface;
                  goto out;
                }
            }
        }
    }

 out:
  return ret;
}

/* ---------------------------------------------------------------------------------------------------- */

static gboolean
on_iscsi_target_handle_get_secret_configuration (UDisksiSCSITarget     *iface,
                                                 GDBusMethodInvocation *invocation,
                                                 const gchar           *host,
                                                 gint                   port,
                                                 gint                   tpgt,
                                                 const gchar           *iface_name,
                                                 GVariant              *options,
                                                 gpointer               user_data)
{
  UDisksiSCSIProvider *provider = UDISKS_ISCSI_PROVIDER (user_data);
  iSCSIIface *iscsi_iface;

  if (!udisks_daemon_util_check_authorization_sync (provider->daemon,
                                                    UDISKS_OBJECT (g_dbus_interface_get_object (G_DBUS_INTERFACE (iface))),
                                                    "org.freedesktop.udisks2.read-system-configuration-secrets",
                                                    options,
                                                    N_("Authentication is required to read passwords used to connect to a remote iSCSI target"),
                                                    invocation))
    goto out;

  iscsi_iface = find_iface (provider, iface, host, port, tpgt, iface_name);
  if (iscsi_iface == NULL)
    {
      g_dbus_method_invocation_return_error (invocation,
                                             UDISKS_ERROR,
                                             UDISKS_ERROR_FAILED,
                                             "Connection not found");
      goto out;
    }

  udisks_iscsi_target_complete_get_secret_configuration (iface,
                                                         invocation,
                                                         iscsi_iface->secret_settings);

 out:
  return TRUE; /* call was handled */
}

/* ---------------------------------------------------------------------------------------------------- */

static gboolean
on_iscsi_target_handle_update_configuration (UDisksiSCSITarget     *iface,
                                             GDBusMethodInvocation *invocation,
                                             const gchar           *host,
                                             gint                   port,
                                             gint                   tpgt,
                                             const gchar           *iface_name,
                                             GVariant              *configuration,
                                             GVariant              *options,
                                             gpointer               user_data)
{
  UDisksiSCSIProvider *provider = UDISKS_ISCSI_PROVIDER (user_data);
  iSCSIIface *iscsi_iface;
  GVariantIter iter;
  const gchar *key;
  const gchar *value;
  gchar *escaped_target = NULL;
  gchar *escaped_host = NULL;
  gchar *escaped_iface_name = NULL;

  if (!udisks_daemon_util_check_authorization_sync (provider->daemon,
                                                    UDISKS_OBJECT (g_dbus_interface_get_object (G_DBUS_INTERFACE (iface))),
                                                    "org.freedesktop.udisks2.iscsi-initiator.modify",
                                                    options,
                                                    N_("Authentication is required to update configuration for how to connect to a remote iSCSI target"),
                                                    invocation))
    goto out;

  iscsi_iface = find_iface (provider, iface, host, port, tpgt, iface_name);
  if (iscsi_iface == NULL)
    {
      g_dbus_method_invocation_return_error (invocation,
                                             UDISKS_ERROR,
                                             UDISKS_ERROR_FAILED,
                                             "Connection not found");
      goto out;
    }

  escaped_target = g_strescape (udisks_iscsi_target_get_name (iface), NULL);
  escaped_host = g_strescape (host, NULL);
  escaped_iface_name = g_strescape (iface_name, NULL);

  g_variant_iter_init (&iter, configuration);
  while (g_variant_iter_next (&iter, "{&s&s}", &key, &value))
    {
      gchar *command_line = NULL;
      gchar *stderror_str = NULL;
      gchar *escaped_key = NULL;
      gchar *escaped_value = NULL;
      gint exit_status;
      GError *error;

      escaped_key = g_strescape (key, NULL);
      escaped_value = g_strescape (value, NULL);

      command_line = g_strdup_printf ("iscsiadm --mode node --target \"%s\" --portal \"%s\":%d "
                                      "--interface \"%s\" --op update --name \"%s\" --value \"%s\"",
                                      escaped_target,
                                      escaped_host,
                                      port == 0 ? 3260 : port,
                                      escaped_iface_name,
                                      escaped_key,
                                      escaped_value);
      g_free (escaped_key);
      g_free (escaped_value);

      error = NULL;
      if (!g_spawn_command_line_sync (command_line,
                                      NULL, /* gchar **stdout */
                                      &stderror_str,
                                      &exit_status,
                                      &error))
        {
          g_dbus_method_invocation_return_error (invocation,
                                                 UDISKS_ERROR,
                                                 UDISKS_ERROR_FAILED,
                                                 "Error spawning command-line `%s': %s (%s, %d)",
                                                 command_line,
                                                 error->message, g_quark_to_string (error->domain), error->code);
          g_error_free (error);
          g_free (command_line);
          goto out;
        }
      if (!(WIFEXITED (exit_status) && WEXITSTATUS (exit_status) == 0))
        {
          g_dbus_method_invocation_return_error (invocation,
                                                 UDISKS_ERROR,
                                                 UDISKS_ERROR_FAILED,
                                                 "Command-line `%s' did not exit with exit status 0: %s",
                                                 command_line, stderror_str);
          g_free (command_line);
          g_free (stderror_str);
          goto out;
        }

      g_free (command_line);
    }

  /* request reload */
  request_reload (provider);

  udisks_iscsi_target_complete_update_configuration (iface, invocation);

 out:
  g_free (escaped_target);
  g_free (escaped_host);
  g_free (escaped_iface_name);
  return TRUE; /* call was handled */
}

/* ---------------------------------------------------------------------------------------------------- */

static void
load_settings (UDisksiSCSIProvider *provider,
               iSCSITarget         *target)
{
  GList *l, *ll;
  gchar *escaped_target;

  escaped_target = g_strescape (target->target_name, NULL);

  target->portals = g_list_sort (target->portals, (GCompareFunc) iscsi_portal_compare);
  for (l = target->portals; l != NULL; l = l->next)
    {
      iSCSIPortal *portal = l->data;
      gchar *escaped_portal;

      escaped_portal = g_strescape (portal->address, NULL);

      portal->ifaces = g_list_sort (portal->ifaces, (GCompareFunc) iscsi_iface_compare);
      for (ll = portal->ifaces; ll != NULL; ll = ll->next)
        {
          iSCSIIface *iface = ll->data;
          gchar *escaped_interface;
          gchar *command_line;
          gchar *ia_out = NULL;
          gchar *ia_err = NULL;
          GError *error = NULL;
          gint exit_status;
          gchar *p;
          GVariantBuilder settings_builder;
          GVariantBuilder secret_settings_builder;

          g_variant_builder_init (&settings_builder, G_VARIANT_TYPE ("a{ss}"));
          g_variant_builder_init (&secret_settings_builder, G_VARIANT_TYPE ("a{ss}"));

          escaped_interface = g_strescape (iface->name, NULL);

          command_line = g_strdup_printf ("iscsiadm --mode node --target \"%s\" --portal \"%s\":%d "
                                          "--interface \"%s\" --op show --show",
                                          escaped_target,
                                          escaped_portal,
                                          portal->port == 0 ? 3260 : portal->port,
                                          escaped_interface);

          error = NULL;
          if (!g_spawn_command_line_sync (command_line,
                                          &ia_out,
                                          &ia_err,
                                          &exit_status,
                                          &error))
            {
              udisks_warning ("Error spawning command-line `%s': %s (%s, %d)",
                              command_line,
                              error->message, g_quark_to_string (error->domain), error->code);
              g_error_free (error);
              goto cont;
            }

          if (!(WIFEXITED (exit_status) && WEXITSTATUS (exit_status) == 0))
            {
              udisks_warning ("Command-line `%s' did not exit with exit status 0: %s",
                              command_line, ia_err);
              goto cont;
            }

          p = ia_out;
          while (p != NULL)
            {
              gchar *p_next;
              gchar *p_middle;
              gchar *p_end;
              gchar *key, *value;
              p_end = strchr (p, '\n');
              if (p_end == NULL)
                {
                  p_next = NULL;
                }
              else
                {
                  p_next = p_end + 1;
                  *p_end = '\0';
                }

              if (p[0] == '#')
                goto loop_cont;

              p_middle = strstr (p, " = ");
              if (p_middle == NULL)
                goto loop_cont;

              *p_middle = '\0';

              key = p;
              value = p_middle + 3;

              /* TODO: ensure @key and @value are valid UTF-8 */
              if (g_strcmp0 (value, "<empty>") == 0)
                value = "";

              if (strstr (key, "password") != NULL)
                {
                  /* key includes the word 'password' => only include value in secret_settings */
                  g_variant_builder_add (&settings_builder, "{ss}", key, "");
                  g_variant_builder_add (&secret_settings_builder, "{ss}", key, value);
                }
              else
                {
                  g_variant_builder_add (&settings_builder, "{ss}", key, value);
                  g_variant_builder_add (&secret_settings_builder, "{ss}", key, value);
                }

            loop_cont:
              p = p_next;
            }

        cont:
          if (iface->settings != NULL)
            g_variant_unref (iface->settings);
          iface->settings = g_variant_ref_sink (g_variant_builder_end (&settings_builder));

          if (iface->secret_settings != NULL)
            g_variant_unref (iface->secret_settings);
          iface->secret_settings = g_variant_ref_sink (g_variant_builder_end (&secret_settings_builder));

          g_free (ia_out);
          g_free (ia_err);
          g_free (command_line);
          g_free (escaped_interface);

        }
      g_free (escaped_portal);
    }
  g_free (escaped_target);
}


static void
add_remove_targets (UDisksiSCSIProvider  *provider,
                    GList                *parsed_targets)
{
  GList *l;
  GList *added;
  GList *removed;

  provider->targets = g_list_sort (provider->targets, (GCompareFunc) iscsi_target_compare);
  diff_sorted_lists (provider->targets,
                     parsed_targets,
                     (GCompareFunc) iscsi_target_compare,
                     &added,
                     &removed);
  for (l = removed; l != NULL; l = l->next)
    {
      iSCSITarget *target = l->data;
      g_dbus_object_manager_server_unexport (udisks_daemon_get_object_manager (udisks_provider_get_daemon (UDISKS_PROVIDER (provider))),
                                             target->object_path);
      provider->targets = g_list_remove (provider->targets, target);
      iscsi_target_unref (target);
    }

  for (l = added; l != NULL; l = l->next)
    {
      iSCSITarget *target = l->data;
      gchar *base;
      base = g_strconcat (target->source_object_path, "/", NULL);
      target->object_path = util_compute_object_path (base, target->target_name);
      g_free (base);
      target->iface = udisks_iscsi_target_skeleton_new ();
      g_dbus_interface_skeleton_set_flags (G_DBUS_INTERFACE_SKELETON (target->iface),
                                           G_DBUS_INTERFACE_SKELETON_FLAGS_HANDLE_METHOD_INVOCATIONS_IN_THREAD);
      g_signal_connect (target->iface,
                        "handle-login",
                        G_CALLBACK (on_iscsi_target_handle_login),
                        provider);
      g_signal_connect (target->iface,
                        "handle-logout",
                        G_CALLBACK (on_iscsi_target_handle_logout),
                        provider);
      g_signal_connect (target->iface,
                        "handle-get-secret-configuration",
                        G_CALLBACK (on_iscsi_target_handle_get_secret_configuration),
                        provider);
      g_signal_connect (target->iface,
                        "handle-update-configuration",
                        G_CALLBACK (on_iscsi_target_handle_update_configuration),
                        provider);
      udisks_iscsi_target_set_name (target->iface, target->target_name);
      udisks_iscsi_target_set_source (target->iface, target->source_object_path);
      provider->targets = g_list_prepend (provider->targets, iscsi_target_ref (target));
    }

  /* re-load all settings */
  for (l = provider->targets; l != NULL; l = l->next)
    {
      iSCSITarget *target = l->data;
      load_settings (provider, target);
    }

  /* update all known targets since portals/interfaces might have changed */
  for (l = provider->targets; l != NULL; l = l->next)
    {
      iSCSITarget *target = l->data;
      udisks_iscsi_target_set_connections (target->iface,
                                           portals_and_ifaces_to_gvariant (provider, target));
    }

  /* finally export added targets */
  for (l = added; l != NULL; l = l->next)
    {
      iSCSITarget *target = l->data;
      target->object = udisks_object_skeleton_new (target->object_path);
      udisks_object_skeleton_set_iscsi_target (target->object, target->iface);
      g_dbus_object_manager_server_export_uniquely (udisks_daemon_get_object_manager (udisks_provider_get_daemon (UDISKS_PROVIDER (provider))),
                                                    G_DBUS_OBJECT_SKELETON (target->object));
    }

  g_list_free (removed);
  g_list_free (added);
}

static void
add_remove_sources (UDisksiSCSIProvider  *provider,
                    GList                *parsed_sources)
{
  GList *l;
  GList *added;
  GList *removed;

  provider->sources = g_list_sort (provider->sources, (GCompareFunc) iscsi_source_compare);
  diff_sorted_lists (provider->sources,
                     parsed_sources,
                     (GCompareFunc) iscsi_source_compare,
                     &added,
                     &removed);
  for (l = removed; l != NULL; l = l->next)
    {
      iSCSISource *source = l->data;
      g_dbus_object_manager_server_unexport (udisks_daemon_get_object_manager (udisks_provider_get_daemon (UDISKS_PROVIDER (provider))),
                                             source->object_path);
      provider->sources = g_list_remove (provider->sources, source);
      iscsi_source_unref (source);
    }

  for (l = added; l != NULL; l = l->next)
    {
      iSCSISource *source = l->data;
      source->iface = udisks_iscsi_source_skeleton_new ();
      g_dbus_interface_skeleton_set_flags (G_DBUS_INTERFACE_SKELETON (source->iface),
                                           G_DBUS_INTERFACE_SKELETON_FLAGS_HANDLE_METHOD_INVOCATIONS_IN_THREAD);
      /* TODO: export methods */
      udisks_iscsi_source_set_mechanism (source->iface, source->mechanism);
      udisks_iscsi_source_set_address (source->iface, source->discovery_address);
      provider->sources = g_list_prepend (provider->sources, iscsi_source_ref (source));
    }

  /* export added sources */
  for (l = added; l != NULL; l = l->next)
    {
      iSCSISource *source = l->data;
      source->object = udisks_object_skeleton_new (source->object_path);
      udisks_object_skeleton_set_iscsi_source (source->object, source->iface);
      g_dbus_object_manager_server_export_uniquely (udisks_daemon_get_object_manager (udisks_provider_get_daemon (UDISKS_PROVIDER (provider))),
                                                    G_DBUS_OBJECT_SKELETON (source->object));
    }

  g_list_free (removed);
  g_list_free (added);
}

enum
{
  MODE_NOWHERE,
  MODE_IN_SENDTARGETS,
  MODE_IN_ISNS,
  MODE_IN_STATIC,
  MODE_IN_FIRMWARE
};

static void
load_and_process_iscsi (UDisksiSCSIProvider *provider)
{
  GError *error;
  const gchar *command_line;
  gchar *ia_out;
  gchar *ia_err;
  gint exit_status;
  GList *parsed_targets;
  GList *parsed_sources;
  const gchar *s;
  iSCSITarget *target;
  iSCSIPortal *portal;
  iSCSISource *source;
  gint mode;

  parsed_targets = NULL;
  parsed_sources = NULL;
  ia_out = NULL;
  ia_err = NULL;

  /* TODO: might be problematic that we block here */
  error = NULL;
  command_line = "iscsiadm --mode discoverydb --print 1";
  if (!g_spawn_command_line_sync (command_line,
                                  &ia_out,
                                  &ia_err,
                                  &exit_status,
                                  &error))
    {
      udisks_warning ("Error spawning `%s': %s",
                      command_line,
                      error->message);
      g_error_free (error);
      goto done_parsing;
    }

  if (!(WIFEXITED (exit_status) && WEXITSTATUS (exit_status) == 0))
    {
      udisks_warning ("The command-line `%s' didn't exit normally with return code 0: %d",
                      command_line, exit_status);
      goto done_parsing;
    }

  mode = MODE_NOWHERE;
  source = NULL;

  s = ia_out;
  target = NULL;
  while (s != NULL)
    {
      const gchar *endl;
      gchar *line;

      endl = strstr (s, "\n");
      if (endl == NULL)
        {
          line = g_strdup (s);
          s = NULL;
        }
      else
        {
          line = g_strndup (s, endl - s);
          s = endl + 1;
        }

      if (g_strcmp0 (line, "SENDTARGETS:") == 0)
        {
          mode = MODE_IN_SENDTARGETS;
          source = NULL;
          target = NULL;
          portal = NULL;
        }
      else if (mode == MODE_IN_SENDTARGETS && g_str_has_prefix (line, "DiscoveryAddress: "))
        {
          source = g_new0 (iSCSISource, 1);
          source->ref_count = 1;
          source->mechanism = "sendtargets";
          source->discovery_address = g_strdup (line + sizeof "DiscoveryAddress: " - 1);
          /* TODO: fix up comma */
          iscsi_source_compute_object_path (source);
          parsed_sources = g_list_prepend (parsed_sources, source);
          target = NULL;
          portal = NULL;
        }
      else if (g_strcmp0 (line, "iSNS:") == 0)
        {
          mode = MODE_IN_ISNS;
          source = NULL;
          target = NULL;
          portal = NULL;
        }
      else if (mode == MODE_IN_ISNS && g_str_has_prefix (line, "DiscoveryAddress: "))
        {
          source = g_new0 (iSCSISource, 1);
          source->ref_count = 1;
          source->mechanism = "isns";
          source->discovery_address = g_strdup (line + sizeof "DiscoveryAddress: " - 1);
          /* TODO: fix up comma */
          iscsi_source_compute_object_path (source);
          parsed_sources = g_list_prepend (parsed_sources, source);
          target = NULL;
          portal = NULL;
        }
      else if (g_strcmp0 (line, "STATIC:") == 0)
        {
          mode = MODE_IN_STATIC;
          source = g_new0 (iSCSISource, 1);
          source->ref_count = 1;
          source->mechanism = "static";
          iscsi_source_compute_object_path (source);
          parsed_sources = g_list_prepend (parsed_sources, source);
          target = NULL;
          portal = NULL;
        }
      else if (g_strcmp0 (line, "FIRMWARE:") == 0)
        {
          mode = MODE_IN_FIRMWARE;
          source = g_new0 (iSCSISource, 1);
          source->ref_count = 1;
          source->mechanism = "firmware";
          iscsi_source_compute_object_path (source);
          parsed_sources = g_list_prepend (parsed_sources, source);
          target = NULL;
          portal = NULL;
        }
      else if (g_strcmp0 (line, "No targets found.") == 0)
        {
          mode = MODE_NOWHERE;
          source = NULL;
          target = NULL;
          portal = NULL;
        }
      else if (g_str_has_prefix (line, "Target: "))
        {
          if (source == NULL)
            {
              g_warning ("Target without a current Source");
            }
          else
            {
              target = g_new0 (iSCSITarget, 1);
              target->ref_count = 1;
              target->source_object_path = g_strdup (source->object_path);
              target->target_name = g_strdup (line + sizeof "Target: " - 1);
              g_strstrip (target->target_name);
              parsed_targets = g_list_prepend (parsed_targets, target);
            }
        }
      else if (g_str_has_prefix (line, "\tPortal: "))
        {
          if (target == NULL)
            {
              g_warning ("Portal without a current target");
            }
          else
            {
              const gchar *s;
              gint port, tpgt;
              s = g_strrstr (line, ":");
              if (s == NULL || sscanf (s + 1, "%d,%d", &port, &tpgt) != 2)
                {
                  g_warning ("Invalid line `%s'", line);
                }
              else
                {
                  const gchar *s2;
                  portal = g_new0 (iSCSIPortal, 1);
                  s2 = line + sizeof "\tPortal: " - 1;
                  g_assert (s - s2 >= 0);
                  portal->address = g_strndup (s2, s - s2);
                  g_strstrip (portal->address);
                  if (portal->address[0] == '[' && portal->address[strlen (portal->address) - 1] == ']')
                    {
                      portal->address[0] = ' ';
                      portal->address[strlen (portal->address) - 1] = '\0';
                      g_strstrip (portal->address);
                    }
                  portal->port = port;
                  portal->tpgt = tpgt;
                  target->portals = g_list_append (target->portals, portal);
                }
            }
        }
      else if (g_str_has_prefix (line, "\t\tIface Name: "))
        {
          if (portal == NULL)
            {
              g_warning ("Iface Name without a current portal");
            }
          else
            {
              iSCSIIface *iface;
              iface = g_new0 (iSCSIIface, 1);
              iface->name = g_strdup (line + sizeof "\t\tIface Name: " - 1);
              portal->ifaces = g_list_append (portal->ifaces, iface);
            }
        }
      else if (strlen (line) > 0)
        {
          g_warning ("Unexpected line `%s'", line);
        }

      g_free (line);
    }

 done_parsing:

  parsed_targets = g_list_sort (parsed_targets, (GCompareFunc) iscsi_target_compare);
  parsed_sources = g_list_sort (parsed_sources, (GCompareFunc) iscsi_source_compare);

  add_remove_targets (provider, parsed_targets);
  add_remove_sources (provider, parsed_sources);

  g_list_foreach (parsed_targets, (GFunc) iscsi_target_unref, NULL);
  g_list_free (parsed_targets);
  g_list_foreach (parsed_sources, (GFunc) iscsi_source_unref, NULL);
  g_list_free (parsed_sources);
  g_free (ia_out);
  g_free (ia_err);
}

static void
update_state (UDisksiSCSIProvider *provider)
{
  GList *l;
  for (l = provider->targets; l != NULL; l = l->next)
    {
      iSCSITarget *target = l->data;
      udisks_iscsi_target_set_connections (target->iface,
                                           portals_and_ifaces_to_gvariant (provider, target));
    }
}

/* ---------------------------------------------------------------------------------------------------- */

static gboolean
on_cool_off_timeout_cb (gpointer user_data)
{
  UDisksiSCSIProvider *provider = UDISKS_ISCSI_PROVIDER (user_data);

  udisks_info ("iscsi refresh..");
  load_and_process_iscsi (provider);
  provider->cool_off_timeout_id = 0;
  return FALSE;
}

static void
request_reload (UDisksiSCSIProvider *provider)
{
  /* coalesce many requests into one */
  if (provider->cool_off_timeout_id == 0)
    provider->cool_off_timeout_id = g_timeout_add (250, on_cool_off_timeout_cb, provider);
}

static void
on_file_monitor_changed (GFileMonitor     *monitor,
                         GFile            *file,
                         GFile            *other_file,
                         GFileMonitorEvent event_type,
                         gpointer          user_data)
{
  UDisksiSCSIProvider *provider = UDISKS_ISCSI_PROVIDER (user_data);
  udisks_info ("iscsi file monitor event..");
  request_reload (provider);
}

/* ---------------------------------------------------------------------------------------------------- */

typedef struct
{
  /* from iscsi_session */
  gchar *target_name;
  gchar *iface_name;
  gint tpgt;
  gchar *state;
  gchar *session_sysfs_path;

  /* from iscsi_connection */
  gchar *address;
  gint port;

  gchar *id;
  gchar *id_without_tpgt;
} Connection;

static void
connection_free (Connection *connection)
{
  g_free (connection->target_name);
  g_free (connection->iface_name);
  g_free (connection->state);
  g_free (connection->session_sysfs_path);
  g_free (connection->address);
  g_free (connection->id);
  g_free (connection->id_without_tpgt);
  g_free (connection);
}

/* ---------------------------------------------------------------------------------------------------- */

/* believe it or not, sometimes the kernel returns a sysfs attr with content "(null)" */
static gboolean
is_null (const gchar *str)
{
  return str == NULL || g_strcmp0 (str, "(null)") == 0;
}

static void
handle_iscsi_connection_uevent (UDisksiSCSIProvider *provider,
                                const gchar         *uevent,
                                GUdevDevice         *device)
{
  const gchar *sysfs_path;
  Connection *connection;

  sysfs_path = g_udev_device_get_sysfs_path (device);
  connection = g_hash_table_lookup (provider->sysfs_to_connection, sysfs_path);
  if (g_strcmp0 (uevent, "remove") == 0)
    {
      if (connection != NULL)
        {
          /* g_debug ("removed %s %s", sysfs_path, connection->id); */
          g_warn_if_fail (g_hash_table_remove (provider->id_to_connection, connection->id));
          g_warn_if_fail (g_hash_table_remove (provider->id_without_tpgt_to_connection, connection->id_without_tpgt));
          g_hash_table_remove (provider->sysfs_to_connection, sysfs_path);
        }
      else
        {
          g_warning ("no object for connection %s", sysfs_path);
        }
    }
  else
    {
      /* This is a bit sketchy and includes assumptions about what sysfs
       * currently looks like...
       */
      if (connection == NULL)
        {
          gchar *session_sysfs_dir;
          GDir *session_dir;
          gchar *session_sysfs_path;
          GUdevDevice *session_device;
          const gchar *name;

          session_sysfs_dir = NULL;
          session_dir = NULL;
          session_sysfs_path = NULL;
          session_device = NULL;

          session_sysfs_dir = g_strdup_printf ("%s/device/../iscsi_session", sysfs_path);
          if (!g_file_test (session_sysfs_dir, G_FILE_TEST_IS_DIR))
            goto skip_connection;
          session_dir = g_dir_open (session_sysfs_dir, 0, NULL);
          if (session_dir == NULL)
            goto skip_connection;
          while ((name = g_dir_read_name (session_dir)) != NULL)
            {
              gint session_num;
              if (sscanf (name, "session%d", &session_num) == 1)
                {
                  session_sysfs_path = g_strdup_printf ("%s/%s", session_sysfs_dir, name);
                  break;
                }
            }
          if (session_sysfs_path == NULL)
            goto skip_connection;
          session_device = g_udev_client_query_by_sysfs_path (provider->udev_client, session_sysfs_path);
          if (session_device == NULL)
            goto skip_connection;

          connection = g_new0 (Connection, 1);
          connection->target_name = g_strdup (g_udev_device_get_sysfs_attr (session_device, "targetname"));
          connection->iface_name = g_strdup (g_udev_device_get_sysfs_attr (session_device, "ifacename"));
          connection->tpgt = g_udev_device_get_sysfs_attr_as_int (session_device, "tpgt");
          connection->address = g_strdup (g_udev_device_get_sysfs_attr (device, "persistent_address"));
          connection->port = g_udev_device_get_sysfs_attr_as_int (device, "persistent_port");
          connection->session_sysfs_path = g_strdup (g_udev_device_get_sysfs_path (session_device));

          if (is_null (connection->target_name) ||
              is_null (connection->iface_name) ||
              is_null (connection->address) ||
              connection->port == 0)
            {
              udisks_warning ("Abandoning incomplete iscsi_connection object at %s"
                              " (target_name=%s)"
                              " (iface_name=%s)"
                              " (address=%s)"
                              " (port=%d)",
                              sysfs_path,
                              connection->target_name,
                              connection->iface_name,
                              connection->address,
                              connection->port);
              connection_free (connection);
              connection = NULL;
              goto skip_connection;
            }

          connection->id = g_strdup_printf ("%d,%s:%d,%s,%s",
                                            connection->tpgt,
                                            connection->address,
                                            connection->port,
                                            connection->iface_name,
                                            connection->target_name);
          connection->id_without_tpgt = g_strdup_printf ("%s:%d,%s,%s",
                                                         connection->address,
                                                         connection->port,
                                                         connection->iface_name,
                                                         connection->target_name);
          /* g_debug ("added %s %s", sysfs_path, connection->id); */
          g_hash_table_insert (provider->sysfs_to_connection, g_strdup (sysfs_path), connection);
          g_hash_table_insert (provider->id_to_connection, connection->id, connection);
          g_hash_table_insert (provider->id_without_tpgt_to_connection, connection->id_without_tpgt, connection);

        skip_connection:
          g_free (session_sysfs_dir);
          if (session_dir != NULL)
            g_dir_close (session_dir);
          g_free (session_sysfs_path);
          if (session_device != NULL)
            g_object_unref (session_device);
        }

      /* update the Connection object */
      if (connection != NULL)
        {
          GUdevDevice *session_device;
          session_device = g_udev_client_query_by_sysfs_path (provider->udev_client,
                                                              connection->session_sysfs_path);
          if (session_device != NULL)
            {
              g_free (connection->state);
              connection->state = g_strdup (g_udev_device_get_sysfs_attr (session_device, "state"));
              g_object_unref (session_device);
            }
          else
            {
              g_warning ("no session device for %s", connection->session_sysfs_path);
            }
        }
    }
}

static void
handle_scsi_target_uevent (UDisksiSCSIProvider *provider,
                           const gchar         *uevent,
                           GUdevDevice         *device)
{
  const gchar *sysfs_path;
  gchar *parent_sysfs_dir;
  GDir *parent_dir;
  gchar *connection_sysfs_path;
  GUdevDevice *connection_device;
  const gchar *name;
  gchar connection_canonical_sysfs_path[PATH_MAX];

  /* Also sketchy and also includes assumptions about what sysfs
   * currently looks like...
   */

  parent_sysfs_dir = NULL;
  parent_dir = NULL;
  connection_sysfs_path = NULL;
  connection_device = NULL;

  if (g_strcmp0 (uevent, "remove") == 0)
    goto skip;

  sysfs_path = g_udev_device_get_sysfs_path (device);

  parent_sysfs_dir = g_strdup_printf ("%s/..", sysfs_path);
  parent_dir = g_dir_open (parent_sysfs_dir, 0, NULL);
  if (parent_dir == NULL)
    goto skip;
  while ((name = g_dir_read_name (parent_dir)) != NULL)
    {
      gint connection_num;
      if (sscanf (name, "connection%d", &connection_num) == 1)
        {
          connection_sysfs_path = g_strdup_printf ("%s/%s/iscsi_connection/%s", parent_sysfs_dir, name, name);
          break;
        }
    }
  if (connection_sysfs_path == NULL)
    goto skip;
  if (realpath (connection_sysfs_path, connection_canonical_sysfs_path) == NULL)
    goto skip;
  connection_device = g_udev_client_query_by_sysfs_path (provider->udev_client, connection_canonical_sysfs_path);
  if (connection_device == NULL)
    goto skip;

  handle_iscsi_connection_uevent (provider, "change", connection_device);
  update_state (provider);

 skip:
  g_free (parent_sysfs_dir);
  if (parent_dir != NULL)
    g_dir_close (parent_dir);
  g_free (connection_sysfs_path);
  if (connection_device != NULL)
    g_object_unref (connection_device);
}

static void
connections_on_uevent (GUdevClient   *udev_client,
                       const gchar   *uevent,
                       GUdevDevice   *device,
                       gpointer       user_data)
{
  UDisksiSCSIProvider *provider = UDISKS_ISCSI_PROVIDER (user_data);
  const gchar *subsystem;
  const gchar *devtype;

  subsystem = g_udev_device_get_subsystem (device);
  devtype = g_udev_device_get_devtype (device);
  if (g_strcmp0 (subsystem, "iscsi_connection") == 0)
    {
      handle_iscsi_connection_uevent (provider, uevent, device);
      update_state (provider);
    }
  else if (g_strcmp0 (subsystem, "scsi") == 0 && g_strcmp0 (devtype, "scsi_target") == 0)
    {
      handle_scsi_target_uevent (provider, uevent, device);
    }
}

static void
connections_init (UDisksiSCSIProvider *provider)
{
  GList *devices;
  GList *l;

  provider->sysfs_to_connection = g_hash_table_new_full (g_str_hash, g_str_equal, g_free,
                                                         (GDestroyNotify) connection_free);
  provider->id_to_connection = g_hash_table_new (g_str_hash, g_str_equal);
  provider->id_without_tpgt_to_connection = g_hash_table_new (g_str_hash, g_str_equal);

  /* hotplug */
  g_signal_connect (provider->udev_client,
                    "uevent",
                    G_CALLBACK (connections_on_uevent),
                    provider);

  /* coldplug */
  devices = g_udev_client_query_by_subsystem (provider->udev_client, "iscsi_connection");
  for (l = devices; l != NULL; l = l->next)
    {
      GUdevDevice *device = G_UDEV_DEVICE (l->data);
      handle_iscsi_connection_uevent (provider, "add", device);
    }
  g_list_foreach (devices, (GFunc) g_object_unref, NULL);
  g_list_free (devices);
}

static void
connections_finalize (UDisksiSCSIProvider *provider)
{
  g_signal_handlers_disconnect_by_func (provider->udev_client,
                                        G_CALLBACK (connections_on_uevent),
                                        provider);
  g_hash_table_unref (provider->id_to_connection);
  g_hash_table_unref (provider->id_without_tpgt_to_connection);
  g_hash_table_unref (provider->sysfs_to_connection);
}

/* ---------------------------------------------------------------------------------------------------- */

static const gchar *
connections_get_state (UDisksiSCSIProvider *provider,
                       const gchar         *target_name,
                       gint                 tpgt,
                       const gchar         *portal_address,
                       gint                 portal_port,
                       const gchar         *iface_name,
                       gint                *out_tpgt)
{
  const gchar *ret;
  gchar *id;
  Connection *connection;

  ret = "";

  if (tpgt != -1)
    {
      id = g_strdup_printf ("%d,%s:%d,%s,%s",
                            tpgt,
                            portal_address,
                            portal_port,
                            iface_name,
                            target_name);
      connection = g_hash_table_lookup (provider->id_to_connection, id);
    }
  else
    {
      id = g_strdup_printf ("%s:%d,%s,%s",
                            portal_address,
                            portal_port,
                            iface_name,
                            target_name);
      connection = g_hash_table_lookup (provider->id_without_tpgt_to_connection, id);
    }

  if (connection != NULL)
    {
      ret = connection->state;
      if (out_tpgt != NULL)
        *out_tpgt = connection->tpgt;
    }

  g_free (id);
  return ret;
}


/* ---------------------------------------------------------------------------------------------------- */
