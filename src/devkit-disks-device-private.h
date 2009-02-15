/* -*- Mode: C; tab-width: 8; indent-tabs-mode: nil; c-basic-offset: 8 -*-
 *
 * Copyright (C) 2008 David Zeuthen <david@fubar.dk>
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

#ifndef __DEVKIT_DISKS_DEVICE_PRIVATE_H__
#define __DEVKIT_DISKS_DEVICE_PRIVATE_H__

#include <glib-object.h>
#include <polkit-dbus/polkit-dbus.h>

#include "devkit-disks-device.h"

G_BEGIN_DECLS

struct Job;
typedef struct Job Job;

#define SMART_DATA_STRUCT_TYPE (dbus_g_type_get_struct ("GValueArray",   \
                                                        G_TYPE_INT,      \
                                                        G_TYPE_STRING,   \
                                                        G_TYPE_INT,      \
                                                        G_TYPE_INT,      \
                                                        G_TYPE_INT,      \
                                                        G_TYPE_INT,      \
                                                        G_TYPE_STRING,   \
                                                        G_TYPE_INVALID))

#define HISTORICAL_SMART_DATA_STRUCT_TYPE (dbus_g_type_get_struct ("GValueArray",   \
                                                                   G_TYPE_UINT64, \
                                                                   G_TYPE_DOUBLE, \
                                                                   G_TYPE_UINT64, \
                                                                   G_TYPE_STRING, \
                                                                   G_TYPE_BOOLEAN, \
                                                                   dbus_g_type_get_collection ("GPtrArray", SMART_DATA_STRUCT_TYPE), \
                                                                   G_TYPE_INVALID))

#define LSOF_DATA_STRUCT_TYPE (dbus_g_type_get_struct ("GValueArray",   \
                                                       G_TYPE_UINT,     \
                                                       G_TYPE_UINT,     \
                                                       G_TYPE_STRING,   \
                                                       G_TYPE_INVALID))

struct DevkitDisksDevicePrivate
{
        DBusGConnection *system_bus_connection;
        DBusGProxy      *system_bus_proxy;
        DevkitDisksDaemon *daemon;
        DevkitDevice *d;

        Job *job;

        char *object_path;
        char *native_path;

        gboolean removed;

        gboolean job_in_progress;
        char *job_id;
        uid_t job_initiated_by_uid;
        gboolean job_is_cancellable;
        int job_num_tasks;
        int job_cur_task;
        char *job_cur_task_id;
        double job_cur_task_percentage;

        guint linux_md_poll_timeout_id;

        gboolean is_updated;

        struct {
                char *device_file;
                GPtrArray *device_file_by_id;
                GPtrArray *device_file_by_path;
                gboolean device_is_system_internal;
                gboolean device_is_partition;
                gboolean device_is_partition_table;
                gboolean device_is_removable;
                gboolean device_is_media_available;
                gboolean device_is_read_only;
                gboolean device_is_drive;
                gboolean device_is_optical_disc;
                gboolean device_is_luks;
                gboolean device_is_luks_cleartext;
                gboolean device_is_linux_md_component;
                gboolean device_is_linux_md;
                guint64 device_size;
                guint64 device_block_size;
                gboolean device_is_mounted;
                char *device_mount_path;
                uid_t device_mounted_by_uid;

                char *id_usage;
                char *id_type;
                char *id_version;
                char *id_uuid;
                char *id_label;

                char *partition_slave;
                char *partition_scheme;
                char *partition_type;
                char *partition_label;
                char *partition_uuid;
                GPtrArray *partition_flags;
                int partition_number;
                guint64 partition_offset;
                guint64 partition_size;

                char *partition_table_scheme;
                int partition_table_count;
                int partition_table_max_number;
                GArray *partition_table_offsets;
                GArray *partition_table_sizes;

                char *drive_vendor;
                char *drive_model;
                char *drive_revision;
                char *drive_serial;
                char *drive_connection_interface;
                guint drive_connection_speed;
                GPtrArray *drive_media_compatibility;
                char *drive_media;
                gboolean drive_is_media_ejectable;
                gboolean drive_requires_eject;

                gboolean optical_disc_is_recordable;
                gboolean optical_disc_is_rewritable;
                gboolean optical_disc_is_blank;
                gboolean optical_disc_is_appendable;
                gboolean optical_disc_is_closed;
                gboolean optical_disc_has_audio;
                guint optical_disc_num_tracks;
                guint optical_disc_num_sessions;

                char *luks_holder;

                char *luks_cleartext_slave;
                uid_t luks_cleartext_unlocked_by_uid;

                char *linux_md_component_level;
                int linux_md_component_num_raid_devices;
                char *linux_md_component_uuid;
                char *linux_md_component_name;
                char *linux_md_component_version;
                guint64 linux_md_component_update_time;
                guint64 linux_md_component_events;

                char *linux_md_level;
                int linux_md_num_raid_devices;
                char *linux_md_uuid;
                char *linux_md_name;
                char *linux_md_version;
                GPtrArray *linux_md_slaves;
                GPtrArray *linux_md_slaves_state;
                gboolean linux_md_is_degraded;
                char *linux_md_sync_action;
                double linux_md_sync_percentage;
                guint64 linux_md_sync_speed;

                /* the following properties are not (yet) exported */
                char *dm_name;
                GPtrArray *slaves_objpath;
                GPtrArray *holders_objpath;
        } info;

        /* We want S.M.A.R.T. to persist over change events */
        gboolean drive_smart_is_capable;
        gboolean drive_smart_is_enabled;
        guint64 drive_smart_time_collected;
        gboolean drive_smart_is_failing;
        double drive_smart_temperature;
        guint64 drive_smart_time_powered_on;
        char *drive_smart_last_self_test_result;
        GPtrArray *drive_smart_attributes;
};


G_END_DECLS

#endif /* __DEVKIT_DISKS_DEVICE_PRIVATE_H__ */
