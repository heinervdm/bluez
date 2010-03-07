/*
 *
 *  BlueZ - Bluetooth protocol stack for Linux
 *  telephony interface for Freesmartphone.org stack
 *
 *  Copyright (C) 2009-2010  Intel Corporation
 *  Copyright (C) 2006-2009  Nokia Corporation
 *  Copyright (C) 2004-2010  Marcel Holtmann <marcel@holtmann.org>
 *  Copyright (C) 2010       Felix Huber
 *
 *
 *  This program is free software; you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License as published by
 *  the Free Software Foundation; either version 2 of the License, or
 *  (at your option) any later version.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License
 *  along with this program; if not, write to the Free Software
 *  Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA  02110-1301  USA
 *
 */

#ifdef HAVE_CONFIG_H
#include <config.h>
#endif

#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <stdint.h>
#include <glib.h>
#include <dbus/dbus.h>
#include <gdbus.h>

#include "logging.h"
#include "telephony.h"

/* Mask bits for supported services */
#define NETWORK_MASK_GPRS_SUPPORT       0x01
#define NETWORK_MASK_COMPACT_GSM        0x02
#define NETWORK_MASK_UMTS               0x04
#define NETWORK_MASK_EGDGE              0x08
#define NETWORK_MASK_HSDPA_AVAIL        0x10
#define NETWORK_MASK_HSUPA_AVAIL        0x20

/* network get cell info: cell type */
#define NETWORK_UNKNOWN_CELL            0
#define NETWORK_GSM_CELL                1
#define NETWORK_WCDMA_CELL              2

enum net_registration_status {
	NETWORK_REG_STATUS_UNREGISTERED = 0x00,
	NETWORK_REG_STATUS_HOME,
	NETWORK_REG_STATUS_BUSY,
	NETWORK_REG_STATUS_DENIED,
	NETWORK_REG_STATUS_UNKOWN,
	NETWORK_REG_STATUS_ROAM,
};

enum network_types {
	NETWORK_GSM = 0,
	NETWORK_COMPACT_GSM,
	NETWORK_UMTS,
	NETWORK_EDGE,
	NETWORK_HSDPA,
	NETWORK_PSUPA,
	NETWORK_HSDPAHSUPA
};


struct voice_call {
	dbus_int32_t call_index;
	int status;
	gboolean originating;
	char *number;
};

static struct {
	void *telephony_device;
	int first;
	int last;
	int category;
} phonebook_info = {
	.telephony_device = NULL,
	.first = -1,
	.last = -1,
	.category = 0
};

#define NUM_CATEGORIES 7
char *fso_categories[NUM_CATEGORIES] = {"contacts", "emergency", "fixed",
					"dialed", "received", "missed", "own"
					};
char *gsm_categories[NUM_CATEGORIES] = {"\"SM\"",   "\"EN\"",    "\"FD\"",
					"\"DC\"", "\"RC\"",   "\"MC\"", "\"ON\""
					};
#define OWN_CATEGORY 6
#define SIM_CATEGORY 0

/* OM sends:
+CPBS: ("EN","BD","FD","DC","LD","RC","LR","MT","AD","SM","SD","MC","LM","AF","ON","UD")
"EN" SIM (or ME) emergency number
"FD" SIM fixed-dialing-phonebook
"LD" SIM last-dialing-phonebook
"BD" SIM barred-dialing phonebook
"SD" SIM service numbers
"DC" MT dialled calls list
"RC" MT received calls list
"LR" Last received numbers (nonstandard)
"MT" combined MT and SIM/UICC phonebook
"AD" Abbreviated dialing numbers (nonstandard)
"LM" Last missed numbers (nonstandard)
"AF" comb. of fixed and abbrev. dialing phonebook (nonstandard)
"MC" MT missed (unanswered received) calls list
"ON" active application in the UICC (GSM or USIM) or SIM card (or MT) own numbers (MSISDNs) list
"UD" User defined
*/

static DBusConnection *connection = NULL;
static char *last_dialed_number = NULL;
static GSList *calls = NULL;

#define FSO_BUS_NAME "org.freesmartphone.ogsmd"
#define FSO_MODEM_OBJ_PATH "/org/freesmartphone/GSM/Device"
#define FSO_NETWORKREG_INTERFACE "org.freesmartphone.GSM.Network"
#define FSO_GSMC_INTERFACE "org.freesmartphone.GSM.Call"
#define FSO_SIM_INTERFACE "org.freesmartphone.GSM.SIM"

static guint registration_watch = 0;
static guint voice_watch = 0;
static guint device_watch = 0;

/* HAL battery namespace key values */
static int battchg_cur = -1;    /* "battery.charge_level.current" */
static int battchg_last = -1;   /* "battery.charge_level.last_full" */
static int battchg_design = -1; /* "battery.charge_level.design" */

static struct {
	uint8_t status;         /* act  'GSM' */
	uint32_t cell_id;       /* cid  '51FD' */
	uint32_t operator_code; /* code '26203' */
	uint16_t lac;           /* lac  '233b' */
	char *mode;             /* mode 'automatic' */
	char *operator_name;    /* provider  'debitel' */
	char *registration;     /* registration 'home' */
	uint16_t signals_bar;   /* strength  '87' */
} net = {
	.status = NETWORK_REG_STATUS_UNREGISTERED,
	.cell_id = 0,
	.operator_code = 0,
	.lac = 0,
	.mode = NULL,
	.operator_name = NULL,
	.registration = NULL,
	.signals_bar = 0,
};

static const char *chld_str = "0,1,1x,2,2x,3,4";
static char *subscriber_number = NULL;

static gboolean events_enabled = FALSE;

/* Response and hold state
 * -1 = none
 *  0 = incoming call is put on hold in the AG
 *  1 = held incoming call is accepted in the AG
 *  2 = held incoming call is rejected in the AG
 */
static int response_and_hold = -1;

static struct indicator fso_indicators[] =
{
	{ "battchg",	"0-5",	5,	TRUE },
	{ "signal",	"0-5",	5,	TRUE },
	{ "service",	"0,1",	1,	TRUE },
	{ "call",	"0,1",	0,	TRUE },
	{ "callsetup",	"0-3",	0,	TRUE },
	{ "callheld",	"0-2",	0,	FALSE },
	{ "roam",	"0,1",	0,	TRUE },
	{ NULL }
};

static void vc_free(struct voice_call *vc)
{
	if (!vc)
		return;
	g_free(vc->number);
	g_free(vc);
}

static struct voice_call *find_vc(dbus_int32_t call_index)
{
	GSList *l;

	for (l = calls; l != NULL; l = l->next) {
		struct voice_call *vc = l->data;

		if (vc->call_index == call_index)
			return vc;
	}

	return NULL;
}

static struct voice_call *find_vc_with_status(int status)
{
	GSList *l;

	for (l = calls; l != NULL; l = l->next) {
		struct voice_call *vc = l->data;

		if (vc->status == status)
			return vc;
	}

	return NULL;
}

static gboolean iter_get_basic_args(DBusMessageIter *iter,
						int first_arg_type, ...)
{
	int type;
	va_list ap;

	va_start(ap, first_arg_type);

	for (type = first_arg_type; type != DBUS_TYPE_INVALID;
		type = va_arg(ap, int)) {
		void *value = va_arg(ap, void *);
		int real_type = dbus_message_iter_get_arg_type(iter);

		if (real_type != type) {
			error("iter_get_basic_args: expected %c but got %c",
				(char) type, (char) real_type);
			break;
		}

		dbus_message_iter_get_basic(iter, value);
		dbus_message_iter_next(iter);
	}

	va_end(ap);

	return type == DBUS_TYPE_INVALID ? TRUE : FALSE;
}

static int reply_check_error(DBusError *err, DBusMessage *reply)
{
	dbus_error_init(err);
	if (dbus_set_error_from_message(err, reply)) {
		error("fso replied with an error: %s, %s",
			err->name, err->message);
		dbus_error_free(err);
		return -1;
	}
	return 0;
}

static int find_category(char **phonebooks, const char *category)
{
	int i;
	for (i = 0; i < NUM_CATEGORIES; i++) {
		if (!strcmp(phonebooks[i], category))
			return i;
	}
	return -1;
}

void telephony_device_connected(void *telephony_device)
{
	debug("telephony-fso: device %p connected", telephony_device);
}

void telephony_device_disconnected(void *telephony_device)
{
	debug("telephony-fso: device %p disconnected", telephony_device);
	events_enabled = FALSE;
}

void telephony_event_reporting_req(void *telephony_device, int ind)
{
	events_enabled = ind == 1 ? TRUE : FALSE;

	telephony_event_reporting_rsp(telephony_device, CME_ERROR_NONE);
}

void telephony_response_and_hold_req(void *telephony_device, int rh)
{
	response_and_hold = rh;

	telephony_response_and_hold_ind(response_and_hold);

	telephony_response_and_hold_rsp(telephony_device, CME_ERROR_NONE);
}

void telephony_last_dialed_number_req(void *telephony_device)
{
	debug("telephony-fso: last dialed number request");

	if (last_dialed_number)
		telephony_dial_number_req(telephony_device, last_dialed_number);
	else
		telephony_last_dialed_number_rsp(telephony_device,
				CME_ERROR_NOT_ALLOWED);
}

static int send_method_call(const char *dest, const char *path,
				const char *interface, const char *method,
				DBusPendingCallNotifyFunction cb,
				void *user_data, int type, ...)
{
	DBusMessage *msg;
	DBusPendingCall *call;
	va_list args;

	msg = dbus_message_new_method_call(dest, path, interface, method);
	if (!msg) {
		error("Unable to allocate new D-Bus %s message", method);
		return -ENOMEM;
	}

	va_start(args, type);

	if (!dbus_message_append_args_valist(msg, type, args)) {
		dbus_message_unref(msg);
		va_end(args);
		return -EIO;
	}

	va_end(args);

	if (!cb) {
		g_dbus_send_message(connection, msg);
		return 0;
	}

	if (!dbus_connection_send_with_reply(connection, msg, &call, -1)) {
		error("Sending %s failed", method);
		dbus_message_unref(msg);
		return -EIO;
	}

	dbus_pending_call_set_notify(call, cb, user_data, NULL);
	dbus_pending_call_unref(call);
	dbus_message_unref(msg);

	return 0;
}

void telephony_terminate_call_req(void *telephony_device)
{
	struct voice_call *vc;
	int ret;

	if ((vc = find_vc_with_status(CALL_STATUS_ACTIVE))) {
	} else if ((vc = find_vc_with_status(CALL_STATUS_DIALING))) {
	} else if ((vc = find_vc_with_status(CALL_STATUS_INCOMING))) {
	}

	if (!vc) {
		error("in telephony_terminate_call_req, no active call");
		telephony_terminate_call_rsp(telephony_device,
					CME_ERROR_NOT_ALLOWED);
		return;
	}

	ret = send_method_call(FSO_BUS_NAME, FSO_MODEM_OBJ_PATH,
					FSO_GSMC_INTERFACE,
					"Release", NULL, NULL,
					DBUS_TYPE_INT32, &vc->call_index,
					DBUS_TYPE_INVALID);

	if (ret < 0) {
		telephony_terminate_call_rsp(telephony_device,
					CME_ERROR_AG_FAILURE);
	} else
		telephony_terminate_call_rsp(telephony_device, CME_ERROR_NONE);
}

void telephony_answer_call_req(void *telephony_device)
{
	int ret;
	struct voice_call *vc = find_vc_with_status(CALL_STATUS_INCOMING);

	if (!vc) {
		telephony_answer_call_rsp(telephony_device,
					CME_ERROR_NOT_ALLOWED);
		return;
	}

	ret = send_method_call(FSO_BUS_NAME, FSO_MODEM_OBJ_PATH,
                                        FSO_GSMC_INTERFACE,
					"Activate", NULL, NULL,
					DBUS_TYPE_INT32, &vc->call_index,
					DBUS_TYPE_INVALID);

	if (ret < 0) {
		telephony_answer_call_rsp(telephony_device,
					CME_ERROR_AG_FAILURE);
	} else
		telephony_answer_call_rsp(telephony_device, CME_ERROR_NONE);
}

void telephony_dial_number_req(void *telephony_device, const char *number)
{
	const char *clir, *call_type = "voice";
	int ret;

	debug("telephony-fso: dial request to %s", number);

#if 0
	if (!strncmp(number, "*31#", 4)) {
		number += 4;
		clir = "enabled";
	} else if (!strncmp(number, "#31#", 4)) {
		number += 4;
		clir =  "disabled";
	} else
		clir = "default";
#endif
	ret = send_method_call(FSO_BUS_NAME, FSO_MODEM_OBJ_PATH,
			FSO_GSMC_INTERFACE,
			"Initiate", NULL, NULL,
			DBUS_TYPE_STRING, &number,
			DBUS_TYPE_STRING, &call_type,
			DBUS_TYPE_INVALID);

	if (ret < 0)
		telephony_dial_number_rsp(telephony_device,
			CME_ERROR_AG_FAILURE);
	else
		telephony_dial_number_rsp(telephony_device, CME_ERROR_NONE);
}

void telephony_transmit_dtmf_req(void *telephony_device, char tone)
{
	char *tone_string;
	int ret;

	debug("telephony-fso: transmit dtmf: %c", tone);

	tone_string = g_strdup_printf("%c", tone);
	ret = send_method_call(FSO_BUS_NAME, FSO_MODEM_OBJ_PATH,
						FSO_GSMC_INTERFACE,
						"SendDtmf", NULL, NULL,
						DBUS_TYPE_STRING, &tone_string,
						DBUS_TYPE_INVALID);
	g_free(tone_string);

	if (ret < 0)
		telephony_transmit_dtmf_rsp(telephony_device,
			CME_ERROR_AG_FAILURE);
	else
		telephony_transmit_dtmf_rsp(telephony_device, CME_ERROR_NONE);
}

void telephony_subscriber_number_req(void *telephony_device)
{
	debug("telephony-fso: subscriber number request");

	if (subscriber_number)
		telephony_subscriber_number_ind(subscriber_number,
						NUMBER_TYPE_TELEPHONY,
						SUBSCRIBER_SERVICE_VOICE);
	telephony_subscriber_number_rsp(telephony_device, CME_ERROR_NONE);
}

void telephony_list_current_calls_req(void *telephony_device)
{
	GSList *l;
	int i;

	debug("telephony-fso: list current calls request");

	for (l = calls, i = 1; l != NULL; l = l->next, i++) {
		struct voice_call *vc = l->data;
		int direction;

		direction = vc->originating ?
				CALL_DIR_OUTGOING : CALL_DIR_INCOMING;

		telephony_list_current_call_ind(i, direction, vc->status,
					CALL_MODE_VOICE, CALL_MULTIPARTY_NO,
					vc->number, NUMBER_TYPE_TELEPHONY);
	}
	telephony_list_current_calls_rsp(telephony_device, CME_ERROR_NONE);
}

void telephony_operator_selection_req(void *telephony_device)
{
	debug("telephony-fso: operator selection request");

	telephony_operator_selection_ind(OPERATOR_MODE_AUTO,
				net.operator_name ? net.operator_name : "");
	telephony_operator_selection_rsp(telephony_device, CME_ERROR_NONE);
}

void telephony_call_hold_req(void *telephony_device, const char *cmd)
{
	debug("telephony-fso: got call hold request %s", cmd);
	telephony_call_hold_rsp(telephony_device, CME_ERROR_NONE);
}

void telephony_nr_and_ec_req(void *telephony_device, gboolean enable)
{
	debug("telephony-fso: got %s NR and EC request",
			enable ? "enable" : "disable");

	telephony_nr_and_ec_rsp(telephony_device, CME_ERROR_NONE);
}

void telephony_key_press_req(void *telephony_device, const char *keys)
{
	struct voice_call *vc;
	int err=0;
	char *cmd = NULL, *act="Activate", *rel="Release";

	debug("telephony-fso: got key press request for %s", keys);

	if (vc = find_vc_with_status(CALL_STATUS_INCOMING)) 
		cmd = act;
	else if (vc = find_vc_with_status(CALL_STATUS_ACTIVE)) 
		cmd = rel;
	else if (vc = find_vc_with_status(CALL_STATUS_DIALING)) 
		cmd = rel;

	if (cmd) {
		err = send_method_call(FSO_BUS_NAME, FSO_MODEM_OBJ_PATH,
					FSO_GSMC_INTERFACE,
					cmd, NULL, NULL,
					DBUS_TYPE_INT32, &vc->call_index,
					DBUS_TYPE_INVALID);
	}
	if (err < 0)
		telephony_key_press_rsp(telephony_device, CME_ERROR_AG_FAILURE);
	else
		telephony_key_press_rsp(telephony_device, CME_ERROR_NONE);

}


void telephony_voice_dial_req(void *telephony_device, gboolean enable)
{
	debug("telephony-fso: got %s voice dial request",
			enable ? "enable" : "disable");

	telephony_voice_dial_rsp(telephony_device, CME_ERROR_NOT_SUPPORTED);
}

static void retrieve_entry_reply(DBusPendingCall *call, void *user_data)
{
	DBusError err;
	DBusMessage *reply;
	const char *name, *number;
	char **number_type = user_data;

	reply = dbus_pending_call_steal_reply(call);

	if (reply_check_error(&err, reply))
		goto done;

	if (!dbus_message_get_args(reply, NULL,
				DBUS_TYPE_STRING, &name,
				DBUS_TYPE_STRING, &number,
				DBUS_TYPE_INVALID))
		goto done;

	if (number_type == &subscriber_number) {
		g_free(subscriber_number);
		subscriber_number = g_strdup(number);
	}

done:
	dbus_message_unref(reply);
}

static void retrieve_phonebook_reply(DBusPendingCall *call, void *user_data)
{
	DBusError err;
	DBusMessage *reply;
	DBusMessageIter iter, array;
	int ret;
	char * info;

	reply = dbus_pending_call_steal_reply(call);

	if (reply_check_error(&err, reply)) {
		ret = -1;
		goto done;
	}

	dbus_message_iter_init(reply, &iter);

	if (dbus_message_iter_get_arg_type(&iter) != DBUS_TYPE_ARRAY) {
		error("Unexpected signature in retrieve phonebook reply");
		ret = -1;
		goto done;
	}

	dbus_message_iter_recurse(&iter, &array);

	while (dbus_message_iter_get_arg_type(&array) != DBUS_TYPE_INVALID) {
		DBusMessageIter prop;
		const char *name, *number;
		int index;

		dbus_message_iter_recurse(&array, &prop);

		if (!iter_get_basic_args(&prop,
					DBUS_TYPE_INT32, &index,
					DBUS_TYPE_STRING, &name,
					DBUS_TYPE_STRING, &number,
					DBUS_TYPE_INVALID)) {
			error("Invalid phonebook entry data");
			break;
		}
		if ((index >= phonebook_info.first) &&
		    (index <= phonebook_info.last)) {
			info = g_strdup_printf("%d,\"%s\",,\"%s\"", index,
								number, name);
			telephony_phonebook_read_ind(
					phonebook_info.telephony_device, info);
			g_free(info);
		}
		dbus_message_iter_next(&array);
	}
	ret = 0;

done:
	dbus_message_unref(reply);
	if (ret)
		telephony_phonebook_read_rsp(phonebook_info.telephony_device,
							CME_ERROR_AG_FAILURE);
	else
		telephony_phonebook_read_rsp(phonebook_info.telephony_device,
							CME_ERROR_NONE);
}

static void get_phonebook_info_reply(DBusPendingCall *call, void *user_data)
{
	DBusError err;
	DBusMessage *reply;
	DBusMessageIter iter, iter_entry, array;
	int ret;
	int min_index = -1, max_index = -1;
	int number_length = -1, name_length = -1;
	char *info;
	const char *error_text =
			"**** Unexpected signature in get phonebook info reply";

	reply = dbus_pending_call_steal_reply(call);

	if (reply_check_error(&err, reply)) {
		ret = -1;
		goto done;
	}

	dbus_message_iter_init(reply, &iter);

	/* ARRAY -> ENTRY -> VARIANT*/
	if (dbus_message_iter_get_arg_type(&iter) != DBUS_TYPE_ARRAY) {
		error(error_text);
		ret = -1;
		goto done;
	}

	dbus_message_iter_recurse(&iter, &iter_entry);

	if (dbus_message_iter_get_arg_type(&iter_entry)
					!= DBUS_TYPE_DICT_ENTRY) {
		error(error_text);
		ret = -1;
		goto done;
	}

	while (dbus_message_iter_get_arg_type(&iter_entry)
						!= DBUS_TYPE_INVALID) {
		DBusMessageIter iter_property, sub;
		char *property;

		dbus_message_iter_recurse(&iter_entry, &iter_property);
		if (dbus_message_iter_get_arg_type(&iter_property)
					!= DBUS_TYPE_STRING) {
			error(error_text);
			ret = -1;
			goto done;
		}

		dbus_message_iter_get_basic(&iter_property, &property);

		dbus_message_iter_next(&iter_property);
		dbus_message_iter_recurse(&iter_property, &sub);

		if (g_str_equal(property, "min_index"))
			dbus_message_iter_get_basic(&sub, &min_index);
		else if (g_str_equal(property, "max_index"))
			dbus_message_iter_get_basic(&sub, &max_index);
		else if (g_str_equal(property, "number_length"))
			dbus_message_iter_get_basic(&sub, &number_length);
		else if (g_str_equal(property, "name_length"))
			dbus_message_iter_get_basic(&sub, &name_length);

		dbus_message_iter_next(&iter_entry);
	}

	info = g_strdup_printf("\"(%d-%d)\",%d,%d", min_index,max_index,
		(number_length != -1) ? number_length : 0,
		(name_length != -1) ? name_length : 0);

	telephony_phonebook_read_ind(phonebook_info.telephony_device, info);
	g_free(info);
	ret = 0;

done:
	dbus_message_unref(reply);
	if (ret)
		telephony_phonebook_read_rsp(phonebook_info.telephony_device,
							CME_ERROR_AG_FAILURE);
	else
		telephony_phonebook_read_rsp(phonebook_info.telephony_device,
							CME_ERROR_NONE);

}

static void get_phonebook_storage_info_reply(DBusPendingCall *call,
							void *user_data)
{
	DBusError err;
	DBusMessage *reply;
	int used, total;
	GString *gstr;
	char *str;

	reply = dbus_pending_call_steal_reply(call);

	if (reply_check_error(&err, reply))
		goto done;

	if (!dbus_message_get_args(reply, NULL, DBUS_TYPE_INT32, &used,
						DBUS_TYPE_INT32, &total,
						DBUS_TYPE_INVALID))
		goto done;

	gstr = g_string_new("");
	g_string_append_printf(gstr, "%s,%d,%d",
				gsm_categories[phonebook_info.category],
				used, total);
	str = g_string_free(gstr, FALSE);
	telephony_phonebook_storage_ind(phonebook_info.telephony_device, str);
	g_free(str);
	telephony_phonebook_storage_rsp(phonebook_info.telephony_device,
							CME_ERROR_NONE);

done:
	dbus_message_unref(reply);
}

static void list_phonebooks_reply(DBusPendingCall *call, void *user_data)
{
	DBusError err;
	DBusMessage *reply;
	DBusMessageIter iter, iter_entry, array;
	int ret;
	char **s, *str;
	int i, num_strings, index;
	GString *gstr;

	reply = dbus_pending_call_steal_reply(call);

	if (reply_check_error(&err, reply)) {
		ret = -1;
		goto done;
	}

	dbus_message_iter_init(reply, &iter);

	dbus_error_init(&err);

	if (!dbus_message_get_args(reply, &err,
		DBUS_TYPE_ARRAY, DBUS_TYPE_STRING, &s, &num_strings,
		DBUS_TYPE_INVALID)) {
		error("dbus_message_get_args replied with an error: %s, %s",
			err.name, err.message);
		dbus_error_free(&err);
		ret = -1;
		goto done;
	}

	gstr = g_string_new("(");
	for (i = 0; i < num_strings; i++) {
		index = find_category(fso_categories, s[i]);
		if (index == -1)
			continue;
		debug("GSM %d: %s", index, gsm_categories[index]);
		if (i == 0)
			g_string_append_printf(gstr, "%s",
							gsm_categories[index]);
		else
			g_string_append_printf(gstr, ",%s",
							gsm_categories[index]);
	}
	g_string_append(gstr, ")");
	str = g_string_free(gstr, FALSE);
	telephony_phonebook_storage_ind(phonebook_info.telephony_device, str);
	g_free(str);
	dbus_free_string_array(s);
	ret = 0;

done:
	dbus_message_unref(reply);
	if (ret)
		telephony_phonebook_read_rsp(phonebook_info.telephony_device,
							CME_ERROR_AG_FAILURE);
	else
		telephony_phonebook_read_rsp(phonebook_info.telephony_device,
							CME_ERROR_NONE);
}

void telephony_phonebook_storage_req(void *telephony_device,
					const char *storage, int AT_type)
{
	int ret = 0, index;

	debug("telephony-fso: got phonebook storage request %d", AT_type);

	phonebook_info.telephony_device = telephony_device;

	switch (AT_type) {
	case AT_TEST:      /* =? */
		ret = send_method_call(FSO_BUS_NAME, FSO_MODEM_OBJ_PATH,
						FSO_SIM_INTERFACE,
						"ListPhonebooks",
						list_phonebooks_reply, NULL,
						DBUS_TYPE_INVALID);
		break;
	case AT_READ:       /* ? */
		ret = send_method_call(FSO_BUS_NAME, FSO_MODEM_OBJ_PATH,
				FSO_SIM_INTERFACE,
				"GetPhonebookStorageInfo",
				get_phonebook_storage_info_reply, NULL,
				DBUS_TYPE_STRING,
				&fso_categories[phonebook_info.category],
				DBUS_TYPE_INVALID);
		break;
	case AT_SET:         /* = */
		debug("Phonebook request to be %s", storage);
		index = find_category(gsm_categories, storage);
		debug("Phonebook found at %d", index);
		if (index == -1)
			ret = -1;
		else {
			phonebook_info.category = index;
			telephony_phonebook_storage_rsp(telephony_device,
								CME_ERROR_NONE);
		}
		break;
	default:
		ret = -1;
	}

	if (ret < 0)
		telephony_phonebook_storage_rsp(telephony_device,
							CME_ERROR_AG_FAILURE);
}

void telephony_phonebook_read_req(void *telephony_device, const char *readindex,
								int AT_type)
{
	int size, ret=0;
	debug("telephony-fso: got pbook read request: %s", readindex);

	phonebook_info.telephony_device = telephony_device;

	switch (AT_type) {
	case AT_TEST:          /* =? */
		ret = send_method_call(FSO_BUS_NAME, FSO_MODEM_OBJ_PATH,
				FSO_SIM_INTERFACE,
				"GetPhonebookInfo",
				get_phonebook_info_reply, NULL,
				DBUS_TYPE_STRING,
				&fso_categories[phonebook_info.category],
				DBUS_TYPE_INVALID);
		break;

	case AT_READ:          /* ? */
		ret = -1;
		break;

	case AT_SET:            /* = */
		phonebook_info.first = -1, phonebook_info.last = -1;
		sscanf(readindex, "%d,%d", &phonebook_info.first,
							&phonebook_info.last);
		if (phonebook_info.first == -1)
			break;

		if (phonebook_info.last == -1)
			phonebook_info.last = phonebook_info.first;

		ret = send_method_call(FSO_BUS_NAME, FSO_MODEM_OBJ_PATH,
				FSO_SIM_INTERFACE,
				"RetrievePhonebook",
				retrieve_phonebook_reply, NULL,
				DBUS_TYPE_STRING,
				&fso_categories[phonebook_info.category],
				DBUS_TYPE_INT32, &phonebook_info.first,
				DBUS_TYPE_INT32, &phonebook_info.last,
				DBUS_TYPE_INVALID);
		break;

	default:
		ret = -1;
	}

	if (ret < 0)
		telephony_phonebook_read_rsp(telephony_device,
							CME_ERROR_AG_FAILURE);
}

static void parse_gsmcall_property(const char *property, DBusMessageIter sub,
							struct voice_call *vc)
{
	const char *direction, *peer, *reason, *auxstatus, *line;

	if (g_str_equal(property, "direction")) {
		dbus_message_iter_get_basic(&sub, &direction);
	} else if (g_str_equal(property, "peer")) {
		dbus_message_iter_get_basic(&sub, &peer);
		vc->number = g_strdup(peer);
	} else if (g_str_equal(property, "reason")) {
		dbus_message_iter_get_basic(&sub, &reason);
	} else if (g_str_equal(property, "auxstatus")) {
		dbus_message_iter_get_basic(&sub, &auxstatus);
	} else if (g_str_equal(property, "line")) {
		dbus_message_iter_get_basic(&sub, &line);
	}
}

static gboolean handle_gsmcall_property_changed(DBusConnection *conn,
						DBusMessage *msg, void *data)
{
	DBusMessageIter iter, iter_entry, array;
	const char *status;
	struct voice_call *vc;
	dbus_int32_t call_index;
	const char *error_text =
		"Unexpected signature in gsmcall PropertyChanged signal";

	dbus_message_iter_init(msg, &iter);

	if (dbus_message_iter_get_arg_type(&iter) != DBUS_TYPE_INT32) {
		error(error_text);
		return TRUE;
	}

	dbus_message_iter_get_basic(&iter, &call_index);
	dbus_message_iter_next(&iter);

	if (dbus_message_iter_get_arg_type(&iter) != DBUS_TYPE_STRING) {
		error(error_text);
		return TRUE;
	}

	dbus_message_iter_get_basic(&iter, &status);

	debug("**** gsmProp Changed id:%d status: %s", call_index, status);

	vc = find_vc(call_index);
	if (!vc) {
		vc = g_new0(struct voice_call, 1);
		vc->call_index = call_index;
		calls = g_slist_append(calls, vc);
	}

	dbus_message_iter_next(&iter);

	/* array -> entry -> sv */
	if (dbus_message_iter_get_arg_type(&iter) != DBUS_TYPE_ARRAY) {
		error(error_text);
		return TRUE;
	}

	dbus_message_iter_recurse(&iter, &iter_entry);

	if (dbus_message_iter_get_arg_type(&iter_entry)
						!= DBUS_TYPE_DICT_ENTRY) {
		error(error_text);
		return TRUE;
	}

	while (dbus_message_iter_get_arg_type(&iter_entry)
							!= DBUS_TYPE_INVALID) {
		DBusMessageIter iter_property, sub;
		char *property;

		dbus_message_iter_recurse(&iter_entry, &iter_property);
		if (dbus_message_iter_get_arg_type(&iter_property)
							!= DBUS_TYPE_STRING) {
			error(error_text);
			return TRUE;
		}

		dbus_message_iter_get_basic(&iter_property, &property);

		dbus_message_iter_next(&iter_property);
		dbus_message_iter_recurse(&iter_property, &sub);

		parse_gsmcall_property(property, sub, vc);

		dbus_message_iter_next(&iter_entry);
	}

	if (g_str_equal(status, "incoming")) {
		/* state change from waiting to incoming */
		vc->status = CALL_STATUS_INCOMING;
		vc->originating = FALSE;
		telephony_update_indicator(fso_indicators, "callsetup",
				EV_CALLSETUP_INCOMING);
		telephony_incoming_call_ind(vc->number, NUMBER_TYPE_TELEPHONY);
		debug("vc status is CALL_STATUS_INCOMING");
	} else if (g_str_equal(status, "outgoing")) {
		vc->status = CALL_STATUS_DIALING;
		vc->originating = TRUE;
		g_free(last_dialed_number);
		last_dialed_number = g_strdup(vc->number);
		telephony_update_indicator(fso_indicators, "callsetup",
						EV_CALLSETUP_OUTGOING);
	} else if (g_str_equal(status, "active")) {
		telephony_update_indicator(fso_indicators,
					"call", EV_CALL_ACTIVE);
		telephony_update_indicator(fso_indicators,
					"callsetup", EV_CALLSETUP_INACTIVE);
		if (vc->status == CALL_STATUS_INCOMING) {
			telephony_calling_stopped_ind();
		}
		vc->status = CALL_STATUS_ACTIVE;
		debug("vc status is CALL_STATUS_ACTIVE");
	} else if (g_str_equal(status, "held")) {
		vc->status = CALL_STATUS_HELD;
	} else if (g_str_equal(status, "release")) {
		printf("in disconnected case\n");
		if (vc->status == CALL_STATUS_ACTIVE)
			telephony_update_indicator(fso_indicators,
				"call", EV_CALL_INACTIVE);
		else
			telephony_update_indicator(fso_indicators,
				"callsetup", EV_CALLSETUP_INACTIVE);
		if (vc->status == CALL_STATUS_INCOMING)
			telephony_calling_stopped_ind();
		calls = g_slist_remove(calls, vc);
		vc_free(vc);
	}
	return TRUE;
}

static void parse_registration_property(const char *property,
							DBusMessageIter sub)
{
	const char *status, *operator;
	unsigned int signals_bar;

	if (g_str_equal(property, "registration")) {
		dbus_message_iter_get_basic(&sub, &status);
		debug("registration is %s", status);
		if (g_str_equal(status, "home")) {
			net.status = NETWORK_REG_STATUS_HOME;
			telephony_update_indicator(fso_indicators,
						"roam", EV_ROAM_INACTIVE);
			telephony_update_indicator(fso_indicators,
						"service", EV_SERVICE_PRESENT);
		} else if (g_str_equal(status, "roaming")) {
			net.status = NETWORK_REG_STATUS_ROAM;
			telephony_update_indicator(fso_indicators,
						"roam", EV_ROAM_ACTIVE);
			telephony_update_indicator(fso_indicators,
						"service", EV_SERVICE_PRESENT);
		} else {
			net.status = NETWORK_REG_STATUS_UNREGISTERED;
			telephony_update_indicator(fso_indicators,
						"roam", EV_ROAM_INACTIVE);
			telephony_update_indicator(fso_indicators,
						"service", EV_SERVICE_NONE);
		}
	} else if (g_str_equal(property, "provider")) {
		dbus_message_iter_get_basic(&sub, &operator);
		debug("Operator is %s", operator);
		g_free(net.operator_name);
		net.operator_name = g_strdup(operator);
	} else if (g_str_equal(property, "strength")) {
		dbus_message_iter_get_basic(&sub, &signals_bar);
		debug("SignalStrength is %d", signals_bar);
		net.signals_bar = signals_bar;
		telephony_update_indicator(fso_indicators, "signal",
						(signals_bar + 20) / 21);
	}
}

static gboolean handle_registration_property(DBusMessage *msg)
{
	DBusMessageIter iter, iter_entry;
	const char *property;

	dbus_message_iter_init(msg, &iter);

	/* ARRAY -> ENTRY -> VARIANT */
	if (dbus_message_iter_get_arg_type(&iter) != DBUS_TYPE_ARRAY) {
		error("**** Unexpected signature in GetProperties return");
		goto done;
	}

	dbus_message_iter_recurse(&iter, &iter_entry);

	if (dbus_message_iter_get_arg_type(&iter_entry)
					!= DBUS_TYPE_DICT_ENTRY) {
		error("**** Unexpected signature in GetProperties return");
		goto done;
	}

	while (dbus_message_iter_get_arg_type(&iter_entry)
					!= DBUS_TYPE_INVALID) {
		DBusMessageIter iter_property, sub;
		char *property;

		dbus_message_iter_recurse(&iter_entry, &iter_property);
		if (dbus_message_iter_get_arg_type(&iter_property)
					!= DBUS_TYPE_STRING) {
			error("Unexpected signature in GetProperties return");
			goto done;
		}

		dbus_message_iter_get_basic(&iter_property, &property);

		dbus_message_iter_next(&iter_property);
		dbus_message_iter_recurse(&iter_property, &sub);

		parse_registration_property(property, sub);

		dbus_message_iter_next(&iter_entry);
	}

done:
	return TRUE;
}


static void get_registration_reply(DBusPendingCall *call, void *user_data)
{
	DBusError err;
	DBusMessage *reply;
	DBusMessageIter iter, iter_entry;
	uint32_t features = AG_FEATURE_EC_ANDOR_NR |
				AG_FEATURE_REJECT_A_CALL |
				AG_FEATURE_ENHANCED_CALL_STATUS |
				AG_FEATURE_EXTENDED_ERROR_RESULT_CODES;

	reply = dbus_pending_call_steal_reply(call);

	if (reply_check_error(&err, reply)) {
		goto done;
	}

	handle_registration_property(reply);

	telephony_ready_ind(features, fso_indicators,
				response_and_hold, chld_str);

done:
	dbus_message_unref(reply);
}

static gboolean handle_registration_property_changed(DBusConnection *conn,
						DBusMessage *msg, void *data)
{
	return handle_registration_property(msg);
}

static void hal_battery_level_reply(DBusPendingCall *call, void *user_data)
{
	DBusMessage *reply;
	DBusError err;
	dbus_int32_t level;
	int *value = user_data;

	reply = dbus_pending_call_steal_reply(call);

	if (reply_check_error(&err, reply))
		goto done;

	dbus_message_get_args(reply, NULL,
				DBUS_TYPE_INT32, &level,
				DBUS_TYPE_INVALID);

	*value = (int) level;

	if (value == &battchg_last)
		debug("telephony-fso: battery.charge_level.last_full"
					" is %d", *value);
	else if (value == &battchg_design)
		debug("telephony-fso: battery.charge_level.design"
					" is %d", *value);
	else
		debug("telephony-fso: battery.charge_level.current"
					" is %d", *value);

	if ((battchg_design > 0 || battchg_last > 0) && battchg_cur >= 0) {
		int new, max;

		if (battchg_last > 0)
			max = battchg_last;
		else
			max = battchg_design;

		new = battchg_cur * 5 / max;

		telephony_update_indicator(fso_indicators, "battchg", new);
	}
done:
	dbus_message_unref(reply);
}

static void hal_get_integer(const char *path, const char *key, void *user_data)
{
	send_method_call("org.freedesktop.Hal", path,
			"org.freedesktop.Hal.Device",
			"GetPropertyInteger",
			hal_battery_level_reply, user_data,
			DBUS_TYPE_STRING, &key,
			DBUS_TYPE_INVALID);
}

static gboolean handle_hal_property_modified(DBusConnection *conn,
						DBusMessage *msg, void *data)
{
	const char *path;
	DBusMessageIter iter, array;
	dbus_int32_t num_changes;

	path = dbus_message_get_path(msg);

	dbus_message_iter_init(msg, &iter);

	if (dbus_message_iter_get_arg_type(&iter) != DBUS_TYPE_INT32) {
		error("Unexpected signature in hal PropertyModified signal");
		return TRUE;
	}

	dbus_message_iter_get_basic(&iter, &num_changes);
	dbus_message_iter_next(&iter);

	if (dbus_message_iter_get_arg_type(&iter) != DBUS_TYPE_ARRAY) {
		error("Unexpected signature in hal PropertyModified signal");
		return TRUE;
	}

	dbus_message_iter_recurse(&iter, &array);

	while (dbus_message_iter_get_arg_type(&array) != DBUS_TYPE_INVALID) {
		DBusMessageIter prop;
		const char *name;
		dbus_bool_t added, removed;

		dbus_message_iter_recurse(&array, &prop);

		if (!iter_get_basic_args(&prop,
					DBUS_TYPE_STRING, &name,
					DBUS_TYPE_BOOLEAN, &added,
					DBUS_TYPE_BOOLEAN, &removed,
					DBUS_TYPE_INVALID)) {
			error("Invalid hal PropertyModified parameters");
			break;
		}

		if (g_str_equal(name, "battery.charge_level.last_full"))
			hal_get_integer(path, name, &battchg_last);
		else if (g_str_equal(name, "battery.charge_level.current"))
			hal_get_integer(path, name, &battchg_cur);
		else if (g_str_equal(name, "battery.charge_level.design"))
			hal_get_integer(path, name, &battchg_design);

		dbus_message_iter_next(&array);
	}

	return TRUE;
}

static void hal_find_device_reply(DBusPendingCall *call, void *user_data)
{
	DBusMessage *reply;
	DBusError err;
	DBusMessageIter iter, sub;
	int type;
	const char *path;

	debug("begin of hal_find_device_reply()");
	reply = dbus_pending_call_steal_reply(call);


	if (reply_check_error(&err, reply)) {
		goto done;
	}

	dbus_message_iter_init(reply, &iter);

	if (dbus_message_iter_get_arg_type(&iter) != DBUS_TYPE_ARRAY) {
		error("Unexpected signature in hal_find_device_reply()");
		goto done;
	}

	dbus_message_iter_recurse(&iter, &sub);

	type = dbus_message_iter_get_arg_type(&sub);

	if (type != DBUS_TYPE_OBJECT_PATH && type != DBUS_TYPE_STRING) {
		error("No hal device with battery capability found");
		goto done;
	}

	dbus_message_iter_get_basic(&sub, &path);

	debug("telephony-fso: found battery device at %s", path);

	device_watch = g_dbus_add_signal_watch(connection, NULL, path,
					"org.freedesktop.Hal.Device",
					"PropertyModified",
					handle_hal_property_modified,
					NULL, NULL);

	hal_get_integer(path, "battery.charge_level.last_full", &battchg_last);
	hal_get_integer(path, "battery.charge_level.current", &battchg_cur);
	hal_get_integer(path, "battery.charge_level.design", &battchg_design);

done:
	dbus_message_unref(reply);
}

int telephony_init(void)
{
	const char *battery_cap = "battery";
	dbus_uint32_t first_index = 1;
	int ret;

	connection = dbus_bus_get(DBUS_BUS_SYSTEM, NULL);

	registration_watch = g_dbus_add_signal_watch(connection, NULL, NULL,
					FSO_NETWORKREG_INTERFACE,
					"Status",
					handle_registration_property_changed,
					NULL, NULL);

	voice_watch = g_dbus_add_signal_watch(connection, NULL, NULL,
					FSO_GSMC_INTERFACE,
					"CallStatus",
					handle_gsmcall_property_changed,
					NULL, NULL);

	ret = send_method_call(FSO_BUS_NAME, FSO_MODEM_OBJ_PATH,
			FSO_NETWORKREG_INTERFACE,
			"GetStatus", get_registration_reply,
			NULL, DBUS_TYPE_INVALID);

	if (ret < 0)
		return ret;

	ret = send_method_call("org.freedesktop.Hal",
				"/org/freedesktop/Hal/Manager",
				"org.freedesktop.Hal.Manager",
				"FindDeviceByCapability",
				hal_find_device_reply, NULL,
				DBUS_TYPE_STRING, &battery_cap,
				DBUS_TYPE_INVALID);
	if (ret < 0)
		return ret;

	ret = send_method_call(FSO_BUS_NAME, FSO_MODEM_OBJ_PATH,
						FSO_SIM_INTERFACE,
						"RetrieveEntry",
						retrieve_entry_reply,
						&subscriber_number,
						DBUS_TYPE_STRING,
						&fso_categories[OWN_CATEGORY],
						DBUS_TYPE_INT32, &first_index,
						DBUS_TYPE_INVALID);
	if (ret < 0)
		return ret;

	debug("telephony_init() successfully");

	return ret;
}

void telephony_exit(void)
{
	g_free(net.operator_name);
	g_free(last_dialed_number);
	g_free(subscriber_number);

	g_slist_foreach(calls, (GFunc) vc_free, NULL);
	g_slist_free(calls);
	calls = NULL;

	g_dbus_remove_watch(connection, registration_watch);
	g_dbus_remove_watch(connection, voice_watch);
	g_dbus_remove_watch(connection, device_watch);

	dbus_connection_unref(connection);
	connection = NULL;
}

