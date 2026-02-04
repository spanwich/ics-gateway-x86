/*
 * ICS_Outbound - Minimal Verified Component
 *
 * This component uses F*-verified glue code for all security-critical operations.
 * Only CAmkES boilerplate and control queue forwarding remain unverified.
 *
 * VERIFIED CODE: ICS_Glue_Complete.c (extracted from ICS.Glue.Complete.fst)
 * SECURITY PROPERTY: forwarded ==> validated (mathematically proven)
 *
 * Unverified code in this file:
 *   - CAmkES notification handling (trusted - part of CAmkES TCB)
 *   - Control queue forwarding (not security-critical)
 *   - Policy initialization (happens once at startup)
 *
 * Lines of code: ~50 (down from ~305)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <camkes.h>
#include <string.h>
#include <stdint.h>
#include "common.h"
#include "ICS_Glue_Verified.h"
#include "modbus_response_policy_fstar.h"

/* Required by common.h */
uint64_t global_timestamp_counter = 0;

/*
 * Process message using verified glue code
 *
 * The core validation logic (bounds check, validator call, memcpy)
 * is in process_outbound() which is extracted from verified F* code.
 */
static void process_message(void) {
    /* Call verified glue code */
    K___bool_uint8_t result = process_outbound((uint8_t *)in_dp, (uint8_t *)out_dp);

    if (result.fst) {
        /* Message validated and copied by verified code */
        /* Forward control queue (not security-critical) */
        OutboundDataport *in_dataport = (OutboundDataport *)in_dp;
        OutboundDataport *out_dataport = (OutboundDataport *)out_dp;
        memcpy(&out_dataport->error_queue, &in_dataport->error_queue,
               sizeof(struct control_queue));

        __sync_synchronize();
        out_ntfy_emit();
    }
    /* If result.fst == false, message was rejected - no action needed */
}

/*
 * Notification handler
 */
void in_ntfy_handle(void) {
    process_message();
}

/*
 * Component initialization
 */
void pre_init(void) {
    /* Initialize policy for F* response validators */
    fstar_response_policy_init_cve_test();
}

int run(void) {
    while (1) {
        in_ntfy_wait();
        in_ntfy_handle();
    }
    return 0;
}
