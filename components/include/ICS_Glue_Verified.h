/*
 * ICS_Glue_Verified.h - F*-verified glue code for ICS gateway
 *
 * Generated from ICS.Glue.Complete.fst by KaRaMeL
 * Modified: Replaced krmllib.h with standard C headers for seL4/CAmkES integration
 *
 * SECURITY PROPERTY: forwarded ==> validated (mathematically proven in F*)
 *
 * Configuration values extracted from:
 *   - common.h:21       MAX_PAYLOAD_SIZE = 60000
 *   - common.h:22       MIN_PAYLOAD_SIZE = 1
 *   - camkes:57         ICS_BUFFER_SIZE = 65536
 *   - common.h struct   payload_length at offset 39
 *   - common.h struct   payload data at offset 41
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#ifndef ICS_Glue_Verified_H
#define ICS_Glue_Verified_H

#include <stdint.h>
#include <stdbool.h>

#ifdef __cplusplus
extern "C" {
#endif

/*
 * External validators (provided by EverParse)
 * These are implemented in modbus_policy_fstar.c and modbus_response_policy_fstar.c
 *
 * Note: The verified glue calls wrapper functions that adapt to actual EverParse API:
 *   - modbus_validate_with_policy() for requests
 *   - modbus_validate_response_with_policy() for responses
 */
extern uint8_t modbus_validate_with_policy(const uint8_t *payload, uint16_t payload_len);
extern uint8_t modbus_validate_response_with_policy(const uint8_t *payload, uint16_t payload_len);

/*
 * Result structure: (forwarded, result_code)
 *
 * VERIFIED PROPERTY: fst == true ==> snd == 0 (RESULT_OK)
 */
typedef struct {
    bool fst;       /* true = message forwarded, false = rejected */
    uint8_t snd;    /* validation result code */
} ICS_Glue_Result;

/* For compatibility with KaRaMeL naming */
typedef ICS_Glue_Result K___bool_uint8_t;

/*
 * Result codes (must match modbus_policy_fstar.h)
 */
#define ICS_GLUE_RESULT_OK           0
#define ICS_GLUE_RESULT_SYNTAX_ERROR 1
#define ICS_GLUE_RESULT_POLICY_REJECT 2
#define ICS_GLUE_RESULT_INVALID_FC   3
#define ICS_GLUE_RESULT_TOO_SHORT    4
#define ICS_GLUE_RESULT_TOO_LARGE    5
#define ICS_GLUE_RESULT_BOUNDS_ERROR 6

/*
 * Process inbound message (SCADA → PLC direction)
 *
 * Reads ICS_Message from in_dp, validates, copies to out_dp if valid.
 *
 * Parameters:
 *   in_dp  - Input dataport (ICS_BUFFER_SIZE bytes)
 *   out_dp - Output dataport (ICS_BUFFER_SIZE bytes)
 *
 * Returns:
 *   .fst = true:  Message validated and copied to out_dp
 *   .fst = false: Message rejected, out_dp unchanged
 *   .snd = result code
 *
 * VERIFIED PROPERTY: .fst == true ==> .snd == ICS_GLUE_RESULT_OK
 */
ICS_Glue_Result process_inbound(uint8_t *in_dp, uint8_t *out_dp);

/*
 * Process outbound message (PLC → SCADA direction)
 *
 * Same interface as process_inbound, but uses response validator.
 *
 * VERIFIED PROPERTY: .fst == true ==> .snd == ICS_GLUE_RESULT_OK
 */
ICS_Glue_Result process_outbound(uint8_t *in_dp, uint8_t *out_dp);

#ifdef __cplusplus
}
#endif

#endif /* ICS_Glue_Verified_H */
