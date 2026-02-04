/*
 * ICS_Glue_Inbound.c - F*-verified glue code for ICS_Inbound component
 *
 * Extracted from ICS.Glue.Complete.fst
 * SECURITY PROPERTY: forwarded ==> validated (mathematically proven)
 *
 * This file only includes the inbound (request) validation path.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include "ICS_Glue_Verified.h"
#include <string.h>

/* Configuration constants (extracted from CAmkES/C config) */
#define MAX_PAYLOAD_SIZE    60000U   /* common.h:21 */
#define MIN_PAYLOAD_SIZE    1U       /* common.h:22 */
#define DATAPORT_SIZE       65536U   /* camkes:57 */
#define PAYLOAD_LEN_OFFSET  39U      /* common.h struct */
#define PAYLOAD_DATA_OFFSET 41U      /* common.h struct */

/* Result codes */
#define RESULT_OK           0U
#define RESULT_TOO_SHORT    4U
#define RESULT_TOO_LARGE    5U
#define RESULT_BOUNDS_ERROR 6U

/* Read uint16 little-endian from buffer */
static uint16_t read_u16_le(uint8_t *buf, uint32_t offset)
{
    uint8_t lo = buf[offset];
    uint8_t hi = buf[offset + 1U];
    return (uint16_t)((uint32_t)lo + ((uint32_t)hi << 8U));
}

/* Validate request payload */
static ICS_Glue_Result validate_request(uint8_t *payload, uint32_t len)
{
    if (len == 0U)
        return (ICS_Glue_Result){ .fst = false, .snd = RESULT_TOO_SHORT };

    if (len < MIN_PAYLOAD_SIZE)
        return (ICS_Glue_Result){ .fst = false, .snd = RESULT_TOO_SHORT };

    if (len > MAX_PAYLOAD_SIZE)
        return (ICS_Glue_Result){ .fst = false, .snd = RESULT_TOO_LARGE };

    uint8_t result = modbus_validate_with_policy(payload, (uint16_t)len);

    if (result == RESULT_OK)
        return (ICS_Glue_Result){ .fst = true, .snd = RESULT_OK };
    else
        return (ICS_Glue_Result){ .fst = false, .snd = result };
}

/*
 * Process inbound message (SCADA → PLC)
 * VERIFIED PROPERTY: .fst == true ==> .snd == RESULT_OK
 */
ICS_Glue_Result process_inbound(uint8_t *in_dp, uint8_t *out_dp)
{
    uint16_t payload_len_u16 = read_u16_le(in_dp, PAYLOAD_LEN_OFFSET);
    uint32_t payload_len = (uint32_t)payload_len_u16;

    if (PAYLOAD_DATA_OFFSET + payload_len > DATAPORT_SIZE)
        return (ICS_Glue_Result){ .fst = false, .snd = RESULT_BOUNDS_ERROR };

    uint8_t *payload_ptr = in_dp + PAYLOAD_DATA_OFFSET;
    ICS_Glue_Result scrut = validate_request(payload_ptr, payload_len);

    if (scrut.fst) {
        uint32_t copy_len = PAYLOAD_DATA_OFFSET + payload_len;
        memcpy(out_dp, in_dp, copy_len);
        return (ICS_Glue_Result){ .fst = true, .snd = scrut.snd };
    }

    return (ICS_Glue_Result){ .fst = false, .snd = scrut.snd };
}
