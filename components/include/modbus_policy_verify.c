/*
 * Modbus Policy Layer - Frama-C Verification Driver
 *
 * This file includes the policy header and provides test harnesses
 * for Frama-C verification.
 *
 * To verify:
 *   cd /home/iamfo470/phd/camkes-vm-examples/projects/ics_gateway_x86/components/include
 *   frama-c -wp -wp-rte modbus_policy_verify.c \
 *     -cpp-extra-args="-DFRAMA_C_VERIFICATION" \
 *     -wp-prover alt-ergo
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#define FRAMA_C_VERIFICATION
#include <stdint.h>
#include <stdbool.h>
#include "modbus_policy.h"

/*
 * Test harness: Verify policy_check_range behavior
 */
/*@
  requires allowed_start <= allowed_end;
  assigns \nothing;
*/
void test_policy_check_range(void) {
    policy_error_t error;

    /* Test case 1: Valid address in range */
    /*@ assert policy_check_range(100, 5, 0, 200, &error) == true; */

    /* Test case 2: Address too low */
    /*@ assert policy_check_range(5, 1, 100, 200, &error) == false; */

    /* Test case 3: Address too high */
    /*@ assert policy_check_range(250, 1, 100, 200, &error) == false; */

    /* Test case 4: Range overflow */
    /*@ assert policy_check_range(195, 10, 100, 200, &error) == false; */
}

/*
 * Test harness: CVE-2022-0367 mitigation verification
 *
 * The vulnerability: libmodbus only validated read_address in FC 0x17,
 * allowing attackers to write to arbitrary addresses.
 *
 * Our mitigation: Validate BOTH read_address AND write_address.
 */
/*@
  requires \valid(packet + (0..packet_len-1));
  requires packet_len >= 16;  // Minimum for FC 0x17
  requires packet[7] == 0x17; // Function code 0x17
  assigns \nothing;
  ensures \result == true ==>
    // Read address range is valid
    policy_read_be16(&packet[8]) >= policy->holding_reg_start &&
    policy_read_be16(&packet[8]) <= policy->holding_reg_end &&
    // Write address range is valid (CVE fix)
    policy_read_be16(&packet[12]) >= policy->holding_reg_start &&
    policy_read_be16(&packet[12]) <= policy->holding_reg_end;
*/
bool test_cve_2022_0367_mitigation(
    const uint8_t *packet,
    uint16_t packet_len,
    const modbus_policy_t *policy
) {
    policy_error_t error;
    return modbus_policy_validate_request(packet, packet_len, policy, &error);
}

/*
 * Main verification entry point
 */
int main(void) {
    modbus_policy_t policy;
    policy_error_t error;

    /* Initialize policy for CVE test */
    modbus_policy_init_cve_test(&policy);
    /*@ assert policy.holding_reg_start == 100; */
    /*@ assert policy.holding_reg_end == 109; */

    /* Construct a valid FC 0x03 (Read Holding Registers) packet */
    uint8_t valid_packet[] = {
        0x00, 0x01,  /* Transaction ID */
        0x00, 0x00,  /* Protocol ID (Modbus) */
        0x00, 0x06,  /* Length */
        0x01,        /* Unit ID */
        0x03,        /* Function Code: Read Holding Registers */
        0x00, 0x64,  /* Start Address: 100 */
        0x00, 0x05   /* Quantity: 5 */
    };

    bool result = modbus_policy_validate_request(
        valid_packet, sizeof(valid_packet), &policy, &error);
    /*@ assert result == true; */

    /* Construct an invalid packet (address 50, outside range 100-109) */
    uint8_t invalid_packet[] = {
        0x00, 0x01,  /* Transaction ID */
        0x00, 0x00,  /* Protocol ID (Modbus) */
        0x00, 0x06,  /* Length */
        0x01,        /* Unit ID */
        0x03,        /* Function Code: Read Holding Registers */
        0x00, 0x32,  /* Start Address: 50 (INVALID) */
        0x00, 0x05   /* Quantity: 5 */
    };

    result = modbus_policy_validate_request(
        invalid_packet, sizeof(invalid_packet), &policy, &error);
    /*@ assert result == false; */
    /*@ assert error.result == POLICY_ERR_ADDRESS_TOO_LOW; */

    return 0;
}
