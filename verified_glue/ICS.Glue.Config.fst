(*
 * ICS.Glue.Config - Configuration constants extracted from CAmkES/C headers
 *
 * TRACEABILITY: These values are extracted from actual system configuration
 * to ensure the verified code matches the deployed system.
 *
 * Source files:
 *   - components/include/common.h
 *   - ics_gateway_x86.camkes
 *
 * IMPORTANT: If you modify the source configuration, regenerate this file
 * or manually update to maintain consistency.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)
module ICS.Glue.Config

open FStar.UInt8
open FStar.UInt16
open FStar.UInt32

module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32

(* ============================================================
 * Constants from common.h
 * Source: components/include/common.h lines 21-23
 * ============================================================ *)

(* MAX_PAYLOAD_SIZE = 60000 (common.h:21) *)
inline_for_extraction noextract
let max_payload_size: U32.t = 60000ul

(* MIN_PAYLOAD_SIZE = 1 (common.h:22) *)
inline_for_extraction noextract
let min_payload_size: U32.t = 1ul

(* DATAPORT_SIZE = 65536 (common.h:23) *)
inline_for_extraction noextract
let dataport_size: U32.t = 65536ul

(* ============================================================
 * Constants from ics_gateway_x86.camkes
 * Source: ics_gateway_x86.camkes line 57
 * ============================================================ *)

(* ICS_BUFFER_SIZE = 65536 (ics_gateway_x86.camkes:57) *)
inline_for_extraction noextract
let ics_buffer_size: U32.t = 65536ul

(* ============================================================
 * Validation result codes
 * Must match modbus_policy_fstar.h
 * ============================================================ *)

inline_for_extraction noextract
let result_ok: U8.t = 0uy

inline_for_extraction noextract
let result_syntax_error: U8.t = 1uy

inline_for_extraction noextract
let result_policy_reject: U8.t = 2uy

inline_for_extraction noextract
let result_invalid_fc: U8.t = 3uy

inline_for_extraction noextract
let result_too_short: U8.t = 4uy

inline_for_extraction noextract
let result_too_large: U8.t = 5uy

(* ============================================================
 * Structure sizes (computed from common.h structures)
 *
 * FrameMetadata layout (packed):
 *   session_id:      4 bytes (uint32_t)
 *   dst_mac:         6 bytes
 *   src_mac:         6 bytes
 *   ethertype:       2 bytes (uint16_t)
 *   vlan_id:         2 bytes (uint16_t)
 *   vlan_priority:   1 byte  (uint8_t)
 *   ip_protocol:     1 byte  (uint8_t)
 *   src_ip:          4 bytes (uint32_t)
 *   dst_ip:          4 bytes (uint32_t)
 *   src_port:        2 bytes (uint16_t)
 *   dst_port:        2 bytes (uint16_t)
 *   payload_offset:  2 bytes (uint16_t)
 *   payload_length:  2 bytes (uint16_t)
 *   flags:           1 byte  (bitfield)
 *   -----------------------------------
 *   Total:          39 bytes
 *
 * ICS_Message layout (packed):
 *   metadata:        39 bytes (FrameMetadata)
 *   payload_length:   2 bytes (uint16_t)
 *   payload:      60000 bytes (uint8_t[MAX_PAYLOAD_SIZE])
 *   -----------------------------------
 *   Total:        60041 bytes
 * ============================================================ *)

inline_for_extraction noextract
let frame_metadata_size: U32.t = 39ul

inline_for_extraction noextract
let ics_message_header_size: U32.t = 41ul  (* metadata + payload_length field *)

inline_for_extraction noextract
let ics_message_max_size: U32.t = 60041ul  (* header + MAX_PAYLOAD_SIZE *)

(* Offset of payload_length field within ICS_Message *)
inline_for_extraction noextract
let payload_length_offset: U32.t = 39ul

(* ============================================================
 * Verification lemmas for configuration consistency
 * ============================================================ *)

(* Verify that dataport can hold maximum message *)
let config_consistency_lemma () : Lemma
  (U32.v ics_buffer_size >= U32.v ics_message_max_size) = ()

(* Verify buffer size matches dataport *)
let buffer_dataport_match_lemma () : Lemma
  (U32.v ics_buffer_size = U32.v dataport_size) = ()
