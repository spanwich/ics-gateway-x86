(*
 * ICS.Glue.Types - Type definitions for verified glue code
 *
 * Defines the ICS_Message structure and constants matching the C definitions.
 * These must match exactly with common.h.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)
module ICS.Glue.Types

open FStar.UInt8
open FStar.UInt16
open FStar.UInt32

module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32

(* ============================================================
 * Constants - must match common.h
 * ============================================================ *)

let max_payload_size: U32.t = 1500ul
let frame_metadata_size: U32.t = 48ul   (* sizeof(FrameMetadata) *)
let payload_length_size: U32.t = 2ul    (* sizeof(uint16_t) *)
let header_size: U32.t = U32.add frame_metadata_size payload_length_size

(* Offset of payload_length field in ICS_Message *)
let payload_length_offset: U32.t = frame_metadata_size

(* Offset of payload field in ICS_Message *)
let payload_offset: U32.t = header_size

(* Maximum size of ICS_Message *)
let max_message_size: U32.t = U32.add header_size max_payload_size

(* ============================================================
 * Validation result codes - must match modbus_policy_fstar.h
 * ============================================================ *)

let fstar_result_ok: U8.t = 0uy
let fstar_result_syntax_error: U8.t = 1uy
let fstar_result_policy_reject: U8.t = 2uy
let fstar_result_invalid_fc: U8.t = 3uy
let fstar_result_too_short: U8.t = 4uy

(* Response validation codes - must match modbus_response_policy_fstar.h *)
let fstar_response_ok: U8.t = 0uy
let fstar_response_syntax_error: U8.t = 1uy
let fstar_response_policy_reject: U8.t = 2uy
let fstar_response_invalid_fc: U8.t = 3uy
let fstar_response_too_short: U8.t = 4uy
let fstar_response_invalid_exception: U8.t = 5uy
