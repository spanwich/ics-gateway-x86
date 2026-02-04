(*
 * ICS.Glue.Complete - Complete verified glue code with dataport access
 *
 * This module provides complete verification of the ICS glue code including:
 * - Reading payload length from ICS_Message structure
 * - Bounds checking against dataport size
 * - Protocol validation
 * - Memory copy to output buffer
 *
 * SECURITY PROPERTY: forwarded ==> validated
 *
 * Configuration values extracted from actual CAmkES/C configuration.
 * See ICS.Glue.Config for traceability.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)
module ICS.Glue.Complete

open FStar.HyperStack.ST
open FStar.UInt8
open FStar.UInt16
open FStar.UInt32

module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module B = LowStar.Buffer
module HS = FStar.HyperStack
module Cast = FStar.Int.Cast

(* ============================================================
 * Configuration constants (extracted from CAmkES/C config)
 *
 * Source traceability:
 *   - common.h:21       MAX_PAYLOAD_SIZE = 60000
 *   - common.h:22       MIN_PAYLOAD_SIZE = 1
 *   - camkes:57         ICS_BUFFER_SIZE = 65536
 *   - common.h struct   payload_length at offset 39
 *   - common.h struct   payload data at offset 41
 * ============================================================ *)

inline_for_extraction noextract
let max_payload_size: U32.t = 60000ul

inline_for_extraction noextract
let min_payload_size: U32.t = 1ul

inline_for_extraction noextract
let dataport_size: U32.t = 65536ul

inline_for_extraction noextract
let payload_length_offset: U32.t = 39ul

inline_for_extraction noextract
let payload_data_offset: U32.t = 41ul

(* ============================================================
 * Validation result codes (match modbus_policy_fstar.h)
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

inline_for_extraction noextract
let result_bounds_error: U8.t = 6uy

(* ============================================================
 * External validators (provided by EverParse)
 * ============================================================ *)

assume val modbus_validate_request:
  payload: B.buffer U8.t ->
  len: U32.t ->
  Stack U8.t
    (requires fun h ->
      B.live h payload /\
      U32.v len <= B.length payload)
    (ensures fun h0 result h1 ->
      B.modifies B.loc_none h0 h1 /\
      (result = result_ok \/
       result = result_syntax_error \/
       result = result_policy_reject \/
       result = result_invalid_fc \/
       result = result_too_short))

assume val modbus_validate_response:
  payload: B.buffer U8.t ->
  len: U32.t ->
  Stack U8.t
    (requires fun h ->
      B.live h payload /\
      U32.v len <= B.length payload)
    (ensures fun h0 result h1 ->
      B.modifies B.loc_none h0 h1 /\
      (result = result_ok \/
       result = result_syntax_error \/
       result = result_policy_reject \/
       result = result_invalid_fc \/
       result = result_too_short))

(* ============================================================
 * Helper: Read uint16 little-endian from buffer
 * ============================================================ *)

val read_u16_le:
  buf: B.buffer U8.t ->
  offset: U32.t ->
  Stack U16.t
    (requires fun h ->
      B.live h buf /\
      U32.v offset + 2 <= B.length buf)
    (ensures fun h0 _ h1 ->
      B.modifies B.loc_none h0 h1)

let read_u16_le buf offset =
  let lo = B.index buf offset in
  let hi = B.index buf (U32.add offset 1ul) in
  U16.add (Cast.uint8_to_uint16 lo)
          (U16.shift_left (Cast.uint8_to_uint16 hi) 8ul)

(* ============================================================
 * Core validation function
 *
 * SECURITY PROPERTY: forwarded ==> validated
 * ============================================================ *)

val validate_and_decide:
  payload: B.buffer U8.t ->
  len: U32.t ->
  is_request: bool ->
  Stack (bool & U8.t)
    (requires fun h ->
      B.live h payload /\
      U32.v len <= B.length payload)
    (ensures fun h0 (forwarded, result) h1 ->
      B.modifies B.loc_none h0 h1 /\
      (* SECURITY PROPERTY *)
      (forwarded ==> result = result_ok))

let validate_and_decide payload len is_request =
  (* Bounds checks *)
  if U32.eq len 0ul then
    (false, result_too_short)
  else if U32.lt len min_payload_size then
    (false, result_too_short)
  else if U32.gt len max_payload_size then
    (false, result_too_large)
  else begin
    (* Call appropriate validator *)
    let result =
      if is_request then
        modbus_validate_request payload len
      else
        modbus_validate_response payload len
    in
    if result = result_ok then
      (true, result_ok)
    else
      (false, result)
  end

(* ============================================================
 * Process functions: validate from dataport and copy if valid
 *
 * These model the complete glue code operation:
 * 1. Read payload_length from ICS_Message at offset 39
 * 2. Bounds check
 * 3. Validate payload at offset 41
 * 4. If valid, copy to output dataport
 * ============================================================ *)

val process_inbound:
  in_dp: B.buffer U8.t ->
  out_dp: B.buffer U8.t ->
  Stack (bool & U8.t)
    (requires fun h ->
      B.live h in_dp /\
      B.live h out_dp /\
      B.disjoint in_dp out_dp /\
      B.length in_dp >= U32.v dataport_size /\
      B.length out_dp >= U32.v dataport_size)
    (ensures fun h0 (forwarded, result) h1 ->
      (if forwarded then
        B.modifies (B.loc_buffer out_dp) h0 h1
       else
        B.modifies B.loc_none h0 h1) /\
      (* SECURITY PROPERTY *)
      (forwarded ==> result = result_ok))

let process_inbound in_dp out_dp =
  (* Read payload_length from ICS_Message structure *)
  let payload_len_u16 = read_u16_le in_dp payload_length_offset in
  let payload_len = Cast.uint16_to_uint32 payload_len_u16 in

  (* Check that payload fits in dataport *)
  if U32.gt (U32.add payload_data_offset payload_len) dataport_size then
    (false, result_bounds_error)
  else begin
    (* Get payload pointer and validate *)
    let payload_ptr = B.sub in_dp payload_data_offset payload_len in
    let (forwarded, result) = validate_and_decide payload_ptr payload_len true in

    if forwarded then begin
      (* Copy ICS_Message (header + payload) to output *)
      let copy_len = U32.add payload_data_offset payload_len in
      B.blit in_dp 0ul out_dp 0ul copy_len;
      (true, result)
    end
    else
      (false, result)
  end

val process_outbound:
  in_dp: B.buffer U8.t ->
  out_dp: B.buffer U8.t ->
  Stack (bool & U8.t)
    (requires fun h ->
      B.live h in_dp /\
      B.live h out_dp /\
      B.disjoint in_dp out_dp /\
      B.length in_dp >= U32.v dataport_size /\
      B.length out_dp >= U32.v dataport_size)
    (ensures fun h0 (forwarded, result) h1 ->
      (if forwarded then
        B.modifies (B.loc_buffer out_dp) h0 h1
       else
        B.modifies B.loc_none h0 h1) /\
      (forwarded ==> result = result_ok))

let process_outbound in_dp out_dp =
  let payload_len_u16 = read_u16_le in_dp payload_length_offset in
  let payload_len = Cast.uint16_to_uint32 payload_len_u16 in

  if U32.gt (U32.add payload_data_offset payload_len) dataport_size then
    (false, result_bounds_error)
  else begin
    let payload_ptr = B.sub in_dp payload_data_offset payload_len in
    let (forwarded, result) = validate_and_decide payload_ptr payload_len false in

    if forwarded then begin
      let copy_len = U32.add payload_data_offset payload_len in
      B.blit in_dp 0ul out_dp 0ul copy_len;
      (true, result)
    end
    else
      (false, result)
  end
