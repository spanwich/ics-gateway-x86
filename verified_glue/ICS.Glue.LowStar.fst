(*
 * ICS.Glue.LowStar - Low* verified glue code for automatic C extraction
 *
 * This module uses Low* (machine integers, buffers) for clean C extraction.
 * Verified security property: forward ==> validated
 *
 * Build:
 *   fstar.exe --include $KRML_HOME/krmllib ICS.Glue.LowStar.fst
 *
 * Extract:
 *   krml -skip-compilation -skip-linking -tmpdir extracted ICS.Glue.LowStar.fst
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)
module ICS.Glue.LowStar

open FStar.HyperStack.ST
open FStar.UInt8
open FStar.UInt16
open FStar.UInt32

module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module B = LowStar.Buffer
module HS = FStar.HyperStack

(* ============================================================
 * Constants - machine integers
 * ============================================================ *)

inline_for_extraction noextract
let max_payload_size_u32: U32.t = 1500ul

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

(* ============================================================
 * External validator (provided by EverParse)
 *
 * This is the F*-verified Modbus parser.
 * We assume its specification here.
 * ============================================================ *)

(* External request validator *)
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

(* External response validator *)
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
 * Core validation function
 *
 * SECURITY PROPERTY (in return type):
 *   fst result = true  ==>  snd result = result_ok
 * ============================================================ *)

(*
 * Validate request and return (forwarded, validation_result)
 *
 * Control flow:
 * 1. Bounds check: if len > MAX_PAYLOAD_SIZE, return (false, too_short)
 * 2. Validate: call EverParse validator
 * 3. If OK: return (true, ok)
 * 4. Else: return (false, error_code)
 *)
val validate_and_decide_request:
  payload: B.buffer U8.t ->
  len: U32.t ->
  Stack (bool & U8.t)
    (requires fun h ->
      B.live h payload /\
      U32.v len <= B.length payload)
    (ensures fun h0 (forwarded, result) h1 ->
      B.modifies B.loc_none h0 h1 /\
      (* SECURITY PROPERTY: forward implies validated *)
      (forwarded ==> result = result_ok))

let validate_and_decide_request payload len =
  (* Step 1: Bounds check *)
  if U32.gt len max_payload_size_u32 then
    (false, result_too_short)
  else begin
    (* Step 2: Call validator *)
    let result = modbus_validate_request payload len in

    (* Step 3: Decide based on result *)
    if result = result_ok then
      (true, result_ok)
    else
      (false, result)
  end

(*
 * Validate response (symmetric to request)
 *)
val validate_and_decide_response:
  payload: B.buffer U8.t ->
  len: U32.t ->
  Stack (bool & U8.t)
    (requires fun h ->
      B.live h payload /\
      U32.v len <= B.length payload)
    (ensures fun h0 (forwarded, result) h1 ->
      B.modifies B.loc_none h0 h1 /\
      (* SECURITY PROPERTY: forward implies validated *)
      (forwarded ==> result = result_ok))

let validate_and_decide_response payload len =
  if U32.gt len max_payload_size_u32 then
    (false, result_too_short)
  else begin
    let result = modbus_validate_response payload len in
    if result = result_ok then
      (true, result_ok)
    else
      (false, result)
  end

(* ============================================================
 * Full process function with buffer copy
 *
 * This models the complete glue code:
 * 1. Validate
 * 2. If valid, copy to output buffer
 * ============================================================ *)

(*
 * Process request: validate and copy if valid
 *
 * Returns (forwarded, validation_result)
 * SECURITY PROPERTY: forwarded = true ==> result = result_ok
 *)
val process_request:
  in_buf: B.buffer U8.t ->
  out_buf: B.buffer U8.t ->
  len: U32.t ->
  Stack (bool & U8.t)
    (requires fun h ->
      B.live h in_buf /\
      B.live h out_buf /\
      B.disjoint in_buf out_buf /\
      U32.v len <= B.length in_buf /\
      U32.v len <= B.length out_buf)
    (ensures fun h0 (forwarded, result) h1 ->
      (* Memory modification depends on forwarding decision *)
      (if forwarded then
        B.modifies (B.loc_buffer out_buf) h0 h1
       else
        B.modifies B.loc_none h0 h1) /\
      (* SECURITY PROPERTY: forward implies validated *)
      (forwarded ==> result = result_ok))

let process_request in_buf out_buf len =
  let (forwarded, result) = validate_and_decide_request in_buf len in

  if forwarded then begin
    (* Copy validated data to output *)
    B.blit in_buf 0ul out_buf 0ul len;
    (true, result)
  end
  else
    (false, result)

(*
 * Process response: validate and copy if valid (symmetric)
 *)
val process_response:
  in_buf: B.buffer U8.t ->
  out_buf: B.buffer U8.t ->
  len: U32.t ->
  Stack (bool & U8.t)
    (requires fun h ->
      B.live h in_buf /\
      B.live h out_buf /\
      B.disjoint in_buf out_buf /\
      U32.v len <= B.length in_buf /\
      U32.v len <= B.length out_buf)
    (ensures fun h0 (forwarded, result) h1 ->
      (if forwarded then
        B.modifies (B.loc_buffer out_buf) h0 h1
       else
        B.modifies B.loc_none h0 h1) /\
      (forwarded ==> result = result_ok))

let process_response in_buf out_buf len =
  let (forwarded, result) = validate_and_decide_response in_buf len in

  if forwarded then begin
    B.blit in_buf 0ul out_buf 0ul len;
    (true, result)
  end
  else
    (false, result)
