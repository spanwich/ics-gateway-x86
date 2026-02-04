(*
 * ICS.Glue.Spec - Standalone specification for verified glue code
 *
 * This is a STANDALONE F* module that doesn't depend on LowStar/KReMLin.
 * It specifies the security properties we want to verify.
 *
 * Can be verified with just F* (no KReMLin needed):
 *   fstar.exe ICS.Glue.Spec.fst
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)
module ICS.Glue.Spec

(* ============================================================
 * Constants
 * ============================================================ *)

let max_payload_size: nat = 1500

(* Validation result codes *)
type validation_result =
  | ResultOK
  | ResultSyntaxError
  | ResultPolicyReject
  | ResultInvalidFC
  | ResultTooShort

(* ============================================================
 * Abstract model of message and validation
 * ============================================================ *)

(* A message with a payload length *)
type message = {
  payload_length: nat;
}

(* Message is well-formed if length is within bounds *)
let well_formed (msg: message): bool =
  msg.payload_length <= max_payload_size

(* Abstract validator - models the EverParse/F* validator *)
assume val validate: msg:message{well_formed msg} -> validation_result

(* ============================================================
 * Process and forward function
 *
 * THIS IS THE SECURITY-CRITICAL SPECIFICATION
 *
 * Returns: (forwarded: bool, validation_passed: bool)
 * ============================================================ *)

(*
 * Specification of process_and_forward:
 *
 * Given an input message:
 * 1. If not well-formed: drop (forwarded = false)
 * 2. If validation fails: drop (forwarded = false)
 * 3. If validation passes: forward (forwarded = true)
 *
 * SECURITY PROPERTY (encoded in return type):
 *   forwarded = true  ==>  validation_result = ResultOK
 *)
let process_and_forward (msg: message): (bool * validation_result) =
  (* Step 1: Check well-formedness (bounds check) *)
  if not (well_formed msg) then
    (* Drop: not well-formed, return dummy result *)
    (false, ResultTooShort)
  else
    (* Step 2: Validate *)
    let result = validate msg in

    if result = ResultOK then
      (* Forward: validation passed *)
      (true, ResultOK)
    else
      (* Drop: validation failed *)
      (false, result)

(* ============================================================
 * Security theorem
 *
 * THE MAIN SECURITY PROPERTY WE VERIFY
 * ============================================================ *)

(*
 * THEOREM: Forward implies validated
 *
 * For any message:
 *   If process_and_forward returns (true, _), then validation passed.
 *
 * This is the core security guarantee.
 *)
let theorem_forward_implies_validated (msg: message)
    : Lemma
      (ensures (
        let (forwarded, result) = process_and_forward msg in
        forwarded ==> result = ResultOK
      ))
= ()  (* Proof: follows directly from the function definition *)

(*
 * THEOREM: Invalid messages are never forwarded
 *
 * If validation fails, the message is dropped.
 *)
let theorem_invalid_not_forwarded (msg: message{well_formed msg})
    : Lemma
      (requires validate msg <> ResultOK)
      (ensures (
        let (forwarded, _) = process_and_forward msg in
        not forwarded
      ))
= ()  (* Proof: the else branch doesn't forward *)

(*
 * THEOREM: Malformed messages are never forwarded
 *
 * If message is not well-formed, it is dropped.
 *)
let theorem_malformed_not_forwarded (msg: message{not (well_formed msg)})
    : Lemma
      (ensures (
        let (forwarded, _) = process_and_forward msg in
        not forwarded
      ))
= ()  (* Proof: first check catches malformed messages *)

(* ============================================================
 * Refinement: Connection to C implementation
 *
 * The C implementation must satisfy:
 *
 * 1. BOUNDS CHECK:
 *    if (payload_length > MAX_PAYLOAD_SIZE) return; // drop
 *
 *    This corresponds to: not (well_formed msg) ==> drop
 *
 * 2. VALIDATION:
 *    result = modbus_validate_with_policy(payload, len);
 *    if (result != FSTAR_RESULT_OK) return; // drop
 *
 *    This corresponds to: validate msg <> ResultOK ==> drop
 *
 * 3. FORWARD:
 *    memcpy(out_dp, msg, size);
 *    out_ntfy_emit();
 *
 *    This corresponds to: forwarded = true
 *
 * The F* proof ensures this logic is correct.
 * Code review ensures the C matches this logic.
 * ============================================================ *)

(* ============================================================
 * Bidirectional property (symmetric validation)
 *
 * Same property applies to both ICS_Inbound and ICS_Outbound
 * ============================================================ *)

(* Response validation uses same pattern *)
assume val validate_response: msg:message{well_formed msg} -> validation_result

let process_and_forward_response (msg: message): (bool * validation_result) =
  if not (well_formed msg) then
    (false, ResultTooShort)
  else
    let result = validate_response msg in
    if result = ResultOK then
      (true, ResultOK)
    else
      (false, result)

(* Same security property for responses *)
let theorem_response_forward_implies_validated (msg: message)
    : Lemma
      (ensures (
        let (forwarded, result) = process_and_forward_response msg in
        forwarded ==> result = ResultOK
      ))
= ()
