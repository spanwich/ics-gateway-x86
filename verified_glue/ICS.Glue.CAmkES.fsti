(*
 * ICS.Glue.CAmkES - Interface specification for CAmkES runtime
 *
 * This module specifies the interface to CAmkES-generated functions.
 * These are ASSUMED correct - we trust seL4/CAmkES runtime.
 *
 * The specifications define:
 * - Dataport buffers (shared memory regions)
 * - Notification primitives (wait/emit)
 * - Memory semantics
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)
module ICS.Glue.CAmkES

open FStar.HyperStack.ST
open LowStar.Buffer
open LowStar.Modifies

module B = LowStar.Buffer
module HS = FStar.HyperStack
module U8 = FStar.UInt8
module U32 = FStar.UInt32

open ICS.Glue.Types

(* ============================================================
 * Dataport buffers
 *
 * CAmkES generates these as global pointers to shared memory.
 * We model them as buffers with fixed size.
 * ============================================================ *)

(* Input dataport - read from previous component *)
val in_dp: B.buffer U8.t

(* Output dataport - write to next component *)
val out_dp: B.buffer U8.t

(* Dataport properties *)
val in_dp_length: unit -> Lemma (B.length in_dp >= U32.v max_message_size)
val out_dp_length: unit -> Lemma (B.length out_dp >= U32.v max_message_size)
val dataports_disjoint: unit -> Lemma (B.disjoint in_dp out_dp)

(* ============================================================
 * Notification primitives
 *
 * CAmkES generates these for inter-component signaling.
 * They do not modify memory buffers, only kernel state.
 * ============================================================ *)

(* Wait for notification from previous component *)
val in_ntfy_wait: unit -> Stack unit
  (requires fun h -> True)
  (ensures fun h0 _ h1 ->
    (* Memory unchanged - only kernel scheduling state changes *)
    modifies loc_none h0 h1)

(* Emit notification to next component *)
val out_ntfy_emit: unit -> Stack unit
  (requires fun h -> True)
  (ensures fun h0 _ h1 ->
    (* Memory unchanged - only kernel signaling state changes *)
    modifies loc_none h0 h1)

(* ============================================================
 * Memory barrier
 *
 * Ensures memory writes are visible before notification.
 * Required for correct shared memory semantics on SMP.
 * ============================================================ *)

val memory_barrier: unit -> Stack unit
  (requires fun h -> True)
  (ensures fun h0 _ h1 ->
    (* No logical memory change, but enforces ordering *)
    modifies loc_none h0 h1)

(* ============================================================
 * Helper functions for reading message fields
 * ============================================================ *)

(* Read payload_length from message buffer *)
val read_payload_length:
  buf: B.buffer U8.t ->
  Stack U16.t
    (requires fun h ->
      B.live h buf /\
      B.length buf >= U32.v header_size)
    (ensures fun h0 len h1 ->
      h0 == h1 /\
      U16.v len <= U16.v (UInt16.uint_to_t (U32.v max_payload_size)))

(* Get pointer to payload within message buffer *)
val get_payload_ptr:
  buf: B.buffer U8.t ->
  Stack (B.buffer U8.t)
    (requires fun h ->
      B.live h buf /\
      B.length buf >= U32.v max_message_size)
    (ensures fun h0 payload h1 ->
      h0 == h1 /\
      B.live h1 payload /\
      B.length payload >= U32.v max_payload_size /\
      (* Payload is within the original buffer *)
      B.loc_includes (B.loc_buffer buf) (B.loc_buffer payload))
