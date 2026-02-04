# Verified Glue Code for ICS Gateway

## Overview

This directory contains **F*-verified glue code** for the ICS Gateway validation components.
The glue code bridges CAmkES infrastructure with EverParse-verified Modbus validators.

### Security Property (Formally Verified)

```
∀ message. forwarded(message) ⟹ validated(message)
```

**In plain English**: Any message that reaches the output MUST have passed the F*-verified validator. No bypass is possible.

## Architecture

```
┌─────────────────────────────────────────────────────────────────┐
│                    ICS_Inbound Component                        │
│                                                                 │
│  ┌──────────────────────────────────────────────────────────┐  │
│  │           Verified Glue (this code)                      │  │
│  │  ┌────────────────┐    ┌─────────────────────────────┐  │  │
│  │  │ CAmkES Interface│───▶│ F* Validator (EverParse)   │  │  │
│  │  │ (assumed)      │    │ (verified)                  │  │  │
│  │  │ - in_dp        │◀───│                             │  │  │
│  │  │ - out_dp       │    │ modbus_validate_with_policy │  │  │
│  │  │ - notifications│    └─────────────────────────────┘  │  │
│  │  └────────────────┘                                      │  │
│  │                     │                                    │  │
│  │      F* proves: forward ⟹ validated                     │  │
│  └──────────────────────────────────────────────────────────┘  │
└─────────────────────────────────────────────────────────────────┘
```

## Files

| File | Purpose |
|------|---------|
| `ICS.Glue.Types.fst` | Type definitions, constants (must match C headers) |
| `ICS.Glue.CAmkES.fsti` | CAmkES interface specification (trusted assumptions) |
| `ICS.Glue.Inbound.fst` | Verified glue for inbound (request) validation |
| `ICS.Glue.Outbound.fst` | Verified glue for outbound (response) validation |
| `Makefile` | Build system for verification and extraction |

## Trust Boundaries

### What We Verify (F* Proof)

1. **Control flow**: Validator is always called before forwarding
2. **Result handling**: Only `FSTAR_RESULT_OK` leads to forwarding
3. **Bounds checking**: Payload length checked before buffer access
4. **Memory safety**: No buffer overflows in glue code

### What We Assume (Trusted)

1. **CAmkES runtime**: `in_dp`, `out_dp`, notifications work correctly
2. **seL4 kernel**: Capability system enforces isolation
3. **EverParse validator**: `modbus_validate_with_policy` is correct
4. **C compiler**: Extracted C matches F* semantics
5. **Hardware**: MMU, memory barriers work as specified

## Setup Instructions

### Prerequisites

```bash
# Install opam (OCaml package manager) if not present
sudo apt-get install opam

# Initialize opam (if first time)
opam init
eval $(opam env)
```

### Install F* and KReMLin

```bash
# Install F* (verification) and Karamel/KReMLin (C extraction)
cd /home/iamfo470/phd/camkes-vm-examples/projects/ics_gateway_x86/verified_glue
make install-fstar

# Update environment
eval $(opam env)

# Verify installation
make info
```

### Verify the Code

```bash
# Run F* verification (type-checking + proof obligations)
make verify

# Expected output:
# === Verifying F* modules ===
# Verified module: ICS.Glue.Types
# Verified module: ICS.Glue.CAmkES
# Verified module: ICS.Glue.Inbound
# Verified module: ICS.Glue.Outbound
# === Verification successful ===
```

### Extract to C

```bash
# Generate verified C code
make extract

# Output in extracted/ directory:
# - ICS_Glue_Inbound.c
# - ICS_Glue_Inbound.h
# - ICS_Glue_Outbound.c
# - ICS_Glue_Outbound.h
```

## Integration with CAmkES

After extraction, the generated C files replace the current glue code:

1. **Replace current implementation**:
   ```
   components/ICS_Inbound/ICS_Inbound.c → extracted/ICS_Glue_Inbound.c
   components/ICS_Outbound/ICS_Outbound.c → extracted/ICS_Glue_Outbound.c
   ```

2. **Add CAmkES stubs**: The extracted code calls assumed functions.
   Create `camkes_stubs.c` implementing:
   - `read_payload_length()`
   - `get_payload_ptr()`
   - `memory_barrier()`

3. **Update CMakeLists.txt**: Link extracted code instead of current.

## Verification Details

### Security Property Encoding

The key security property is encoded in the `ensures` clause:

```fstar
val process_and_forward: unit -> Stack unit
  (requires fun h -> ...)
  (ensures fun h0 _ h1 ->
    (* If output was modified, validation passed *)
    (modifies (B.loc_buffer out_dp) h0 h1 ==>
      modbus_validate_with_policy payload len == fstar_result_ok))
```

F*'s type system ensures this property holds for ALL executions.

### What F* Checks

1. **Exhaustive path analysis**: Every code path is analyzed
2. **Refinement types**: Values constrained by types (e.g., `len <= MAX`)
3. **Pre/post conditions**: Function contracts are verified
4. **Memory safety**: Buffer accesses are bounds-checked
5. **Termination**: (Optional) Loops terminate

### Proof Obligations

When you run `make verify`, F* checks:

- `process_and_forward` meets its specification
- All buffer accesses are within bounds
- Validator result is correctly handled
- Forward only happens after validation

If verification fails, F* reports which obligation couldn't be proven.

## Comparison with Frama-C Approach

| Aspect | F* (this approach) | Frama-C |
|--------|-------------------|---------|
| Language | Write in F*, extract to C | Annotate existing C |
| Proof style | Dependent types, refinements | Hoare logic, WP |
| Unified with EverParse | ✅ Same framework | ❌ Different tool |
| Learning curve | Steeper | Moderate |
| Extraction | Auto-generated C | Use existing C |
| Composability | Excellent | Good |

## Known Limitations

1. **CAmkES interface is assumed**: We can't verify CAmkES-generated code
2. **Infinite loop**: `run()` doesn't terminate (intentional for embedded)
3. **Concurrency**: Single-threaded model; no interrupt handling
4. **Struct layout**: Must manually match C struct offsets

## Future Work

1. **Full composition**: Prove end-to-end with EverParse validators
2. **CAmkES modeling**: More precise model of CAmkES semantics
3. **Concurrency**: Model interrupt handlers if needed
4. **Hardware abstraction**: Model memory barriers more precisely

## References

- [F* Tutorial](https://www.fstar-lang.org/tutorial/)
- [Low* for Verified C](https://fstarlang.github.io/lowstar/html/)
- [EverParse Documentation](https://project-everest.github.io/everparse/)
- [KReMLin/Karamel](https://github.com/FStarLang/karamel)
