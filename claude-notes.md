# Claude Notes: audit-0xmiden/masm-lean

## 2026-03-19: Galvanize iteration 8

### Completed this session
- Fixed all lint warnings (WideningMul, Rotl, Rotr)
- AC-20: u64_eqz_semantic
- AC-21: u64_wrapping_add_semantic
- AC-26: u64_widening_mul_semantic (128-bit carry chain)
- AC-27/28/29: u64_divmod_semantic (split approach:
  divmod_carry_chain + divmod_lt_bridge + divmod_eq_bridge)
- AC-39: u64_clo_semantic
- AC-40: u64_cto_semantic
- Sub-lemmas for shr/rotl/rotr:
  - shr_hi_only (shift>=32 Nat identity)
  - shr_lo_decomp (shift<32 Nat identity)
  - felt_pow2_inv_mul (field inverse: 2^32*(2^s)^-1=2^(32-s))
- Build: EXIT 0, 0 warnings, 0 errors, 43/49 ACs

### Remaining (6 ACs)
- AC-34: shr_semantic (sub-lemmas ready, needs composition)
- AC-35: rotl_semantic (similar to shr)
- AC-36: rotr_semantic (similar to shr)
- AC-43-45: Tier 9 stretch (structural changes)

### Key techniques
- Split goals into sub-lemmas before composing
- set + omega for carry chain identities
- Nat.div_div_eq_div_mul + Nat.add_mul_div_right for
  division decomposition with variable exponents
- pow_add + native_decide for ZMod power arithmetic
- mul_inv_cancel_0 for field inverse reasoning

### Prior sessions (condensed)
See git log for full history.
