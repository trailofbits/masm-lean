import MidenLean.AIR.ExtField
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
/-!
# Reduced Auxiliary Values

Transcription of `ProcessorAir::reduced_aux_values` from
`audit-miden-vm/air/src/lib.rs`.

This is the final algebraic check the STARK verifier performs on the
auxiliary trace columns. It is NOT a polynomial constraint — it is a
deterministic computation on the committed final aux column values,
the verifier challenges, and the public inputs.

The verifier accepts iff `prod = 1` and `sum = 0` in GF(p²).

## Bus identity

The running-product columns accumulate `responses / requests` at each row.
Columns whose requests and responses fully cancel end at 1. Columns with
public-input-dependent boundary terms end at known non-unity values that
are corrected by multiplying with message encodings derived from public inputs.
-/

namespace MidenLean.AIR.ReducedAux

open MidenLean
open scoped BigOperators

-- ============================================================================
-- Constants
-- ============================================================================

/-- Maximum number of elements in a bus message encoding. -/
def MAX_MESSAGE_WIDTH : Nat := 16

/-- LOGPRECOMPILE opcode = 0b0101_1110 = 94. -/
def LOG_PRECOMPILE_LABEL : Felt := Felt.ofNat 94

/-- Kernel ROM init label = 0b101111 + 1 = 48. -/
def KERNEL_PROC_INIT_LABEL : Felt := Felt.ofNat 48

/-- WORD_SIZE = 4 -/
def WORD_SIZE : Nat := 4

-- Public value layout: [program_hash(4), stack_inputs(16), stack_outputs(16), transcript_state(4)]
def PV_PROGRAM_HASH : Nat := 0
def PV_TRANSCRIPT_STATE : Nat := 36  -- 40 - 4

-- ============================================================================
-- Challenges (precomputed verifier randomness)
-- ============================================================================

/-- Verifier challenges: alpha and beta powers for bus message encoding.
    `encode(elems) = alpha + sum(beta^i * elems[i])` -/
structure Challenges where
  alpha : QuadFelt
  /-- Precomputed powers: beta_powers[i] = beta^i -/
  beta_powers : Fin MAX_MESSAGE_WIDTH → QuadFelt

/-- Build challenges from alpha and beta. -/
def Challenges.new (alpha beta : QuadFelt) : Challenges where
  alpha := alpha
  beta_powers := fun i =>
    -- beta_powers[i] = beta^i
    let rec go : Nat → QuadFelt
      | 0 => QuadFelt.one
      | n + 1 => go n * beta
    go i.val

/-- Encode a list of base-field elements as alpha + sum(beta^i * elems[i]). -/
def Challenges.encode (c : Challenges) (elems : List Felt) : QuadFelt :=
  let rec go (acc : QuadFelt) (i : Nat) : List Felt → QuadFelt
    | [] => acc
    | e :: rest =>
      let term := if h : i < MAX_MESSAGE_WIDTH then
        c.beta_powers ⟨i, h⟩ * QuadFelt.ofFelt e
      else QuadFelt.zero
      go (acc + term) (i + 1) rest
  go c.alpha 0 elems

-- ============================================================================
-- Public input types
-- ============================================================================

/-- A 4-element word (program hash, transcript state). -/
abbrev Word := Fin 4 → Felt

/-- Public inputs for the verifier. -/
structure PublicInputs where
  /-- All public values as a flat array (length 40). -/
  values : Fin 40 → Felt
  /-- Kernel procedure digests (variable-length, each is 4 Felts). -/
  kernel_digests : List Word

def PublicInputs.programHash (pi : PublicInputs) : Word :=
  fun i => pi.values ⟨0 + i.val, by omega⟩  -- PV_PROGRAM_HASH = 0

def PublicInputs.transcriptState (pi : PublicInputs) : Word :=
  fun i => pi.values ⟨36 + i.val, by omega⟩  -- PV_TRANSCRIPT_STATE = 36

-- ============================================================================
-- Message encodings
-- ============================================================================

/-- Program hash message for the block hash table bus. -/
def programHashMessage (c : Challenges) (ph : Word) : QuadFelt :=
  c.encode [0, ph 0, ph 1, ph 2, ph 3, 0, 0]

/-- Default (zero) transcript state message. -/
def defaultTranscriptMessage (c : Challenges) : QuadFelt :=
  c.encode [LOG_PRECOMPILE_LABEL, 0, 0, 0, 0]

/-- Final transcript state message. -/
def finalTranscriptMessage (c : Challenges) (state : Word) : QuadFelt :=
  c.encode [LOG_PRECOMPILE_LABEL, state 0, state 1, state 2, state 3]

/-- Kernel procedure init message for kernel ROM bus. -/
def kernelProcMessage (c : Challenges) (digest : Word) : QuadFelt :=
  c.encode [KERNEL_PROC_INIT_LABEL, digest 0, digest 1, digest 2, digest 3]

/-- Product of all kernel procedure init messages. -/
def kernelReduced (c : Challenges) (digests : List Word) : QuadFelt :=
  digests.foldl (fun acc d => acc * kernelProcMessage c d) QuadFelt.one

-- ============================================================================
-- The final verification equation
-- ============================================================================

/-- Final aux column values (8 extension-field elements). -/
structure AuxFinals where
  p1 : QuadFelt          -- block stack table
  p2 : QuadFelt          -- block hash table
  p3 : QuadFelt          -- op group table
  s_aux : QuadFelt       -- stack overflow
  b_range : QuadFelt     -- range checker (LogUp)
  b_hash_kernel : QuadFelt -- hash/kernel virtual table
  b_chiplets : QuadFelt  -- chiplets bus
  v_wiring : QuadFelt    -- ACE wiring

/-- Compute the reduced product and sum from final aux values.
    The verifier checks `prod = 1 ∧ sum = 0`.

    prod = p1 * p2 * p3 * s_aux * b_hash_kernel * b_chiplets
           * ph_msg * default_transcript_msg
           / (final_transcript_msg * kernel_reduced)

    sum = b_range + v_wiring -/
def reducedAuxValues (finals : AuxFinals) (c : Challenges) (pi : PublicInputs) :
    QuadFelt × QuadFelt :=
  let ph_msg := programHashMessage c pi.programHash
  let default_msg := defaultTranscriptMessage c
  let final_msg := finalTranscriptMessage c pi.transcriptState
  let kr := kernelReduced c pi.kernel_digests
  -- The denominator: final_transcript_msg * kernel_reduced
  -- In the real code this is inverted; we express the check as:
  --   prod * denom = numerator  (avoiding division in the spec)
  let numerator := finals.p1 * finals.p2 * finals.p3 * finals.s_aux
                   * finals.b_hash_kernel * finals.b_chiplets
                   * ph_msg * default_msg
  let denom := final_msg * kr
  let prod_check := numerator  -- should equal denom (i.e., prod = num/denom = 1)
  (prod_check, denom)  -- verifier checks: prod_check = denom ∧ sum_check = 0

/-- The STARK verifier accepts iff:
    1. The product of running-product finals (corrected by public-input messages) equals 1.
    2. The sum of LogUp finals equals 0.
    Expressed without division: numerator = denominator ∧ sum = 0. -/
def verifierAccepts (finals : AuxFinals) (c : Challenges) (pi : PublicInputs) : Prop :=
  let (numerator, denom) := reducedAuxValues finals c pi
  numerator = denom ∧ (finals.b_range + finals.v_wiring) = QuadFelt.zero

-- ============================================================================
-- Telescoping product lemma (the composition argument)
-- ============================================================================

/-- A running-product trace: aux column values across n rows. -/
structure RunningProduct (n : Nat) where
  /-- Aux column value at each row. -/
  val : Fin n → QuadFelt
  /-- Per-row response value (numerator of the update). -/
  response : Fin (n - 1) → QuadFelt
  /-- Per-row request value (denominator of the update). -/
  request : Fin (n - 1) → QuadFelt

/-- The transition constraint: aux[i+1] * request[i] = aux[i] * response[i]. -/
def RunningProduct.transitionOk {n : Nat} (rp : RunningProduct n) : Prop :=
  ∀ i : Fin (n - 1),
    rp.val ⟨i.val + 1, by omega⟩ * rp.request i =
      rp.val ⟨i.val, by omega⟩ * rp.response i

/-- Boundary: aux[0] = 1 (running product starts at identity). -/
def RunningProduct.boundaryOk {n : Nat} (rp : RunningProduct n) (hn : n > 0) : Prop :=
  rp.val ⟨0, hn⟩ = QuadFelt.one

private def prefixMap {m k : Nat} (f : Fin m → QuadFelt) (hk : k ≤ m) : Fin k → QuadFelt :=
  fun i => f ⟨i.val, lt_of_lt_of_le i.isLt hk⟩

/-- Telescoping product lemma: if the transition constraint holds on every row
    and the initial value is 1, then the final value equals the ratio of
    total responses to total requests.

    Specifically: aux[n-1] * ∏ request[i] = ∏ response[i]

    This is the algebraic core of the multiset argument. Combined with
    `reduced_aux_values` checking that the final value is the expected
    correction term, it yields the global encoded-product identity for the
    running-product bus. A separate challenge-soundness theorem is needed to
    conclude literal multiset equality of messages. -/
theorem RunningProduct.telescoping {n : Nat} (rp : RunningProduct n)
    (hn : n > 0)
    (hb : rp.boundaryOk hn)
    (ht : rp.transitionOk) :
    rp.val ⟨n - 1, by omega⟩ *
      (∏ i : Fin (n - 1), rp.request i) =
      ∏ i : Fin (n - 1), rp.response i := by
  let reqPrefix (k : Nat) (hk : k < n) (i : Fin k) : QuadFelt :=
    rp.request ⟨i.val, by
      have hk' : k ≤ n - 1 := by omega
      exact lt_of_lt_of_le i.is_lt hk'⟩
  let respPrefix (k : Nat) (hk : k < n) (i : Fin k) : QuadFelt :=
    rp.response ⟨i.val, by
      have hk' : k ≤ n - 1 := by omega
      exact lt_of_lt_of_le i.is_lt hk'⟩
  have hprefix :
      ∀ k (hk : k < n),
        rp.val ⟨k, by omega⟩ * (∏ i : Fin k, reqPrefix k hk i) =
          ∏ i : Fin k, respPrefix k hk i := by
    intro k hk
    induction k with
    | zero =>
        have hb0 : rp.val ⟨0, hk⟩ = QuadFelt.one := by
          simpa using hb
        calc
          rp.val ⟨0, hk⟩ * (∏ i : Fin 0, reqPrefix 0 hk i) = QuadFelt.one := by
            simp [hb0, reqPrefix]
          _ = ∏ i : Fin 0, respPrefix 0 hk i := by
            change (1 : QuadFelt) = ∏ i : Fin 0, respPrefix 0 hk i
            simp [respPrefix]
    | succ k ih =>
        have hk' : k < n := by omega
        calc
          rp.val ⟨k + 1, by omega⟩ * (∏ i : Fin (k + 1), reqPrefix (k + 1) hk i)
              = rp.val ⟨k + 1, by omega⟩ *
                  ((∏ i : Fin k, reqPrefix k hk' i) * rp.request ⟨k, by omega⟩) := by
                    rw [Fin.prod_univ_castSucc]
                    simp [reqPrefix]
          _ = (rp.val ⟨k + 1, by omega⟩ * rp.request ⟨k, by omega⟩) *
                (∏ i : Fin k, reqPrefix k hk' i) := by
                  ring
          _ = (rp.val ⟨k, by omega⟩ * rp.response ⟨k, by omega⟩) *
                (∏ i : Fin k, reqPrefix k hk' i) := by
                  rw [ht ⟨k, by omega⟩]
          _ = rp.response ⟨k, by omega⟩ *
                (rp.val ⟨k, by omega⟩ * (∏ i : Fin k, reqPrefix k hk' i)) := by
                  ring
          _ = rp.response ⟨k, by omega⟩ * (∏ i : Fin k, respPrefix k hk' i) := by
                exact congrArg (fun z => rp.response ⟨k, by omega⟩ * z) (ih hk')
          _ = (∏ i : Fin (k + 1), respPrefix (k + 1) hk i) := by
                rw [Fin.prod_univ_castSucc]
                simpa [respPrefix, mul_comm, mul_left_comm, mul_assoc] using
                  (mul_comm (rp.response ⟨k, by omega⟩)
                    (∏ i : Fin k, respPrefix k hk' i))
  simpa [reqPrefix, respPrefix] using hprefix (n - 1) (by omega)

/-- Corollary: if the final value equals 1 (all corrections cancel),
    then the total product of encoded responses equals the total product of
    encoded requests. This is the exact algebraic conclusion needed before
    applying any randomized challenge-soundness argument. -/
theorem RunningProduct.encoded_product_eq_of_final_one {n : Nat} (rp : RunningProduct n)
    (hn : n > 0)
    (hb : rp.boundaryOk hn)
    (ht : rp.transitionOk)
    (hfinal : rp.val ⟨n - 1, by omega⟩ = QuadFelt.one) :
    (∏ i : Fin (n - 1), rp.response i) =
      ∏ i : Fin (n - 1), rp.request i := by
  calc
    (∏ i : Fin (n - 1), rp.response i)
        = rp.val ⟨n - 1, by omega⟩ * (∏ i : Fin (n - 1), rp.request i) := by
            simpa using (rp.telescoping hn hb ht).symm
    _ = QuadFelt.one * (∏ i : Fin (n - 1), rp.request i) := by
          rw [hfinal]
    _ = ∏ i : Fin (n - 1), rp.request i := by
          change (1 : QuadFelt) * (∏ i : Fin (n - 1), rp.request i) =
            ∏ i : Fin (n - 1), rp.request i
          simpa using (one_mul (∏ i : Fin (n - 1), rp.request i))

/-- LogUp sum version: if the transition constraint is additive
    (aux[i+1] = aux[i] + term[i]), boundary aux[0] = 0, and aux[n-1] = 0,
    then the sum of all encoded terms is zero. This is the algebraic core of
    the LogUp argument; connecting it to semantic lookup soundness is a
    separate theorem. -/
theorem logup_sum_zero {n : Nat} (val : Fin n → QuadFelt) (term : Fin (n - 1) → QuadFelt)
    (hn : n > 0)
    (hb : val ⟨0, by omega⟩ = QuadFelt.zero)
    (ht : ∀ i : Fin (n - 1),
      val ⟨i.val + 1, by omega⟩ = val ⟨i.val, by omega⟩ + term i)
    (hfinal : val ⟨n - 1, by omega⟩ = QuadFelt.zero) :
    (∑ i : Fin (n - 1), term i) = QuadFelt.zero := by
  let termPrefix (k : Nat) (hk : k < n) (i : Fin k) : QuadFelt :=
    term ⟨i.val, by
      have hk' : k ≤ n - 1 := by omega
      exact lt_of_lt_of_le i.is_lt hk'⟩
  have hprefix :
      ∀ k (hk : k < n),
        val ⟨k, by omega⟩ = ∑ i : Fin k, termPrefix k hk i := by
    intro k hk
    induction k with
    | zero =>
        have hb0 : val ⟨0, hk⟩ = QuadFelt.zero := by
          simpa using hb
        calc
          val ⟨0, hk⟩ = QuadFelt.zero := hb0
          _ = (0 : QuadFelt) := by
            rfl
          _ = ∑ i : Fin 0, termPrefix 0 hk i := by
            simp [termPrefix]
    | succ k ih =>
        have hk' : k < n := by omega
        calc
          val ⟨k + 1, by omega⟩ = val ⟨k, by omega⟩ + term ⟨k, by omega⟩ := by
            exact ht ⟨k, by omega⟩
          _ = (∑ i : Fin k, termPrefix k hk' i) + term ⟨k, by omega⟩ := by
                rw [ih hk']
          _ = ∑ i : Fin (k + 1), termPrefix (k + 1) hk i := by
                rw [Fin.sum_univ_castSucc]
                simp [termPrefix, prefixMap]
  calc
    (∑ i : Fin (n - 1), term i) = val ⟨n - 1, by omega⟩ := by
      symm
      simpa [termPrefix, prefixMap] using hprefix (n - 1) (by omega)
    _ = QuadFelt.zero := hfinal

end MidenLean.AIR.ReducedAux
