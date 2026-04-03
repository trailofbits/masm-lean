import MidenLean.Proofs.Sha256.Common
import MidenLean.Proofs.Sha256.ComputeMessageScheduleWord
import MidenLean.Proofs.Sha256.ConsumeMessageWord

namespace MidenLean.Proofs.Sha256

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

-- ============================================================================
-- Bridge lemmas: sub-procedures at fuel 2125
-- (inner fuel when outer prepare_message_schedule_and_consume runs at fuel 2126)
-- ============================================================================

/-- Every procedure in `sha256ProcEnv` has `numLocals = 0`. -/
lemma sha256ProcEnv_numLocals_zero (name : String) (proc : Procedure)
    (h : sha256ProcEnv name = some proc) : proc.numLocals = 0 := by
  simp only [sha256ProcEnv] at h
  split at h <;>
  first
  | (simp only [Option.some.injEq,
       Miden.Core.Sha256.small_sigma_0, Miden.Core.Sha256.small_sigma_1,
       Miden.Core.Sha256.cap_sigma_0, Miden.Core.Sha256.cap_sigma_1,
       Miden.Core.Sha256.ch, Miden.Core.Sha256.maj,
       Miden.Core.Sha256.rev_element_order,
       Miden.Core.Sha256.compute_message_schedule_word,
       Miden.Core.Sha256.consume_message_word,
       Procedure.ofOps] at h; subst h; rfl)
  | simp at h

/-- `compute_message_schedule_word` at the inner fuel 2125 available inside
    `prepare_message_schedule_and_consume`.  Follows directly from the fuel-40
    proof via `execWithEnv_fuel_mono`. -/
lemma compute_message_schedule_word_at_2125
    (a b c d : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = a :: b :: c :: d :: rest)
    (ha : a.isU32 = true) (hb : b.isU32 = true)
    (hc : c.isU32 = true) (hd : d.isU32 = true) :
    execWithEnv sha256ProcEnv 2125 s Miden.Core.Sha256.compute_message_schedule_word =
    some (s.withStack (
      let sig1 := u32RotateRight a.val 17 ^^^ (u32RotateRight a.val 19 ^^^ a.val / 2^10)
      let sig0 := u32RotateRight c.val 7 ^^^ (u32RotateRight c.val 18 ^^^ c.val / 2^3)
      Felt.ofNat ((d.val + (b.val + sig1 + sig0) % 2^32) % 2^32) :: rest)) :=
  execWithEnv_fuel_mono sha256ProcEnv sha256ProcEnv_numLocals_zero (by norm_num)
    (by simp [Miden.Core.Sha256.compute_message_schedule_word])
    (sha256_compute_message_schedule_word_correct a b c d rest s hs ha hb hc hd)

/-- `consume_message_word` at the inner fuel 2125 available inside
    `prepare_message_schedule_and_consume`.  Follows directly from the fuel-94
    proof via `execWithEnv_fuel_mono`. -/
lemma consume_message_word_at_2125
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: rest)
    (h0 : x0.isU32 = true) (h1 : x1.isU32 = true) (h2 : x2.isU32 = true)
    (h3 : x3.isU32 = true) (h4 : x4.isU32 = true) (h5 : x5.isU32 = true)
    (h6 : x6.isU32 = true) (h7 : x7.isU32 = true) (h8 : x8.isU32 = true)
    (h9 : x9.isU32 = true) :
    execWithEnv sha256ProcEnv 2125 s Miden.Core.Sha256.consume_message_word =
    some (s.withStack (
      let ch_v  := (x5.val &&& x4.val) ^^^ ((u32Max - 1 - x4.val) &&& x6.val)
      let t1p   := (ch_v + x8.val + x9.val) % 2^32
      let sig1  := u32RotateRight x4.val 6 ^^^
                   (u32RotateRight x4.val 11 ^^^ u32RotateRight x4.val 25)
      let T1    := (t1p + sig1 + x7.val) % 2^32
      let maj_v := (x1.val &&& x0.val) ^^^
                   ((x0.val &&& x2.val) ^^^ (x1.val &&& x2.val))
      let sig0  := u32RotateRight x0.val 2 ^^^
                   (u32RotateRight x0.val 13 ^^^ u32RotateRight x0.val 22)
      let T2    := (maj_v + sig0) % 2^32
      Felt.ofNat ((T1 + T2) % 2^32) :: x0 :: x1 :: x2 ::
        Felt.ofNat ((x3.val + T1) % 2^32) :: x4 :: x5 :: x6 :: rest)) :=
  execWithEnv_fuel_mono sha256ProcEnv sha256ProcEnv_numLocals_zero (by norm_num)
    (by simp [Miden.Core.Sha256.consume_message_word])
    (sha256_consume_message_word_correct x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 rest s hs
      h0 h1 h2 h3 h4 h5 h6 h7 h8 h9)

-- ============================================================================
-- Helper: rev_element_order at fuel 2125
-- rev_element_order = [swap 1, movup 2, movup 3]
-- reverses the top 4 stack elements: [a,b,c,d,...] → [d,c,b,a,...]
-- ============================================================================

lemma rev_element_order_at_2125
    (a b c d : Felt) (rest : List Felt)
    (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt) :
    execWithEnv sha256ProcEnv 2125 ⟨a :: b :: c :: d :: rest, mem, frames, adv⟩
      Miden.Core.Sha256.rev_element_order =
    some ⟨d :: c :: b :: a :: rest, mem, frames, adv⟩ := by
  unfold execWithEnv Miden.Core.Sha256.rev_element_order
  simp only [List.foldlM]
  rw [stepSwap (hn := by decide) (htop := rfl) (hnth := rfl)]; miden_bind
  rw [stepMovup (hn := rfl) (hv := rfl)]; miden_bind
  rw [stepMovup (hn := rfl) (hv := rfl)]; miden_bind
  dsimp only [pure, Pure.pure]

-- ============================================================================
-- Helper: sha256WorkingLocs
-- Represents the locs state at each super-block boundary.
-- Working state in locs[0..7], backup H values in locs[8..15].
-- Storage convention (locStorewBe stores top at idx+3):
--   locs[0]=d, locs[1]=c, locs[2]=b, locs[3]=a  (compression a..d)
--   locs[4]=h, locs[5]=g, locs[6]=f, locs[7]=e  (compression e..h)
-- Backup (set during init, never changed):
--   locs[8]=H3, locs[9]=H2, locs[10]=H1, locs[11]=H0
--   locs[12]=H7, locs[13]=H6, locs[14]=H5, locs[15]=H4
-- ============================================================================

def sha256WorkingLocs
    (a b c d e f g h : Felt)
    (H0 H1 H2 H3 H4 H5 H6 H7 : Felt)
    (base : Nat → Felt) : Nat → Felt :=
  fun i =>
    if i = 3  then a else if i = 2  then b
    else if i = 1  then c else if i = 0  then d
    else if i = 7  then e else if i = 6  then f
    else if i = 5  then g else if i = 4  then h
    else if i = 11 then H0 else if i = 10 then H1
    else if i = 9  then H2 else if i = 8  then H3
    else if i = 15 then H4 else if i = 14 then H5
    else if i = 13 then H6 else if i = 12 then H7
    else base i

-- Evaluation lemmas for sha256WorkingLocs at specific indices
@[simp] lemma sha256WorkingLocs_0 (a b c d e f g h H0 H1 H2 H3 H4 H5 H6 H7 : Felt)
    (base : Nat → Felt) : sha256WorkingLocs a b c d e f g h H0 H1 H2 H3 H4 H5 H6 H7 base 0 = d := by
  simp [sha256WorkingLocs]
@[simp] lemma sha256WorkingLocs_1 (a b c d e f g h H0 H1 H2 H3 H4 H5 H6 H7 : Felt)
    (base : Nat → Felt) : sha256WorkingLocs a b c d e f g h H0 H1 H2 H3 H4 H5 H6 H7 base 1 = c := by
  simp [sha256WorkingLocs]
@[simp] lemma sha256WorkingLocs_2 (a b c d e f g h H0 H1 H2 H3 H4 H5 H6 H7 : Felt)
    (base : Nat → Felt) : sha256WorkingLocs a b c d e f g h H0 H1 H2 H3 H4 H5 H6 H7 base 2 = b := by
  simp [sha256WorkingLocs]
@[simp] lemma sha256WorkingLocs_3 (a b c d e f g h H0 H1 H2 H3 H4 H5 H6 H7 : Felt)
    (base : Nat → Felt) : sha256WorkingLocs a b c d e f g h H0 H1 H2 H3 H4 H5 H6 H7 base 3 = a := by
  simp [sha256WorkingLocs]
@[simp] lemma sha256WorkingLocs_4 (a b c d e f g h H0 H1 H2 H3 H4 H5 H6 H7 : Felt)
    (base : Nat → Felt) : sha256WorkingLocs a b c d e f g h H0 H1 H2 H3 H4 H5 H6 H7 base 4 = h := by
  simp [sha256WorkingLocs]
@[simp] lemma sha256WorkingLocs_5 (a b c d e f g h H0 H1 H2 H3 H4 H5 H6 H7 : Felt)
    (base : Nat → Felt) : sha256WorkingLocs a b c d e f g h H0 H1 H2 H3 H4 H5 H6 H7 base 5 = g := by
  simp [sha256WorkingLocs]
@[simp] lemma sha256WorkingLocs_6 (a b c d e f g h H0 H1 H2 H3 H4 H5 H6 H7 : Felt)
    (base : Nat → Felt) : sha256WorkingLocs a b c d e f g h H0 H1 H2 H3 H4 H5 H6 H7 base 6 = f := by
  simp [sha256WorkingLocs]
@[simp] lemma sha256WorkingLocs_7 (a b c d e f g h H0 H1 H2 H3 H4 H5 H6 H7 : Felt)
    (base : Nat → Felt) : sha256WorkingLocs a b c d e f g h H0 H1 H2 H3 H4 H5 H6 H7 base 7 = e := by
  simp [sha256WorkingLocs]
@[simp] lemma sha256WorkingLocs_8 (a b c d e f g h H0 H1 H2 H3 H4 H5 H6 H7 : Felt)
    (base : Nat → Felt) : sha256WorkingLocs a b c d e f g h H0 H1 H2 H3 H4 H5 H6 H7 base 8 = H3 := by
  simp [sha256WorkingLocs]
@[simp] lemma sha256WorkingLocs_9 (a b c d e f g h H0 H1 H2 H3 H4 H5 H6 H7 : Felt)
    (base : Nat → Felt) : sha256WorkingLocs a b c d e f g h H0 H1 H2 H3 H4 H5 H6 H7 base 9 = H2 := by
  simp [sha256WorkingLocs]
@[simp] lemma sha256WorkingLocs_10 (a b c d e f g h H0 H1 H2 H3 H4 H5 H6 H7 : Felt)
    (base : Nat → Felt) : sha256WorkingLocs a b c d e f g h H0 H1 H2 H3 H4 H5 H6 H7 base 10 = H1 := by
  simp [sha256WorkingLocs]
@[simp] lemma sha256WorkingLocs_11 (a b c d e f g h H0 H1 H2 H3 H4 H5 H6 H7 : Felt)
    (base : Nat → Felt) : sha256WorkingLocs a b c d e f g h H0 H1 H2 H3 H4 H5 H6 H7 base 11 = H0 := by
  simp [sha256WorkingLocs]
@[simp] lemma sha256WorkingLocs_12 (a b c d e f g h H0 H1 H2 H3 H4 H5 H6 H7 : Felt)
    (base : Nat → Felt) : sha256WorkingLocs a b c d e f g h H0 H1 H2 H3 H4 H5 H6 H7 base 12 = H7 := by
  simp [sha256WorkingLocs]
@[simp] lemma sha256WorkingLocs_13 (a b c d e f g h H0 H1 H2 H3 H4 H5 H6 H7 : Felt)
    (base : Nat → Felt) : sha256WorkingLocs a b c d e f g h H0 H1 H2 H3 H4 H5 H6 H7 base 13 = H6 := by
  simp [sha256WorkingLocs]
@[simp] lemma sha256WorkingLocs_14 (a b c d e f g h H0 H1 H2 H3 H4 H5 H6 H7 : Felt)
    (base : Nat → Felt) : sha256WorkingLocs a b c d e f g h H0 H1 H2 H3 H4 H5 H6 H7 base 14 = H5 := by
  simp [sha256WorkingLocs]
@[simp] lemma sha256WorkingLocs_15 (a b c d e f g h H0 H1 H2 H3 H4 H5 H6 H7 : Felt)
    (base : Nat → Felt) : sha256WorkingLocs a b c d e f g h H0 H1 H2 H3 H4 H5 H6 H7 base 15 = H4 := by
  simp [sha256WorkingLocs]

-- ============================================================================
-- SHA-256 block computation output specification
-- ============================================================================

-- The procedure:
--   Input:  [H0,H1,H2,H3,H4,H5,H6,H7, W0,..,W15] ++ rest  (24 felts)
--   Init:   stores H0..H7 to local memory (locs[0..15], two copies for working + backup)
--           drops H words, leaving W0..W15 on stack
--   Body:   computes W16..W63 (message schedule) interleaved with 64 compression rounds
--           working state held in locs[0..7] between rounds
--   Final:  loads backup H0..H7 from locs[8..15], adds to working state element-wise
--   Output: [a+H0, b+H1, c+H2, d+H3, e+H4, f+H5, g+H6, h+H7] ++ rest
--           where (a..h) is the 64-round SHA-256 compression result
--
-- Memory layout (BE word order, so locStorewBe/locLoadwBe reverse within each group-of-4):
--   locs[0..3]  working copy of H0..H3 (updated after every 4 consume calls)
--   locs[4..7]  working copy of H4..H7 (updated after every 4 consume calls)
--   locs[8..11] backup H0..H3 (never overwritten, loaded at the end)
--   locs[12..15] backup H4..H7 (never overwritten, loaded at the end)

-- ============================================================================
-- SHA-256 round constants K[0..63] and message schedule W[0..63]
-- ============================================================================

def sha256KArray : Array Nat := #[
  1116352408, 1899447441, 3049323471, 3921009573, 961987163,  1508970993, 2453635748, 2870763221,
  3624381080, 310598401,  607225278,  1426881987, 1925078388, 2162078206, 2614888103, 3248222580,
  3835390401, 4022224774, 264347078,  604807628,  770255983,  1249150122, 1555081692, 1996064986,
  2554220882, 2821834349, 2952996808, 3210313671, 3336571891, 3584528711, 113926993,  338241895,
  666307205,  773529912,  1294757372, 1396182291, 1695183700, 1986661051, 2177026350, 2456956037,
  2730485921, 2820302411, 3259730800, 3345764771, 3516065817, 3600352804, 4094571909, 275423344,
  430227734,  506948616,  659060556,  883997877,  958139571,  1322822218, 1537002063, 1747873779,
  1955562222, 2024104815, 2227730452, 2361852424, 2428436474, 2756734187, 3204031479, 3329325298]

def sha256KVal (i : Fin 64) : Nat := sha256KArray[i]

/-- Build the full 64-word SHA-256 message schedule from W[0..15] inputs.
    W[i] for i ≥ 16 = σ₁(W[i-2]) + W[i-7] + σ₀(W[i-15]) + W[i-16] (mod 2³²). -/
def sha256Schedule
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : Nat) :
    Fin 64 → Nat :=
  let arr : Array Nat :=
    (List.range 48).foldl (fun a i =>
      let j := i + 16
      let wim2  := a[j - 2]!
      let wim7  := a[j - 7]!
      let wim15 := a[j - 15]!
      let wim16 := a[j - 16]!
      let sig1 := u32RotateRight wim2 17 ^^^ (u32RotateRight wim2 19 ^^^ wim2 / 2^10)
      let sig0 := u32RotateRight wim15 7 ^^^ (u32RotateRight wim15 18 ^^^ wim15 / 2^3)
      a.push ((wim16 + (wim7 + sig1 + sig0) % 2^32) % 2^32))
    #[w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15]
  fun i => arr[i.val]!

-- ============================================================================
-- SHA-256 block compression: 64-round fold
-- ============================================================================

/-- One SHA-256 compression round: advances (a,b,c,d,e,f,g,h) by one step with
    message word W and round constant K. -/
def sha256RoundStep (a b c d e f g h W K : Nat) :
    Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat :=
  let ch_v  := (f &&& e) ^^^ ((u32Max - 1 - e) &&& g)
  let t1p   := (ch_v + W + K) % 2^32
  let sig1  := u32RotateRight e 6 ^^^ (u32RotateRight e 11 ^^^ u32RotateRight e 25)
  let T1    := (t1p + sig1 + h) % 2^32
  let maj_v := (b &&& a) ^^^ ((a &&& c) ^^^ (b &&& c))
  let sig0  := u32RotateRight a 2 ^^^ (u32RotateRight a 13 ^^^ u32RotateRight a 22)
  let T2    := (maj_v + sig0) % 2^32
  ((T1 + T2) % 2^32, a, b, c, (d + T1) % 2^32, e, f, g)

/-- Full SHA-256 block: 64 rounds of compression starting from initial state (H0..H7)
    with message schedule W[0..63] and round constants K[0..63]. -/
def sha256Block
    (H0 H1 H2 H3 H4 H5 H6 H7 : Nat)
    (W : Fin 64 → Nat) :
    Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat :=
  (List.finRange 64).foldl (fun (st : Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat) i =>
    let (a, b, c, d, e, f, g, h) := st
    sha256RoundStep a b c d e f g h (W i) (sha256KVal i))
  (H0, H1, H2, H3, H4, H5, H6, H7)

-- ============================================================================
-- Consume result helpers
-- ============================================================================

-- Shorthand: result of one sha256RoundStep applied to Felt values
-- Input stack: [a,b,c,d,e,f,g,h, K, W, rest...]  (x0=a, x4=e, x8=K, x9=W)
def consumeResult (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : Felt) :
    Felt × Felt × Felt × Felt × Felt × Felt × Felt × Felt :=
  let ch_v  := (x5.val &&& x4.val) ^^^ ((u32Max - 1 - x4.val) &&& x6.val)
  let t1p   := (ch_v + x8.val + x9.val) % 2^32
  let sig1  := u32RotateRight x4.val 6 ^^^
               (u32RotateRight x4.val 11 ^^^ u32RotateRight x4.val 25)
  let T1    := (t1p + sig1 + x7.val) % 2^32
  let maj_v := (x1.val &&& x0.val) ^^^
               ((x0.val &&& x2.val) ^^^ (x1.val &&& x2.val))
  let sig0  := u32RotateRight x0.val 2 ^^^
               (u32RotateRight x0.val 13 ^^^ u32RotateRight x0.val 22)
  let T2    := (maj_v + sig0) % 2^32
  (Felt.ofNat ((T1 + T2) % 2^32), x0, x1, x2,
   Felt.ofNat ((x3.val + T1) % 2^32), x4, x5, x6)

-- ============================================================================
-- isU32 helper lemmas
-- ============================================================================

lemma u32_ofNat_isU32 (n : Nat) (h : n < 2^32) : (Felt.ofNat n).isU32 = true :=
  felt_ofNat_isU32_of_lt n h

-- All sha256 round results are u32
lemma consumeResult_isU32 (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : Felt)
    (h0 : x0.isU32 = true) (h1 : x1.isU32 = true) (h2 : x2.isU32 = true)
    (h3 : x3.isU32 = true) (h4 : x4.isU32 = true) (h5 : x5.isU32 = true)
    (h6 : x6.isU32 = true) (h7 : x7.isU32 = true) (h8 : x8.isU32 = true)
    (h9 : x9.isU32 = true) :
    let (na, nb, nc, nd, ne, nf, ng, nh) := consumeResult x0 x1 x2 x3 x4 x5 x6 x7 x8 x9
    na.isU32 = true ∧ nb.isU32 = true ∧ nc.isU32 = true ∧ nd.isU32 = true ∧
    ne.isU32 = true ∧ nf.isU32 = true ∧ ng.isU32 = true ∧ nh.isU32 = true := by
  simp only [consumeResult]
  exact ⟨u32_mod_isU32 _, h0, h1, h2, u32_mod_isU32 _, h4, h5, h6⟩

-- ============================================================================
-- Ops segment definitions
-- ============================================================================

/-- The 6-instruction initialization block that stores H0..H7 to local memory. -/
def sha256InitOps : List Op := [
  .inst (.locStorewBe 0), .inst (.locStorewBe 8), .inst (.dropw),
  .inst (.locStorewBe 4), .inst (.locStorewBe 12), .inst (.dropw)]

/-- The final 5-operation block that loads backup H values and adds them to the
    compressed state element-wise (mod 2³²). -/
def sha256FinalOps : List Op := [
  .inst (.padw), .inst (.locLoadwBe 12),
  .inst (.padw), .inst (.locLoadwBe 8),
  .repeat 8 [.inst (.movup 8), .inst (.u32WrappingAdd), .inst (.movdn 7)]]

/-- The body of prepare_message_schedule_and_consume: everything between the
    6-instruction init block and the 5-operation final block. -/
def sha256BodyOps : List Op :=
  (Miden.Core.Sha256.prepare_message_schedule_and_consume.drop 6).take
    ((Miden.Core.Sha256.prepare_message_schedule_and_consume.drop 6).length - 5)

-- ============================================================================
-- Super-block op segments (16 SBs partitioning sha256BodyOps)
-- Each SBi corresponds to 4 message schedule expansion steps + 4 compression
-- rounds, plus associated local memory store/load bookkeeping.
-- SBs 0–11 each end with: locStorewBe 0; dropw; locStorewBe 4; dropw
-- SBs 12–15 are compression-only with different stack management.
-- ============================================================================

def sha256SB0Ops  : List Op := sha256BodyOps.take 52
def sha256SB1Ops  : List Op := (sha256BodyOps.drop 52).take 50
def sha256SB2Ops  : List Op := (sha256BodyOps.drop 102).take 47
def sha256SB3Ops  : List Op := (sha256BodyOps.drop 149).take 50
def sha256SB4Ops  : List Op := (sha256BodyOps.drop 199).take 50
def sha256SB5Ops  : List Op := (sha256BodyOps.drop 249).take 50
def sha256SB6Ops  : List Op := (sha256BodyOps.drop 299).take 50
def sha256SB7Ops  : List Op := (sha256BodyOps.drop 349).take 50
def sha256SB8Ops  : List Op := (sha256BodyOps.drop 399).take 50
def sha256SB9Ops  : List Op := (sha256BodyOps.drop 449).take 50
def sha256SB10Ops : List Op := (sha256BodyOps.drop 499).take 50
def sha256SB11Ops : List Op := (sha256BodyOps.drop 549).take 50
def sha256SB12Ops : List Op := (sha256BodyOps.drop 599).take 22
def sha256SB13Ops : List Op := (sha256BodyOps.drop 621).take 15
def sha256SB14Ops : List Op := (sha256BodyOps.drop 636).take 15
def sha256SB15Ops : List Op := sha256BodyOps.drop 651

-- ============================================================================
-- SBs 4–11: Generic "regular" super-block helpers
-- All SBs 4–11 share the same expand structure:
--   movupw 3, 4× compute_message_schedule_word, movupw 3, rev_element_order
-- The only differences are:
--   - K constants (different per SB)
--   - SB6 has slightly different dup indices in the 4th compute
--     (but produces the same result)
-- ============================================================================

/-- Generic message-schedule word computation: σ₁(a) + b + σ₀(c) + d (mod 2³²) -/
def sha256W (a b c d : Felt) : Felt :=
  let sig1 := u32RotateRight a.val 17 ^^^ (u32RotateRight a.val 19 ^^^ a.val / 2^10)
  let sig0 := u32RotateRight c.val 7 ^^^ (u32RotateRight c.val 18 ^^^ c.val / 2^3)
  Felt.ofNat ((d.val + (b.val + sig1 + sig0) % 2^32) % 2^32)

/-- Generic 4-round compression with constants K0..K3 consuming message words w0..w3 -/
def sha256Compress4 (a b c d e f g h w0 w1 w2 w3 : Felt) (k0 k1 k2 k3 : Nat) :
    Felt × Felt × Felt × Felt × Felt × Felt × Felt × Felt :=
  let (a1,b1,c1,d1,e1,f1,g1,h1) := consumeResult a b c d e f g h (Felt.ofNat k0) w0
  let (a2,b2,c2,d2,e2,f2,g2,h2) := consumeResult a1 b1 c1 d1 e1 f1 g1 h1 (Felt.ofNat k1) w1
  let (a3,b3,c3,d3,e3,f3,g3,h3) := consumeResult a2 b2 c2 d2 e2 f2 g2 h2 (Felt.ofNat k2) w2
  consumeResult a3 b3 c3 d3 e3 f3 g3 h3 (Felt.ofNat k3) w3

-- ============================================================================
-- Regular expand ops (shared by SBs 4,5,7,8,9,10,11)
-- ============================================================================

/-- Expand phase ops for "regular" SBs (Type A): 31 instructions -/
def sha256RegularExpandOps : List Op := [
    .inst (.movupw 3),
    .inst (.dup 14), .inst (.dup 6), .inst (.dup 13), .inst (.dup 13),
    .inst (.movdn 3), .inst (.movdn 3), .inst (.exec "compute_message_schedule_word"),
    .inst (.dup 14), .inst (.dup 6), .inst (.dup 13), .inst (.dup 13),
    .inst (.movdn 3), .inst (.movdn 3), .inst (.exec "compute_message_schedule_word"),
    .inst (.dup 14), .inst (.dup 2), .inst (.dup 13), .inst (.dup 13),
    .inst (.movdn 3), .inst (.movdn 3), .inst (.exec "compute_message_schedule_word"),
    .inst (.dup 10), .inst (.dup 2), .inst (.dup 8), .inst (.dup 14),
    .inst (.movdn 3), .inst (.movdn 2), .inst (.exec "compute_message_schedule_word"),
    .inst (.movupw 3), .inst (.exec "rev_element_order")]

/-- SB6 expand phase ops (Type B): 31 instructions, differs in 4th compute -/
def sha256SB6ExpandOps : List Op := [
    .inst (.movupw 3),
    .inst (.dup 14), .inst (.dup 6), .inst (.dup 13), .inst (.dup 13),
    .inst (.movdn 3), .inst (.movdn 3), .inst (.exec "compute_message_schedule_word"),
    .inst (.dup 14), .inst (.dup 6), .inst (.dup 13), .inst (.dup 13),
    .inst (.movdn 3), .inst (.movdn 3), .inst (.exec "compute_message_schedule_word"),
    .inst (.dup 14), .inst (.dup 2), .inst (.dup 13), .inst (.dup 13),
    .inst (.movdn 3), .inst (.movdn 3), .inst (.exec "compute_message_schedule_word"),
    .inst (.dup 10), .inst (.dup 2), .inst (.dup 13), .inst (.dup 9),
    .inst (.movdn 3), .inst (.movdn 3), .inst (.exec "compute_message_schedule_word"),
    .inst (.movupw 3), .inst (.exec "rev_element_order")]

/-- Consume+store ops parameterized by 4 round constants -/
def sha256RegularConsumeOps (k0 k1 k2 k3 : Nat) : List Op := [
    .inst (.push k0), .inst .padw, .inst (.locLoadwBe 4),
    .inst .padw, .inst (.locLoadwBe 0),
    .inst (.exec "consume_message_word"),
    .inst (.push k1), .inst (.movdn 8),
    .inst (.exec "consume_message_word"),
    .inst (.push k2), .inst (.movdn 8),
    .inst (.exec "consume_message_word"),
    .inst (.push k3), .inst (.movdn 8),
    .inst (.exec "consume_message_word"),
    .inst (.locStorewBe 0), .inst .dropw,
    .inst (.locStorewBe 4), .inst .dropw]

end MidenLean.Proofs.Sha256
