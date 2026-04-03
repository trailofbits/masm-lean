import MidenLean.Proofs.Sha256.Common
import MidenLean.Proofs.Sha256.ConsumeMessageWord

namespace MidenLean.Proofs.Sha256

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

-- ============================================================================
-- One SHA-256 compression round as a Felt 8-tuple
-- ============================================================================

/-- Applies one SHA-256 compression round.
    Inputs a..h are the current state, Kf = round constant (at stack pos 8),
    Wf = message word (at stack pos 9), matching sha256_consume_message_word_correct. -/
private def sha256OneRoundState (a b c d e f g h Kf Wf : Felt) :
    Felt × Felt × Felt × Felt × Felt × Felt × Felt × Felt :=
  let ch_v  := (f.val &&& e.val) ^^^ ((u32Max - 1 - e.val) &&& g.val)
  let t1p   := (ch_v + Kf.val + Wf.val) % 2^32
  let sig1  := u32RotateRight e.val 6 ^^^
               (u32RotateRight e.val 11 ^^^ u32RotateRight e.val 25)
  let T1    := (t1p + sig1 + h.val) % 2^32
  let maj_v := (b.val &&& a.val) ^^^
               ((a.val &&& c.val) ^^^ (b.val &&& c.val))
  let sig0  := u32RotateRight a.val 2 ^^^
               (u32RotateRight a.val 13 ^^^ u32RotateRight a.val 22)
  let T2    := (maj_v + sig0) % 2^32
  (Felt.ofNat ((T1 + T2) % 2^32), a, b, c,
   Felt.ofNat ((d.val + T1) % 2^32), e, f, g)

private def sha256OneRoundFelt (a b c d e f g h Kf Wf : Felt) : List Felt :=
  let (a', b', c', d', e', f', g', h') := sha256OneRoundState a b c d e f g h Kf Wf
  [a', b', c', d', e', f', g', h']

-- ============================================================================
-- Fold over 64 rounds
-- ============================================================================

private def sha256FeltFold :
    Felt × Felt × Felt × Felt × Felt × Felt × Felt × Felt →
    List (Nat × Nat) →
    Felt × Felt × Felt × Felt × Felt × Felt × Felt × Felt
  | st, [] => st
  | (a, b, c, d, e, f, g, h), (W, K) :: rest =>
    sha256FeltFold (sha256OneRoundState a b c d e f g h (Felt.ofNat K) (Felt.ofNat W)) rest

private def sha256FoldList (init : Felt × Felt × Felt × Felt × Felt × Felt × Felt × Felt)
    (pairs : List (Nat × Nat)) : List Felt :=
  let (a', b', c', d', e', f', g', h') := sha256FeltFold init pairs
  [a', b', c', d', e', f', g', h']

-- ============================================================================
-- 64 (W_i, K_i) constants (W first pushed → pos 9, K second → pos 8)
-- ============================================================================

private def sha256PaddingConstants : List (Nat × Nat) := [
  (2147483648, 1116352408), (0, 1899447441), (0, 3049323471), (0, 3921009573),
  (0, 961987163), (0, 1508970993), (0, 2453635748), (0, 2870763221),
  (0, 3624381080), (0, 310598401), (0, 607225278), (0, 1426881987),
  (0, 1925078388), (0, 2162078206), (0, 2614888103), (512, 3248222580),
  (2147483648, 3835390401), (20971520, 4022224774), (2117632, 264347078),
  (20616, 604807628), (570427392, 770255983), (575995924, 1249150122),
  (84449090, 1555081692), (2684354592, 1996064986), (1518862336, 2554220882),
  (6067200, 2821834349), (1496221, 2952996808), (4202700544, 3210313671),
  (3543279056, 3336571891), (291985753, 3584528711), (4142317530, 113926993),
  (3003913545, 338241895), (145928272, 666307205), (2642168871, 773529912),
  (216179603, 1294757372), (2296832490, 1396182291), (2771075893, 1695183700),
  (1738633033, 1986661051), (3610378607, 2177026350), (1324035729, 2456956037),
  (1572820453, 2730485921), (2397971253, 2820302411), (3803995842, 3259730800),
  (2822718356, 3345764771), (1168996599, 3516065817), (921948365, 3600352804),
  (3650881000, 4094571909), (2958106055, 275423344), (1773959876, 430227734),
  (3172022107, 506948616), (3820646885, 659060556), (991993842, 883997877),
  (419360279, 958139571), (3797604839, 1322822218), (322392134, 1537002063),
  (85264541, 1747873779), (1326255876, 1955562222), (640108622, 2024104815),
  (822159570, 2227730452), (3328750644, 2361852424), (1107837388, 2428436474),
  (1657999800, 2756734187), (3852183409, 3204031479), (2242356356, 3329325298)]

-- ============================================================================
-- Ops list for a sequence of rounds
-- ============================================================================

private def sha256PaddingOps : List (Nat × Nat) → List Op
  | [] => []
  | (W, K) :: rest =>
    [.inst (.push (Felt.ofNat W)), .inst (.movdn 8),
     .inst (.push (Felt.ofNat K)), .inst (.movdn 8),
     .inst (.exec "consume_message_word")] ++ sha256PaddingOps rest

-- ============================================================================
-- isU32 preservation through the fold
-- ============================================================================

private lemma sha256FeltFold_isU32
    (a b c d e f g h : Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true) (hc : c.isU32 = true) (hd : d.isU32 = true)
    (he : e.isU32 = true) (hf : f.isU32 = true) (hg : g.isU32 = true) (hh : h.isU32 = true)
    (pairs : List (Nat × Nat)) :
    let (a', b', c', d', e', f', g', h') := sha256FeltFold (a, b, c, d, e, f, g, h) pairs
    a'.isU32 = true ∧ b'.isU32 = true ∧ c'.isU32 = true ∧ d'.isU32 = true ∧
    e'.isU32 = true ∧ f'.isU32 = true ∧ g'.isU32 = true ∧ h'.isU32 = true := by
  induction pairs generalizing a b c d e f g h with
  | nil => exact ⟨ha, hb, hc, hd, he, hf, hg, hh⟩
  | cons p rest ih =>
    obtain ⟨W, K⟩ := p
    simp only [sha256FeltFold, sha256OneRoundState]
    apply ih
    · exact u32_mod_isU32 _
    · exact ha
    · exact hb
    · exact hc
    · exact u32_mod_isU32 _
    · exact he
    · exact hf
    · exact hg

-- ============================================================================
-- Bridge lemma: 64-round execution
-- ============================================================================

set_option maxHeartbeats 2000000 in
private lemma sha256PaddingRounds_bridge
    (a b c d e f g h : Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true) (hc : c.isU32 = true) (hd : d.isU32 = true)
    (he : e.isU32 = true) (hf : f.isU32 = true) (hg : g.isU32 = true) (hh : h.isU32 = true)
    (pairs : List (Nat × Nat))
    (hpairs : ∀ p ∈ pairs, p.1 < 2^32 ∧ p.2 < 2^32)
    (tail : List Felt) (mem locs : Nat → Felt) (adv : List Felt) :
    execWithEnv sha256ProcEnv 95 ⟨a :: b :: c :: d :: e :: f :: g :: h :: tail, mem, locs, adv⟩
      (sha256PaddingOps pairs) =
    some ⟨sha256FoldList (a, b, c, d, e, f, g, h) pairs ++ tail, mem, locs, adv⟩ := by
  induction pairs generalizing a b c d e f g h with
  | nil =>
    simp [sha256PaddingOps, sha256FoldList, sha256FeltFold, execWithEnv, List.foldlM]
  | cons p rest ih =>
    obtain ⟨W, K⟩ := p
    have hW : W < 2^32 := (hpairs ⟨W, K⟩ List.mem_cons_self).1
    have hK : K < 2^32 := (hpairs ⟨W, K⟩ List.mem_cons_self).2
    have hKf : (Felt.ofNat K : Felt).isU32 = true :=
      felt_ofNat_isU32_of_lt _ hK
    have hWf : (Felt.ofNat W : Felt).isU32 = true :=
      felt_ofNat_isU32_of_lt _ hW
    have hpairs_rest : ∀ p ∈ rest, p.1 < 2^32 ∧ p.2 < 2^32 :=
      fun p hp => hpairs p (List.mem_cons_of_mem _ hp)
    simp only [sha256PaddingOps]
    rw [execWithEnv_append]
    have hround : execWithEnv sha256ProcEnv 95
        ⟨a :: b :: c :: d :: e :: f :: g :: h :: tail, mem, locs, adv⟩
        [.inst (.push (Felt.ofNat W)), .inst (.movdn 8),
         .inst (.push (Felt.ofNat K)), .inst (.movdn 8),
         .inst (.exec "consume_message_word")] =
        some ⟨sha256OneRoundFelt a b c d e f g h (Felt.ofNat K) (Felt.ofNat W) ++ tail,
              mem, locs, adv⟩ := by
      unfold execWithEnv
      simp only [List.foldlM]
      rw [stepPush]; miden_bind
      miden_movdn
      rw [stepPush]; miden_bind
      miden_movdn
      simp only [show sha256ProcEnv "consume_message_word" =
          some Miden.Core.Sha256.consume_message_word from rfl]
      rw [sha256_consume_message_word_correct (hs := rfl) (h0 := ha) (h1 := hb) (h2 := hc)
          (h3 := hd) (h4 := he) (h5 := hf) (h6 := hg) (h7 := hh) (h8 := hKf) (h9 := hWf)]
      simp [sha256OneRoundFelt, sha256OneRoundState, MidenState.withStack]
    rw [hround]
    simp only [bind, Bind.bind, Option.bind]
    simp only [sha256OneRoundFelt, sha256OneRoundState]
    -- Prove isU32 for the new a' and e' (first and fifth elements of the next-round state)
    have ha' : (Felt.ofNat (
        let ch_v := (f.val &&& e.val) ^^^ ((u32Max - 1 - e.val) &&& g.val)
        let t1p  := (ch_v + (Felt.ofNat K).val + (Felt.ofNat W).val) % 2^32
        let sig1 := u32RotateRight e.val 6 ^^^
                    (u32RotateRight e.val 11 ^^^ u32RotateRight e.val 25)
        let T1   := (t1p + sig1 + h.val) % 2^32
        let maj_v := (b.val &&& a.val) ^^^
                     ((a.val &&& c.val) ^^^ (b.val &&& c.val))
        let sig0 := u32RotateRight a.val 2 ^^^
                    (u32RotateRight a.val 13 ^^^ u32RotateRight a.val 22)
        let T2   := (maj_v + sig0) % 2^32
        (T1 + T2) % 2^32)).isU32 = true := u32_mod_isU32 _
    have he' : (Felt.ofNat (
        let ch_v := (f.val &&& e.val) ^^^ ((u32Max - 1 - e.val) &&& g.val)
        let t1p  := (ch_v + (Felt.ofNat K).val + (Felt.ofNat W).val) % 2^32
        let sig1 := u32RotateRight e.val 6 ^^^
                    (u32RotateRight e.val 11 ^^^ u32RotateRight e.val 25)
        let T1   := (t1p + sig1 + h.val) % 2^32
        (d.val + T1) % 2^32)).isU32 = true := u32_mod_isU32 _
    -- Apply the IH: execWithEnv on the remaining rounds
    apply ih
    · exact ha'
    · exact ha
    · exact hb
    · exact hc
    · exact he'
    · exact he
    · exact hf
    · exact hg
    · exact hpairs_rest

-- ============================================================================
-- Finalization ops (30 instructions: element-wise Merkle-Damgård addition)
-- ============================================================================

private def sha256FinalizeOps : List Op := [
  .inst (.movup 8), .inst .u32WrappingAdd, .inst (.swap 1),
  .inst (.movup 8), .inst .u32WrappingAdd, .inst (.swap 1),
  .inst (.movup 2), .inst (.movup 8), .inst .u32WrappingAdd, .inst (.movdn 2),
  .inst (.movup 3), .inst (.movup 8), .inst .u32WrappingAdd, .inst (.movdn 3),
  .inst (.movup 4), .inst (.movup 8), .inst .u32WrappingAdd, .inst (.movdn 4),
  .inst (.movup 5), .inst (.movup 8), .inst .u32WrappingAdd, .inst (.movdn 5),
  .inst (.movup 6), .inst (.movup 8), .inst .u32WrappingAdd, .inst (.movdn 6),
  .inst (.movup 7), .inst (.movup 8), .inst .u32WrappingAdd, .inst (.movdn 7)]

set_option maxHeartbeats 4000000 in
private lemma sha256Finalize_bridge
    (a64 b64 c64 d64 e64 f64 g64 h64 : Felt)
    (x0 x1 x2 x3 x4 x5 x6 x7 : Felt)
    (ha64 : a64.isU32 = true) (hb64 : b64.isU32 = true)
    (hc64 : c64.isU32 = true) (hd64 : d64.isU32 = true)
    (he64 : e64.isU32 = true) (hf64 : f64.isU32 = true)
    (hg64 : g64.isU32 = true) (hh64 : h64.isU32 = true)
    (hx0 : x0.isU32 = true) (hx1 : x1.isU32 = true)
    (hx2 : x2.isU32 = true) (hx3 : x3.isU32 = true)
    (hx4 : x4.isU32 = true) (hx5 : x5.isU32 = true)
    (hx6 : x6.isU32 = true) (hx7 : x7.isU32 = true)
    (rest : List Felt) (mem locs : Nat → Felt) (adv : List Felt) :
    execWithEnv sha256ProcEnv 95
      ⟨a64 :: b64 :: c64 :: d64 :: e64 :: f64 :: g64 :: h64 ::
       x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: rest, mem, locs, adv⟩
      sha256FinalizeOps =
    some ⟨[Felt.ofNat ((a64.val + x0.val) % 2^32),
           Felt.ofNat ((b64.val + x1.val) % 2^32),
           Felt.ofNat ((c64.val + x2.val) % 2^32),
           Felt.ofNat ((d64.val + x3.val) % 2^32),
           Felt.ofNat ((e64.val + x4.val) % 2^32),
           Felt.ofNat ((f64.val + x5.val) % 2^32),
           Felt.ofNat ((g64.val + x6.val) % 2^32),
           Felt.ofNat ((h64.val + x7.val) % 2^32)] ++ rest,
          mem, locs, adv⟩ := by
  unfold execWithEnv
  simp only [List.foldlM, sha256FinalizeOps]
  miden_movup
  rw [stepU32WrappingAdd (ha := ha64) (hb := hx0)]; miden_bind
  miden_swap
  miden_movup
  rw [stepU32WrappingAdd (ha := hb64) (hb := hx1)]; miden_bind
  miden_swap
  miden_movup
  miden_movup
  rw [stepU32WrappingAdd (ha := hc64) (hb := hx2)]; miden_bind
  miden_movdn
  miden_movup
  miden_movup
  rw [stepU32WrappingAdd (ha := hd64) (hb := hx3)]; miden_bind
  miden_movdn
  miden_movup
  miden_movup
  rw [stepU32WrappingAdd (ha := he64) (hb := hx4)]; miden_bind
  miden_movdn
  miden_movup
  miden_movup
  rw [stepU32WrappingAdd (ha := hf64) (hb := hx5)]; miden_bind
  miden_movdn
  miden_movup
  miden_movup
  rw [stepU32WrappingAdd (ha := hg64) (hb := hx6)]; miden_bind
  miden_movdn
  miden_movup
  miden_movup
  rw [stepU32WrappingAdd (ha := hh64) (hb := hx7)]; miden_bind
  miden_movdn
  simp [pure, Pure.pure]

-- ============================================================================
-- The SHA-256 padding state (opaque output function)
-- ============================================================================

/-- The output of `consume_padding_message_schedule`: runs 64 rounds of SHA-256
    compression with the padding message schedule constants, then performs
    the Merkle-Damgård addition with the initial state. -/
def sha256PaddingState (x0 x1 x2 x3 x4 x5 x6 x7 : Felt) : List Felt :=
  let (a64, b64, c64, d64, e64, f64, g64, h64) :=
    sha256FeltFold (x0, x1, x2, x3, x4, x5, x6, x7) sha256PaddingConstants
  [Felt.ofNat ((a64.val + x0.val) % 2^32),
   Felt.ofNat ((b64.val + x1.val) % 2^32),
   Felt.ofNat ((c64.val + x2.val) % 2^32),
   Felt.ofNat ((d64.val + x3.val) % 2^32),
   Felt.ofNat ((e64.val + x4.val) % 2^32),
   Felt.ofNat ((f64.val + x5.val) % 2^32),
   Felt.ofNat ((g64.val + x6.val) % 2^32),
   Felt.ofNat ((h64.val + x7.val) % 2^32)]

-- ============================================================================
-- Main correctness theorem
-- ============================================================================

set_option maxHeartbeats 8000000 in
/-- `sha256::consume_padding_message_schedule` applies 64 SHA-256 compression rounds
    using the padding block message schedule (with hardcoded W_i, K_i constants),
    followed by the Merkle-Damgård addition of the initial state.
    Input stack:  [x0, x1, x2, x3, x4, x5, x6, x7] ++ rest
    Output stack: [sha256PaddingState x0..x7] ++ rest -/
theorem sha256_consume_padding_message_schedule_correct
    (x0 x1 x2 x3 x4 x5 x6 x7 : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: rest)
    (h0 : x0.isU32 = true) (h1 : x1.isU32 = true) (h2 : x2.isU32 = true)
    (h3 : x3.isU32 = true) (h4 : x4.isU32 = true) (h5 : x5.isU32 = true)
    (h6 : x6.isU32 = true) (h7 : x7.isU32 = true) :
    execWithEnv sha256ProcEnv 95 s Miden.Core.Sha256.consume_padding_message_schedule =
    some (s.withStack (sha256PaddingState x0 x1 x2 x3 x4 x5 x6 x7 ++ rest)) := by
  obtain ⟨stk, mem, locs, adv⟩ := s
  simp only [MidenState.withStack] at hs ⊢
  subst hs
  rw [show Miden.Core.Sha256.consume_padding_message_schedule =
      [.inst (.dupw 1), .inst (.dupw 1)] ++
      sha256PaddingOps sha256PaddingConstants ++
      sha256FinalizeOps from rfl]
  rw [execWithEnv_append, execWithEnv_append]
  unfold execWithEnv
  simp only [List.foldlM]
  rw [stepDupw1]; miden_bind
  rw [stepDupw1]; miden_bind
  rw [sha256PaddingRounds_bridge h0 h1 h2 h3 h4 h5 h6 h7
      sha256PaddingConstants
      (by native_decide)
      (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: rest)]
  simp only [bind, Bind.bind, Option.bind]
  rcases h_fold_eq : sha256FeltFold (x0, x1, x2, x3, x4, x5, x6, x7) sha256PaddingConstants with
    ⟨a64, b64, c64, d64, e64, f64, g64, h64⟩
  have hflist : sha256FoldList (x0, x1, x2, x3, x4, x5, x6, x7) sha256PaddingConstants =
      [a64, b64, c64, d64, e64, f64, g64, h64] := by
    simp [sha256FoldList, h_fold_eq]
  rw [hflist]
  have ⟨ha64, hb64, hc64, hd64, he64, hf64, hg64, hh64⟩ :
      a64.isU32 = true ∧ b64.isU32 = true ∧ c64.isU32 = true ∧ d64.isU32 = true ∧
      e64.isU32 = true ∧ f64.isU32 = true ∧ g64.isU32 = true ∧ h64.isU32 = true := by
    have h := sha256FeltFold_isU32 x0 x1 x2 x3 x4 x5 x6 x7
        h0 h1 h2 h3 h4 h5 h6 h7 sha256PaddingConstants
    simp [h_fold_eq] at h; exact h
  rw [show [a64, b64, c64, d64, e64, f64, g64, h64] ++
      x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: rest =
      a64 :: b64 :: c64 :: d64 :: e64 :: f64 :: g64 :: h64 ::
      x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: rest from rfl]
  rw [sha256Finalize_bridge ha64 hb64 hc64 hd64 he64 hf64 hg64 hh64
      h0 h1 h2 h3 h4 h5 h6 h7]
  simp [sha256PaddingState, h_fold_eq]

end MidenLean.Proofs.Sha256
