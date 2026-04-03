import MidenLean.Proofs.Sha256.Common

namespace MidenLean.Proofs.Sha256

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

-- ============================================================================
-- Bridge lemmas: sub-procedures evaluated under sha256ProcEnv in isolation.
-- ============================================================================

set_option maxHeartbeats 4000000 in
private lemma execWithEnv_ch_bridge
    (e f g : Felt) (rest : List Felt) (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (he : e.isU32 = true) (hf : f.isU32 = true) (hg : g.isU32 = true) :
    execWithEnv sha256ProcEnv 93 ⟨e :: f :: g :: rest, mem, frames, adv⟩
        Miden.Core.Sha256.ch =
    some ⟨Felt.ofNat ((f.val &&& e.val) ^^^ ((u32Max - 1 - e.val) &&& g.val)) :: rest,
          mem, frames, adv⟩ := by
  have he_lt : e.val < 2^32 := by simpa [Felt.isU32] using he
  have hf_lt : f.val < 2^32 := by simpa [Felt.isU32] using hf
  have hg_lt : g.val < 2^32 := by simpa [Felt.isU32] using hg
  have hef_lt  : f.val &&& e.val < 2^32      := Nat.bitwise_lt_two_pow hf_lt he_lt
  have hef_u32 : (Felt.ofNat (f.val &&& e.val)).isU32 = true := felt_ofNat_isU32_of_lt _ hef_lt
  have hef_val : (Felt.ofNat (f.val &&& e.val)).val = f.val &&& e.val :=
    felt_ofNat_val_of_u32 _ hef_lt
  have hnot_lt  : u32Max - 1 - e.val < 2^32 := by unfold u32Max; omega
  have hnot_u32 : (Felt.ofNat (u32Max - 1 - e.val)).isU32 = true :=
    felt_ofNat_isU32_of_lt _ hnot_lt
  have hnot_val : (Felt.ofNat (u32Max - 1 - e.val)).val = u32Max - 1 - e.val :=
    felt_ofNat_val_of_u32 _ hnot_lt
  have hng_lt  : (u32Max - 1 - e.val) &&& g.val < 2^32 :=
    Nat.bitwise_lt_two_pow hnot_lt hg_lt
  have hng_u32 : (Felt.ofNat ((u32Max - 1 - e.val) &&& g.val)).isU32 = true :=
    felt_ofNat_isU32_of_lt _ hng_lt
  have hng_val : (Felt.ofNat ((u32Max - 1 - e.val) &&& g.val)).val =
      (u32Max - 1 - e.val) &&& g.val := felt_ofNat_val_of_u32 _ hng_lt
  unfold Miden.Core.Sha256.ch execWithEnv
  simp only [List.foldlM]
  miden_swap; miden_dup
  rw [stepU32And (ha := hf) (hb := he)]; miden_bind
  miden_swap
  rw [stepU32Not (ha := he)]; miden_bind
  miden_movup
  rw [stepU32And (ha := hnot_u32) (hb := hg)]; miden_bind; rw [hnot_val]
  rw [stepU32Xor (ha := hef_u32) (hb := hng_u32)]; miden_bind; rw [hef_val, hng_val]
  simp only [pure, Pure.pure]

set_option maxHeartbeats 4000000 in
private lemma execWithEnv_cap_sigma_1_bridge
    (a : Felt) (rest : List Felt) (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (ha : a.isU32 = true) :
    execWithEnv sha256ProcEnv 93 ⟨a :: rest, mem, frames, adv⟩
        Miden.Core.Sha256.cap_sigma_1 =
    some ⟨Felt.ofNat (u32RotateRight a.val 6 ^^^
            (u32RotateRight a.val 11 ^^^ u32RotateRight a.val 25)) :: rest,
          mem, frames, adv⟩ := by
  have ha_lt : a.val < 2^32 := by simpa [Felt.isU32] using ha
  have hr6_u32  : (Felt.ofNat (u32RotateRight a.val 6)).isU32  = true :=
    u32RotateRight_isU32 a ha 6
  have hr11_u32 : (Felt.ofNat (u32RotateRight a.val 11)).isU32 = true :=
    u32RotateRight_isU32 a ha 11
  have hr25_u32 : (Felt.ofNat (u32RotateRight a.val 25)).isU32 = true :=
    u32RotateRight_isU32 a ha 25
  have hr6_val  : (Felt.ofNat (u32RotateRight a.val 6)).val  = u32RotateRight a.val 6 :=
    felt_ofNat_val_of_u32 _ (u32RotateRight_lt a.val 6 ha_lt)
  have hr11_val : (Felt.ofNat (u32RotateRight a.val 11)).val = u32RotateRight a.val 11 :=
    felt_ofNat_val_of_u32 _ (u32RotateRight_lt a.val 11 ha_lt)
  have hr25_val : (Felt.ofNat (u32RotateRight a.val 25)).val = u32RotateRight a.val 25 :=
    felt_ofNat_val_of_u32 _ (u32RotateRight_lt a.val 25 ha_lt)
  have hx_lt : u32RotateRight a.val 11 ^^^ u32RotateRight a.val 25 < 2^32 :=
    Nat.bitwise_lt_two_pow (u32RotateRight_lt a.val 11 ha_lt) (u32RotateRight_lt a.val 25 ha_lt)
  have hx_u32 : (Felt.ofNat (u32RotateRight a.val 11 ^^^ u32RotateRight a.val 25)).isU32 = true :=
    felt_ofNat_isU32_of_lt _ hx_lt
  have hx_val : (Felt.ofNat (u32RotateRight a.val 11 ^^^ u32RotateRight a.val 25)).val =
      u32RotateRight a.val 11 ^^^ u32RotateRight a.val 25 :=
    felt_ofNat_val_of_u32 _ hx_lt
  unfold Miden.Core.Sha256.cap_sigma_1 execWithEnv
  simp only [List.foldlM]
  miden_dup
  rw [stepU32RotrImm (ha := ha) (hn := by decide)]; miden_bind
  miden_swap; miden_dup
  rw [stepU32RotrImm (ha := ha) (hn := by decide)]; miden_bind
  miden_swap
  rw [stepU32RotrImm (ha := ha) (hn := by decide)]; miden_bind
  rw [stepU32Xor (ha := hr11_u32) (hb := hr25_u32)]; miden_bind; rw [hr11_val, hr25_val]
  rw [stepU32Xor (ha := hr6_u32) (hb := hx_u32)]; miden_bind; rw [hr6_val, hx_val]
  simp only [pure, Pure.pure]

set_option maxHeartbeats 4000000 in
private lemma execWithEnv_maj_bridge
    (a b c : Felt) (rest : List Felt) (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true) (hc : c.isU32 = true) :
    execWithEnv sha256ProcEnv 93 ⟨a :: b :: c :: rest, mem, frames, adv⟩
        Miden.Core.Sha256.maj =
    some ⟨Felt.ofNat ((b.val &&& a.val) ^^^
            ((a.val &&& c.val) ^^^ (b.val &&& c.val))) :: rest,
          mem, frames, adv⟩ := by
  have ha_lt : a.val < 2^32 := by simpa [Felt.isU32] using ha
  have hb_lt : b.val < 2^32 := by simpa [Felt.isU32] using hb
  have hc_lt : c.val < 2^32 := by simpa [Felt.isU32] using hc
  have hab_lt  : b.val &&& a.val < 2^32 := Nat.bitwise_lt_two_pow hb_lt ha_lt
  have hab_u32 : (Felt.ofNat (b.val &&& a.val)).isU32 = true := felt_ofNat_isU32_of_lt _ hab_lt
  have hab_val : (Felt.ofNat (b.val &&& a.val)).val = b.val &&& a.val :=
    felt_ofNat_val_of_u32 _ hab_lt
  have hac_lt  : a.val &&& c.val < 2^32 := Nat.bitwise_lt_two_pow ha_lt hc_lt
  have hac_u32 : (Felt.ofNat (a.val &&& c.val)).isU32 = true := felt_ofNat_isU32_of_lt _ hac_lt
  have hac_val : (Felt.ofNat (a.val &&& c.val)).val = a.val &&& c.val :=
    felt_ofNat_val_of_u32 _ hac_lt
  have hbc_lt  : b.val &&& c.val < 2^32 := Nat.bitwise_lt_two_pow hb_lt hc_lt
  have hbc_u32 : (Felt.ofNat (b.val &&& c.val)).isU32 = true := felt_ofNat_isU32_of_lt _ hbc_lt
  have hbc_val : (Felt.ofNat (b.val &&& c.val)).val = b.val &&& c.val :=
    felt_ofNat_val_of_u32 _ hbc_lt
  have hx_lt   : (a.val &&& c.val) ^^^ (b.val &&& c.val) < 2^32 :=
    Nat.bitwise_lt_two_pow hac_lt hbc_lt
  have hx_u32  : (Felt.ofNat ((a.val &&& c.val) ^^^ (b.val &&& c.val))).isU32 = true :=
    felt_ofNat_isU32_of_lt _ hx_lt
  have hx_val  : (Felt.ofNat ((a.val &&& c.val) ^^^ (b.val &&& c.val))).val =
      (a.val &&& c.val) ^^^ (b.val &&& c.val) := felt_ofNat_val_of_u32 _ hx_lt
  unfold Miden.Core.Sha256.maj execWithEnv
  simp only [List.foldlM]
  miden_dup; miden_dup
  rw [stepU32And (ha := hb) (hb := ha)]; miden_bind
  miden_swap; miden_dup
  rw [stepU32And (ha := ha) (hb := hc)]; miden_bind
  miden_movup; miden_movup
  rw [stepU32And (ha := hb) (hb := hc)]; miden_bind
  rw [stepU32Xor (ha := hac_u32) (hb := hbc_u32)]; miden_bind; rw [hac_val, hbc_val]
  rw [stepU32Xor (ha := hab_u32) (hb := hx_u32)]; miden_bind; rw [hab_val, hx_val]
  simp only [pure, Pure.pure]

set_option maxHeartbeats 4000000 in
private lemma execWithEnv_cap_sigma_0_bridge
    (a : Felt) (rest : List Felt) (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (ha : a.isU32 = true) :
    execWithEnv sha256ProcEnv 93 ⟨a :: rest, mem, frames, adv⟩
        Miden.Core.Sha256.cap_sigma_0 =
    some ⟨Felt.ofNat (u32RotateRight a.val 2 ^^^
            (u32RotateRight a.val 13 ^^^ u32RotateRight a.val 22)) :: rest,
          mem, frames, adv⟩ := by
  have ha_lt : a.val < 2^32 := by simpa [Felt.isU32] using ha
  have hr2_u32  : (Felt.ofNat (u32RotateRight a.val 2)).isU32  = true :=
    u32RotateRight_isU32 a ha 2
  have hr13_u32 : (Felt.ofNat (u32RotateRight a.val 13)).isU32 = true :=
    u32RotateRight_isU32 a ha 13
  have hr22_u32 : (Felt.ofNat (u32RotateRight a.val 22)).isU32 = true :=
    u32RotateRight_isU32 a ha 22
  have hr2_val  : (Felt.ofNat (u32RotateRight a.val 2)).val  = u32RotateRight a.val 2 :=
    felt_ofNat_val_of_u32 _ (u32RotateRight_lt a.val 2 ha_lt)
  have hr13_val : (Felt.ofNat (u32RotateRight a.val 13)).val = u32RotateRight a.val 13 :=
    felt_ofNat_val_of_u32 _ (u32RotateRight_lt a.val 13 ha_lt)
  have hr22_val : (Felt.ofNat (u32RotateRight a.val 22)).val = u32RotateRight a.val 22 :=
    felt_ofNat_val_of_u32 _ (u32RotateRight_lt a.val 22 ha_lt)
  have hx_lt : u32RotateRight a.val 13 ^^^ u32RotateRight a.val 22 < 2^32 :=
    Nat.bitwise_lt_two_pow (u32RotateRight_lt a.val 13 ha_lt) (u32RotateRight_lt a.val 22 ha_lt)
  have hx_u32 : (Felt.ofNat (u32RotateRight a.val 13 ^^^ u32RotateRight a.val 22)).isU32 = true :=
    felt_ofNat_isU32_of_lt _ hx_lt
  have hx_val : (Felt.ofNat (u32RotateRight a.val 13 ^^^ u32RotateRight a.val 22)).val =
      u32RotateRight a.val 13 ^^^ u32RotateRight a.val 22 :=
    felt_ofNat_val_of_u32 _ hx_lt
  unfold Miden.Core.Sha256.cap_sigma_0 execWithEnv
  simp only [List.foldlM]
  miden_dup
  rw [stepU32RotrImm (ha := ha) (hn := by decide)]; miden_bind
  miden_swap; miden_dup
  rw [stepU32RotrImm (ha := ha) (hn := by decide)]; miden_bind
  miden_swap
  rw [stepU32RotrImm (ha := ha) (hn := by decide)]; miden_bind
  rw [stepU32Xor (ha := hr13_u32) (hb := hr22_u32)]; miden_bind; rw [hr13_val, hr22_val]
  rw [stepU32Xor (ha := hr2_u32) (hb := hx_u32)]; miden_bind; rw [hr2_val, hx_val]
  simp only [pure, Pure.pure]

-- ============================================================================
-- Execution chunk lemmas.
-- Each chunk takes explicit Nat values for intermediate results (not Felt)
-- to avoid Felt.val unification issues in the final proof step.
-- ============================================================================

-- Chunk A: dup6 dup6 dup6  exec"ch"  movup9 movup10 u32WrappingAdd3
-- Input:  [x0,x1,x2,x3,x4,x5,x6,x7,x8,x9]++rest
-- Output: [Felt.ofNat t1p, x0,x1,x2,x3,x4,x5,x6,x7]++rest
set_option maxHeartbeats 4000000 in
private lemma consume_chunkA
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : Felt) (rest : List Felt)
    (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (h4 : x4.isU32 = true) (h5 : x5.isU32 = true) (h6 : x6.isU32 = true)
    (h8 : x8.isU32 = true) (h9 : x9.isU32 = true) :
    execWithEnv sha256ProcEnv 94
        ⟨x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: rest, mem, frames, adv⟩
        [Op.inst (.dup 6), Op.inst (.dup 6), Op.inst (.dup 6), Op.inst (.exec "ch"),
         Op.inst (.movup 9), Op.inst (.movup 10), Op.inst (.u32WrappingAdd3)] =
    some ⟨Felt.ofNat ((((x5.val &&& x4.val) ^^^ ((u32Max - 1 - x4.val) &&& x6.val)) +
                       x8.val + x9.val) % 2^32) ::
          x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: rest, mem, frames, adv⟩ := by
  have h4_lt : x4.val < 2^32 := by simpa [Felt.isU32] using h4
  have hch_lt : (x5.val &&& x4.val) ^^^ ((u32Max - 1 - x4.val) &&& x6.val) < 2^32 :=
    Nat.bitwise_lt_two_pow
      (Nat.bitwise_lt_two_pow (by simpa [Felt.isU32] using h5) h4_lt)
      (Nat.bitwise_lt_two_pow (by unfold u32Max; omega) (by simpa [Felt.isU32] using h6))
  have hch_u32 : (Felt.ofNat ((x5.val &&& x4.val) ^^^
      ((u32Max - 1 - x4.val) &&& x6.val))).isU32 = true := felt_ofNat_isU32_of_lt _ hch_lt
  have hch_val : (Felt.ofNat ((x5.val &&& x4.val) ^^^
      ((u32Max - 1 - x4.val) &&& x6.val))).val =
      (x5.val &&& x4.val) ^^^ ((u32Max - 1 - x4.val) &&& x6.val) :=
    felt_ofNat_val_of_u32 _ hch_lt
  unfold execWithEnv
  simp only [List.foldlM]
  miden_dup; miden_dup; miden_dup
  simp only [show sha256ProcEnv "ch" = some Miden.Core.Sha256.ch from rfl]
  rw [execWithEnv_ch_bridge (he := h4) (hf := h5) (hg := h6)]
  simp only [bind, Bind.bind, Option.bind]
  miden_movup; miden_movup
  rw [stepU32WrappingAdd3 (ha := hch_u32) (hb := h8) (hc := h9)]; miden_bind
  rw [hch_val]
  rfl

-- Chunk B: dup5  exec"cap_sigma_1"  movup9 u32WrappingAdd3
-- Input:  [Felt.ofNat t1p, x0,x1,x2,x3,x4,x5,x6,x7]++rest
-- Output: [Felt.ofNat T1, x0,x1,x2,x3,x4,x5,x6]++rest
--         T1 = (t1p + σ₁(x4) + x7.val) % 2^32
set_option maxHeartbeats 4000000 in
private lemma consume_chunkB
    (t1p : Nat) (x0 x1 x2 x3 x4 x5 x6 x7 : Felt) (rest : List Felt)
    (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (ht1p : t1p < 2^32) (h4 : x4.isU32 = true) (h7 : x7.isU32 = true) :
    execWithEnv sha256ProcEnv 94
        ⟨Felt.ofNat t1p :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: rest, mem, frames, adv⟩
        [Op.inst (.dup 5), Op.inst (.exec "cap_sigma_1"),
         Op.inst (.movup 9), Op.inst (.u32WrappingAdd3)] =
    some ⟨Felt.ofNat ((t1p +
              (u32RotateRight x4.val 6 ^^^
               (u32RotateRight x4.val 11 ^^^ u32RotateRight x4.val 25)) +
              x7.val) % 2^32) ::
          x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: rest, mem, frames, adv⟩ := by
  have ht1p_u32 : (Felt.ofNat t1p).isU32 = true := felt_ofNat_isU32_of_lt _ ht1p
  have ht1p_val : (Felt.ofNat t1p).val = t1p := felt_ofNat_val_of_u32 _ ht1p
  have h4_lt : x4.val < 2^32 := by simpa [Felt.isU32] using h4
  have hx_lt : u32RotateRight x4.val 11 ^^^ u32RotateRight x4.val 25 < 2^32 :=
    Nat.bitwise_lt_two_pow (u32RotateRight_lt x4.val 11 h4_lt) (u32RotateRight_lt x4.val 25 h4_lt)
  have hsig1_lt : u32RotateRight x4.val 6 ^^^
      (u32RotateRight x4.val 11 ^^^ u32RotateRight x4.val 25) < 2^32 :=
    Nat.bitwise_lt_two_pow (u32RotateRight_lt x4.val 6 h4_lt) hx_lt
  have hsig1_u32 : (Felt.ofNat (u32RotateRight x4.val 6 ^^^
      (u32RotateRight x4.val 11 ^^^ u32RotateRight x4.val 25))).isU32 = true :=
    felt_ofNat_isU32_of_lt _ hsig1_lt
  have hsig1_val : (Felt.ofNat (u32RotateRight x4.val 6 ^^^
      (u32RotateRight x4.val 11 ^^^ u32RotateRight x4.val 25))).val =
      u32RotateRight x4.val 6 ^^^ (u32RotateRight x4.val 11 ^^^ u32RotateRight x4.val 25) :=
    felt_ofNat_val_of_u32 _ hsig1_lt
  unfold execWithEnv
  simp only [List.foldlM]
  miden_dup
  simp only [show sha256ProcEnv "cap_sigma_1" = some Miden.Core.Sha256.cap_sigma_1 from rfl]
  rw [execWithEnv_cap_sigma_1_bridge (ha := h4)]
  simp only [bind, Bind.bind, Option.bind]
  miden_movup
  rw [stepU32WrappingAdd3 (ha := ht1p_u32) (hb := hsig1_u32) (hc := h7)]; miden_bind
  rw [ht1p_val, hsig1_val]
  simp only [pure, Pure.pure]

-- Chunk C: dup3 dup3 dup3  exec"maj"
-- Input:  [Felt.ofNat T1, x0,x1,x2,x3,x4,x5,x6]++rest
-- Output: [Felt.ofNat maj_v, Felt.ofNat T1, x0,x1,x2,x3,x4,x5,x6]++rest
set_option maxHeartbeats 4000000 in
private lemma consume_chunkC
    (T1 : Nat) (x0 x1 x2 x3 x4 x5 x6 : Felt) (rest : List Felt)
    (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (h0 : x0.isU32 = true) (h1 : x1.isU32 = true) (h2 : x2.isU32 = true) :
    execWithEnv sha256ProcEnv 94
        ⟨Felt.ofNat T1 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: rest, mem, frames, adv⟩
        [Op.inst (.dup 3), Op.inst (.dup 3), Op.inst (.dup 3), Op.inst (.exec "maj")] =
    some ⟨Felt.ofNat ((x1.val &&& x0.val) ^^^
              ((x0.val &&& x2.val) ^^^ (x1.val &&& x2.val))) ::
          Felt.ofNat T1 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: rest,
          mem, frames, adv⟩ := by
  unfold execWithEnv
  simp only [List.foldlM]
  miden_dup; miden_dup; miden_dup
  simp only [show sha256ProcEnv "maj" = some Miden.Core.Sha256.maj from rfl]
  rw [execWithEnv_maj_bridge (ha := h0) (hb := h1) (hc := h2)]
  simp only [bind, Bind.bind, Option.bind, pure, Pure.pure]

-- Chunk D: dup2  exec"cap_sigma_0"  u32WrappingAdd  movup5 dup2 u32WrappingAdd  movdn5 u32WrappingAdd
-- Input:  [Felt.ofNat maj_v, Felt.ofNat T1, x0,x1,x2,x3,x4,x5,x6]++rest
-- Output: [Felt.ofNat ((T1+T2)%2^32), x0,x1,x2, Felt.ofNat ((x3.val+T1)%2^32), x4,x5,x6]++rest
--         T2 = (maj_v + σ₀(x0)) % 2^32
set_option maxHeartbeats 4000000 in
private lemma consume_chunkD
    (maj_v T1 : Nat) (x0 x1 x2 x3 x4 x5 x6 : Felt) (rest : List Felt)
    (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (hmaj : maj_v < 2^32) (hT1 : T1 < 2^32)
    (h0 : x0.isU32 = true) (h3 : x3.isU32 = true) :
    execWithEnv sha256ProcEnv 94
        ⟨Felt.ofNat maj_v :: Felt.ofNat T1 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: rest,
         mem, frames, adv⟩
        [Op.inst (.dup 2), Op.inst (.exec "cap_sigma_0"), Op.inst (.u32WrappingAdd),
         Op.inst (.movup 5), Op.inst (.dup 2), Op.inst (.u32WrappingAdd),
         Op.inst (.movdn 5), Op.inst (.u32WrappingAdd)] =
    some ⟨Felt.ofNat ((T1 + (maj_v + (u32RotateRight x0.val 2 ^^^
              (u32RotateRight x0.val 13 ^^^ u32RotateRight x0.val 22))) % 2^32) % 2^32) ::
          x0 :: x1 :: x2 ::
          Felt.ofNat ((x3.val + T1) % 2^32) ::
          x4 :: x5 :: x6 :: rest, mem, frames, adv⟩ := by
  have hmaj_u32 : (Felt.ofNat maj_v).isU32 = true := felt_ofNat_isU32_of_lt _ hmaj
  have hmaj_val : (Felt.ofNat maj_v).val = maj_v := felt_ofNat_val_of_u32 _ hmaj
  have hT1_u32  : (Felt.ofNat T1).isU32 = true  := felt_ofNat_isU32_of_lt _ hT1
  have hT1_val  : (Felt.ofNat T1).val = T1       := felt_ofNat_val_of_u32 _ hT1
  have h0_lt : x0.val < 2^32 := by simpa [Felt.isU32] using h0
  have hx_lt : u32RotateRight x0.val 13 ^^^ u32RotateRight x0.val 22 < 2^32 :=
    Nat.bitwise_lt_two_pow (u32RotateRight_lt x0.val 13 h0_lt) (u32RotateRight_lt x0.val 22 h0_lt)
  have hsig0_lt : u32RotateRight x0.val 2 ^^^
      (u32RotateRight x0.val 13 ^^^ u32RotateRight x0.val 22) < 2^32 :=
    Nat.bitwise_lt_two_pow (u32RotateRight_lt x0.val 2 h0_lt) hx_lt
  have hsig0_u32 : (Felt.ofNat (u32RotateRight x0.val 2 ^^^
      (u32RotateRight x0.val 13 ^^^ u32RotateRight x0.val 22))).isU32 = true :=
    felt_ofNat_isU32_of_lt _ hsig0_lt
  have hsig0_val : (Felt.ofNat (u32RotateRight x0.val 2 ^^^
      (u32RotateRight x0.val 13 ^^^ u32RotateRight x0.val 22))).val =
      u32RotateRight x0.val 2 ^^^ (u32RotateRight x0.val 13 ^^^ u32RotateRight x0.val 22) :=
    felt_ofNat_val_of_u32 _ hsig0_lt
  have hT2_u32 : (Felt.ofNat ((maj_v + (u32RotateRight x0.val 2 ^^^
      (u32RotateRight x0.val 13 ^^^ u32RotateRight x0.val 22))) % 2^32)).isU32 = true :=
    u32_mod_isU32 _
  have hT2_val : (Felt.ofNat ((maj_v + (u32RotateRight x0.val 2 ^^^
      (u32RotateRight x0.val 13 ^^^ u32RotateRight x0.val 22))) % 2^32)).val =
      (maj_v + (u32RotateRight x0.val 2 ^^^
       (u32RotateRight x0.val 13 ^^^ u32RotateRight x0.val 22))) % 2^32 :=
    felt_ofNat_val_of_u32 _ (Nat.mod_lt _ (by norm_num))
  unfold execWithEnv
  simp only [List.foldlM]
  miden_dup
  simp only [show sha256ProcEnv "cap_sigma_0" = some Miden.Core.Sha256.cap_sigma_0 from rfl]
  rw [execWithEnv_cap_sigma_0_bridge (ha := h0)]
  simp only [bind, Bind.bind, Option.bind]
  rw [stepU32WrappingAdd (ha := hmaj_u32) (hb := hsig0_u32)]; miden_bind
  rw [hmaj_val, hsig0_val]
  miden_movup; miden_dup
  rw [stepU32WrappingAdd (ha := h3) (hb := hT1_u32)]; miden_bind
  rw [hT1_val]
  miden_movdn
  rw [stepU32WrappingAdd (ha := hT1_u32) (hb := hT2_u32)]; miden_bind
  rw [hT1_val, hT2_val]
  simp only [pure, Pure.pure]

-- ============================================================================
-- Main theorem
-- ============================================================================

set_option maxHeartbeats 2000000 in
/-- `sha256::consume_message_word` performs one SHA-256 compression round. Given working
    state [a, b, c, d, e, f, g, h] and round inputs [W, K], computes
    T1 = h + Σ₁(e) + Ch(e,f,g) + K + W and T2 = Σ₀(a) + Maj(a,b,c), and returns
    the updated state [T1+T2, a, b, c, d+T1, e, f, g] (all mod 2³²).
    Input stack:  [a, b, c, d, e, f, g, h, W, K] ++ rest
    Output stack: [T1+T2, a, b, c, d+T1, e, f, g] ++ rest -/
theorem sha256_consume_message_word_correct
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: rest)
    (h0 : x0.isU32 = true) (h1 : x1.isU32 = true) (h2 : x2.isU32 = true)
    (h3 : x3.isU32 = true) (h4 : x4.isU32 = true) (h5 : x5.isU32 = true)
    (h6 : x6.isU32 = true) (h7 : x7.isU32 = true) (h8 : x8.isU32 = true)
    (h9 : x9.isU32 = true) :
    execWithEnv sha256ProcEnv 94 s Miden.Core.Sha256.consume_message_word =
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
        Felt.ofNat ((x3.val + T1) % 2^32) :: x4 :: x5 :: x6 :: rest)) := by
  obtain ⟨stk, mem, frames, adv⟩ := s
  simp only [MidenState.withStack] at hs ⊢
  subst hs
  -- Intermediate nat bounds for chunk instantiation
  have hmaj_lt : (x1.val &&& x0.val) ^^^
      ((x0.val &&& x2.val) ^^^ (x1.val &&& x2.val)) < 2^32 :=
    Nat.bitwise_lt_two_pow
      (Nat.bitwise_lt_two_pow (by simpa [Felt.isU32] using h1) (by simpa [Felt.isU32] using h0))
      (Nat.bitwise_lt_two_pow
        (Nat.bitwise_lt_two_pow (by simpa [Felt.isU32] using h0) (by simpa [Felt.isU32] using h2))
        (Nat.bitwise_lt_two_pow (by simpa [Felt.isU32] using h1) (by simpa [Felt.isU32] using h2)))
  -- Split consume_message_word into 4 chunks (right-associative for sequential splitting)
  rw [execWithEnv_body_eq (h := rfl) (h0 := rfl),
      show Miden.Core.Sha256.consume_message_word.body =
        [Op.inst (.dup 6), Op.inst (.dup 6), Op.inst (.dup 6), Op.inst (.exec "ch"),
         Op.inst (.movup 9), Op.inst (.movup 10), Op.inst (.u32WrappingAdd3)] ++
        ([Op.inst (.dup 5), Op.inst (.exec "cap_sigma_1"),
          Op.inst (.movup 9), Op.inst (.u32WrappingAdd3)] ++
         ([Op.inst (.dup 3), Op.inst (.dup 3), Op.inst (.dup 3), Op.inst (.exec "maj")] ++
          [Op.inst (.dup 2), Op.inst (.exec "cap_sigma_0"), Op.inst (.u32WrappingAdd),
           Op.inst (.movup 5), Op.inst (.dup 2), Op.inst (.u32WrappingAdd),
           Op.inst (.movdn 5), Op.inst (.u32WrappingAdd)])) from rfl]
  -- Apply chunks sequentially
  rw [execWithEnv_append]
  rw [consume_chunkA (h4 := h4) (h5 := h5) (h6 := h6) (h8 := h8) (h9 := h9)]
  simp only [bind, Bind.bind, Option.bind]
  rw [execWithEnv_append]
  rw [consume_chunkB (ht1p := Nat.mod_lt _ (by norm_num)) (h4 := h4) (h7 := h7)]
  simp only [bind, Bind.bind, Option.bind]
  rw [execWithEnv_append]
  rw [consume_chunkC (h0 := h0) (h1 := h1) (h2 := h2)]
  simp only [bind, Bind.bind, Option.bind]
  rw [consume_chunkD (hmaj := hmaj_lt) (hT1 := Nat.mod_lt _ (by norm_num))
      (h0 := h0) (h3 := h3)]

end MidenLean.Proofs.Sha256
