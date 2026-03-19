import MidenLean.Proofs.Tactics
import MidenLean.Generated.Word

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

private theorem felt4_val : (4 : Felt).val = 4 :=
  felt_ofNat_val_lt 4 (by unfold GOLDILOCKS_PRIME; omega)

private theorem ptr_add4_val (ptr : Felt) (hptr_room : ptr.val + 4 < 2 ^ 32) :
    (ptr + 4).val = ptr.val + 4 := by
  have hlt : ptr.val + 4 < GOLDILOCKS_PRIME := by
    unfold GOLDILOCKS_PRIME
    omega
  rw [ZMod.val_add, felt4_val, Nat.mod_eq_of_lt hlt]

private theorem stepMemStorewLeLocal
    (mem locs : Nat → Felt) (adv : List Felt)
    (a e0 e1 e2 e3 : Felt) (rest : List Felt)
    (ha_lt : a.val < 2 ^ 32) (ha_aligned : a.val % 4 = 0) :
    execInstruction ⟨a :: e0 :: e1 :: e2 :: e3 :: rest, mem, locs, adv⟩ .memStorewLe =
      some ⟨e0 :: e1 :: e2 :: e3 :: rest,
        fun addr =>
          if addr = a.val + 3 then e3
          else if addr = a.val + 2 then e2
          else if addr = a.val + 1 then e1
          else if addr = a.val then e0
          else mem addr,
        locs, adv⟩ := by
  unfold execInstruction execMemStorewLe
  have hlt : ¬a.val >= u32Max := by
    unfold u32Max
    omega
  simp [hlt, ha_aligned, MidenState.writeMemory, MidenState.withStack]

set_option maxHeartbeats 8000000 in
/-- word.store_word_u32s_le correctly writes a word to memory as eight u32 limbs in
    little-endian order.
    Input stack:  [w0, w1, w2, w3, out_ptr] ++ rest
    Output stack: rest
    Memory layout after the call:
    [w0.lo32, w0.hi32, w1.lo32, w1.hi32, w2.lo32, w2.hi32, w3.lo32, w3.hi32]
    stored at addresses out_ptr .. out_ptr + 7. -/
theorem word_store_word_u32s_le_correct
    (w0 w1 w2 w3 out_ptr : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = w0 :: w1 :: w2 :: w3 :: out_ptr :: rest)
    (hout_ptr_aligned : out_ptr.val % 4 = 0)
    (hout_ptr_room : out_ptr.val + 4 < 2 ^ 32) :
    let addr := out_ptr.val
    exec 20 s Miden.Core.Word.store_word_u32s_le =
      some ((s.writeMemory addr w0.lo32
          |>.writeMemory (addr + 1) w0.hi32
          |>.writeMemory (addr + 2) w1.lo32
          |>.writeMemory (addr + 3) w1.hi32
          |>.writeMemory (addr + 4) w2.lo32
          |>.writeMemory (addr + 5) w2.hi32
          |>.writeMemory (addr + 6) w3.lo32
          |>.writeMemory (addr + 7) w3.hi32
          |>.withStack rest)) := by
  obtain ⟨stk, mem, locs, adv⟩ := s
  simp only at hs
  subst hs
  let addr := out_ptr.val
  have h_ptr_lt : out_ptr.val < 2 ^ 32 := by
    omega
  have h_ptr4_val : (out_ptr + 4).val = out_ptr.val + 4 :=
    ptr_add4_val out_ptr hout_ptr_room
  have h_ptr4_lt : (out_ptr + 4).val < 2 ^ 32 := by
    rw [h_ptr4_val]
    exact hout_ptr_room
  have h_ptr4_aligned : (out_ptr + 4).val % 4 = 0 := by
    rw [h_ptr4_val]
    omega
  unfold exec Miden.Core.Word.store_word_u32s_le execWithEnv
  simp only [List.foldlM]
  miden_swap
  rw [stepU32Split]
  miden_bind
  miden_movup
  rw [stepU32Split]
  miden_bind
  miden_dup
  rw [stepMemStorewLeLocal (ha_lt := h_ptr_lt) (ha_aligned := hout_ptr_aligned)]
  miden_bind
  rw [stepDropw]
  miden_bind
  miden_swap
  rw [stepU32Split]
  miden_bind
  miden_movup
  rw [stepU32Split]
  miden_bind
  miden_movup
  rw [stepAddImm]
  miden_bind
  rw [stepMemStorewLeLocal (a := out_ptr + 4) (ha_lt := h_ptr4_lt) (ha_aligned := h_ptr4_aligned)]
  miden_bind
  rw [h_ptr4_val]
  rw [stepDropw]
  simp only [pure, Pure.pure]
  ext a
  simp [MidenState.writeMemory, MidenState.withStack]

end MidenLean.Proofs
