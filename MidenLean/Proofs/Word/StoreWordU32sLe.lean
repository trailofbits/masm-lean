import MidenLean.Proofs.Tactics
import MidenLean.Generated.Word

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

/-- word.store_word_u32s_le: splits 4 felts into 8 u32
    limbs via u32Split and stores them as two words in
    memory at addr and addr+4. -/
theorem word_store_word_u32s_le_correct
    (x0 x1 x2 x3 addr : Felt)
    (rest : List Felt)
    (mem locs : Nat → Word) (adv : List Felt)
    (evts : List Felt)
    (haddr_lt : addr.val + 4 < u32Max)
    (haddr_val : (addr + 4 : Felt).val = addr.val + 4)
    (hlen : rest.length + 30 ≤ MAX_STACK_DEPTH) :
    exec 20
      ⟨x0 :: x1 :: x2 :: x3 :: addr :: rest,
       mem, locs, adv, evts⟩
      Miden.Core.Word.store_word_u32s_le =
    some ⟨rest,
      fun a =>
        if a = addr.val + 4 then
          (x2.lo32, x2.hi32, x3.lo32, x3.hi32)
        else if a = addr.val then
          (x0.lo32, x0.hi32, x1.lo32, x1.hi32)
        else mem a,
      locs, adv, evts⟩ := by
  unfold exec Miden.Core.Word.store_word_u32s_le
    execWithEnv
  simp only [List.foldlM]
  -- swap 1
  miden_swap
  -- u32Split
  rw [stepU32Split (hov := by simp [List.length_cons]; omega)]; miden_bind
  -- movup 2
  miden_movup
  -- u32Split
  rw [stepU32Split (hov := by simp [List.length_cons]; omega)]; miden_bind
  -- dup 6
  miden_dup
  -- memStorewLe (first store at addr)
  rw [stepMemStorewLe (ha_lt := by omega)]
  miden_bind
  -- dropw
  rw [stepDropw]; miden_bind
  -- swap 1
  miden_swap
  -- u32Split
  rw [stepU32Split (hov := by simp [List.length_cons]; omega)]; miden_bind
  -- movup 2
  miden_movup
  -- u32Split
  rw [stepU32Split (hov := by simp [List.length_cons]; omega)]; miden_bind
  -- movup 4
  miden_movup
  -- addImm 4
  rw [stepAddImm]; miden_bind
  -- memStorewLe (second store at addr+4)
  rw [stepMemStorewLe (ha_lt := by
    simp only [haddr_val]; omega)]
  miden_bind
  -- dropw
  rw [stepDropw]
  dsimp only [bind, Bind.bind, Option.bind, pure,
    Pure.pure]
  simp only [haddr_val]

end MidenLean.Proofs
