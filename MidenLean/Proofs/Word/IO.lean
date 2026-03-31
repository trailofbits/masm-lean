import MidenLean.Proofs.Helpers
import MidenLean.Proofs.StepLemmas
import MidenLean.Spec.WordOrder

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas

/-- `memLoadwBe` overwrites the top word with the big-endian stack view of memory. -/
theorem memLoadwBe_exact
    (mem locs : Nat → Felt) (adv : List Felt)
    (a x0 x1 x2 x3 : Felt) (tail : List Felt)
    (ha_lt : a.val < 2 ^ 32) (ha_aligned : a.val % 4 = 0) :
    execInstruction ⟨a :: x0 :: x1 :: x2 :: x3 :: tail, mem, locs, adv⟩ .memLoadwBe =
      some ⟨sourceWordBe mem a.val ++ tail, mem, locs, adv⟩ := by
  simpa [sourceWordBe, stackWord] using
    stepMemLoadwBe mem locs adv a x0 x1 x2 x3 tail ha_lt ha_aligned

/-- `memLoadwLe` overwrites the top word with the little-endian stack view of memory. -/
theorem memLoadwLe_exact
    (mem locs : Nat → Felt) (adv : List Felt)
    (a x0 x1 x2 x3 : Felt) (tail : List Felt)
    (ha_lt : a.val < 2 ^ 32) (ha_aligned : a.val % 4 = 0) :
    execInstruction ⟨a :: x0 :: x1 :: x2 :: x3 :: tail, mem, locs, adv⟩ .memLoadwLe =
      some ⟨sourceWordLe mem a.val ++ tail, mem, locs, adv⟩ := by
  simpa [sourceWordLe, stackWord] using
    stepMemLoadwLe mem locs adv a x0 x1 x2 x3 tail ha_lt ha_aligned

/-- `memLoadwBe.<addr>` overwrites the top word with the big-endian stack view of memory. -/
theorem memLoadwBeImm_exact
    (mem locs : Nat → Felt) (adv : List Felt)
    (addr : Nat) (x0 x1 x2 x3 : Felt) (tail : List Felt)
    (haddr_lt : addr < 2 ^ 32) (haddr_aligned : addr % 4 = 0) :
    execInstruction ⟨x0 :: x1 :: x2 :: x3 :: tail, mem, locs, adv⟩ (.memLoadwBeImm addr) =
      some ⟨sourceWordBe mem addr ++ tail, mem, locs, adv⟩ := by
  simpa [sourceWordBe, stackWord] using
    stepMemLoadwBeImm mem locs adv addr x0 x1 x2 x3 tail haddr_lt haddr_aligned

/-- `memLoadwLe.<addr>` overwrites the top word with the little-endian stack view of memory. -/
theorem memLoadwLeImm_exact
    (mem locs : Nat → Felt) (adv : List Felt)
    (addr : Nat) (x0 x1 x2 x3 : Felt) (tail : List Felt)
    (haddr_lt : addr < 2 ^ 32) (haddr_aligned : addr % 4 = 0) :
    execInstruction ⟨x0 :: x1 :: x2 :: x3 :: tail, mem, locs, adv⟩ (.memLoadwLeImm addr) =
      some ⟨sourceWordLe mem addr ++ tail, mem, locs, adv⟩ := by
  simpa [sourceWordLe, stackWord] using
    stepMemLoadwLeImm mem locs adv addr x0 x1 x2 x3 tail haddr_lt haddr_aligned

/-- `memStorewBe` preserves the stack word and writes it to memory in big-endian order. -/
theorem memStorewBe_exact
    (mem locs : Nat → Felt) (adv : List Felt)
    (a e0 e1 e2 e3 : Felt) (tail : List Felt)
    (ha_lt : a.val < 2 ^ 32) (ha_aligned : a.val % 4 = 0) :
    execInstruction ⟨a :: e0 :: e1 :: e2 :: e3 :: tail, mem, locs, adv⟩ .memStorewBe =
      some ⟨stackWord e0 e1 e2 e3 ++ tail, writeWordBe mem a.val e0 e1 e2 e3, locs, adv⟩ := by
  simpa [stackWord, writeWordBe] using
    stepMemStorewBe mem locs adv a e0 e1 e2 e3 tail ha_lt ha_aligned

/-- `memStorewLe` preserves the stack word and writes it to memory in little-endian order. -/
theorem memStorewLe_exact
    (mem locs : Nat → Felt) (adv : List Felt)
    (a e0 e1 e2 e3 : Felt) (tail : List Felt)
    (ha_lt : a.val < 2 ^ 32) (ha_aligned : a.val % 4 = 0) :
    execInstruction ⟨a :: e0 :: e1 :: e2 :: e3 :: tail, mem, locs, adv⟩ .memStorewLe =
      some ⟨stackWord e0 e1 e2 e3 ++ tail, writeWordLe mem a.val e0 e1 e2 e3, locs, adv⟩ := by
  simpa [stackWord, writeWordLe] using
    stepMemStorewLe mem locs adv a e0 e1 e2 e3 tail ha_lt ha_aligned

/-- `memStorewBe.<addr>` preserves the stack word and writes it to memory in big-endian order. -/
theorem memStorewBeImm_exact
    (mem locs : Nat → Felt) (adv : List Felt)
    (addr : Nat) (e0 e1 e2 e3 : Felt) (tail : List Felt)
    (haddr_lt : addr < 2 ^ 32) (haddr_aligned : addr % 4 = 0) :
    execInstruction ⟨e0 :: e1 :: e2 :: e3 :: tail, mem, locs, adv⟩ (.memStorewBeImm addr) =
      some ⟨stackWord e0 e1 e2 e3 ++ tail, writeWordBe mem addr e0 e1 e2 e3, locs, adv⟩ := by
  simpa [stackWord, writeWordBe] using
    stepMemStorewBeImm mem locs adv addr e0 e1 e2 e3 tail haddr_lt haddr_aligned

/-- `memStorewLe.<addr>` preserves the stack word and writes it to memory in little-endian order. -/
theorem memStorewLeImm_exact
    (mem locs : Nat → Felt) (adv : List Felt)
    (addr : Nat) (e0 e1 e2 e3 : Felt) (tail : List Felt)
    (haddr_lt : addr < 2 ^ 32) (haddr_aligned : addr % 4 = 0) :
    execInstruction ⟨e0 :: e1 :: e2 :: e3 :: tail, mem, locs, adv⟩ (.memStorewLeImm addr) =
      some ⟨stackWord e0 e1 e2 e3 ++ tail, writeWordLe mem addr e0 e1 e2 e3, locs, adv⟩ := by
  simpa [stackWord, writeWordLe] using
    stepMemStorewLeImm mem locs adv addr e0 e1 e2 e3 tail haddr_lt haddr_aligned

/-- `locLoadwBe` overwrites the top word with the big-endian local-memory view. -/
theorem locLoadwBe_exact
    (idx : Nat) (mem locs : Nat → Felt) (adv : List Felt)
    (x0 x1 x2 x3 : Felt) (tail : List Felt) :
    execInstruction ⟨x0 :: x1 :: x2 :: x3 :: tail, mem, locs, adv⟩ (.locLoadwBe idx) =
      some ⟨sourceWordBe locs idx ++ tail, mem, locs, adv⟩ := by
  simpa [sourceWordBe, stackWord] using
    stepLocLoadwBe idx mem locs adv x0 x1 x2 x3 tail

/-- `locLoadwLe` overwrites the top word with the little-endian local-memory view. -/
theorem locLoadwLe_exact
    (idx : Nat) (mem locs : Nat → Felt) (adv : List Felt)
    (x0 x1 x2 x3 : Felt) (tail : List Felt) :
    execInstruction ⟨x0 :: x1 :: x2 :: x3 :: tail, mem, locs, adv⟩ (.locLoadwLe idx) =
      some ⟨sourceWordLe locs idx ++ tail, mem, locs, adv⟩ := by
  simpa [sourceWordLe, stackWord] using
    stepLocLoadwLe idx mem locs adv x0 x1 x2 x3 tail

/-- `locStorewBe` preserves the stack word and writes it to locals in big-endian order. -/
theorem locStorewBe_exact
    (idx : Nat) (mem locs : Nat → Felt) (adv : List Felt)
    (e0 e1 e2 e3 : Felt) (tail : List Felt) :
    execInstruction ⟨e0 :: e1 :: e2 :: e3 :: tail, mem, locs, adv⟩ (.locStorewBe idx) =
      some ⟨stackWord e0 e1 e2 e3 ++ tail, mem, writeWordBe locs idx e0 e1 e2 e3, adv⟩ := by
  simpa [stackWord, writeWordBe] using
    stepLocStorewBe idx mem locs adv e0 e1 e2 e3 tail

/-- `locStorewLe` preserves the stack word and writes it to locals in little-endian order. -/
theorem locStorewLe_exact
    (idx : Nat) (mem locs : Nat → Felt) (adv : List Felt)
    (e0 e1 e2 e3 : Felt) (tail : List Felt) :
    execInstruction ⟨e0 :: e1 :: e2 :: e3 :: tail, mem, locs, adv⟩ (.locStorewLe idx) =
      some ⟨stackWord e0 e1 e2 e3 ++ tail, mem, writeWordLe locs idx e0 e1 e2 e3, adv⟩ := by
  simpa [stackWord, writeWordLe] using
    stepLocStorewLe idx mem locs adv e0 e1 e2 e3 tail

/-- `memLoadwLe` is exactly `memLoadwBe` followed by `reversew`. -/
theorem memLoadwLe_via_memLoadwBe_reversew
    (mem locs : Nat → Felt) (adv : List Felt)
    (a x0 x1 x2 x3 : Felt) (tail : List Felt)
    (ha_lt : a.val < 2 ^ 32) (ha_aligned : a.val % 4 = 0) :
    exec 2 ⟨a :: x0 :: x1 :: x2 :: x3 :: tail, mem, locs, adv⟩
        [Op.inst .memLoadwBe, Op.inst .reversew] =
      execInstruction ⟨a :: x0 :: x1 :: x2 :: x3 :: tail, mem, locs, adv⟩ .memLoadwLe := by
  unfold exec execWithEnv
  simp only [List.foldlM]
  rw [stepMemLoadwBe mem locs adv a x0 x1 x2 x3 tail ha_lt ha_aligned]
  simp [sourceWordBe, stackWord, stepReversew]
  rw [stepMemLoadwLe mem locs adv a x0 x1 x2 x3 tail ha_lt ha_aligned]
  rfl

/-- `memLoadwLe.<addr>` is exactly `memLoadwBe.<addr>` followed by `reversew`. -/
theorem memLoadwLeImm_via_memLoadwBeImm_reversew
    (mem locs : Nat → Felt) (adv : List Felt)
    (addr : Nat) (x0 x1 x2 x3 : Felt) (tail : List Felt)
    (haddr_lt : addr < 2 ^ 32) (haddr_aligned : addr % 4 = 0) :
    exec 2 ⟨x0 :: x1 :: x2 :: x3 :: tail, mem, locs, adv⟩
        [Op.inst (.memLoadwBeImm addr), Op.inst .reversew] =
      execInstruction ⟨x0 :: x1 :: x2 :: x3 :: tail, mem, locs, adv⟩ (.memLoadwLeImm addr) := by
  unfold exec execWithEnv
  simp only [List.foldlM]
  rw [stepMemLoadwBeImm mem locs adv addr x0 x1 x2 x3 tail haddr_lt haddr_aligned]
  simp [sourceWordBe, stackWord, stepReversew]
  rw [stepMemLoadwLeImm mem locs adv addr x0 x1 x2 x3 tail haddr_lt haddr_aligned]
  rfl

/-- For the immediate-address form, `memStorewLe.<addr>` is exactly
    `reversew; memStorewBe.<addr>; reversew`. This is the corrected doc claim:
    the plain three-instruction pattern does not hold for the stack-address form because
    the address occupies the top stack slot. -/
theorem memStorewLeImm_via_reversew_memStorewBeImm_reversew
    (mem locs : Nat → Felt) (adv : List Felt)
    (addr : Nat) (e0 e1 e2 e3 : Felt) (tail : List Felt)
    (haddr_lt : addr < 2 ^ 32) (haddr_aligned : addr % 4 = 0) :
    exec 3 ⟨e0 :: e1 :: e2 :: e3 :: tail, mem, locs, adv⟩
        [Op.inst .reversew, Op.inst (.memStorewBeImm addr), Op.inst .reversew] =
      execInstruction ⟨e0 :: e1 :: e2 :: e3 :: tail, mem, locs, adv⟩ (.memStorewLeImm addr) := by
  unfold exec execWithEnv
  simp only [List.foldlM]
  rw [stepReversew mem locs adv e0 e1 e2 e3 tail]
  simp only [bind, Bind.bind, Option.bind, pure, Pure.pure]
  rw [stepMemStorewBeImm mem locs adv addr e3 e2 e1 e0 tail haddr_lt haddr_aligned]
  simp [stepReversew, stackWord]
  rw [stepMemStorewLeImm mem locs adv addr e0 e1 e2 e3 tail haddr_lt haddr_aligned]
  simp [writeWordLe_eq_writeWordBe_reversed]

/-- `locLoadwLe` is exactly `locLoadwBe` followed by `reversew`. -/
theorem locLoadwLe_via_locLoadwBe_reversew
    (idx : Nat) (mem locs : Nat → Felt) (adv : List Felt)
    (x0 x1 x2 x3 : Felt) (tail : List Felt) :
    exec 2 ⟨x0 :: x1 :: x2 :: x3 :: tail, mem, locs, adv⟩
        [Op.inst (.locLoadwBe idx), Op.inst .reversew] =
      execInstruction ⟨x0 :: x1 :: x2 :: x3 :: tail, mem, locs, adv⟩ (.locLoadwLe idx) := by
  unfold exec execWithEnv
  simp only [List.foldlM]
  rw [stepLocLoadwBe idx mem locs adv x0 x1 x2 x3 tail]
  simp [sourceWordBe, stackWord, stepReversew]
  rw [stepLocLoadwLe idx mem locs adv x0 x1 x2 x3 tail]
  rfl

/-- `locStorewLe` is exactly `reversew; locStorewBe; reversew`. -/
theorem locStorewLe_via_reversew_locStorewBe_reversew
    (idx : Nat) (mem locs : Nat → Felt) (adv : List Felt)
    (e0 e1 e2 e3 : Felt) (tail : List Felt) :
    exec 3 ⟨e0 :: e1 :: e2 :: e3 :: tail, mem, locs, adv⟩
        [Op.inst .reversew, Op.inst (.locStorewBe idx), Op.inst .reversew] =
      execInstruction ⟨e0 :: e1 :: e2 :: e3 :: tail, mem, locs, adv⟩ (.locStorewLe idx) := by
  unfold exec execWithEnv
  simp only [List.foldlM]
  rw [stepReversew mem locs adv e0 e1 e2 e3 tail]
  simp only [bind, Bind.bind, Option.bind, pure, Pure.pure]
  rw [stepLocStorewBe idx mem locs adv e3 e2 e1 e0 tail]
  simp [stepReversew, stackWord]
  rw [stepLocStorewLe idx mem locs adv e0 e1 e2 e3 tail]
  simp [writeWordLe_eq_writeWordBe_reversed]

end MidenLean.Proofs
