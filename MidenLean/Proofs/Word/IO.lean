import MidenLean.Proofs.Helpers
import MidenLean.Proofs.StepLemmas
import MidenLean.Spec.WordOrder

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas

private theorem writeWordLe_eq_reordered
    (src : Nat → Felt) (base : Nat) (e0 e1 e2 e3 : Felt) :
    (fun addr =>
      if addr = base + 3 then e3
      else if addr = base + 2 then e2
      else if addr = base + 1 then e1
      else if addr = base then e0
      else src addr) = writeWordLe src base e0 e1 e2 e3 := by
  calc
    (fun addr =>
      if addr = base + 3 then e3
      else if addr = base + 2 then e2
      else if addr = base + 1 then e1
      else if addr = base then e0
      else src addr) = writeWordBe src base e3 e2 e1 e0 := by
        simpa using writeWordBe_eq_reordered src base e3 e2 e1 e0
    _ = writeWordLe src base e0 e1 e2 e3 := by
      symm
      exact writeWordLe_eq_writeWordBe_reversed src base e0 e1 e2 e3

/-- `memLoadwBe` overwrites the top word with the big-endian stack view of memory. -/
theorem memLoadwBe_exact
    (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a x0 x1 x2 x3 : Felt) (tail : List Felt)
    (ha_lt : a.val < 2 ^ 32) (ha_aligned : a.val % 4 = 0) :
    execInstruction ⟨a :: x0 :: x1 :: x2 :: x3 :: tail, mem, frames, adv⟩ .memLoadwBe =
      some ⟨sourceWordBe mem a.val ++ tail, mem, frames, adv⟩ := by
  unfold execInstruction execMemLoadwBe
  have hlt : ¬a.val >= u32Max := by
    unfold u32Max
    omega
  simp [hlt, ha_aligned, sourceWordBe, stackWord, MidenState.withStack]

/-- `memLoadwLe` overwrites the top word with the little-endian stack view of memory. -/
theorem memLoadwLe_exact
    (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a x0 x1 x2 x3 : Felt) (tail : List Felt)
    (ha_lt : a.val < 2 ^ 32) (ha_aligned : a.val % 4 = 0) :
    execInstruction ⟨a :: x0 :: x1 :: x2 :: x3 :: tail, mem, frames, adv⟩ .memLoadwLe =
      some ⟨sourceWordLe mem a.val ++ tail, mem, frames, adv⟩ := by
  unfold execInstruction execMemLoadwLe
  have hlt : ¬a.val >= u32Max := by
    unfold u32Max
    omega
  simp [hlt, ha_aligned, sourceWordLe, stackWord, MidenState.withStack]

/-- `memLoadwBe.<addr>` overwrites the top word with the big-endian stack view of memory. -/
theorem memLoadwBeImm_exact
    (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (addr : Nat) (x0 x1 x2 x3 : Felt) (tail : List Felt)
    (haddr_lt : addr < 2 ^ 32) (haddr_aligned : addr % 4 = 0) :
    execInstruction ⟨x0 :: x1 :: x2 :: x3 :: tail, mem, frames, adv⟩ (.memLoadwBeImm addr) =
      some ⟨sourceWordBe mem addr ++ tail, mem, frames, adv⟩ := by
  unfold execInstruction execMemLoadwBeImm
  have hlt : ¬addr >= u32Max := by
    unfold u32Max
    omega
  simp [hlt, haddr_aligned, sourceWordBe, stackWord, MidenState.withStack]

/-- `memLoadwLe.<addr>` overwrites the top word with the little-endian stack view of memory. -/
theorem memLoadwLeImm_exact
    (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (addr : Nat) (x0 x1 x2 x3 : Felt) (tail : List Felt)
    (haddr_lt : addr < 2 ^ 32) (haddr_aligned : addr % 4 = 0) :
    execInstruction ⟨x0 :: x1 :: x2 :: x3 :: tail, mem, frames, adv⟩ (.memLoadwLeImm addr) =
      some ⟨sourceWordLe mem addr ++ tail, mem, frames, adv⟩ := by
  unfold execInstruction execMemLoadwLeImm
  have hlt : ¬addr >= u32Max := by
    unfold u32Max
    omega
  simp [hlt, haddr_aligned, sourceWordLe, stackWord, MidenState.withStack]

/-- `memStorewBe` preserves the stack word and writes it to memory in big-endian order. -/
theorem memStorewBe_exact
    (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a e0 e1 e2 e3 : Felt) (tail : List Felt)
    (ha_lt : a.val < 2 ^ 32) (ha_aligned : a.val % 4 = 0) :
    execInstruction ⟨a :: e0 :: e1 :: e2 :: e3 :: tail, mem, frames, adv⟩ .memStorewBe =
      some ⟨stackWord e0 e1 e2 e3 ++ tail, writeWordBe mem a.val e0 e1 e2 e3, frames, adv⟩ := by
  unfold execInstruction execMemStorewBe
  have hlt : ¬a.val >= u32Max := by
    unfold u32Max
    omega
  simp [hlt, ha_aligned, MidenState.writeMemory, MidenState.withStack, stackWord]
  exact writeWordBe_eq_reordered mem a.val e0 e1 e2 e3

/-- `memStorewLe` preserves the stack word and writes it to memory in little-endian order. -/
theorem memStorewLe_exact
    (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a e0 e1 e2 e3 : Felt) (tail : List Felt)
    (ha_lt : a.val < 2 ^ 32) (ha_aligned : a.val % 4 = 0) :
    execInstruction ⟨a :: e0 :: e1 :: e2 :: e3 :: tail, mem, frames, adv⟩ .memStorewLe =
      some ⟨stackWord e0 e1 e2 e3 ++ tail, writeWordLe mem a.val e0 e1 e2 e3, frames, adv⟩ := by
  unfold execInstruction execMemStorewLe
  have hlt : ¬a.val >= u32Max := by
    unfold u32Max
    omega
  simp [hlt, ha_aligned, MidenState.writeMemory, MidenState.withStack, stackWord]
  exact writeWordLe_eq_reordered mem a.val e0 e1 e2 e3

/-- `memStorewBe.<addr>` preserves the stack word and writes it to memory in big-endian order. -/
theorem memStorewBeImm_exact
    (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (addr : Nat) (e0 e1 e2 e3 : Felt) (tail : List Felt)
    (haddr_lt : addr < 2 ^ 32) (haddr_aligned : addr % 4 = 0) :
    execInstruction ⟨e0 :: e1 :: e2 :: e3 :: tail, mem, frames, adv⟩ (.memStorewBeImm addr) =
      some ⟨stackWord e0 e1 e2 e3 ++ tail, writeWordBe mem addr e0 e1 e2 e3, frames, adv⟩ := by
  unfold execInstruction execMemStorewBeImm
  have hlt : ¬addr >= u32Max := by
    unfold u32Max
    omega
  simp [hlt, haddr_aligned, MidenState.writeMemory, MidenState.withStack, stackWord]
  exact writeWordBe_eq_reordered mem addr e0 e1 e2 e3

/-- `memStorewLe.<addr>` preserves the stack word and writes it to memory in little-endian order. -/
theorem memStorewLeImm_exact
    (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (addr : Nat) (e0 e1 e2 e3 : Felt) (tail : List Felt)
    (haddr_lt : addr < 2 ^ 32) (haddr_aligned : addr % 4 = 0) :
    execInstruction ⟨e0 :: e1 :: e2 :: e3 :: tail, mem, frames, adv⟩ (.memStorewLeImm addr) =
      some ⟨stackWord e0 e1 e2 e3 ++ tail, writeWordLe mem addr e0 e1 e2 e3, frames, adv⟩ := by
  unfold execInstruction execMemStorewLeImm
  have hlt : ¬addr >= u32Max := by
    unfold u32Max
    omega
  simp [hlt, haddr_aligned, MidenState.writeMemory, MidenState.withStack, stackWord]
  exact writeWordLe_eq_reordered mem addr e0 e1 e2 e3

/-- `locLoadwBe` overwrites the top word with the big-endian local-memory view. -/
theorem locLoadwBe_exact
    (idx : Nat) (frame : LocalFrame) (frames_rest : List LocalFrame)
    (mem : Nat → Felt) (adv : List Felt)
    (x0 x1 x2 x3 : Felt) (tail : List Felt)
    (halign : idx % 4 = 0) (hbound : idx + 4 ≤ frame.numLocals) :
    execInstruction ⟨x0 :: x1 :: x2 :: x3 :: tail, mem, frame :: frames_rest, adv⟩ (.locLoadwBe idx) =
      some ⟨sourceWordBe mem (frame.localAddr idx) ++ tail, mem, frame :: frames_rest, adv⟩ := by
  simpa [sourceWordBe, stackWord] using
    stepLocLoadwBe idx frame frames_rest mem adv x0 x1 x2 x3 tail halign hbound

/-- `locLoadwLe` overwrites the top word with the little-endian local-memory view. -/
theorem locLoadwLe_exact
    (idx : Nat) (frame : LocalFrame) (frames_rest : List LocalFrame)
    (mem : Nat → Felt) (adv : List Felt)
    (x0 x1 x2 x3 : Felt) (tail : List Felt)
    (halign : idx % 4 = 0) (hbound : idx + 4 ≤ frame.numLocals) :
    execInstruction ⟨x0 :: x1 :: x2 :: x3 :: tail, mem, frame :: frames_rest, adv⟩ (.locLoadwLe idx) =
      some ⟨sourceWordLe mem (frame.localAddr idx) ++ tail, mem, frame :: frames_rest, adv⟩ := by
  simpa [sourceWordLe, stackWord] using
    stepLocLoadwLe idx frame frames_rest mem adv x0 x1 x2 x3 tail halign hbound

/-- `locStorewBe` preserves the stack word and writes it to locals in big-endian order. -/
theorem locStorewBe_exact
    (idx : Nat) (frame : LocalFrame) (frames_rest : List LocalFrame)
    (mem : Nat → Felt) (adv : List Felt)
    (e0 e1 e2 e3 : Felt) (tail : List Felt)
    (halign : idx % 4 = 0) (hbound : idx + 4 ≤ frame.numLocals) :
    execInstruction ⟨e0 :: e1 :: e2 :: e3 :: tail, mem, frame :: frames_rest, adv⟩ (.locStorewBe idx) =
      some ⟨stackWord e0 e1 e2 e3 ++ tail,
        writeWordBe mem (frame.localAddr idx) e0 e1 e2 e3,
        frame :: frames_rest, adv⟩ := by
  unfold execInstruction execLocStorewBe currentFrame
  simp [halign, Nat.not_lt_of_le hbound, MidenState.writeMemory, MidenState.withStack, stackWord]
  exact writeWordBe_eq_reordered mem (frame.localAddr idx) e0 e1 e2 e3

/-- `locStorewLe` preserves the stack word and writes it to locals in little-endian order. -/
theorem locStorewLe_exact
    (idx : Nat) (frame : LocalFrame) (frames_rest : List LocalFrame)
    (mem : Nat → Felt) (adv : List Felt)
    (e0 e1 e2 e3 : Felt) (tail : List Felt)
    (halign : idx % 4 = 0) (hbound : idx + 4 ≤ frame.numLocals) :
    execInstruction ⟨e0 :: e1 :: e2 :: e3 :: tail, mem, frame :: frames_rest, adv⟩ (.locStorewLe idx) =
      some ⟨stackWord e0 e1 e2 e3 ++ tail,
        writeWordLe mem (frame.localAddr idx) e0 e1 e2 e3,
        frame :: frames_rest, adv⟩ := by
  unfold execInstruction execLocStorewLe currentFrame
  simp [halign, Nat.not_lt_of_le hbound, MidenState.writeMemory, MidenState.withStack, stackWord]
  exact writeWordLe_eq_reordered mem (frame.localAddr idx) e0 e1 e2 e3

/-- `memLoadwLe` is exactly `memLoadwBe` followed by `reversew`. -/
theorem memLoadwLe_via_memLoadwBe_reversew
    (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a x0 x1 x2 x3 : Felt) (tail : List Felt)
    (ha_lt : a.val < 2 ^ 32) (ha_aligned : a.val % 4 = 0) :
    exec 2 ⟨a :: x0 :: x1 :: x2 :: x3 :: tail, mem, frames, adv⟩
        [Op.inst .memLoadwBe, Op.inst .reversew] =
      execInstruction ⟨a :: x0 :: x1 :: x2 :: x3 :: tail, mem, frames, adv⟩ .memLoadwLe := by
  unfold exec execWithEnv
  simp only [List.foldlM]
  rw [memLoadwBe_exact mem frames adv a x0 x1 x2 x3 tail ha_lt ha_aligned]
  rw [memLoadwLe_exact mem frames adv a x0 x1 x2 x3 tail ha_lt ha_aligned]
  simpa [sourceWordBe, sourceWordLe, stackWord] using
    (stepReversew mem frames adv (mem (a.val + 3)) (mem (a.val + 2)) (mem (a.val + 1)) (mem a.val) tail)

/-- `memLoadwLe.<addr>` is exactly `memLoadwBe.<addr>` followed by `reversew`. -/
theorem memLoadwLeImm_via_memLoadwBeImm_reversew
    (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (addr : Nat) (x0 x1 x2 x3 : Felt) (tail : List Felt)
    (haddr_lt : addr < 2 ^ 32) (haddr_aligned : addr % 4 = 0) :
    exec 2 ⟨x0 :: x1 :: x2 :: x3 :: tail, mem, frames, adv⟩
        [Op.inst (.memLoadwBeImm addr), Op.inst .reversew] =
      execInstruction ⟨x0 :: x1 :: x2 :: x3 :: tail, mem, frames, adv⟩ (.memLoadwLeImm addr) := by
  unfold exec execWithEnv
  simp only [List.foldlM]
  rw [memLoadwBeImm_exact mem frames adv addr x0 x1 x2 x3 tail haddr_lt haddr_aligned]
  rw [memLoadwLeImm_exact mem frames adv addr x0 x1 x2 x3 tail haddr_lt haddr_aligned]
  simpa [sourceWordBe, sourceWordLe, stackWord] using
    (stepReversew mem frames adv (mem (addr + 3)) (mem (addr + 2)) (mem (addr + 1)) (mem addr) tail)

/-- For the immediate-address form, `memStorewLe.<addr>` is exactly
    `reversew; memStorewBe.<addr>; reversew`. -/
theorem memStorewLeImm_via_reversew_memStorewBeImm_reversew
    (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (addr : Nat) (e0 e1 e2 e3 : Felt) (tail : List Felt)
    (haddr_lt : addr < 2 ^ 32) (haddr_aligned : addr % 4 = 0) :
    exec 3 ⟨e0 :: e1 :: e2 :: e3 :: tail, mem, frames, adv⟩
        [Op.inst .reversew, Op.inst (.memStorewBeImm addr), Op.inst .reversew] =
      execInstruction ⟨e0 :: e1 :: e2 :: e3 :: tail, mem, frames, adv⟩ (.memStorewLeImm addr) := by
  unfold exec execWithEnv
  simp only [List.foldlM]
  rw [stepReversew mem frames adv e0 e1 e2 e3 tail]
  simp only [bind, Bind.bind, Option.bind, pure, Pure.pure]
  rw [memStorewBeImm_exact mem frames adv addr e3 e2 e1 e0 tail haddr_lt haddr_aligned]
  rw [memStorewLeImm_exact mem frames adv addr e0 e1 e2 e3 tail haddr_lt haddr_aligned]
  change execInstruction
      { stack := [e3, e2, e1, e0] ++ tail, memory := writeWordBe mem addr e3 e2 e1 e0, frames := frames,
        advice := adv }
      Instruction.reversew =
    some
      { stack := stackWord e0 e1 e2 e3 ++ tail, memory := writeWordLe mem addr e0 e1 e2 e3, frames := frames,
        advice := adv }
  simpa [stackWord, writeWordLe_eq_writeWordBe_reversed] using
    (stepReversew (writeWordBe mem addr e3 e2 e1 e0) frames adv e3 e2 e1 e0 tail)

/-- `locLoadwLe` is exactly `locLoadwBe` followed by `reversew`. -/
theorem locLoadwLe_via_locLoadwBe_reversew
    (idx : Nat) (frame : LocalFrame) (frames_rest : List LocalFrame)
    (mem : Nat → Felt) (adv : List Felt)
    (x0 x1 x2 x3 : Felt) (tail : List Felt)
    (halign : idx % 4 = 0) (hbound : idx + 4 ≤ frame.numLocals) :
    exec 2 ⟨x0 :: x1 :: x2 :: x3 :: tail, mem, frame :: frames_rest, adv⟩
        [Op.inst (.locLoadwBe idx), Op.inst .reversew] =
      execInstruction ⟨x0 :: x1 :: x2 :: x3 :: tail, mem, frame :: frames_rest, adv⟩ (.locLoadwLe idx) := by
  unfold exec execWithEnv
  simp only [List.foldlM]
  rw [locLoadwBe_exact idx frame frames_rest mem adv x0 x1 x2 x3 tail halign hbound]
  rw [locLoadwLe_exact idx frame frames_rest mem adv x0 x1 x2 x3 tail halign hbound]
  simpa [sourceWordBe, sourceWordLe, stackWord] using
    (stepReversew mem (frame :: frames_rest) adv
      (mem (frame.localAddr idx + 3))
      (mem (frame.localAddr idx + 2))
      (mem (frame.localAddr idx + 1))
      (mem (frame.localAddr idx))
      tail)

/-- `locStorewLe` is exactly `reversew; locStorewBe; reversew`. -/
theorem locStorewLe_via_reversew_locStorewBe_reversew
    (idx : Nat) (frame : LocalFrame) (frames_rest : List LocalFrame)
    (mem : Nat → Felt) (adv : List Felt)
    (e0 e1 e2 e3 : Felt) (tail : List Felt)
    (halign : idx % 4 = 0) (hbound : idx + 4 ≤ frame.numLocals) :
    exec 3 ⟨e0 :: e1 :: e2 :: e3 :: tail, mem, frame :: frames_rest, adv⟩
        [Op.inst .reversew, Op.inst (.locStorewBe idx), Op.inst .reversew] =
      execInstruction ⟨e0 :: e1 :: e2 :: e3 :: tail, mem, frame :: frames_rest, adv⟩ (.locStorewLe idx) := by
  unfold exec execWithEnv
  simp only [List.foldlM]
  rw [stepReversew mem (frame :: frames_rest) adv e0 e1 e2 e3 tail]
  simp only [bind, Bind.bind, Option.bind, pure, Pure.pure]
  rw [locStorewBe_exact idx frame frames_rest mem adv e3 e2 e1 e0 tail halign hbound]
  rw [locStorewLe_exact idx frame frames_rest mem adv e0 e1 e2 e3 tail halign hbound]
  change execInstruction
      { stack := [e3, e2, e1, e0] ++ tail, memory := writeWordBe mem (frame.localAddr idx) e3 e2 e1 e0,
        frames := frame :: frames_rest, advice := adv }
      Instruction.reversew =
    some
      { stack := stackWord e0 e1 e2 e3 ++ tail,
        memory := writeWordLe mem (frame.localAddr idx) e0 e1 e2 e3,
        frames := frame :: frames_rest, advice := adv }
  simpa [stackWord, writeWordLe_eq_writeWordBe_reversed] using
    (stepReversew (writeWordBe mem (frame.localAddr idx) e3 e2 e1 e0) (frame :: frames_rest) adv e3 e2 e1 e0 tail)

end MidenLean.Proofs
