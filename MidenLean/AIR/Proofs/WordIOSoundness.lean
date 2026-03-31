import MidenLean.Spec.WordOrder

/-!
# AIR Word-I/O Soundness (Scoped)

This file proves the word-order-sensitive part of lowered load/store helpers under
an explicit boundary:

- We model exact visible-stack rewrites for `reversew`, `movdn.4`, and `movup.4`.
- We assume abstract single-step acceptance for the underlying core word-I/O primitives
  (`*LoadwLe*` / `*StorewLe*`) and use those assumptions as hypotheses.

So these theorems are local lowering soundness results. They do **not** claim full
memory-chiplet / whole-VM AIR soundness by themselves.
-/

namespace MidenLean.AIR.Proofs.WordIOSoundness

open MidenLean

/-- Minimal state slice used by this local word-I/O proof package. -/
structure IOState where
  stack : List Felt
  mem : Nat → Felt
  locs : Nat → Felt

/-- Local AIR slice for `reversew`: top word is reversed, memory/local views unchanged. -/
def airReversewFull (σ σ' : IOState) : Prop :=
  ∃ a b c d tail,
    σ.stack = a :: b :: c :: d :: tail ∧
    σ'.stack = d :: c :: b :: a :: tail ∧
    σ'.mem = σ.mem ∧
    σ'.locs = σ.locs

/-- Local AIR slice for `movdn.4`: top element moved to index 4. -/
def airMovdn4Full (σ σ' : IOState) : Prop :=
  ∃ a b c d e tail,
    σ.stack = a :: b :: c :: d :: e :: tail ∧
    σ'.stack = b :: c :: d :: e :: a :: tail ∧
    σ'.mem = σ.mem ∧
    σ'.locs = σ.locs

/-- Local AIR slice for `movup.4`: element at index 4 moved to top. -/
def airMovup4Full (σ σ' : IOState) : Prop :=
  ∃ a b c d e tail,
    σ.stack = a :: b :: c :: d :: e :: tail ∧
    σ'.stack = e :: a :: b :: c :: d :: tail ∧
    σ'.mem = σ.mem ∧
    σ'.locs = σ.locs

theorem airReversewFull_sound
    {a b c d : Felt} {tail : List Felt} {mem locs : Nat → Felt} {σ' : IOState}
    (h : airReversewFull { stack := a :: b :: c :: d :: tail, mem := mem, locs := locs } σ') :
    σ' = { stack := d :: c :: b :: a :: tail, mem := mem, locs := locs } := by
  rcases h with ⟨a', b', c', d', tail', hin, hout, hmem, hlocs⟩
  cases hin
  cases σ' with
  | mk st mem' locs' =>
    simp at hmem hlocs
    subst hmem hlocs
    simp at hout
    subst hout
    rfl

theorem airMovdn4Full_sound
    {a b c d e : Felt} {tail : List Felt} {mem locs : Nat → Felt} {σ' : IOState}
    (h : airMovdn4Full { stack := a :: b :: c :: d :: e :: tail, mem := mem, locs := locs } σ') :
    σ' = { stack := b :: c :: d :: e :: a :: tail, mem := mem, locs := locs } := by
  rcases h with ⟨a', b', c', d', e', tail', hin, hout, hmem, hlocs⟩
  cases hin
  cases σ' with
  | mk st mem' locs' =>
    simp at hmem hlocs
    subst hmem hlocs
    simp at hout
    subst hout
    rfl

theorem airMovup4Full_sound
    {a b c d e : Felt} {tail : List Felt} {mem locs : Nat → Felt} {σ' : IOState}
    (h : airMovup4Full { stack := a :: b :: c :: d :: e :: tail, mem := mem, locs := locs } σ') :
    σ' = { stack := e :: a :: b :: c :: d :: tail, mem := mem, locs := locs } := by
  rcases h with ⟨a', b', c', d', e', tail', hin, hout, hmem, hlocs⟩
  cases hin
  cases σ' with
  | mk st mem' locs' =>
    simp at hmem hlocs
    subst hmem hlocs
    simp at hout
    subst hout
    rfl

/-- Lowered acceptance model for `memLoadwBe`:
core `memLoadwLe` followed by `reversew`. -/
def memLoadwBeAccepts
    (coreMemLoadwLeAccepts : IOState → IOState → Prop)
    (σ σ' : IOState) : Prop :=
  ∃ σ1, coreMemLoadwLeAccepts σ σ1 ∧ airReversewFull σ1 σ'

/-- Lowered acceptance model for `memLoadwBe.<addr>`:
core `memLoadwLe.<addr>` followed by `reversew`. -/
def memLoadwBeImmAccepts
    (coreMemLoadwLeImmAccepts : Nat → IOState → IOState → Prop)
    (addr : Nat) (σ σ' : IOState) : Prop :=
  ∃ σ1, coreMemLoadwLeImmAccepts addr σ σ1 ∧ airReversewFull σ1 σ'

/-- Lowered acceptance model for `memStorewBe`:
`movdn.4; reversew; movup.4; core memStorewLe; reversew`. -/
def memStorewBeAccepts
    (coreMemStorewLeAccepts : IOState → IOState → Prop)
    (σ σ' : IOState) : Prop :=
  ∃ σ1 σ2 σ3 σ4,
    airMovdn4Full σ σ1 ∧
    airReversewFull σ1 σ2 ∧
    airMovup4Full σ2 σ3 ∧
    coreMemStorewLeAccepts σ3 σ4 ∧
    airReversewFull σ4 σ'

/-- Lowered acceptance model for `memStorewBe.<addr>`:
`reversew; core memStorewLe.<addr>; reversew`. -/
def memStorewBeImmAccepts
    (coreMemStorewLeImmAccepts : Nat → IOState → IOState → Prop)
    (addr : Nat) (σ σ' : IOState) : Prop :=
  ∃ σ1 σ2,
    airReversewFull σ σ1 ∧
    coreMemStorewLeImmAccepts addr σ1 σ2 ∧
    airReversewFull σ2 σ'

/-- Lowered acceptance model for `locLoadwBe`:
core `locLoadwLe` followed by `reversew`. -/
def locLoadwBeAccepts
    (coreLocLoadwLeAccepts : Nat → IOState → IOState → Prop)
    (idx : Nat) (σ σ' : IOState) : Prop :=
  ∃ σ1, coreLocLoadwLeAccepts idx σ σ1 ∧ airReversewFull σ1 σ'

/-- Lowered acceptance model for `locStorewBe`:
`reversew; core locStorewLe; reversew`. -/
def locStorewBeAccepts
    (coreLocStorewLeAccepts : Nat → IOState → IOState → Prop)
    (idx : Nat) (σ σ' : IOState) : Prop :=
  ∃ σ1 σ2,
    airReversewFull σ σ1 ∧
    coreLocStorewLeAccepts idx σ1 σ2 ∧
    airReversewFull σ2 σ'

-- Residual assumption shapes for core primitives.
def CoreMemLoadwLeSound (coreMemLoadwLeAccepts : IOState → IOState → Prop) : Prop :=
  ∀ {a x0 x1 x2 x3 : Felt} {tail : List Felt} {mem locs : Nat → Felt} {σ' : IOState},
    (ha_lt : a.val < 2 ^ 32) → (ha_aligned : a.val % 4 = 0) →
    coreMemLoadwLeAccepts
      { stack := a :: x0 :: x1 :: x2 :: x3 :: tail, mem := mem, locs := locs } σ' →
    σ' = { stack := sourceWordLe mem a.val ++ tail, mem := mem, locs := locs }

def CoreMemLoadwLeImmSound (coreMemLoadwLeImmAccepts : Nat → IOState → IOState → Prop) : Prop :=
  ∀ {addr : Nat} {x0 x1 x2 x3 : Felt} {tail : List Felt} {mem locs : Nat → Felt} {σ' : IOState},
    (haddr_lt : addr < 2 ^ 32) → (haddr_aligned : addr % 4 = 0) →
    coreMemLoadwLeImmAccepts addr
      { stack := x0 :: x1 :: x2 :: x3 :: tail, mem := mem, locs := locs } σ' →
    σ' = { stack := sourceWordLe mem addr ++ tail, mem := mem, locs := locs }

def CoreMemStorewLeSound (coreMemStorewLeAccepts : IOState → IOState → Prop) : Prop :=
  ∀ {a e0 e1 e2 e3 : Felt} {tail : List Felt} {mem locs : Nat → Felt} {σ' : IOState},
    (ha_lt : a.val < 2 ^ 32) → (ha_aligned : a.val % 4 = 0) →
    coreMemStorewLeAccepts
      { stack := a :: e0 :: e1 :: e2 :: e3 :: tail, mem := mem, locs := locs } σ' →
    σ' = { stack := stackWord e0 e1 e2 e3 ++ tail,
           mem := writeWordLe mem a.val e0 e1 e2 e3,
           locs := locs }

def CoreMemStorewLeImmSound (coreMemStorewLeImmAccepts : Nat → IOState → IOState → Prop) : Prop :=
  ∀ {addr : Nat} {e0 e1 e2 e3 : Felt} {tail : List Felt} {mem locs : Nat → Felt} {σ' : IOState},
    (haddr_lt : addr < 2 ^ 32) → (haddr_aligned : addr % 4 = 0) →
    coreMemStorewLeImmAccepts addr
      { stack := e0 :: e1 :: e2 :: e3 :: tail, mem := mem, locs := locs } σ' →
    σ' = { stack := stackWord e0 e1 e2 e3 ++ tail,
           mem := writeWordLe mem addr e0 e1 e2 e3,
           locs := locs }

def CoreLocLoadwLeSound (coreLocLoadwLeAccepts : Nat → IOState → IOState → Prop) : Prop :=
  ∀ {idx : Nat} {x0 x1 x2 x3 : Felt} {tail : List Felt} {mem locs : Nat → Felt} {σ' : IOState},
    coreLocLoadwLeAccepts idx
      { stack := x0 :: x1 :: x2 :: x3 :: tail, mem := mem, locs := locs } σ' →
    σ' = { stack := sourceWordLe locs idx ++ tail, mem := mem, locs := locs }

def CoreLocStorewLeSound (coreLocStorewLeAccepts : Nat → IOState → IOState → Prop) : Prop :=
  ∀ {idx : Nat} {e0 e1 e2 e3 : Felt} {tail : List Felt} {mem locs : Nat → Felt} {σ' : IOState},
    coreLocStorewLeAccepts idx
      { stack := e0 :: e1 :: e2 :: e3 :: tail, mem := mem, locs := locs } σ' →
    σ' = { stack := stackWord e0 e1 e2 e3 ++ tail,
           mem := mem,
           locs := writeWordLe locs idx e0 e1 e2 e3 }

section

variable (coreMemLoadwLeAccepts : IOState → IOState → Prop)
variable (coreMemLoadwLeImmAccepts : Nat → IOState → IOState → Prop)
variable (coreMemStorewLeAccepts : IOState → IOState → Prop)
variable (coreMemStorewLeImmAccepts : Nat → IOState → IOState → Prop)
variable (coreLocLoadwLeAccepts : Nat → IOState → IOState → Prop)
variable (coreLocStorewLeAccepts : Nat → IOState → IOState → Prop)

theorem memLoadwLe_core_sound
    (hCoreMemLoadwLe : CoreMemLoadwLeSound coreMemLoadwLeAccepts)
    {a x0 x1 x2 x3 : Felt} {tail : List Felt} {mem locs : Nat → Felt} {σ' : IOState}
    (ha_lt : a.val < 2 ^ 32) (ha_aligned : a.val % 4 = 0)
    (hacc : coreMemLoadwLeAccepts
      { stack := a :: x0 :: x1 :: x2 :: x3 :: tail, mem := mem, locs := locs } σ') :
    σ' = { stack := sourceWordLe mem a.val ++ tail, mem := mem, locs := locs } :=
  hCoreMemLoadwLe ha_lt ha_aligned hacc

theorem memLoadwLeImm_core_sound
    (hCoreMemLoadwLeImm : CoreMemLoadwLeImmSound coreMemLoadwLeImmAccepts)
    {addr : Nat} {x0 x1 x2 x3 : Felt} {tail : List Felt} {mem locs : Nat → Felt} {σ' : IOState}
    (haddr_lt : addr < 2 ^ 32) (haddr_aligned : addr % 4 = 0)
    (hacc : coreMemLoadwLeImmAccepts addr
      { stack := x0 :: x1 :: x2 :: x3 :: tail, mem := mem, locs := locs } σ') :
    σ' = { stack := sourceWordLe mem addr ++ tail, mem := mem, locs := locs } :=
  hCoreMemLoadwLeImm haddr_lt haddr_aligned hacc

theorem memStorewLe_core_sound
    (hCoreMemStorewLe : CoreMemStorewLeSound coreMemStorewLeAccepts)
    {a e0 e1 e2 e3 : Felt} {tail : List Felt} {mem locs : Nat → Felt} {σ' : IOState}
    (ha_lt : a.val < 2 ^ 32) (ha_aligned : a.val % 4 = 0)
    (hacc : coreMemStorewLeAccepts
      { stack := a :: e0 :: e1 :: e2 :: e3 :: tail, mem := mem, locs := locs } σ') :
    σ' = { stack := stackWord e0 e1 e2 e3 ++ tail,
           mem := writeWordLe mem a.val e0 e1 e2 e3,
           locs := locs } :=
  hCoreMemStorewLe ha_lt ha_aligned hacc

theorem memStorewLeImm_core_sound
    (hCoreMemStorewLeImm : CoreMemStorewLeImmSound coreMemStorewLeImmAccepts)
    {addr : Nat} {e0 e1 e2 e3 : Felt} {tail : List Felt} {mem locs : Nat → Felt} {σ' : IOState}
    (haddr_lt : addr < 2 ^ 32) (haddr_aligned : addr % 4 = 0)
    (hacc : coreMemStorewLeImmAccepts addr
      { stack := e0 :: e1 :: e2 :: e3 :: tail, mem := mem, locs := locs } σ') :
    σ' = { stack := stackWord e0 e1 e2 e3 ++ tail,
           mem := writeWordLe mem addr e0 e1 e2 e3,
           locs := locs } :=
  hCoreMemStorewLeImm haddr_lt haddr_aligned hacc

theorem locLoadwLe_core_sound
    (hCoreLocLoadwLe : CoreLocLoadwLeSound coreLocLoadwLeAccepts)
    {idx : Nat} {x0 x1 x2 x3 : Felt} {tail : List Felt} {mem locs : Nat → Felt} {σ' : IOState}
    (hacc : coreLocLoadwLeAccepts idx
      { stack := x0 :: x1 :: x2 :: x3 :: tail, mem := mem, locs := locs } σ') :
    σ' = { stack := sourceWordLe locs idx ++ tail, mem := mem, locs := locs } :=
  hCoreLocLoadwLe hacc

theorem locStorewLe_core_sound
    (hCoreLocStorewLe : CoreLocStorewLeSound coreLocStorewLeAccepts)
    {idx : Nat} {e0 e1 e2 e3 : Felt} {tail : List Felt} {mem locs : Nat → Felt} {σ' : IOState}
    (hacc : coreLocStorewLeAccepts idx
      { stack := e0 :: e1 :: e2 :: e3 :: tail, mem := mem, locs := locs } σ') :
    σ' = { stack := stackWord e0 e1 e2 e3 ++ tail,
           mem := mem,
           locs := writeWordLe locs idx e0 e1 e2 e3 } :=
  hCoreLocStorewLe hacc

theorem memLoadwBe_lowered_sound
    (hCoreMemLoadwLe : CoreMemLoadwLeSound coreMemLoadwLeAccepts)
    {a x0 x1 x2 x3 : Felt} {tail : List Felt} {mem locs : Nat → Felt} {σ' : IOState}
    (ha_lt : a.val < 2 ^ 32) (ha_aligned : a.val % 4 = 0)
    (hacc : memLoadwBeAccepts coreMemLoadwLeAccepts
      { stack := a :: x0 :: x1 :: x2 :: x3 :: tail, mem := mem, locs := locs } σ') :
    σ' = { stack := sourceWordBe mem a.val ++ tail, mem := mem, locs := locs } := by
  rcases hacc with ⟨σ1, hcore, hrev⟩
  have hσ1 : σ1 =
      { stack := sourceWordLe mem a.val ++ tail, mem := mem, locs := locs } :=
    hCoreMemLoadwLe ha_lt ha_aligned hcore
  have hrev' :
      airReversewFull
        { stack := sourceWordLe mem a.val ++ tail, mem := mem, locs := locs } σ' := by
    simpa [hσ1] using hrev
  have hrev'' :
      airReversewFull
        { stack := mem a.val :: mem (a.val + 1) :: mem (a.val + 2) :: mem (a.val + 3) :: tail,
          mem := mem, locs := locs } σ' := by
    simpa [sourceWordLe, stackWord] using hrev'
  have hfinal := airReversewFull_sound (a := mem a.val) (b := mem (a.val + 1))
    (c := mem (a.val + 2)) (d := mem (a.val + 3)) (tail := tail) (mem := mem) (locs := locs) hrev''
  simpa [sourceWordBe, stackWord] using hfinal

theorem memLoadwBeImm_lowered_sound
    (hCoreMemLoadwLeImm : CoreMemLoadwLeImmSound coreMemLoadwLeImmAccepts)
    {addr : Nat} {x0 x1 x2 x3 : Felt} {tail : List Felt} {mem locs : Nat → Felt} {σ' : IOState}
    (haddr_lt : addr < 2 ^ 32) (haddr_aligned : addr % 4 = 0)
    (hacc : memLoadwBeImmAccepts coreMemLoadwLeImmAccepts addr
      { stack := x0 :: x1 :: x2 :: x3 :: tail, mem := mem, locs := locs } σ') :
    σ' = { stack := sourceWordBe mem addr ++ tail, mem := mem, locs := locs } := by
  rcases hacc with ⟨σ1, hcore, hrev⟩
  have hσ1 : σ1 =
      { stack := sourceWordLe mem addr ++ tail, mem := mem, locs := locs } :=
    hCoreMemLoadwLeImm haddr_lt haddr_aligned hcore
  have hrev' :
      airReversewFull
        { stack := sourceWordLe mem addr ++ tail, mem := mem, locs := locs } σ' := by
    simpa [hσ1] using hrev
  have hrev'' :
      airReversewFull
        { stack := mem addr :: mem (addr + 1) :: mem (addr + 2) :: mem (addr + 3) :: tail,
          mem := mem, locs := locs } σ' := by
    simpa [sourceWordLe, stackWord] using hrev'
  have hfinal := airReversewFull_sound (a := mem addr) (b := mem (addr + 1))
    (c := mem (addr + 2)) (d := mem (addr + 3)) (tail := tail) (mem := mem) (locs := locs) hrev''
  simpa [sourceWordBe, stackWord] using hfinal

theorem locLoadwBe_lowered_sound
    (hCoreLocLoadwLe : CoreLocLoadwLeSound coreLocLoadwLeAccepts)
    {idx : Nat} {x0 x1 x2 x3 : Felt} {tail : List Felt} {mem locs : Nat → Felt} {σ' : IOState}
    (hacc : locLoadwBeAccepts coreLocLoadwLeAccepts idx
      { stack := x0 :: x1 :: x2 :: x3 :: tail, mem := mem, locs := locs } σ') :
    σ' = { stack := sourceWordBe locs idx ++ tail, mem := mem, locs := locs } := by
  rcases hacc with ⟨σ1, hcore, hrev⟩
  have hσ1 : σ1 = { stack := sourceWordLe locs idx ++ tail, mem := mem, locs := locs } :=
    hCoreLocLoadwLe hcore
  have hrev' :
      airReversewFull
        { stack := sourceWordLe locs idx ++ tail, mem := mem, locs := locs } σ' := by
    simpa [hσ1] using hrev
  have hrev'' :
      airReversewFull
        { stack := locs idx :: locs (idx + 1) :: locs (idx + 2) :: locs (idx + 3) :: tail,
          mem := mem, locs := locs } σ' := by
    simpa [sourceWordLe, stackWord] using hrev'
  have hfinal := airReversewFull_sound (a := locs idx) (b := locs (idx + 1))
    (c := locs (idx + 2)) (d := locs (idx + 3)) (tail := tail) (mem := mem) (locs := locs) hrev''
  simpa [sourceWordBe, stackWord] using hfinal

theorem memStorewBeImm_lowered_sound
    (hCoreMemStorewLeImm : CoreMemStorewLeImmSound coreMemStorewLeImmAccepts)
    {addr : Nat} {e0 e1 e2 e3 : Felt} {tail : List Felt} {mem locs : Nat → Felt} {σ' : IOState}
    (haddr_lt : addr < 2 ^ 32) (haddr_aligned : addr % 4 = 0)
    (hacc : memStorewBeImmAccepts coreMemStorewLeImmAccepts addr
      { stack := e0 :: e1 :: e2 :: e3 :: tail, mem := mem, locs := locs } σ') :
    σ' = { stack := stackWord e0 e1 e2 e3 ++ tail,
           mem := writeWordBe mem addr e0 e1 e2 e3,
           locs := locs } := by
  rcases hacc with ⟨σ1, σ2, hrev1, hcore, hrev2⟩
  have hσ1 := airReversewFull_sound (a := e0) (b := e1) (c := e2) (d := e3)
    (tail := tail) (mem := mem) (locs := locs) hrev1
  have hcore' :
      coreMemStorewLeImmAccepts addr
        { stack := e3 :: e2 :: e1 :: e0 :: tail, mem := mem, locs := locs } σ2 := by
    simpa [hσ1, stackWord] using hcore
  have hσ2 :
      σ2 = { stack := stackWord e3 e2 e1 e0 ++ tail,
             mem := writeWordLe mem addr e3 e2 e1 e0,
             locs := locs } :=
    hCoreMemStorewLeImm haddr_lt haddr_aligned hcore'
  have hrev2' :
      airReversewFull
        { stack := stackWord e3 e2 e1 e0 ++ tail,
          mem := writeWordLe mem addr e3 e2 e1 e0,
          locs := locs } σ' := by
    simpa [hσ2] using hrev2
  have hfinal := airReversewFull_sound (a := e3) (b := e2) (c := e1) (d := e0)
    (tail := tail) (mem := writeWordLe mem addr e3 e2 e1 e0) (locs := locs) (by
      simpa [stackWord] using hrev2')
  simpa [stackWord, writeWordLe_eq_writeWordBe_reversed] using hfinal

theorem locStorewBe_lowered_sound
    (hCoreLocStorewLe : CoreLocStorewLeSound coreLocStorewLeAccepts)
    {idx : Nat} {e0 e1 e2 e3 : Felt} {tail : List Felt} {mem locs : Nat → Felt} {σ' : IOState}
    (hacc : locStorewBeAccepts coreLocStorewLeAccepts idx
      { stack := e0 :: e1 :: e2 :: e3 :: tail, mem := mem, locs := locs } σ') :
    σ' = { stack := stackWord e0 e1 e2 e3 ++ tail,
           mem := mem,
           locs := writeWordBe locs idx e0 e1 e2 e3 } := by
  rcases hacc with ⟨σ1, σ2, hrev1, hcore, hrev2⟩
  have hσ1 := airReversewFull_sound (a := e0) (b := e1) (c := e2) (d := e3)
    (tail := tail) (mem := mem) (locs := locs) hrev1
  have hcore' :
      coreLocStorewLeAccepts idx
        { stack := e3 :: e2 :: e1 :: e0 :: tail, mem := mem, locs := locs } σ2 := by
    simpa [hσ1, stackWord] using hcore
  have hσ2 :
      σ2 = { stack := stackWord e3 e2 e1 e0 ++ tail,
             mem := mem,
             locs := writeWordLe locs idx e3 e2 e1 e0 } :=
    hCoreLocStorewLe hcore'
  have hrev2' :
      airReversewFull
        { stack := stackWord e3 e2 e1 e0 ++ tail,
          mem := mem,
          locs := writeWordLe locs idx e3 e2 e1 e0 } σ' := by
    simpa [hσ2] using hrev2
  have hfinal := airReversewFull_sound (a := e3) (b := e2) (c := e1) (d := e0)
    (tail := tail) (mem := mem) (locs := writeWordLe locs idx e3 e2 e1 e0) (by
      simpa [stackWord] using hrev2')
  simpa [stackWord, writeWordLe_eq_writeWordBe_reversed] using hfinal

theorem memStorewBe_lowered_sound
    (hCoreMemStorewLe : CoreMemStorewLeSound coreMemStorewLeAccepts)
    {a e0 e1 e2 e3 : Felt} {tail : List Felt} {mem locs : Nat → Felt} {σ' : IOState}
    (ha_lt : a.val < 2 ^ 32) (ha_aligned : a.val % 4 = 0)
    (hacc : memStorewBeAccepts coreMemStorewLeAccepts
      { stack := a :: e0 :: e1 :: e2 :: e3 :: tail, mem := mem, locs := locs } σ') :
    σ' = { stack := stackWord e0 e1 e2 e3 ++ tail,
           mem := writeWordBe mem a.val e0 e1 e2 e3,
           locs := locs } := by
  rcases hacc with ⟨σ1, σ2, σ3, σ4, hmovdn, hrev1, hmovup, hcore, hrev2⟩
  have hσ1 := airMovdn4Full_sound (a := a) (b := e0) (c := e1) (d := e2) (e := e3)
    (tail := tail) (mem := mem) (locs := locs) hmovdn
  have hrev1' :
      airReversewFull
        { stack := e0 :: e1 :: e2 :: e3 :: a :: tail, mem := mem, locs := locs } σ2 := by
    simpa [hσ1] using hrev1
  have hσ2 := airReversewFull_sound (a := e0) (b := e1) (c := e2) (d := e3)
    (tail := a :: tail) (mem := mem) (locs := locs) hrev1'
  have hmovup' :
      airMovup4Full
        { stack := e3 :: e2 :: e1 :: e0 :: a :: tail, mem := mem, locs := locs } σ3 := by
    simpa [hσ2] using hmovup
  have hσ3 := airMovup4Full_sound (a := e3) (b := e2) (c := e1) (d := e0) (e := a)
    (tail := tail) (mem := mem) (locs := locs) hmovup'
  have hcore' :
      coreMemStorewLeAccepts
        { stack := a :: e3 :: e2 :: e1 :: e0 :: tail, mem := mem, locs := locs } σ4 := by
    simpa [hσ3] using hcore
  have hσ4 :
      σ4 = { stack := stackWord e3 e2 e1 e0 ++ tail,
             mem := writeWordLe mem a.val e3 e2 e1 e0,
             locs := locs } :=
    hCoreMemStorewLe ha_lt ha_aligned hcore'
  have hrev2' :
      airReversewFull
        { stack := stackWord e3 e2 e1 e0 ++ tail,
          mem := writeWordLe mem a.val e3 e2 e1 e0,
          locs := locs } σ' := by
    simpa [hσ4] using hrev2
  have hfinal := airReversewFull_sound (a := e3) (b := e2) (c := e1) (d := e0)
    (tail := tail) (mem := writeWordLe mem a.val e3 e2 e1 e0) (locs := locs) (by
      simpa [stackWord] using hrev2')
  simpa [stackWord, writeWordLe_eq_writeWordBe_reversed] using hfinal

end

end MidenLean.AIR.Proofs.WordIOSoundness
