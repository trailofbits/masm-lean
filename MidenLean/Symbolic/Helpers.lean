import MidenLean.Symbolic.Exec

/-!
# Per-instruction soundness helpers

Helper theorems for `execInstruction_sound` proving that each supported instruction's
symbolic execution is sound with respect to concrete execution.

Organized by proof pattern:
- **Shared helpers**: list and precondition lemmas used across patterns
- **Simple stack ops**: no preconditions, pure stack transformation
- **Assertion ops**: state-preserving, precondition-guarded assertions
- **Guarded stack ops**: precondition extraction, then stack transformation
- **Word ops**: multi-element indexed access via `getElem?`
-/

namespace MidenLean.Symbolic

-- Shared helper lemmas

theorem getElem?_some_lt {α : Type} (l : List α) (n : Nat) (v : α)
    (h : l[n]? = some v) : n < l.length :=
  List.getElem?_eq_some_iff.mp h |>.1

theorem getElem_of_getElem?_some {α : Type} (l : List α) (n : Nat) (v : α)
    (h : l[n]? = some v) : l[n]'(getElem?_some_lt l n v h) = v := by
  have := List.getElem?_eq_getElem (getElem?_some_lt l n v h) (α := α)
  rw [this] at h; exact Option.some.inj h

theorem getElem?_map_append_left {α β : Type} (f : α → β)
    (l : List α) (rest : List β) (n : Nat) (hn : n < l.length) :
    (l.map f ++ rest)[n]? = some (f l[n]) := by
  rw [List.getElem?_append, if_pos (by simp; omega), List.getElem?_map,
      List.getElem?_eq_getElem (by omega)]
  rfl

theorem set_map_append_left {α β : Type} (f : α → β)
    (l : List α) (rest : List β) (n : Nat) (x : α) (hn : n < l.length) :
    (l.set n x).map f ++ rest = (l.map f ++ rest).set n (f x) := by
  rw [List.map_set, List.set_append, if_pos (by simp; omega)]

theorem eraseIdx_map_append_left {α β : Type} (f : α → β)
    (l : List α) (rest : List β) (n : Nat) (hn : n < l.length) :
    (l.map f ++ rest).eraseIdx n = (l.eraseIdx n).map f ++ rest := by
  rw [List.eraseIdx_append_of_lt_length (by simp; omega), List.eraseIdx_map]

theorem isBool_guard (x : Felt) (h : x = 0 ∨ x = 1) : x.isBool = true := by
  unfold Felt.isBool
  rcases h with rfl | rfl <;> decide

theorem bne_if_eq_if {α : Type} {β : Type} [BEq α] (a b : α) (x y : β) :
    (if !(a == b) then x else y) = (if a == b then y else x) := by
  cases h : a == b <;> simp [h]

theorem map_lit_map_eval (σ : Assignment) (vs : List Felt) :
    (vs.map Expr.lit).map (Expr.eval σ) = vs := by
  induction vs with
  | nil => rfl
  | cons v rest ih => simp [Expr.eval, ih]

-- Helper: (a.eval σ) = 1 → (a.eval σ).val == 1 = true
theorem eqOne_val_guard (x : Felt) (h : x = 1) : ((x.val == 1) = true) := by
  simp [h, ZMod.val_one]

-- Helper: (a.eval σ) = 0 → (a.eval σ).val == 0 = true
theorem eqZero_val_guard (x : Felt) (h : x = 0) : ((x.val == 0) = true) := by
  simp [h, ZMod.val_zero]

-- Helper: a = b → (a == b) = true for Felt
theorem feltEq_beq_guard (a b : Felt) (h : a = b) : ((a == b) = true) := by
  subst h; simp [BEq.beq, DecidableEq]

theorem valLeq_to_not_gt (x : Felt) (h : x.val ≤ 63) : ¬(x.val > 63) := by omega

/-- Convert the symbolic `.nonzero` precondition (Felt BEq with 0 is false)
    to a Nat-level `val == 0 = false` fact usable in concrete guards. -/
theorem felt_nonzero_val_ne_zero {x : Felt}
    (h : ((x == (0 : Felt)) = false)) : ((x.val == 0) = false) := by
  simp only [beq_eq_false_iff_ne, ne_eq] at h ⊢
  intro hval
  apply h
  exact (ZMod.val_eq_zero x).mp hval

/-- For small n (n ≤ 31), (Felt.ofNat n).val = n. Used in Imm instruction proofs
    to bridge symbolic evaluation (which goes through .lit (Felt.ofNat n)) and
    concrete execution (which uses n directly). -/
theorem feltOfNat_val_small (n : Nat) (hn : n ≤ 31) :
    (Felt.ofNat n).val = n := by
  unfold Felt.ofNat
  simp only [Felt, GOLDILOCKS_PRIME]
  rw [ZMod.val_natCast]
  apply Nat.mod_eq_of_lt
  omega

-- Simple stack ops (no preconditions, pure stack transformation)

theorem execInstruction_sound_nop
    (ss : State) (cs : MidenState)
    (σ : Assignment) (rest : List Felt)
    (ss' : State) (preconds : List Precondition)
    (hmodels : ss.models cs σ rest)
    (hexec : execInstruction ss .nop = some (ss', preconds))
    (hpreconds : ∀ p ∈ preconds, p.holds σ) :
    ∃ cs', MidenLean.execInstruction cs .nop = some cs' ∧ ss'.models cs' σ rest := by
  obtain ⟨hstack, hmem, hframes, hadv⟩ := hmodels
  simp only [execInstruction] at hexec
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hexec)
  exact ⟨cs,
    by simp only [MidenLean.execInstruction],
    hstack, hmem, hframes, hadv⟩

theorem execInstruction_sound_padw
    (ss : State) (cs : MidenState)
    (σ : Assignment) (rest : List Felt)
    (ss' : State) (preconds : List Precondition)
    (hmodels : ss.models cs σ rest)
    (hexec : execInstruction ss .padw = some (ss', preconds))
    (hpreconds : ∀ p ∈ preconds, p.holds σ) :
    ∃ cs', MidenLean.execInstruction cs .padw = some cs' ∧ ss'.models cs' σ rest := by
  obtain ⟨hstack, hmem, hframes, hadv⟩ := hmodels
  simp only [execInstruction] at hexec
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hexec)
  exact ⟨cs.withStack (0 :: 0 :: 0 :: 0 :: cs.stack),
    by simp only [MidenLean.execInstruction, execPadw, hstack, MidenState.withStack],
    ⟨by simp only [MidenState.withStack, List.map_cons, Expr.eval, hstack,
         List.cons_append], hmem, hframes, hadv⟩⟩

theorem execInstruction_sound_push
    (v : Felt) (ss : State) (cs : MidenState)
    (σ : Assignment) (rest : List Felt)
    (ss' : State) (preconds : List Precondition)
    (hmodels : ss.models cs σ rest)
    (hexec : execInstruction ss (.push v) = some (ss', preconds))
    (hpreconds : ∀ p ∈ preconds, p.holds σ) :
    ∃ cs', MidenLean.execInstruction cs (.push v) = some cs' ∧ ss'.models cs' σ rest := by
  obtain ⟨hstack, hmem, hframes, hadv⟩ := hmodels
  simp only [execInstruction] at hexec
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hexec)
  exact ⟨cs.withStack (v :: cs.stack),
    by simp only [MidenLean.execInstruction, execPush, hstack, MidenState.withStack],
    ⟨by simp only [MidenState.withStack, List.map_cons, Expr.eval, hstack,
         List.cons_append], hmem, hframes, hadv⟩⟩

theorem execInstruction_sound_pushList
    (vs : List Felt) (ss : State) (cs : MidenState)
    (σ : Assignment) (rest : List Felt)
    (ss' : State) (preconds : List Precondition)
    (hmodels : ss.models cs σ rest)
    (hexec : execInstruction ss (.pushList vs) = some (ss', preconds))
    (hpreconds : ∀ p ∈ preconds, p.holds σ) :
    ∃ cs', MidenLean.execInstruction cs (.pushList vs) = some cs' ∧ ss'.models cs' σ rest := by
  obtain ⟨hstack, hmem, hframes, hadv⟩ := hmodels
  simp only [execInstruction] at hexec
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hexec)
  exact ⟨cs.withStack (vs ++ cs.stack),
    by simp only [MidenLean.execInstruction, execPushList, hstack, MidenState.withStack],
    ⟨by simp only [MidenState.withStack, List.map_append, hstack, List.append_assoc]; congr 1; exact (map_lit_map_eval σ vs).symm, hmem, hframes, hadv⟩⟩

theorem execInstruction_sound_dropw
    (ss : State) (cs : MidenState)
    (σ : Assignment) (rest : List Felt)
    (ss' : State) (preconds : List Precondition)
    (hmodels : ss.models cs σ rest)
    (hexec : execInstruction ss .dropw = some (ss', preconds))
    (hpreconds : ∀ p ∈ preconds, p.holds σ) :
    ∃ cs', MidenLean.execInstruction cs .dropw = some cs' ∧ ss'.models cs' σ rest := by
  obtain ⟨hstack, hmem, hframes, hadv⟩ := hmodels
  simp only [execInstruction] at hexec
  match hstk : ss.stack with
  | [] | [_] | [_, _] | [_, _, _] => simp [hstk] at hexec
  | _ :: _ :: _ :: _ :: tail =>
    simp only [hstk] at hexec
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hexec)
    rw [hstk, List.map_cons, List.map_cons, List.map_cons, List.map_cons] at hstack
    exact ⟨cs.withStack (tail.map (Expr.eval σ) ++ rest),
      by simp only [MidenLean.execInstruction, execDropw, hstack]; rfl,
      ⟨by simp only [MidenState.withStack], hmem, hframes, hadv⟩⟩

theorem execInstruction_sound_swapdw
    (ss : State) (cs : MidenState)
    (σ : Assignment) (rest : List Felt)
    (ss' : State) (preconds : List Precondition)
    (hmodels : ss.models cs σ rest)
    (hexec : execInstruction ss .swapdw = some (ss', preconds))
    (hpreconds : ∀ p ∈ preconds, p.holds σ) :
    ∃ cs', MidenLean.execInstruction cs .swapdw = some cs' ∧ ss'.models cs' σ rest := by
  obtain ⟨hstack, hmem, hframes, hadv⟩ := hmodels
  simp only [execInstruction] at hexec
  match hstk : ss.stack with
  | a0::a1::a2::a3::b0::b1::b2::b3::c0::c1::c2::c3::d0::d1::d2::d3::tail =>
    simp only [hstk] at hexec
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hexec)
    rw [hstk] at hstack
    simp only [List.map_cons, List.cons_append] at hstack
    exact ⟨cs.withStack (c0.eval σ::c1.eval σ::c2.eval σ::c3.eval σ::
                          d0.eval σ::d1.eval σ::d2.eval σ::d3.eval σ::
                          a0.eval σ::a1.eval σ::a2.eval σ::a3.eval σ::
                          b0.eval σ::b1.eval σ::b2.eval σ::b3.eval σ::
                          tail.map (Expr.eval σ) ++ rest),
      by simp only [MidenLean.execInstruction, execSwapdw, hstack, MidenState.withStack]; rfl,
      ⟨by simp only [MidenState.withStack, List.map_cons, Expr.eval], hmem, hframes, hadv⟩⟩
  | _ =>
    split at hexec
    · -- overlap: the 16+ element pattern matched both arms; proceed like the main case
      rename_i a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 d0 d1 d2 d3 tail heq_stk
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hexec)
      rw [heq_stk] at hstack
      simp only [List.map_cons, List.cons_append] at hstack
      exact ⟨cs.withStack (c0.eval σ::c1.eval σ::c2.eval σ::c3.eval σ::
                            d0.eval σ::d1.eval σ::d2.eval σ::d3.eval σ::
                            a0.eval σ::a1.eval σ::a2.eval σ::a3.eval σ::
                            b0.eval σ::b1.eval σ::b2.eval σ::b3.eval σ::
                            tail.map (Expr.eval σ) ++ rest),
        by simp only [MidenLean.execInstruction, execSwapdw, hstack, MidenState.withStack]; rfl,
        ⟨by simp only [MidenState.withStack, List.map_cons, Expr.eval], hmem, hframes, hadv⟩⟩
    · simp at hexec

theorem execInstruction_sound_reversew
    (ss : State) (cs : MidenState)
    (σ : Assignment) (rest : List Felt)
    (ss' : State) (preconds : List Precondition)
    (hmodels : ss.models cs σ rest)
    (hexec : execInstruction ss .reversew = some (ss', preconds))
    (hpreconds : ∀ p ∈ preconds, p.holds σ) :
    ∃ cs', MidenLean.execInstruction cs .reversew = some cs' ∧ ss'.models cs' σ rest := by
  obtain ⟨hstack, hmem, hframes, hadv⟩ := hmodels
  simp only [execInstruction] at hexec
  match hstk : ss.stack with
  | [] | [_] | [_, _] | [_, _, _] => simp [hstk] at hexec
  | a :: b :: c :: d :: tail =>
    simp only [hstk] at hexec
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hexec)
    rw [hstk, List.map_cons, List.map_cons, List.map_cons, List.map_cons] at hstack
    exact ⟨cs.withStack (d.eval σ :: c.eval σ :: b.eval σ :: a.eval σ ::
                          tail.map (Expr.eval σ) ++ rest),
      by simp only [MidenLean.execInstruction, execReversew, hstack]; rfl,
      ⟨by simp only [MidenState.withStack, List.map_cons, Expr.eval], hmem, hframes, hadv⟩⟩

theorem execInstruction_sound_addImm
    (v : Felt) (ss : State) (cs : MidenState)
    (σ : Assignment) (rest : List Felt)
    (ss' : State) (preconds : List Precondition)
    (hmodels : ss.models cs σ rest)
    (hexec : execInstruction ss (.addImm v) = some (ss', preconds))
    (hpreconds : ∀ p ∈ preconds, p.holds σ) :
    ∃ cs', MidenLean.execInstruction cs (.addImm v) = some cs' ∧ ss'.models cs' σ rest := by
  obtain ⟨hstack, hmem, hframes, hadv⟩ := hmodels
  simp only [execInstruction] at hexec
  match hstk : ss.stack with
  | [] => simp [hstk] at hexec
  | a :: tail =>
    simp only [hstk] at hexec
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hexec)
    rw [hstk, List.map_cons] at hstack
    exact ⟨cs.withStack ((a.eval σ + v) :: tail.map (Expr.eval σ) ++ rest),
      by simp only [MidenLean.execInstruction, execAddImm, hstack]; rfl,
      ⟨by simp only [MidenState.withStack, List.map_cons, Expr.eval], hmem, hframes, hadv⟩⟩

theorem execInstruction_sound_subImm
    (v : Felt) (ss : State) (cs : MidenState)
    (σ : Assignment) (rest : List Felt)
    (ss' : State) (preconds : List Precondition)
    (hmodels : ss.models cs σ rest)
    (hexec : execInstruction ss (.subImm v) = some (ss', preconds))
    (hpreconds : ∀ p ∈ preconds, p.holds σ) :
    ∃ cs', MidenLean.execInstruction cs (.subImm v) = some cs' ∧ ss'.models cs' σ rest := by
  obtain ⟨hstack, hmem, hframes, hadv⟩ := hmodels
  simp only [execInstruction] at hexec
  match hstk : ss.stack with
  | [] => simp [hstk] at hexec
  | a :: tail =>
    simp only [hstk] at hexec
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hexec)
    rw [hstk, List.map_cons] at hstack
    exact ⟨cs.withStack ((a.eval σ - v) :: tail.map (Expr.eval σ) ++ rest),
      by simp only [MidenLean.execInstruction, execSubImm, hstack]; rfl,
      ⟨by simp only [MidenState.withStack, List.map_cons, Expr.eval], hmem, hframes, hadv⟩⟩

theorem execInstruction_sound_mulImm
    (v : Felt) (ss : State) (cs : MidenState)
    (σ : Assignment) (rest : List Felt)
    (ss' : State) (preconds : List Precondition)
    (hmodels : ss.models cs σ rest)
    (hexec : execInstruction ss (.mulImm v) = some (ss', preconds))
    (hpreconds : ∀ p ∈ preconds, p.holds σ) :
    ∃ cs', MidenLean.execInstruction cs (.mulImm v) = some cs' ∧ ss'.models cs' σ rest := by
  obtain ⟨hstack, hmem, hframes, hadv⟩ := hmodels
  simp only [execInstruction] at hexec
  match hstk : ss.stack with
  | [] => simp [hstk] at hexec
  | a :: tail =>
    simp only [hstk] at hexec
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hexec)
    rw [hstk, List.map_cons] at hstack
    exact ⟨cs.withStack ((a.eval σ * v) :: tail.map (Expr.eval σ) ++ rest),
      by simp only [MidenLean.execInstruction, execMulImm, hstack]; rfl,
      ⟨by simp only [MidenState.withStack, List.map_cons, Expr.eval], hmem, hframes, hadv⟩⟩

theorem execInstruction_sound_neg
    (ss : State) (cs : MidenState)
    (σ : Assignment) (rest : List Felt)
    (ss' : State) (preconds : List Precondition)
    (hmodels : ss.models cs σ rest)
    (hexec : execInstruction ss .neg = some (ss', preconds))
    (hpreconds : ∀ p ∈ preconds, p.holds σ) :
    ∃ cs', MidenLean.execInstruction cs .neg = some cs' ∧ ss'.models cs' σ rest := by
  obtain ⟨hstack, hmem, hframes, hadv⟩ := hmodels
  simp only [execInstruction] at hexec
  match hstk : ss.stack with
  | [] => simp [hstk] at hexec
  | a :: tail =>
    simp only [hstk] at hexec
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hexec)
    rw [hstk, List.map_cons] at hstack
    exact ⟨cs.withStack (-(a.eval σ) :: tail.map (Expr.eval σ) ++ rest),
      by simp only [MidenLean.execInstruction, execNeg, hstack]; rfl,
      ⟨by simp only [MidenState.withStack, List.map_cons, Expr.eval], hmem, hframes, hadv⟩⟩

theorem execInstruction_sound_incr
    (ss : State) (cs : MidenState)
    (σ : Assignment) (rest : List Felt)
    (ss' : State) (preconds : List Precondition)
    (hmodels : ss.models cs σ rest)
    (hexec : execInstruction ss .incr = some (ss', preconds))
    (hpreconds : ∀ p ∈ preconds, p.holds σ) :
    ∃ cs', MidenLean.execInstruction cs .incr = some cs' ∧ ss'.models cs' σ rest := by
  obtain ⟨hstack, hmem, hframes, hadv⟩ := hmodels
  simp only [execInstruction] at hexec
  match hstk : ss.stack with
  | [] => simp [hstk] at hexec
  | a :: tail =>
    simp only [hstk] at hexec
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hexec)
    rw [hstk, List.map_cons] at hstack
    exact ⟨cs.withStack ((a.eval σ + 1) :: tail.map (Expr.eval σ) ++ rest),
      by simp only [MidenLean.execInstruction, execIncr, hstack]; rfl,
      ⟨by simp only [MidenState.withStack, List.map_cons, Expr.eval], hmem, hframes, hadv⟩⟩

theorem execInstruction_sound_eqImm
    (v : Felt) (ss : State) (cs : MidenState)
    (σ : Assignment) (rest : List Felt)
    (ss' : State) (preconds : List Precondition)
    (hmodels : ss.models cs σ rest)
    (hexec : execInstruction ss (.eqImm v) = some (ss', preconds))
    (hpreconds : ∀ p ∈ preconds, p.holds σ) :
    ∃ cs', MidenLean.execInstruction cs (.eqImm v) = some cs' ∧ ss'.models cs' σ rest := by
  obtain ⟨hstack, hmem, hframes, hadv⟩ := hmodels
  simp only [execInstruction] at hexec
  match hstk : ss.stack with
  | [] => simp [hstk] at hexec
  | a :: tail =>
    simp only [hstk] at hexec
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hexec)
    rw [hstk, List.map_cons] at hstack
    exact ⟨cs.withStack ((if a.eval σ == v then (1 : Felt) else 0) ::
                          tail.map (Expr.eval σ) ++ rest),
      by simp only [MidenLean.execInstruction, execEqImm, hstack]; rfl,
      ⟨by simp only [MidenState.withStack, List.map_cons, Expr.eval], hmem, hframes, hadv⟩⟩

theorem execInstruction_sound_neq
    (ss : State) (cs : MidenState)
    (σ : Assignment) (rest : List Felt)
    (ss' : State) (preconds : List Precondition)
    (hmodels : ss.models cs σ rest)
    (hexec : execInstruction ss .neq = some (ss', preconds))
    (hpreconds : ∀ p ∈ preconds, p.holds σ) :
    ∃ cs', MidenLean.execInstruction cs .neq = some cs' ∧ ss'.models cs' σ rest := by
  obtain ⟨hstack, hmem, hframes, hadv⟩ := hmodels
  simp only [execInstruction] at hexec
  match hstk : ss.stack with
  | [] | [_] => simp [hstk] at hexec
  | b :: a :: tail =>
    simp only [hstk] at hexec
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hexec)
    rw [hstk, List.map_cons, List.map_cons] at hstack
    refine ⟨cs.withStack ((if a.eval σ != b.eval σ then (1 : Felt) else 0) ::
                           tail.map (Expr.eval σ) ++ rest), ?_, ?_⟩
    · simp only [MidenLean.execInstruction, execNeq, hstack]; rfl
    · exact ⟨by simp only [MidenState.withStack, List.map_cons, Expr.eval]; congr 1; congr 1; exact bne_if_eq_if (a.eval σ) (b.eval σ) 1 0, hmem, hframes, hadv⟩

theorem execInstruction_sound_neqImm
    (v : Felt) (ss : State) (cs : MidenState)
    (σ : Assignment) (rest : List Felt)
    (ss' : State) (preconds : List Precondition)
    (hmodels : ss.models cs σ rest)
    (hexec : execInstruction ss (.neqImm v) = some (ss', preconds))
    (hpreconds : ∀ p ∈ preconds, p.holds σ) :
    ∃ cs', MidenLean.execInstruction cs (.neqImm v) = some cs' ∧ ss'.models cs' σ rest := by
  obtain ⟨hstack, hmem, hframes, hadv⟩ := hmodels
  simp only [execInstruction] at hexec
  match hstk : ss.stack with
  | [] => simp [hstk] at hexec
  | a :: tail =>
    simp only [hstk] at hexec
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hexec)
    rw [hstk, List.map_cons] at hstack
    refine ⟨cs.withStack ((if a.eval σ != v then (1 : Felt) else 0) ::
                           tail.map (Expr.eval σ) ++ rest), ?_, ?_⟩
    · simp only [MidenLean.execInstruction, execNeqImm, hstack]; rfl
    · exact ⟨by simp only [MidenState.withStack, List.map_cons, Expr.eval]; congr 1; congr 1; exact bne_if_eq_if (a.eval σ) v 1 0, hmem, hframes, hadv⟩

theorem execInstruction_sound_lt
    (ss : State) (cs : MidenState)
    (σ : Assignment) (rest : List Felt)
    (ss' : State) (preconds : List Precondition)
    (hmodels : ss.models cs σ rest)
    (hexec : execInstruction ss .lt = some (ss', preconds))
    (hpreconds : ∀ p ∈ preconds, p.holds σ) :
    ∃ cs', MidenLean.execInstruction cs .lt = some cs' ∧ ss'.models cs' σ rest := by
  obtain ⟨hstack, hmem, hframes, hadv⟩ := hmodels
  simp only [execInstruction] at hexec
  match hstk : ss.stack with
  | [] | [_] => simp [hstk] at hexec
  | b :: a :: tail =>
    simp only [hstk] at hexec
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hexec)
    rw [hstk, List.map_cons, List.map_cons] at hstack
    exact ⟨cs.withStack ((if (a.eval σ).val < (b.eval σ).val then (1 : Felt) else 0) ::
                          tail.map (Expr.eval σ) ++ rest),
      by simp only [MidenLean.execInstruction, execLt, hstack]; rfl,
      ⟨by simp only [MidenState.withStack, List.map_cons, Expr.eval], hmem, hframes, hadv⟩⟩

theorem execInstruction_sound_lte
    (ss : State) (cs : MidenState)
    (σ : Assignment) (rest : List Felt)
    (ss' : State) (preconds : List Precondition)
    (hmodels : ss.models cs σ rest)
    (hexec : execInstruction ss .lte = some (ss', preconds))
    (hpreconds : ∀ p ∈ preconds, p.holds σ) :
    ∃ cs', MidenLean.execInstruction cs .lte = some cs' ∧ ss'.models cs' σ rest := by
  obtain ⟨hstack, hmem, hframes, hadv⟩ := hmodels
  simp only [execInstruction] at hexec
  match hstk : ss.stack with
  | [] | [_] => simp [hstk] at hexec
  | b :: a :: tail =>
    simp only [hstk] at hexec
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hexec)
    rw [hstk, List.map_cons, List.map_cons] at hstack
    exact ⟨cs.withStack ((if (a.eval σ).val ≤ (b.eval σ).val then (1 : Felt) else 0) ::
                          tail.map (Expr.eval σ) ++ rest),
      by simp only [MidenLean.execInstruction, execLte, hstack]; rfl,
      ⟨by simp only [MidenState.withStack, List.map_cons, Expr.eval], hmem, hframes, hadv⟩⟩

theorem execInstruction_sound_gt
    (ss : State) (cs : MidenState)
    (σ : Assignment) (rest : List Felt)
    (ss' : State) (preconds : List Precondition)
    (hmodels : ss.models cs σ rest)
    (hexec : execInstruction ss .gt = some (ss', preconds))
    (hpreconds : ∀ p ∈ preconds, p.holds σ) :
    ∃ cs', MidenLean.execInstruction cs .gt = some cs' ∧ ss'.models cs' σ rest := by
  obtain ⟨hstack, hmem, hframes, hadv⟩ := hmodels
  simp only [execInstruction] at hexec
  match hstk : ss.stack with
  | [] | [_] => simp [hstk] at hexec
  | b :: a :: tail =>
    simp only [hstk] at hexec
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hexec)
    rw [hstk, List.map_cons, List.map_cons] at hstack
    exact ⟨cs.withStack ((if (a.eval σ).val > (b.eval σ).val then (1 : Felt) else 0) ::
                          tail.map (Expr.eval σ) ++ rest),
      by simp only [MidenLean.execInstruction, execGt, hstack]; rfl,
      ⟨by simp only [MidenState.withStack, List.map_cons, Expr.eval], hmem, hframes, hadv⟩⟩

theorem execInstruction_sound_gte
    (ss : State) (cs : MidenState)
    (σ : Assignment) (rest : List Felt)
    (ss' : State) (preconds : List Precondition)
    (hmodels : ss.models cs σ rest)
    (hexec : execInstruction ss .gte = some (ss', preconds))
    (hpreconds : ∀ p ∈ preconds, p.holds σ) :
    ∃ cs', MidenLean.execInstruction cs .gte = some cs' ∧ ss'.models cs' σ rest := by
  obtain ⟨hstack, hmem, hframes, hadv⟩ := hmodels
  simp only [execInstruction] at hexec
  match hstk : ss.stack with
  | [] | [_] => simp [hstk] at hexec
  | b :: a :: tail =>
    simp only [hstk] at hexec
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hexec)
    rw [hstk, List.map_cons, List.map_cons] at hstack
    exact ⟨cs.withStack ((if (a.eval σ).val ≥ (b.eval σ).val then (1 : Felt) else 0) ::
                          tail.map (Expr.eval σ) ++ rest),
      by simp only [MidenLean.execInstruction, execGte, hstack]; rfl,
      ⟨by simp only [MidenState.withStack, List.map_cons, Expr.eval], hmem, hframes, hadv⟩⟩

theorem execInstruction_sound_isOdd
    (ss : State) (cs : MidenState)
    (σ : Assignment) (rest : List Felt)
    (ss' : State) (preconds : List Precondition)
    (hmodels : ss.models cs σ rest)
    (hexec : execInstruction ss .isOdd = some (ss', preconds))
    (hpreconds : ∀ p ∈ preconds, p.holds σ) :
    ∃ cs', MidenLean.execInstruction cs .isOdd = some cs' ∧ ss'.models cs' σ rest := by
  obtain ⟨hstack, hmem, hframes, hadv⟩ := hmodels
  simp only [execInstruction] at hexec
  match hstk : ss.stack with
  | [] => simp [hstk] at hexec
  | a :: tail =>
    simp only [hstk] at hexec
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hexec)
    rw [hstk, List.map_cons] at hstack
    exact ⟨cs.withStack ((if (a.eval σ).val % 2 == 1 then (1 : Felt) else 0) ::
                          tail.map (Expr.eval σ) ++ rest),
      by simp only [MidenLean.execInstruction, execIsOdd, hstack]; rfl,
      ⟨by simp only [MidenState.withStack, List.map_cons, Expr.eval], hmem, hframes, hadv⟩⟩

theorem execInstruction_sound_u32Cast
    (ss : State) (cs : MidenState)
    (σ : Assignment) (rest : List Felt)
    (ss' : State) (preconds : List Precondition)
    (hmodels : ss.models cs σ rest)
    (hexec : execInstruction ss .u32Cast = some (ss', preconds))
    (hpreconds : ∀ p ∈ preconds, p.holds σ) :
    ∃ cs', MidenLean.execInstruction cs .u32Cast = some cs' ∧ ss'.models cs' σ rest := by
  obtain ⟨hstack, hmem, hframes, hadv⟩ := hmodels
  simp only [execInstruction] at hexec
  match hstk : ss.stack with
  | [] => simp [hstk] at hexec
  | a :: tail =>
    simp only [hstk] at hexec
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hexec)
    rw [hstk, List.map_cons] at hstack
    refine ⟨cs.withStack ((a.eval σ).lo32 :: tail.map (Expr.eval σ) ++ rest), ?_, ?_⟩
    · change execU32Cast cs = _
      unfold execU32Cast
      rw [hstack]; simp [MidenState.withStack]
    · exact ⟨by simp only [MidenState.withStack, List.map_cons, Expr.eval], hmem, hframes, hadv⟩

theorem execInstruction_sound_u32Split
    (ss : State) (cs : MidenState)
    (σ : Assignment) (rest : List Felt)
    (ss' : State) (preconds : List Precondition)
    (hmodels : ss.models cs σ rest)
    (hexec : execInstruction ss .u32Split = some (ss', preconds))
    (hpreconds : ∀ p ∈ preconds, p.holds σ) :
    ∃ cs', MidenLean.execInstruction cs .u32Split = some cs' ∧ ss'.models cs' σ rest := by
  obtain ⟨hstack, hmem, hframes, hadv⟩ := hmodels
  simp only [execInstruction] at hexec
  match hstk : ss.stack with
  | [] => simp [hstk] at hexec
  | a :: tail =>
    simp only [hstk] at hexec
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hexec)
    rw [hstk, List.map_cons] at hstack
    refine ⟨cs.withStack ((a.eval σ).lo32 :: (a.eval σ).hi32 :: tail.map (Expr.eval σ) ++ rest), ?_, ?_⟩
    · change execU32Split cs = _
      unfold execU32Split
      rw [hstack]; simp [MidenState.withStack]
    · exact ⟨by simp only [MidenState.withStack, List.map_cons, Expr.eval,
          List.cons_append], hmem, hframes, hadv⟩

set_option maxHeartbeats 400000 in
theorem execInstruction_sound_eqw
    (ss : State) (cs : MidenState)
    (σ : Assignment) (rest : List Felt)
    (ss' : State) (preconds : List Precondition)
    (hmodels : ss.models cs σ rest)
    (hexec : execInstruction ss .eqw = some (ss', preconds))
    (hpreconds : ∀ p ∈ preconds, p.holds σ) :
    ∃ cs', MidenLean.execInstruction cs .eqw = some cs' ∧ ss'.models cs' σ rest := by
  obtain ⟨hstack, hmem, hframes, hadv⟩ := hmodels
  simp only [execInstruction] at hexec
  match hstk : ss.stack with
  | [] | [_] | [_, _] | [_, _, _] | [_, _, _, _]
  | [_, _, _, _, _] | [_, _, _, _, _, _] | [_, _, _, _, _, _, _] =>
    simp [hstk] at hexec
  | b0 :: b1 :: b2 :: b3 :: a0 :: a1 :: a2 :: a3 :: tail =>
    simp only [hstk] at hexec
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hexec)
    rw [hstk, List.map_cons, List.map_cons, List.map_cons, List.map_cons,
        List.map_cons, List.map_cons, List.map_cons, List.map_cons] at hstack
    refine ⟨cs.withStack ((if a0.eval σ == b0.eval σ && a1.eval σ == b1.eval σ &&
                               a2.eval σ == b2.eval σ && a3.eval σ == b3.eval σ
                           then (1 : Felt) else 0)
                           :: b0.eval σ :: b1.eval σ :: b2.eval σ :: b3.eval σ
                           :: a0.eval σ :: a1.eval σ :: a2.eval σ :: a3.eval σ
                           :: tail.map (Expr.eval σ) ++ rest), ?_, ?_⟩
    · change execEqw cs = _
      unfold execEqw
      rw [hstack]; simp [MidenState.withStack]
    · exact ⟨by simp only [MidenState.withStack, List.map_cons, Expr.eval,
          List.cons_append], hmem, hframes, hadv⟩


-- Assertion ops (state-preserving, precondition-guarded assertions)

theorem execInstruction_sound_assert
    (ss : State) (cs : MidenState)
    (σ : Assignment) (rest : List Felt)
    (ss' : State) (preconds : List Precondition)
    (hmodels : ss.models cs σ rest)
    (hexec : execInstruction ss .assert = some (ss', preconds))
    (hpreconds : ∀ p ∈ preconds, p.holds σ) :
    ∃ cs', MidenLean.execInstruction cs .assert = some cs' ∧ ss'.models cs' σ rest := by
  obtain ⟨hstack, hmem, hframes, hadv⟩ := hmodels
  simp only [execInstruction] at hexec
  match hstk : ss.stack with
  | [] => simp [hstk] at hexec
  | a :: tail =>
    simp only [hstk] at hexec
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hexec)
    rw [hstk, List.map_cons] at hstack
    have h1 : (a.eval σ) = 1 :=
      hpreconds (.eqOne a) (by simp)
    have hguard : ((a.eval σ).val == 1) = true := eqOne_val_guard _ h1
    refine ⟨cs.withStack (tail.map (Expr.eval σ) ++ rest), ?_, ?_⟩
    · change execAssert cs = _
      unfold execAssert
      rw [hstack]; simp [hguard, MidenState.withStack]
    · exact ⟨by simp only [MidenState.withStack], hmem, hframes, hadv⟩


theorem execInstruction_sound_assertWithError
    (msg : String) (ss : State) (cs : MidenState)
    (σ : Assignment) (rest : List Felt)
    (ss' : State) (preconds : List Precondition)
    (hmodels : ss.models cs σ rest)
    (hexec : execInstruction ss (.assertWithError msg) = some (ss', preconds))
    (hpreconds : ∀ p ∈ preconds, p.holds σ) :
    ∃ cs', MidenLean.execInstruction cs (.assertWithError msg) = some cs' ∧ ss'.models cs' σ rest := by
  obtain ⟨hstack, hmem, hframes, hadv⟩ := hmodels
  simp only [execInstruction] at hexec
  match hstk : ss.stack with
  | [] => simp [hstk] at hexec
  | a :: tail =>
    simp only [hstk] at hexec
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hexec)
    rw [hstk, List.map_cons] at hstack
    have h1 : (a.eval σ) = 1 :=
      hpreconds (.eqOne a) (by simp)
    have hguard : ((a.eval σ).val == 1) = true := eqOne_val_guard _ h1
    refine ⟨cs.withStack (tail.map (Expr.eval σ) ++ rest), ?_, ?_⟩
    · change execAssert cs = _
      unfold execAssert
      rw [hstack]; simp [hguard, MidenState.withStack]
    · exact ⟨by simp only [MidenState.withStack], hmem, hframes, hadv⟩

theorem execInstruction_sound_assertz
    (ss : State) (cs : MidenState)
    (σ : Assignment) (rest : List Felt)
    (ss' : State) (preconds : List Precondition)
    (hmodels : ss.models cs σ rest)
    (hexec : execInstruction ss .assertz = some (ss', preconds))
    (hpreconds : ∀ p ∈ preconds, p.holds σ) :
    ∃ cs', MidenLean.execInstruction cs .assertz = some cs' ∧ ss'.models cs' σ rest := by
  obtain ⟨hstack, hmem, hframes, hadv⟩ := hmodels
  simp only [execInstruction] at hexec
  match hstk : ss.stack with
  | [] => simp [hstk] at hexec
  | a :: tail =>
    simp only [hstk] at hexec
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hexec)
    rw [hstk, List.map_cons] at hstack
    have h0 : (a.eval σ) = 0 :=
      hpreconds (.eqZero a) (by simp)
    have hguard : ((a.eval σ).val == 0) = true := eqZero_val_guard _ h0
    refine ⟨cs.withStack (tail.map (Expr.eval σ) ++ rest), ?_, ?_⟩
    · change execAssertz cs = _
      unfold execAssertz
      rw [hstack]; simp [hguard, MidenState.withStack]
    · exact ⟨by simp only [MidenState.withStack], hmem, hframes, hadv⟩

theorem execInstruction_sound_assertzWithError
    (msg : String) (ss : State) (cs : MidenState)
    (σ : Assignment) (rest : List Felt)
    (ss' : State) (preconds : List Precondition)
    (hmodels : ss.models cs σ rest)
    (hexec : execInstruction ss (.assertzWithError msg) = some (ss', preconds))
    (hpreconds : ∀ p ∈ preconds, p.holds σ) :
    ∃ cs', MidenLean.execInstruction cs (.assertzWithError msg) = some cs' ∧ ss'.models cs' σ rest := by
  obtain ⟨hstack, hmem, hframes, hadv⟩ := hmodels
  simp only [execInstruction] at hexec
  match hstk : ss.stack with
  | [] => simp [hstk] at hexec
  | a :: tail =>
    simp only [hstk] at hexec
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hexec)
    rw [hstk, List.map_cons] at hstack
    have h0 : (a.eval σ) = 0 :=
      hpreconds (.eqZero a) (by simp)
    have hguard : ((a.eval σ).val == 0) = true := eqZero_val_guard _ h0
    refine ⟨cs.withStack (tail.map (Expr.eval σ) ++ rest), ?_, ?_⟩
    · change execAssertz cs = _
      unfold execAssertz
      rw [hstack]; simp [hguard, MidenState.withStack]
    · exact ⟨by simp only [MidenState.withStack], hmem, hframes, hadv⟩

theorem execInstruction_sound_assertEq
    (ss : State) (cs : MidenState)
    (σ : Assignment) (rest : List Felt)
    (ss' : State) (preconds : List Precondition)
    (hmodels : ss.models cs σ rest)
    (hexec : execInstruction ss .assertEq = some (ss', preconds))
    (hpreconds : ∀ p ∈ preconds, p.holds σ) :
    ∃ cs', MidenLean.execInstruction cs .assertEq = some cs' ∧ ss'.models cs' σ rest := by
  obtain ⟨hstack, hmem, hframes, hadv⟩ := hmodels
  simp only [execInstruction] at hexec
  match hstk : ss.stack with
  | [] | [_] => simp [hstk] at hexec
  | b :: a :: tail =>
    simp only [hstk] at hexec
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hexec)
    rw [hstk, List.map_cons, List.map_cons] at hstack
    have hab : (a.eval σ) = (b.eval σ) :=
      hpreconds (.feltEq a b) (by simp)
    have hguard : (a.eval σ == b.eval σ) = true := feltEq_beq_guard _ _ hab
    refine ⟨cs.withStack (tail.map (Expr.eval σ) ++ rest), ?_, ?_⟩
    · change execAssertEq cs = _
      unfold execAssertEq
      rw [hstack]; simp [hguard, MidenState.withStack]
    · exact ⟨by simp only [MidenState.withStack], hmem, hframes, hadv⟩

theorem execInstruction_sound_assertEqWithError
    (msg : String) (ss : State) (cs : MidenState)
    (σ : Assignment) (rest : List Felt)
    (ss' : State) (preconds : List Precondition)
    (hmodels : ss.models cs σ rest)
    (hexec : execInstruction ss (.assertEqWithError msg) = some (ss', preconds))
    (hpreconds : ∀ p ∈ preconds, p.holds σ) :
    ∃ cs', MidenLean.execInstruction cs (.assertEqWithError msg) = some cs' ∧ ss'.models cs' σ rest := by
  obtain ⟨hstack, hmem, hframes, hadv⟩ := hmodels
  simp only [execInstruction] at hexec
  match hstk : ss.stack with
  | [] | [_] => simp [hstk] at hexec
  | b :: a :: tail =>
    simp only [hstk] at hexec
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hexec)
    rw [hstk, List.map_cons, List.map_cons] at hstack
    have hab : (a.eval σ) = (b.eval σ) :=
      hpreconds (.feltEq a b) (by simp)
    have hguard : (a.eval σ == b.eval σ) = true := feltEq_beq_guard _ _ hab
    refine ⟨cs.withStack (tail.map (Expr.eval σ) ++ rest), ?_, ?_⟩
    · change execAssertEq cs = _
      unfold execAssertEq
      rw [hstack]; simp [hguard, MidenState.withStack]
    · exact ⟨by simp only [MidenState.withStack], hmem, hframes, hadv⟩

set_option maxHeartbeats 400000 in
theorem execInstruction_sound_assertEqw
    (ss : State) (cs : MidenState)
    (σ : Assignment) (rest : List Felt)
    (ss' : State) (preconds : List Precondition)
    (hmodels : ss.models cs σ rest)
    (hexec : execInstruction ss .assertEqw = some (ss', preconds))
    (hpreconds : ∀ p ∈ preconds, p.holds σ) :
    ∃ cs', MidenLean.execInstruction cs .assertEqw = some cs' ∧ ss'.models cs' σ rest := by
  obtain ⟨hstack, hmem, hframes, hadv⟩ := hmodels
  simp only [execInstruction] at hexec
  match hstk : ss.stack with
  | [] | [_] | [_, _] | [_, _, _] | [_, _, _, _]
  | [_, _, _, _, _] | [_, _, _, _, _, _] | [_, _, _, _, _, _, _] =>
    simp [hstk] at hexec
  | b0 :: b1 :: b2 :: b3 :: a0 :: a1 :: a2 :: a3 :: tail =>
    simp only [hstk] at hexec
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hexec)
    rw [hstk, List.map_cons, List.map_cons, List.map_cons, List.map_cons,
        List.map_cons, List.map_cons, List.map_cons, List.map_cons] at hstack
    have h0 : (a0.eval σ) = (b0.eval σ) :=
      hpreconds (.feltEq a0 b0) (by simp)
    have h1 : (a1.eval σ) = (b1.eval σ) :=
      hpreconds (.feltEq a1 b1) (by simp)
    have h2 : (a2.eval σ) = (b2.eval σ) :=
      hpreconds (.feltEq a2 b2) (by simp)
    have h3 : (a3.eval σ) = (b3.eval σ) :=
      hpreconds (.feltEq a3 b3) (by simp)
    have hg0 : (a0.eval σ == b0.eval σ) = true := feltEq_beq_guard _ _ h0
    have hg1 : (a1.eval σ == b1.eval σ) = true := feltEq_beq_guard _ _ h1
    have hg2 : (a2.eval σ == b2.eval σ) = true := feltEq_beq_guard _ _ h2
    have hg3 : (a3.eval σ == b3.eval σ) = true := feltEq_beq_guard _ _ h3
    have hguard : (a0.eval σ == b0.eval σ && (a1.eval σ == b1.eval σ) &&
                   (a2.eval σ == b2.eval σ) && (a3.eval σ == b3.eval σ)) = true := by
      rw [hg0, hg1, hg2, hg3]; rfl
    refine ⟨cs.withStack (tail.map (Expr.eval σ) ++ rest), ?_, ?_⟩
    · change execAssertEqw cs = _
      unfold execAssertEqw
      rw [hstack]; simp [hguard, MidenState.withStack]
    · exact ⟨by simp only [MidenState.withStack], hmem, hframes, hadv⟩

theorem execInstruction_sound_u32Assert
    (ss : State) (cs : MidenState)
    (σ : Assignment) (rest : List Felt)
    (ss' : State) (preconds : List Precondition)
    (hmodels : ss.models cs σ rest)
    (hexec : execInstruction ss .u32Assert = some (ss', preconds))
    (hpreconds : ∀ p ∈ preconds, p.holds σ) :
    ∃ cs', MidenLean.execInstruction cs .u32Assert = some cs' ∧ ss'.models cs' σ rest := by
  obtain ⟨hstack, hmem, hframes, hadv⟩ := hmodels
  simp only [execInstruction] at hexec
  match hstk : ss.stack with
  | [] => simp [hstk] at hexec
  | a :: tail =>
    simp only [hstk] at hexec
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hexec)
    rw [hstk, List.map_cons] at hstack
    have ha : (a.eval σ).isU32 = true :=
      hpreconds (.isU32 a) (by simp)
    refine ⟨cs, ?_, ?_⟩
    · change execU32Assert cs = _
      unfold execU32Assert
      rw [hstack]; simp [ha]
    · exact ⟨by simp only [hstk, hstack, List.map_cons], hmem, hframes, hadv⟩

theorem execInstruction_sound_u32Assert2
    (ss : State) (cs : MidenState)
    (σ : Assignment) (rest : List Felt)
    (ss' : State) (preconds : List Precondition)
    (hmodels : ss.models cs σ rest)
    (hexec : execInstruction ss .u32Assert2 = some (ss', preconds))
    (hpreconds : ∀ p ∈ preconds, p.holds σ) :
    ∃ cs', MidenLean.execInstruction cs .u32Assert2 = some cs' ∧ ss'.models cs' σ rest := by
  obtain ⟨hstack, hmem, hframes, hadv⟩ := hmodels
  simp only [execInstruction] at hexec
  match hstk : ss.stack with
  | [] | [_] => simp [hstk] at hexec
  | b :: a :: tail =>
    simp only [hstk] at hexec
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hexec)
    rw [hstk, List.map_cons, List.map_cons] at hstack
    have ha : (a.eval σ).isU32 = true :=
      hpreconds (.isU32 a) (by simp)
    have hb : (b.eval σ).isU32 = true :=
      hpreconds (.isU32 b) (by simp)
    have hguard : ((a.eval σ).isU32 && (b.eval σ).isU32) = true := by rw [ha, hb]; rfl
    refine ⟨cs, ?_, ?_⟩
    · change execU32Assert2 cs = _
      unfold execU32Assert2
      rw [hstack]; simp [hguard]
    · exact ⟨by simp only [hstk, hstack, List.map_cons], hmem, hframes, hadv⟩

theorem execInstruction_sound_u32AssertW
    (ss : State) (cs : MidenState)
    (σ : Assignment) (rest : List Felt)
    (ss' : State) (preconds : List Precondition)
    (hmodels : ss.models cs σ rest)
    (hexec : execInstruction ss .u32AssertW = some (ss', preconds))
    (hpreconds : ∀ p ∈ preconds, p.holds σ) :
    ∃ cs', MidenLean.execInstruction cs .u32AssertW = some cs' ∧ ss'.models cs' σ rest := by
  obtain ⟨hstack, hmem, hframes, hadv⟩ := hmodels
  simp only [execInstruction] at hexec
  match hstk : ss.stack with
  | [] | [_] | [_, _] | [_, _, _] => simp [hstk] at hexec
  | a :: b :: c :: d :: tail =>
    simp only [hstk] at hexec
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hexec)
    rw [hstk, List.map_cons, List.map_cons, List.map_cons, List.map_cons] at hstack
    have ha : (a.eval σ).isU32 = true :=
      hpreconds (.isU32 a) (by simp)
    have hb : (b.eval σ).isU32 = true :=
      hpreconds (.isU32 b) (by simp)
    have hc : (c.eval σ).isU32 = true :=
      hpreconds (.isU32 c) (by simp)
    have hd : (d.eval σ).isU32 = true :=
      hpreconds (.isU32 d) (by simp)
    have hguard : ((a.eval σ).isU32 && (b.eval σ).isU32 &&
                   (c.eval σ).isU32 && (d.eval σ).isU32) = true := by
      rw [ha, hb, hc, hd]; rfl
    refine ⟨cs, ?_, ?_⟩
    · change execU32AssertW cs = _
      unfold execU32AssertW
      rw [hstack]; simp [hguard]
    · exact ⟨by simp only [hstk, hstack, List.map_cons], hmem, hframes, hadv⟩

-- Guarded stack ops (precondition extraction + stack transformation)

-- 1. Boolean-guarded (isBool preconditions)

theorem execInstruction_sound_or
    (ss : State) (cs : MidenState)
    (σ : Assignment) (rest : List Felt)
    (ss' : State) (preconds : List Precondition)
    (hmodels : ss.models cs σ rest)
    (hexec : execInstruction ss .or = some (ss', preconds))
    (hpreconds : ∀ p ∈ preconds, p.holds σ) :
    ∃ cs', MidenLean.execInstruction cs .or = some cs' ∧ ss'.models cs' σ rest := by
  obtain ⟨hstack, hmem, hframes, hadv⟩ := hmodels
  simp only [execInstruction] at hexec
  match hstk : ss.stack with
  | [] | [_] => simp [hstk] at hexec
  | b :: a :: tail =>
    simp only [hstk] at hexec
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hexec)
    rw [hstk, List.map_cons, List.map_cons] at hstack
    have ha : (a.eval σ).isBool = true :=
      isBool_guard _ (hpreconds (.isBool a) (by simp))
    have hb : (b.eval σ).isBool = true :=
      isBool_guard _ (hpreconds (.isBool b) (by simp))
    have hguard : ((a.eval σ).isBool && (b.eval σ).isBool) = true := by rw [ha, hb]; rfl
    refine ⟨cs.withStack ((a.eval σ + b.eval σ - a.eval σ * b.eval σ) :: tail.map (Expr.eval σ) ++ rest), ?_, ?_⟩
    · change execOr cs = _
      unfold execOr
      rw [hstack]; simp [hguard, MidenState.withStack]
    · exact ⟨by simp only [MidenState.withStack, List.map_cons, Expr.eval], hmem, hframes, hadv⟩

theorem execInstruction_sound_xor
    (ss : State) (cs : MidenState)
    (σ : Assignment) (rest : List Felt)
    (ss' : State) (preconds : List Precondition)
    (hmodels : ss.models cs σ rest)
    (hexec : execInstruction ss .xor = some (ss', preconds))
    (hpreconds : ∀ p ∈ preconds, p.holds σ) :
    ∃ cs', MidenLean.execInstruction cs .xor = some cs' ∧ ss'.models cs' σ rest := by
  obtain ⟨hstack, hmem, hframes, hadv⟩ := hmodels
  simp only [execInstruction] at hexec
  match hstk : ss.stack with
  | [] | [_] => simp [hstk] at hexec
  | b :: a :: tail =>
    simp only [hstk] at hexec
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hexec)
    rw [hstk, List.map_cons, List.map_cons] at hstack
    have ha : (a.eval σ).isBool = true :=
      isBool_guard _ (hpreconds (.isBool a) (by simp))
    have hb : (b.eval σ).isBool = true :=
      isBool_guard _ (hpreconds (.isBool b) (by simp))
    have hguard : ((a.eval σ).isBool && (b.eval σ).isBool) = true := by rw [ha, hb]; rfl
    refine ⟨cs.withStack ((a.eval σ + b.eval σ - 2 * a.eval σ * b.eval σ) :: tail.map (Expr.eval σ) ++ rest), ?_, ?_⟩
    · change execXor cs = _
      unfold execXor
      rw [hstack]; simp [hguard, MidenState.withStack]
    · exact ⟨by simp only [MidenState.withStack, List.map_cons, Expr.eval], hmem, hframes, hadv⟩

theorem execInstruction_sound_not
    (ss : State) (cs : MidenState)
    (σ : Assignment) (rest : List Felt)
    (ss' : State) (preconds : List Precondition)
    (hmodels : ss.models cs σ rest)
    (hexec : execInstruction ss .not = some (ss', preconds))
    (hpreconds : ∀ p ∈ preconds, p.holds σ) :
    ∃ cs', MidenLean.execInstruction cs .not = some cs' ∧ ss'.models cs' σ rest := by
  obtain ⟨hstack, hmem, hframes, hadv⟩ := hmodels
  simp only [execInstruction] at hexec
  match hstk : ss.stack with
  | [] => simp [hstk] at hexec
  | a :: tail =>
    simp only [hstk] at hexec
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hexec)
    rw [hstk, List.map_cons] at hstack
    have ha : (a.eval σ).isBool = true :=
      isBool_guard _ (hpreconds (.isBool a) (by simp))
    refine ⟨cs.withStack ((1 - a.eval σ) :: tail.map (Expr.eval σ) ++ rest), ?_, ?_⟩
    · change execNot cs = _
      unfold execNot
      rw [hstack]; simp [ha, MidenState.withStack]
    · exact ⟨by simp only [MidenState.withStack, List.map_cons, Expr.eval], hmem, hframes, hadv⟩

-- 2. Nonzero-guarded (nonzero precondition)

theorem execInstruction_sound_div
    (ss : State) (cs : MidenState)
    (σ : Assignment) (rest : List Felt)
    (ss' : State) (preconds : List Precondition)
    (hmodels : ss.models cs σ rest)
    (hexec : execInstruction ss .div = some (ss', preconds))
    (hpreconds : ∀ p ∈ preconds, p.holds σ) :
    ∃ cs', MidenLean.execInstruction cs .div = some cs' ∧ ss'.models cs' σ rest := by
  obtain ⟨hstack, hmem, hframes, hadv⟩ := hmodels
  simp only [execInstruction] at hexec
  match hstk : ss.stack with
  | [] | [_] => simp [hstk] at hexec
  | b :: a :: tail =>
    simp only [hstk] at hexec
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hexec)
    rw [hstk, List.map_cons, List.map_cons] at hstack
    have hnz : (b.eval σ == (0 : Felt)) = false :=
      hpreconds (.nonzero b) (by simp)
    refine ⟨cs.withStack ((a.eval σ * (b.eval σ)⁻¹) :: tail.map (Expr.eval σ) ++ rest), ?_, ?_⟩
    · change execDiv cs = _
      unfold execDiv
      rw [hstack]; simp [hnz, MidenState.withStack]
    · exact ⟨by simp only [MidenState.withStack, List.map_cons, Expr.eval], hmem, hframes, hadv⟩

theorem execInstruction_sound_divImm
    (v : Felt) (ss : State) (cs : MidenState)
    (σ : Assignment) (rest : List Felt)
    (ss' : State) (preconds : List Precondition)
    (hmodels : ss.models cs σ rest)
    (hexec : execInstruction ss (.divImm v) = some (ss', preconds))
    (hpreconds : ∀ p ∈ preconds, p.holds σ) :
    ∃ cs', MidenLean.execInstruction cs (.divImm v) = some cs' ∧ ss'.models cs' σ rest := by
  obtain ⟨hstack, hmem, hframes, hadv⟩ := hmodels
  simp only [execInstruction] at hexec
  match hstk : ss.stack with
  | [] => simp [hstk] at hexec
  | a :: tail =>
    simp only [hstk] at hexec
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hexec)
    rw [hstk, List.map_cons] at hstack
    have hnz : (Expr.eval σ (.lit v) == (0 : Felt)) = false :=
      hpreconds (.nonzero (.lit v)) (by simp)
    simp only [Expr.eval] at hnz
    refine ⟨cs.withStack ((a.eval σ * v⁻¹) :: tail.map (Expr.eval σ) ++ rest), ?_, ?_⟩
    · change execDivImm v cs = _
      unfold execDivImm
      rw [hstack]; simp [hnz, MidenState.withStack]
    · exact ⟨by simp only [MidenState.withStack, List.map_cons, Expr.eval], hmem, hframes, hadv⟩

theorem execInstruction_sound_inv
    (ss : State) (cs : MidenState)
    (σ : Assignment) (rest : List Felt)
    (ss' : State) (preconds : List Precondition)
    (hmodels : ss.models cs σ rest)
    (hexec : execInstruction ss .inv = some (ss', preconds))
    (hpreconds : ∀ p ∈ preconds, p.holds σ) :
    ∃ cs', MidenLean.execInstruction cs .inv = some cs' ∧ ss'.models cs' σ rest := by
  obtain ⟨hstack, hmem, hframes, hadv⟩ := hmodels
  simp only [execInstruction] at hexec
  match hstk : ss.stack with
  | [] => simp [hstk] at hexec
  | a :: tail =>
    simp only [hstk] at hexec
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hexec)
    rw [hstk, List.map_cons] at hstack
    have hnz : (a.eval σ == (0 : Felt)) = false :=
      hpreconds (.nonzero a) (by simp)
    refine ⟨cs.withStack ((a.eval σ)⁻¹ :: tail.map (Expr.eval σ) ++ rest), ?_, ?_⟩
    · change execInv cs = _
      unfold execInv
      rw [hstack]; simp [hnz, MidenState.withStack]
    · exact ⟨by simp only [MidenState.withStack, List.map_cons, Expr.eval], hmem, hframes, hadv⟩

-- 3. Value-bounded (valLeq precondition)

theorem execInstruction_sound_pow2
    (ss : State) (cs : MidenState)
    (σ : Assignment) (rest : List Felt)
    (ss' : State) (preconds : List Precondition)
    (hmodels : ss.models cs σ rest)
    (hexec : execInstruction ss .pow2 = some (ss', preconds))
    (hpreconds : ∀ p ∈ preconds, p.holds σ) :
    ∃ cs', MidenLean.execInstruction cs .pow2 = some cs' ∧ ss'.models cs' σ rest := by
  obtain ⟨hstack, hmem, hframes, hadv⟩ := hmodels
  simp only [execInstruction] at hexec
  match hstk : ss.stack with
  | [] => simp [hstk] at hexec
  | a :: tail =>
    simp only [hstk] at hexec
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hexec)
    rw [hstk, List.map_cons] at hstack
    have hle : (a.eval σ).val ≤ 63 :=
      hpreconds (.valLeq a 63) (by simp)
    have hguard : ¬((a.eval σ).val > 63) := valLeq_to_not_gt _ hle
    refine ⟨cs.withStack (Felt.ofNat (2 ^ (a.eval σ).val) :: tail.map (Expr.eval σ) ++ rest), ?_, ?_⟩
    · change execPow2 cs = _
      unfold execPow2
      rw [hstack]; simp [hguard, MidenState.withStack]
    · exact ⟨by simp only [MidenState.withStack, List.map_cons, Expr.eval], hmem, hframes, hadv⟩

-- 4. U32 binary arithmetic

theorem execInstruction_sound_u32OverflowAdd
    (ss : State) (cs : MidenState)
    (σ : Assignment) (rest : List Felt)
    (ss' : State) (preconds : List Precondition)
    (hmodels : ss.models cs σ rest)
    (hexec : execInstruction ss .u32OverflowAdd = some (ss', preconds))
    (hpreconds : ∀ p ∈ preconds, p.holds σ) :
    ∃ cs', MidenLean.execInstruction cs .u32OverflowAdd = some cs' ∧ ss'.models cs' σ rest := by
  obtain ⟨hstack, hmem, hframes, hadv⟩ := hmodels
  simp only [execInstruction] at hexec
  match hstk : ss.stack with
  | [] | [_] => simp [hstk] at hexec
  | b :: a :: tail =>
    simp only [hstk] at hexec
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hexec)
    rw [hstk, List.map_cons, List.map_cons, List.cons_append, List.cons_append] at hstack
    have ha : (a.eval σ).isU32 = true :=
      hpreconds (.isU32 a) (by simp)
    have hb : (b.eval σ).isU32 = true :=
      hpreconds (.isU32 b) (by simp)
    refine ⟨cs.withStack (Felt.ofNat (((a.eval σ).val + (b.eval σ).val) / u32Max) ::
                          Felt.ofNat (((a.eval σ).val + (b.eval σ).val) % u32Max) ::
                          tail.map (Expr.eval σ) ++ rest), ?_, ?_⟩
    · change execU32OverflowAdd cs = _
      unfold execU32OverflowAdd
      rw [hstack]; simp [ha, hb, u32WideAdd, MidenState.withStack]
    · exact ⟨by simp only [MidenState.withStack, List.map_cons, Expr.eval,
          List.cons_append], hmem, hframes, hadv⟩

theorem execInstruction_sound_u32WrappingAdd
    (ss : State) (cs : MidenState)
    (σ : Assignment) (rest : List Felt)
    (ss' : State) (preconds : List Precondition)
    (hmodels : ss.models cs σ rest)
    (hexec : execInstruction ss .u32WrappingAdd = some (ss', preconds))
    (hpreconds : ∀ p ∈ preconds, p.holds σ) :
    ∃ cs', MidenLean.execInstruction cs .u32WrappingAdd = some cs' ∧ ss'.models cs' σ rest := by
  obtain ⟨hstack, hmem, hframes, hadv⟩ := hmodels
  simp only [execInstruction] at hexec
  match hstk : ss.stack with
  | [] | [_] => simp [hstk] at hexec
  | b :: a :: tail =>
    simp only [hstk] at hexec
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hexec)
    rw [hstk, List.map_cons, List.map_cons, List.cons_append, List.cons_append] at hstack
    have ha : (a.eval σ).isU32 = true :=
      hpreconds (.isU32 a) (by simp)
    have hb : (b.eval σ).isU32 = true :=
      hpreconds (.isU32 b) (by simp)
    refine ⟨cs.withStack (Felt.ofNat (u32WAdd (a.eval σ).val (b.eval σ).val) ::
                          tail.map (Expr.eval σ) ++ rest), ?_, ?_⟩
    · change execU32WrappingAdd cs = _
      unfold execU32WrappingAdd
      rw [hstack]; simp [ha, hb, MidenState.withStack]
    · exact ⟨by simp only [MidenState.withStack, List.map_cons, Expr.eval,
          u32WAdd, u32Max, List.cons_append], hmem, hframes, hadv⟩

theorem execInstruction_sound_u32OverflowAdd3
    (ss : State) (cs : MidenState)
    (σ : Assignment) (rest : List Felt)
    (ss' : State) (preconds : List Precondition)
    (hmodels : ss.models cs σ rest)
    (hexec : execInstruction ss .u32OverflowAdd3 = some (ss', preconds))
    (hpreconds : ∀ p ∈ preconds, p.holds σ) :
    ∃ cs', MidenLean.execInstruction cs .u32OverflowAdd3 = some cs' ∧ ss'.models cs' σ rest := by
  obtain ⟨hstack, hmem, hframes, hadv⟩ := hmodels
  simp only [execInstruction] at hexec
  match hstk : ss.stack with
  | [] | [_] | [_, _] => simp [hstk] at hexec
  | c :: b :: a :: tail =>
    simp only [hstk] at hexec
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hexec)
    rw [hstk, List.map_cons, List.map_cons, List.map_cons] at hstack
    have ha : (a.eval σ).isU32 = true :=
      hpreconds (.isU32 a) (by simp)
    have hb : (b.eval σ).isU32 = true :=
      hpreconds (.isU32 b) (by simp)
    have hc : (c.eval σ).isU32 = true :=
      hpreconds (.isU32 c) (by simp)
    refine ⟨cs.withStack (Felt.ofNat (((a.eval σ).val + (b.eval σ).val + (c.eval σ).val) / u32Max) ::
                          Felt.ofNat (((a.eval σ).val + (b.eval σ).val + (c.eval σ).val) % u32Max) ::
                          tail.map (Expr.eval σ) ++ rest), ?_, ?_⟩
    · change execU32OverflowAdd3 cs = _
      unfold execU32OverflowAdd3
      rw [hstack]; simp [ha, hb, hc, u32WideAdd3, MidenState.withStack]
    · exact ⟨by simp only [MidenState.withStack, List.map_cons, Expr.eval,
          List.cons_append], hmem, hframes, hadv⟩

theorem execInstruction_sound_u32WrappingAdd3
    (ss : State) (cs : MidenState)
    (σ : Assignment) (rest : List Felt)
    (ss' : State) (preconds : List Precondition)
    (hmodels : ss.models cs σ rest)
    (hexec : execInstruction ss .u32WrappingAdd3 = some (ss', preconds))
    (hpreconds : ∀ p ∈ preconds, p.holds σ) :
    ∃ cs', MidenLean.execInstruction cs .u32WrappingAdd3 = some cs' ∧ ss'.models cs' σ rest := by
  obtain ⟨hstack, hmem, hframes, hadv⟩ := hmodels
  simp only [execInstruction] at hexec
  match hstk : ss.stack with
  | [] | [_] | [_, _] => simp [hstk] at hexec
  | c :: b :: a :: tail =>
    simp only [hstk] at hexec
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hexec)
    rw [hstk, List.map_cons, List.map_cons, List.map_cons] at hstack
    have ha : (a.eval σ).isU32 = true :=
      hpreconds (.isU32 a) (by simp)
    have hb : (b.eval σ).isU32 = true :=
      hpreconds (.isU32 b) (by simp)
    have hc : (c.eval σ).isU32 = true :=
      hpreconds (.isU32 c) (by simp)
    refine ⟨cs.withStack (Felt.ofNat (((a.eval σ).val + (b.eval σ).val + (c.eval σ).val) % u32Max) ::
                          tail.map (Expr.eval σ) ++ rest), ?_, ?_⟩
    · change execU32WrappingAdd3 cs = _
      unfold execU32WrappingAdd3
      rw [hstack]; simp [ha, hb, hc, MidenState.withStack]
    · exact ⟨by simp only [MidenState.withStack, List.map_cons, Expr.eval,
          u32Max, List.cons_append], hmem, hframes, hadv⟩

theorem execInstruction_sound_u32WrappingSub
    (ss : State) (cs : MidenState)
    (σ : Assignment) (rest : List Felt)
    (ss' : State) (preconds : List Precondition)
    (hmodels : ss.models cs σ rest)
    (hexec : execInstruction ss .u32WrappingSub = some (ss', preconds))
    (hpreconds : ∀ p ∈ preconds, p.holds σ) :
    ∃ cs', MidenLean.execInstruction cs .u32WrappingSub = some cs' ∧ ss'.models cs' σ rest := by
  obtain ⟨hstack, hmem, hframes, hadv⟩ := hmodels
  simp only [execInstruction] at hexec
  match hstk : ss.stack with
  | [] | [_] => simp [hstk] at hexec
  | b :: a :: tail =>
    simp only [hstk] at hexec
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hexec)
    rw [hstk, List.map_cons, List.map_cons, List.cons_append, List.cons_append] at hstack
    have ha : (a.eval σ).isU32 = true :=
      hpreconds (.isU32 a) (by simp)
    have hb : (b.eval σ).isU32 = true :=
      hpreconds (.isU32 b) (by simp)
    refine ⟨cs.withStack (Felt.ofNat (u32OverflowingSub (a.eval σ).val (b.eval σ).val).2 ::
                          tail.map (Expr.eval σ) ++ rest), ?_, ?_⟩
    · change execU32WrappingSub cs = _
      unfold execU32WrappingSub
      rw [hstack]; simp [ha, hb, MidenState.withStack]
    · exact ⟨by simp only [MidenState.withStack, List.map_cons, Expr.eval,
          List.cons_append], hmem, hframes, hadv⟩

theorem execInstruction_sound_u32WidenMul
    (ss : State) (cs : MidenState)
    (σ : Assignment) (rest : List Felt)
    (ss' : State) (preconds : List Precondition)
    (hmodels : ss.models cs σ rest)
    (hexec : execInstruction ss .u32WidenMul = some (ss', preconds))
    (hpreconds : ∀ p ∈ preconds, p.holds σ) :
    ∃ cs', MidenLean.execInstruction cs .u32WidenMul = some cs' ∧ ss'.models cs' σ rest := by
  obtain ⟨hstack, hmem, hframes, hadv⟩ := hmodels
  simp only [execInstruction] at hexec
  match hstk : ss.stack with
  | [] | [_] => simp [hstk] at hexec
  | b :: a :: tail =>
    simp only [hstk] at hexec
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hexec)
    rw [hstk, List.map_cons, List.map_cons, List.cons_append, List.cons_append] at hstack
    have ha : (a.eval σ).isU32 = true :=
      hpreconds (.isU32 a) (by simp)
    have hb : (b.eval σ).isU32 = true :=
      hpreconds (.isU32 b) (by simp)
    refine ⟨cs.withStack (Felt.ofNat (u32WideMul (a.eval σ).val (b.eval σ).val).1 ::
                          Felt.ofNat (u32WideMul (a.eval σ).val (b.eval σ).val).2 ::
                          tail.map (Expr.eval σ) ++ rest), ?_, ?_⟩
    · change execU32WidenMul cs = _
      unfold execU32WidenMul
      rw [hstack]; simp [ha, hb, u32WideMul, MidenState.withStack]
    · exact ⟨by simp only [MidenState.withStack, List.map_cons, Expr.eval,
          List.cons_append], hmem, hframes, hadv⟩

theorem execInstruction_sound_u32WrappingMul
    (ss : State) (cs : MidenState)
    (σ : Assignment) (rest : List Felt)
    (ss' : State) (preconds : List Precondition)
    (hmodels : ss.models cs σ rest)
    (hexec : execInstruction ss .u32WrappingMul = some (ss', preconds))
    (hpreconds : ∀ p ∈ preconds, p.holds σ) :
    ∃ cs', MidenLean.execInstruction cs .u32WrappingMul = some cs' ∧ ss'.models cs' σ rest := by
  obtain ⟨hstack, hmem, hframes, hadv⟩ := hmodels
  simp only [execInstruction] at hexec
  match hstk : ss.stack with
  | [] | [_] => simp [hstk] at hexec
  | b :: a :: tail =>
    simp only [hstk] at hexec
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hexec)
    rw [hstk, List.map_cons, List.map_cons, List.cons_append, List.cons_append] at hstack
    have ha : (a.eval σ).isU32 = true :=
      hpreconds (.isU32 a) (by simp)
    have hb : (b.eval σ).isU32 = true :=
      hpreconds (.isU32 b) (by simp)
    refine ⟨cs.withStack (Felt.ofNat (((a.eval σ).val * (b.eval σ).val) % u32Max) ::
                          tail.map (Expr.eval σ) ++ rest), ?_, ?_⟩
    · change execU32WrappingMul cs = _
      unfold execU32WrappingMul
      rw [hstack]; simp [ha, hb, MidenState.withStack]
    · exact ⟨by simp only [MidenState.withStack, List.map_cons, Expr.eval,
          u32Max, List.cons_append], hmem, hframes, hadv⟩

theorem execInstruction_sound_u32WidenMadd
    (ss : State) (cs : MidenState)
    (σ : Assignment) (rest : List Felt)
    (ss' : State) (preconds : List Precondition)
    (hmodels : ss.models cs σ rest)
    (hexec : execInstruction ss .u32WidenMadd = some (ss', preconds))
    (hpreconds : ∀ p ∈ preconds, p.holds σ) :
    ∃ cs', MidenLean.execInstruction cs .u32WidenMadd = some cs' ∧ ss'.models cs' σ rest := by
  obtain ⟨hstack, hmem, hframes, hadv⟩ := hmodels
  simp only [execInstruction] at hexec
  match hstk : ss.stack with
  | [] | [_] | [_, _] => simp [hstk] at hexec
  | b :: a :: c :: tail =>
    simp only [hstk] at hexec
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hexec)
    rw [hstk, List.map_cons, List.map_cons, List.map_cons] at hstack
    have ha : (a.eval σ).isU32 = true :=
      hpreconds (.isU32 a) (by simp)
    have hb : (b.eval σ).isU32 = true :=
      hpreconds (.isU32 b) (by simp)
    have hc : (c.eval σ).isU32 = true :=
      hpreconds (.isU32 c) (by simp)
    refine ⟨cs.withStack (Felt.ofNat (u32WideMadd (a.eval σ).val (b.eval σ).val (c.eval σ).val).1 ::
                          Felt.ofNat (u32WideMadd (a.eval σ).val (b.eval σ).val (c.eval σ).val).2 ::
                          tail.map (Expr.eval σ) ++ rest), ?_, ?_⟩
    · change execU32WidenMadd cs = _
      unfold execU32WidenMadd
      rw [hstack]; simp [ha, hb, hc, u32WideMadd, MidenState.withStack]
    · exact ⟨by simp only [MidenState.withStack, List.map_cons, Expr.eval,
          List.cons_append], hmem, hframes, hadv⟩

theorem execInstruction_sound_u32WrappingMadd
    (ss : State) (cs : MidenState)
    (σ : Assignment) (rest : List Felt)
    (ss' : State) (preconds : List Precondition)
    (hmodels : ss.models cs σ rest)
    (hexec : execInstruction ss .u32WrappingMadd = some (ss', preconds))
    (hpreconds : ∀ p ∈ preconds, p.holds σ) :
    ∃ cs', MidenLean.execInstruction cs .u32WrappingMadd = some cs' ∧ ss'.models cs' σ rest := by
  obtain ⟨hstack, hmem, hframes, hadv⟩ := hmodels
  simp only [execInstruction] at hexec
  match hstk : ss.stack with
  | [] | [_] | [_, _] => simp [hstk] at hexec
  | b :: a :: c :: tail =>
    simp only [hstk] at hexec
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hexec)
    rw [hstk, List.map_cons, List.map_cons, List.map_cons] at hstack
    have ha : (a.eval σ).isU32 = true :=
      hpreconds (.isU32 a) (by simp)
    have hb : (b.eval σ).isU32 = true :=
      hpreconds (.isU32 b) (by simp)
    have hc : (c.eval σ).isU32 = true :=
      hpreconds (.isU32 c) (by simp)
    refine ⟨cs.withStack (Felt.ofNat (((a.eval σ).val * (b.eval σ).val + (c.eval σ).val) % u32Max) ::
                          tail.map (Expr.eval σ) ++ rest), ?_, ?_⟩
    · change execU32WrappingMadd cs = _
      unfold execU32WrappingMadd
      rw [hstack]; simp [ha, hb, hc, MidenState.withStack]
    · exact ⟨by simp only [MidenState.withStack, List.map_cons, Expr.eval,
          u32Max, List.cons_append], hmem, hframes, hadv⟩

-- 5. U32 division (isU32 + nonzero preconditions)

theorem execInstruction_sound_u32DivMod
    (ss : State) (cs : MidenState)
    (σ : Assignment) (rest : List Felt)
    (ss' : State) (preconds : List Precondition)
    (hmodels : ss.models cs σ rest)
    (hexec : execInstruction ss .u32DivMod = some (ss', preconds))
    (hpreconds : ∀ p ∈ preconds, p.holds σ) :
    ∃ cs', MidenLean.execInstruction cs .u32DivMod = some cs' ∧ ss'.models cs' σ rest := by
  obtain ⟨hstack, hmem, hframes, hadv⟩ := hmodels
  simp only [execInstruction] at hexec
  match hstk : ss.stack with
  | [] | [_] => simp [hstk] at hexec
  | b :: a :: tail =>
    simp only [hstk] at hexec
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hexec)
    rw [hstk, List.map_cons, List.map_cons, List.cons_append, List.cons_append] at hstack
    have ha : (a.eval σ).isU32 = true :=
      hpreconds (.isU32 a) (by simp)
    have hb : (b.eval σ).isU32 = true :=
      hpreconds (.isU32 b) (by simp)
    have hnz : (b.eval σ == (0 : Felt)) = false :=
      hpreconds (.nonzero b) (by simp)
    have hbval : ((b.eval σ).val == 0) = false := felt_nonzero_val_ne_zero hnz
    refine ⟨cs.withStack (Felt.ofNat ((a.eval σ).val % (b.eval σ).val) ::
                          Felt.ofNat ((a.eval σ).val / (b.eval σ).val) ::
                          tail.map (Expr.eval σ) ++ rest), ?_, ?_⟩
    · change execU32DivMod cs = _
      unfold execU32DivMod
      rw [hstack]; simp [ha, hb, hbval, MidenState.withStack]
    · exact ⟨by simp only [MidenState.withStack, List.map_cons, Expr.eval,
          List.cons_append], hmem, hframes, hadv⟩

theorem execInstruction_sound_u32Div
    (ss : State) (cs : MidenState)
    (σ : Assignment) (rest : List Felt)
    (ss' : State) (preconds : List Precondition)
    (hmodels : ss.models cs σ rest)
    (hexec : execInstruction ss .u32Div = some (ss', preconds))
    (hpreconds : ∀ p ∈ preconds, p.holds σ) :
    ∃ cs', MidenLean.execInstruction cs .u32Div = some cs' ∧ ss'.models cs' σ rest := by
  obtain ⟨hstack, hmem, hframes, hadv⟩ := hmodels
  simp only [execInstruction] at hexec
  match hstk : ss.stack with
  | [] | [_] => simp [hstk] at hexec
  | b :: a :: tail =>
    simp only [hstk] at hexec
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hexec)
    rw [hstk, List.map_cons, List.map_cons, List.cons_append, List.cons_append] at hstack
    have ha : (a.eval σ).isU32 = true :=
      hpreconds (.isU32 a) (by simp)
    have hb : (b.eval σ).isU32 = true :=
      hpreconds (.isU32 b) (by simp)
    have hnz : (b.eval σ == (0 : Felt)) = false :=
      hpreconds (.nonzero b) (by simp)
    have hbval : ((b.eval σ).val == 0) = false := felt_nonzero_val_ne_zero hnz
    refine ⟨cs.withStack (Felt.ofNat ((a.eval σ).val / (b.eval σ).val) ::
                          tail.map (Expr.eval σ) ++ rest), ?_, ?_⟩
    · change execU32Div cs = _
      unfold execU32Div
      rw [hstack]; simp [ha, hb, hbval, MidenState.withStack]
    · exact ⟨by simp only [MidenState.withStack, List.map_cons, Expr.eval,
          List.cons_append], hmem, hframes, hadv⟩

theorem execInstruction_sound_u32Mod
    (ss : State) (cs : MidenState)
    (σ : Assignment) (rest : List Felt)
    (ss' : State) (preconds : List Precondition)
    (hmodels : ss.models cs σ rest)
    (hexec : execInstruction ss .u32Mod = some (ss', preconds))
    (hpreconds : ∀ p ∈ preconds, p.holds σ) :
    ∃ cs', MidenLean.execInstruction cs .u32Mod = some cs' ∧ ss'.models cs' σ rest := by
  obtain ⟨hstack, hmem, hframes, hadv⟩ := hmodels
  simp only [execInstruction] at hexec
  match hstk : ss.stack with
  | [] | [_] => simp [hstk] at hexec
  | b :: a :: tail =>
    simp only [hstk] at hexec
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hexec)
    rw [hstk, List.map_cons, List.map_cons, List.cons_append, List.cons_append] at hstack
    have ha : (a.eval σ).isU32 = true :=
      hpreconds (.isU32 a) (by simp)
    have hb : (b.eval σ).isU32 = true :=
      hpreconds (.isU32 b) (by simp)
    have hnz : (b.eval σ == (0 : Felt)) = false :=
      hpreconds (.nonzero b) (by simp)
    have hbval : ((b.eval σ).val == 0) = false := felt_nonzero_val_ne_zero hnz
    refine ⟨cs.withStack (Felt.ofNat ((a.eval σ).val % (b.eval σ).val) ::
                          tail.map (Expr.eval σ) ++ rest), ?_, ?_⟩
    · change execU32Mod cs = _
      unfold execU32Mod
      rw [hstack]; simp [ha, hb, hbval, MidenState.withStack]
    · exact ⟨by simp only [MidenState.withStack, List.map_cons, Expr.eval,
          List.cons_append], hmem, hframes, hadv⟩

-- 6. U32 bitwise

theorem execInstruction_sound_u32And
    (ss : State) (cs : MidenState)
    (σ : Assignment) (rest : List Felt)
    (ss' : State) (preconds : List Precondition)
    (hmodels : ss.models cs σ rest)
    (hexec : execInstruction ss .u32And = some (ss', preconds))
    (hpreconds : ∀ p ∈ preconds, p.holds σ) :
    ∃ cs', MidenLean.execInstruction cs .u32And = some cs' ∧ ss'.models cs' σ rest := by
  obtain ⟨hstack, hmem, hframes, hadv⟩ := hmodels
  simp only [execInstruction] at hexec
  match hstk : ss.stack with
  | [] | [_] => simp [hstk] at hexec
  | b :: a :: tail =>
    simp only [hstk] at hexec
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hexec)
    rw [hstk, List.map_cons, List.map_cons, List.cons_append, List.cons_append] at hstack
    have ha : (a.eval σ).isU32 = true :=
      hpreconds (.isU32 a) (by simp)
    have hb : (b.eval σ).isU32 = true :=
      hpreconds (.isU32 b) (by simp)
    refine ⟨cs.withStack (Felt.ofNat ((a.eval σ).val &&& (b.eval σ).val) ::
                          tail.map (Expr.eval σ) ++ rest), ?_, ?_⟩
    · change execU32And cs = _
      unfold execU32And
      rw [hstack]; simp [ha, hb, MidenState.withStack]
    · exact ⟨by simp only [MidenState.withStack, List.map_cons, Expr.eval,
          List.cons_append]; rfl, hmem, hframes, hadv⟩

theorem execInstruction_sound_u32Or
    (ss : State) (cs : MidenState)
    (σ : Assignment) (rest : List Felt)
    (ss' : State) (preconds : List Precondition)
    (hmodels : ss.models cs σ rest)
    (hexec : execInstruction ss .u32Or = some (ss', preconds))
    (hpreconds : ∀ p ∈ preconds, p.holds σ) :
    ∃ cs', MidenLean.execInstruction cs .u32Or = some cs' ∧ ss'.models cs' σ rest := by
  obtain ⟨hstack, hmem, hframes, hadv⟩ := hmodels
  simp only [execInstruction] at hexec
  match hstk : ss.stack with
  | [] | [_] => simp [hstk] at hexec
  | b :: a :: tail =>
    simp only [hstk] at hexec
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hexec)
    rw [hstk, List.map_cons, List.map_cons, List.cons_append, List.cons_append] at hstack
    have ha : (a.eval σ).isU32 = true :=
      hpreconds (.isU32 a) (by simp)
    have hb : (b.eval σ).isU32 = true :=
      hpreconds (.isU32 b) (by simp)
    refine ⟨cs.withStack (Felt.ofNat ((a.eval σ).val ||| (b.eval σ).val) ::
                          tail.map (Expr.eval σ) ++ rest), ?_, ?_⟩
    · change execU32Or cs = _
      unfold execU32Or
      rw [hstack]; simp [ha, hb, MidenState.withStack]
    · exact ⟨by simp only [MidenState.withStack, List.map_cons, Expr.eval,
          List.cons_append]; rfl, hmem, hframes, hadv⟩

theorem execInstruction_sound_u32Xor
    (ss : State) (cs : MidenState)
    (σ : Assignment) (rest : List Felt)
    (ss' : State) (preconds : List Precondition)
    (hmodels : ss.models cs σ rest)
    (hexec : execInstruction ss .u32Xor = some (ss', preconds))
    (hpreconds : ∀ p ∈ preconds, p.holds σ) :
    ∃ cs', MidenLean.execInstruction cs .u32Xor = some cs' ∧ ss'.models cs' σ rest := by
  obtain ⟨hstack, hmem, hframes, hadv⟩ := hmodels
  simp only [execInstruction] at hexec
  match hstk : ss.stack with
  | [] | [_] => simp [hstk] at hexec
  | b :: a :: tail =>
    simp only [hstk] at hexec
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hexec)
    rw [hstk, List.map_cons, List.map_cons, List.cons_append, List.cons_append] at hstack
    have ha : (a.eval σ).isU32 = true :=
      hpreconds (.isU32 a) (by simp)
    have hb : (b.eval σ).isU32 = true :=
      hpreconds (.isU32 b) (by simp)
    refine ⟨cs.withStack (Felt.ofNat ((a.eval σ).val ^^^ (b.eval σ).val) ::
                          tail.map (Expr.eval σ) ++ rest), ?_, ?_⟩
    · change execU32Xor cs = _
      unfold execU32Xor
      rw [hstack]; simp [ha, hb, MidenState.withStack]
    · exact ⟨by simp only [MidenState.withStack, List.map_cons, Expr.eval,
          List.cons_append]; rfl, hmem, hframes, hadv⟩

-- 7. U32 unary (single isU32 precondition)

theorem execInstruction_sound_u32Not
    (ss : State) (cs : MidenState)
    (σ : Assignment) (rest : List Felt)
    (ss' : State) (preconds : List Precondition)
    (hmodels : ss.models cs σ rest)
    (hexec : execInstruction ss .u32Not = some (ss', preconds))
    (hpreconds : ∀ p ∈ preconds, p.holds σ) :
    ∃ cs', MidenLean.execInstruction cs .u32Not = some cs' ∧ ss'.models cs' σ rest := by
  obtain ⟨hstack, hmem, hframes, hadv⟩ := hmodels
  simp only [execInstruction] at hexec
  match hstk : ss.stack with
  | [] => simp [hstk] at hexec
  | a :: tail =>
    simp only [hstk] at hexec
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hexec)
    rw [hstk, List.map_cons, List.cons_append] at hstack
    have ha : (a.eval σ).isU32 = true :=
      hpreconds (.isU32 a) (by simp)
    refine ⟨cs.withStack (Felt.ofNat (u32Max - 1 - (a.eval σ).val) ::
                          tail.map (Expr.eval σ) ++ rest), ?_, ?_⟩
    · change execU32Not cs = _
      unfold execU32Not
      rw [hstack]; simp [ha, MidenState.withStack]
    · exact ⟨by simp only [MidenState.withStack, List.map_cons, Expr.eval,
          List.cons_append], hmem, hframes, hadv⟩

theorem execInstruction_sound_u32Popcnt
    (ss : State) (cs : MidenState)
    (σ : Assignment) (rest : List Felt)
    (ss' : State) (preconds : List Precondition)
    (hmodels : ss.models cs σ rest)
    (hexec : execInstruction ss .u32Popcnt = some (ss', preconds))
    (hpreconds : ∀ p ∈ preconds, p.holds σ) :
    ∃ cs', MidenLean.execInstruction cs .u32Popcnt = some cs' ∧ ss'.models cs' σ rest := by
  obtain ⟨hstack, hmem, hframes, hadv⟩ := hmodels
  simp only [execInstruction] at hexec
  match hstk : ss.stack with
  | [] => simp [hstk] at hexec
  | a :: tail =>
    simp only [hstk] at hexec
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hexec)
    rw [hstk, List.map_cons, List.cons_append] at hstack
    have ha : (a.eval σ).isU32 = true :=
      hpreconds (.isU32 a) (by simp)
    refine ⟨cs.withStack (Felt.ofNat (u32PopCount (a.eval σ).val) ::
                          tail.map (Expr.eval σ) ++ rest), ?_, ?_⟩
    · change execU32Popcnt cs = _
      unfold execU32Popcnt
      rw [hstack]; simp [ha, MidenState.withStack]
    · exact ⟨by simp only [MidenState.withStack, List.map_cons, Expr.eval,
          List.cons_append], hmem, hframes, hadv⟩

theorem execInstruction_sound_u32Clz
    (ss : State) (cs : MidenState)
    (σ : Assignment) (rest : List Felt)
    (ss' : State) (preconds : List Precondition)
    (hmodels : ss.models cs σ rest)
    (hexec : execInstruction ss .u32Clz = some (ss', preconds))
    (hpreconds : ∀ p ∈ preconds, p.holds σ) :
    ∃ cs', MidenLean.execInstruction cs .u32Clz = some cs' ∧ ss'.models cs' σ rest := by
  obtain ⟨hstack, hmem, hframes, hadv⟩ := hmodels
  simp only [execInstruction] at hexec
  match hstk : ss.stack with
  | [] => simp [hstk] at hexec
  | a :: tail =>
    simp only [hstk] at hexec
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hexec)
    rw [hstk, List.map_cons, List.cons_append] at hstack
    have ha : (a.eval σ).isU32 = true :=
      hpreconds (.isU32 a) (by simp)
    refine ⟨cs.withStack (Felt.ofNat (u32CountLeadingZeros (a.eval σ).val) ::
                          tail.map (Expr.eval σ) ++ rest), ?_, ?_⟩
    · change execU32Clz cs = _
      unfold execU32Clz
      rw [hstack]; simp [ha, MidenState.withStack]
    · exact ⟨by simp only [MidenState.withStack, List.map_cons, Expr.eval,
          List.cons_append], hmem, hframes, hadv⟩

theorem execInstruction_sound_u32Ctz
    (ss : State) (cs : MidenState)
    (σ : Assignment) (rest : List Felt)
    (ss' : State) (preconds : List Precondition)
    (hmodels : ss.models cs σ rest)
    (hexec : execInstruction ss .u32Ctz = some (ss', preconds))
    (hpreconds : ∀ p ∈ preconds, p.holds σ) :
    ∃ cs', MidenLean.execInstruction cs .u32Ctz = some cs' ∧ ss'.models cs' σ rest := by
  obtain ⟨hstack, hmem, hframes, hadv⟩ := hmodels
  simp only [execInstruction] at hexec
  match hstk : ss.stack with
  | [] => simp [hstk] at hexec
  | a :: tail =>
    simp only [hstk] at hexec
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hexec)
    rw [hstk, List.map_cons, List.cons_append] at hstack
    have ha : (a.eval σ).isU32 = true :=
      hpreconds (.isU32 a) (by simp)
    refine ⟨cs.withStack (Felt.ofNat (u32CountTrailingZeros (a.eval σ).val) ::
                          tail.map (Expr.eval σ) ++ rest), ?_, ?_⟩
    · change execU32Ctz cs = _
      unfold execU32Ctz
      rw [hstack]; simp [ha, MidenState.withStack]
    · exact ⟨by simp only [MidenState.withStack, List.map_cons, Expr.eval,
          List.cons_append], hmem, hframes, hadv⟩

theorem execInstruction_sound_u32Clo
    (ss : State) (cs : MidenState)
    (σ : Assignment) (rest : List Felt)
    (ss' : State) (preconds : List Precondition)
    (hmodels : ss.models cs σ rest)
    (hexec : execInstruction ss .u32Clo = some (ss', preconds))
    (hpreconds : ∀ p ∈ preconds, p.holds σ) :
    ∃ cs', MidenLean.execInstruction cs .u32Clo = some cs' ∧ ss'.models cs' σ rest := by
  obtain ⟨hstack, hmem, hframes, hadv⟩ := hmodels
  simp only [execInstruction] at hexec
  match hstk : ss.stack with
  | [] => simp [hstk] at hexec
  | a :: tail =>
    simp only [hstk] at hexec
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hexec)
    rw [hstk, List.map_cons, List.cons_append] at hstack
    have ha : (a.eval σ).isU32 = true :=
      hpreconds (.isU32 a) (by simp)
    refine ⟨cs.withStack (Felt.ofNat (u32CountLeadingOnes (a.eval σ).val) ::
                          tail.map (Expr.eval σ) ++ rest), ?_, ?_⟩
    · change execU32Clo cs = _
      unfold execU32Clo
      rw [hstack]; simp [ha, MidenState.withStack]
    · exact ⟨by simp only [MidenState.withStack, List.map_cons, Expr.eval,
          List.cons_append], hmem, hframes, hadv⟩

theorem execInstruction_sound_u32Cto
    (ss : State) (cs : MidenState)
    (σ : Assignment) (rest : List Felt)
    (ss' : State) (preconds : List Precondition)
    (hmodels : ss.models cs σ rest)
    (hexec : execInstruction ss .u32Cto = some (ss', preconds))
    (hpreconds : ∀ p ∈ preconds, p.holds σ) :
    ∃ cs', MidenLean.execInstruction cs .u32Cto = some cs' ∧ ss'.models cs' σ rest := by
  obtain ⟨hstack, hmem, hframes, hadv⟩ := hmodels
  simp only [execInstruction] at hexec
  match hstk : ss.stack with
  | [] => simp [hstk] at hexec
  | a :: tail =>
    simp only [hstk] at hexec
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hexec)
    rw [hstk, List.map_cons, List.cons_append] at hstack
    have ha : (a.eval σ).isU32 = true :=
      hpreconds (.isU32 a) (by simp)
    refine ⟨cs.withStack (Felt.ofNat (u32CountTrailingOnes (a.eval σ).val) ::
                          tail.map (Expr.eval σ) ++ rest), ?_, ?_⟩
    · change execU32Cto cs = _
      unfold execU32Cto
      rw [hstack]; simp [ha, MidenState.withStack]
    · exact ⟨by simp only [MidenState.withStack, List.map_cons, Expr.eval,
          List.cons_append], hmem, hframes, hadv⟩

-- 8. U32 shift/rotate (isU32 + valLeq preconditions)

theorem execInstruction_sound_u32Shl
    (ss : State) (cs : MidenState)
    (σ : Assignment) (rest : List Felt)
    (ss' : State) (preconds : List Precondition)
    (hmodels : ss.models cs σ rest)
    (hexec : execInstruction ss .u32Shl = some (ss', preconds))
    (hpreconds : ∀ p ∈ preconds, p.holds σ) :
    ∃ cs', MidenLean.execInstruction cs .u32Shl = some cs' ∧ ss'.models cs' σ rest := by
  obtain ⟨hstack, hmem, hframes, hadv⟩ := hmodels
  simp only [execInstruction] at hexec
  match hstk : ss.stack with
  | [] | [_] => simp [hstk] at hexec
  | b :: a :: tail =>
    simp only [hstk] at hexec
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hexec)
    rw [hstk, List.map_cons, List.map_cons, List.cons_append, List.cons_append] at hstack
    have ha : (a.eval σ).isU32 = true :=
      hpreconds (.isU32 a) (by simp)
    have hb : (b.eval σ).isU32 = true :=
      hpreconds (.isU32 b) (by simp)
    have hbleq : (b.eval σ).val ≤ 31 :=
      hpreconds (.valLeq b 31) (by simp)
    have hbguard : ¬((b.eval σ).val > 31) := by omega
    refine ⟨cs.withStack (Felt.ofNat (((a.eval σ).val * 2 ^ (b.eval σ).val) % u32Max) ::
                          tail.map (Expr.eval σ) ++ rest), ?_, ?_⟩
    · change execU32Shl cs = _
      unfold execU32Shl
      rw [hstack]; simp [ha, hb, hbguard, MidenState.withStack]
    · exact ⟨by simp only [MidenState.withStack, List.map_cons, Expr.eval,
          List.cons_append], hmem, hframes, hadv⟩

theorem execInstruction_sound_u32Shr
    (ss : State) (cs : MidenState)
    (σ : Assignment) (rest : List Felt)
    (ss' : State) (preconds : List Precondition)
    (hmodels : ss.models cs σ rest)
    (hexec : execInstruction ss .u32Shr = some (ss', preconds))
    (hpreconds : ∀ p ∈ preconds, p.holds σ) :
    ∃ cs', MidenLean.execInstruction cs .u32Shr = some cs' ∧ ss'.models cs' σ rest := by
  obtain ⟨hstack, hmem, hframes, hadv⟩ := hmodels
  simp only [execInstruction] at hexec
  match hstk : ss.stack with
  | [] | [_] => simp [hstk] at hexec
  | b :: a :: tail =>
    simp only [hstk] at hexec
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hexec)
    rw [hstk, List.map_cons, List.map_cons, List.cons_append, List.cons_append] at hstack
    have ha : (a.eval σ).isU32 = true :=
      hpreconds (.isU32 a) (by simp)
    have hb : (b.eval σ).isU32 = true :=
      hpreconds (.isU32 b) (by simp)
    have hbleq : (b.eval σ).val ≤ 31 :=
      hpreconds (.valLeq b 31) (by simp)
    have hbguard : ¬((b.eval σ).val > 31) := by omega
    refine ⟨cs.withStack (Felt.ofNat ((a.eval σ).val / 2 ^ (b.eval σ).val) ::
                          tail.map (Expr.eval σ) ++ rest), ?_, ?_⟩
    · change execU32Shr cs = _
      unfold execU32Shr
      rw [hstack]; simp [ha, hb, hbguard, MidenState.withStack]
    · exact ⟨by simp only [MidenState.withStack, List.map_cons, Expr.eval,
          List.cons_append], hmem, hframes, hadv⟩

theorem execInstruction_sound_u32Rotl
    (ss : State) (cs : MidenState)
    (σ : Assignment) (rest : List Felt)
    (ss' : State) (preconds : List Precondition)
    (hmodels : ss.models cs σ rest)
    (hexec : execInstruction ss .u32Rotl = some (ss', preconds))
    (hpreconds : ∀ p ∈ preconds, p.holds σ) :
    ∃ cs', MidenLean.execInstruction cs .u32Rotl = some cs' ∧ ss'.models cs' σ rest := by
  obtain ⟨hstack, hmem, hframes, hadv⟩ := hmodels
  simp only [execInstruction] at hexec
  match hstk : ss.stack with
  | [] | [_] => simp [hstk] at hexec
  | b :: a :: tail =>
    simp only [hstk] at hexec
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hexec)
    rw [hstk, List.map_cons, List.map_cons, List.cons_append, List.cons_append] at hstack
    have ha : (a.eval σ).isU32 = true :=
      hpreconds (.isU32 a) (by simp)
    have hb : (b.eval σ).isU32 = true :=
      hpreconds (.isU32 b) (by simp)
    have hbleq : (b.eval σ).val ≤ 31 :=
      hpreconds (.valLeq b 31) (by simp)
    have hbguard : ¬((b.eval σ).val > 31) := by omega
    refine ⟨cs.withStack (Felt.ofNat (u32RotateLeft (a.eval σ).val (b.eval σ).val) ::
                          tail.map (Expr.eval σ) ++ rest), ?_, ?_⟩
    · change execU32Rotl cs = _
      unfold execU32Rotl
      rw [hstack]; simp [ha, hb, hbguard, MidenState.withStack]
    · exact ⟨by simp only [MidenState.withStack, List.map_cons, Expr.eval,
          List.cons_append], hmem, hframes, hadv⟩

theorem execInstruction_sound_u32Rotr
    (ss : State) (cs : MidenState)
    (σ : Assignment) (rest : List Felt)
    (ss' : State) (preconds : List Precondition)
    (hmodels : ss.models cs σ rest)
    (hexec : execInstruction ss .u32Rotr = some (ss', preconds))
    (hpreconds : ∀ p ∈ preconds, p.holds σ) :
    ∃ cs', MidenLean.execInstruction cs .u32Rotr = some cs' ∧ ss'.models cs' σ rest := by
  obtain ⟨hstack, hmem, hframes, hadv⟩ := hmodels
  simp only [execInstruction] at hexec
  match hstk : ss.stack with
  | [] | [_] => simp [hstk] at hexec
  | b :: a :: tail =>
    simp only [hstk] at hexec
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hexec)
    rw [hstk, List.map_cons, List.map_cons, List.cons_append, List.cons_append] at hstack
    have ha : (a.eval σ).isU32 = true :=
      hpreconds (.isU32 a) (by simp)
    have hb : (b.eval σ).isU32 = true :=
      hpreconds (.isU32 b) (by simp)
    have hbleq : (b.eval σ).val ≤ 31 :=
      hpreconds (.valLeq b 31) (by simp)
    have hbguard : ¬((b.eval σ).val > 31) := by omega
    refine ⟨cs.withStack (Felt.ofNat (u32RotateRight (a.eval σ).val (b.eval σ).val) ::
                          tail.map (Expr.eval σ) ++ rest), ?_, ?_⟩
    · change execU32Rotr cs = _
      unfold execU32Rotr
      rw [hstack]; simp [ha, hb, hbguard, MidenState.withStack]
    · exact ⟨by simp only [MidenState.withStack, List.map_cons, Expr.eval,
          List.cons_append], hmem, hframes, hadv⟩

-- 9. U32 shift/rotate Imm (isU32 + static bound)

theorem execInstruction_sound_u32ShlImm
    (n : Nat) (ss : State) (cs : MidenState)
    (σ : Assignment) (rest : List Felt)
    (ss' : State) (preconds : List Precondition)
    (hmodels : ss.models cs σ rest)
    (hexec : execInstruction ss (.u32ShlImm n) = some (ss', preconds))
    (hpreconds : ∀ p ∈ preconds, p.holds σ) :
    ∃ cs', MidenLean.execInstruction cs (.u32ShlImm n) = some cs' ∧ ss'.models cs' σ rest := by
  obtain ⟨hstack, hmem, hframes, hadv⟩ := hmodels
  simp only [execInstruction] at hexec
  by_cases hn : n ≤ 31
  · simp only [hn, ite_true, decide_true] at hexec
    match hstk : ss.stack with
    | [] => simp [hstk] at hexec
    | a :: tail =>
      simp only [hstk] at hexec
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hexec)
      rw [hstk, List.map_cons, List.cons_append] at hstack
      have ha : (a.eval σ).isU32 = true :=
        hpreconds (.isU32 a) (by simp)
      have hnguard : ¬(n > 31) := by omega
      have hnval : (Felt.ofNat n).val = n := feltOfNat_val_small n hn
      refine ⟨cs.withStack (Felt.ofNat (((a.eval σ).val * 2 ^ n) % u32Max) ::
                            tail.map (Expr.eval σ) ++ rest), ?_, ?_⟩
      · change execU32ShlImm n cs = _
        unfold execU32ShlImm
        rw [hstack]; simp [ha, hnguard, MidenState.withStack]
      · exact ⟨by simp only [MidenState.withStack, List.map_cons, Expr.eval,
            List.cons_append, hnval], hmem, hframes, hadv⟩
  · simp [hn] at hexec

theorem execInstruction_sound_u32ShrImm
    (n : Nat) (ss : State) (cs : MidenState)
    (σ : Assignment) (rest : List Felt)
    (ss' : State) (preconds : List Precondition)
    (hmodels : ss.models cs σ rest)
    (hexec : execInstruction ss (.u32ShrImm n) = some (ss', preconds))
    (hpreconds : ∀ p ∈ preconds, p.holds σ) :
    ∃ cs', MidenLean.execInstruction cs (.u32ShrImm n) = some cs' ∧ ss'.models cs' σ rest := by
  obtain ⟨hstack, hmem, hframes, hadv⟩ := hmodels
  simp only [execInstruction] at hexec
  by_cases hn : n ≤ 31
  · simp only [hn, ite_true, decide_true] at hexec
    match hstk : ss.stack with
    | [] => simp [hstk] at hexec
    | a :: tail =>
      simp only [hstk] at hexec
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hexec)
      rw [hstk, List.map_cons, List.cons_append] at hstack
      have ha : (a.eval σ).isU32 = true :=
        hpreconds (.isU32 a) (by simp)
      have hnguard : ¬(n > 31) := by omega
      have hnval : (Felt.ofNat n).val = n := feltOfNat_val_small n hn
      refine ⟨cs.withStack (Felt.ofNat ((a.eval σ).val / 2 ^ n) ::
                            tail.map (Expr.eval σ) ++ rest), ?_, ?_⟩
      · change execU32ShrImm n cs = _
        unfold execU32ShrImm
        rw [hstack]; simp [ha, hnguard, MidenState.withStack]
      · exact ⟨by simp only [MidenState.withStack, List.map_cons, Expr.eval,
            List.cons_append, hnval], hmem, hframes, hadv⟩
  · simp [hn] at hexec

theorem execInstruction_sound_u32RotlImm
    (n : Nat) (ss : State) (cs : MidenState)
    (σ : Assignment) (rest : List Felt)
    (ss' : State) (preconds : List Precondition)
    (hmodels : ss.models cs σ rest)
    (hexec : execInstruction ss (.u32RotlImm n) = some (ss', preconds))
    (hpreconds : ∀ p ∈ preconds, p.holds σ) :
    ∃ cs', MidenLean.execInstruction cs (.u32RotlImm n) = some cs' ∧ ss'.models cs' σ rest := by
  obtain ⟨hstack, hmem, hframes, hadv⟩ := hmodels
  simp only [execInstruction] at hexec
  by_cases hn : n ≤ 31
  · simp only [hn, ite_true, decide_true] at hexec
    match hstk : ss.stack with
    | [] => simp [hstk] at hexec
    | a :: tail =>
      simp only [hstk] at hexec
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hexec)
      rw [hstk, List.map_cons, List.cons_append] at hstack
      have ha : (a.eval σ).isU32 = true :=
        hpreconds (.isU32 a) (by simp)
      have hnguard : ¬(n > 31) := by omega
      have hnval : (Felt.ofNat n).val = n := feltOfNat_val_small n hn
      refine ⟨cs.withStack (Felt.ofNat (u32RotateLeft (a.eval σ).val n) ::
                            tail.map (Expr.eval σ) ++ rest), ?_, ?_⟩
      · change execU32RotlImm n cs = _
        unfold execU32RotlImm
        rw [hstack]; simp [ha, hnguard, MidenState.withStack]
      · exact ⟨by simp only [MidenState.withStack, List.map_cons, Expr.eval,
            List.cons_append, hnval], hmem, hframes, hadv⟩
  · simp [hn] at hexec

theorem execInstruction_sound_u32RotrImm
    (n : Nat) (ss : State) (cs : MidenState)
    (σ : Assignment) (rest : List Felt)
    (ss' : State) (preconds : List Precondition)
    (hmodels : ss.models cs σ rest)
    (hexec : execInstruction ss (.u32RotrImm n) = some (ss', preconds))
    (hpreconds : ∀ p ∈ preconds, p.holds σ) :
    ∃ cs', MidenLean.execInstruction cs (.u32RotrImm n) = some cs' ∧ ss'.models cs' σ rest := by
  obtain ⟨hstack, hmem, hframes, hadv⟩ := hmodels
  simp only [execInstruction] at hexec
  by_cases hn : n ≤ 31
  · simp only [hn, ite_true, decide_true] at hexec
    match hstk : ss.stack with
    | [] => simp [hstk] at hexec
    | a :: tail =>
      simp only [hstk] at hexec
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hexec)
      rw [hstk, List.map_cons, List.cons_append] at hstack
      have ha : (a.eval σ).isU32 = true :=
        hpreconds (.isU32 a) (by simp)
      have hnguard : ¬(n > 31) := by omega
      have hnval : (Felt.ofNat n).val = n := feltOfNat_val_small n hn
      refine ⟨cs.withStack (Felt.ofNat (u32RotateRight (a.eval σ).val n) ::
                            tail.map (Expr.eval σ) ++ rest), ?_, ?_⟩
      · change execU32RotrImm n cs = _
        unfold execU32RotrImm
        rw [hstack]; simp [ha, hnguard, MidenState.withStack]
      · exact ⟨by simp only [MidenState.withStack, List.map_cons, Expr.eval,
            List.cons_append, hnval], hmem, hframes, hadv⟩
  · simp [hn] at hexec

-- 10. U32 comparison

theorem execInstruction_sound_u32Lt
    (ss : State) (cs : MidenState)
    (σ : Assignment) (rest : List Felt)
    (ss' : State) (preconds : List Precondition)
    (hmodels : ss.models cs σ rest)
    (hexec : execInstruction ss .u32Lt = some (ss', preconds))
    (hpreconds : ∀ p ∈ preconds, p.holds σ) :
    ∃ cs', MidenLean.execInstruction cs .u32Lt = some cs' ∧ ss'.models cs' σ rest := by
  obtain ⟨hstack, hmem, hframes, hadv⟩ := hmodels
  simp only [execInstruction] at hexec
  match hstk : ss.stack with
  | [] | [_] => simp [hstk] at hexec
  | b :: a :: tail =>
    simp only [hstk] at hexec
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hexec)
    rw [hstk, List.map_cons, List.map_cons, List.cons_append, List.cons_append] at hstack
    have ha : (a.eval σ).isU32 = true :=
      hpreconds (.isU32 a) (by simp)
    have hb : (b.eval σ).isU32 = true :=
      hpreconds (.isU32 b) (by simp)
    refine ⟨cs.withStack ((if (a.eval σ).val < (b.eval σ).val then (1 : Felt) else 0) ::
                          tail.map (Expr.eval σ) ++ rest), ?_, ?_⟩
    · change execU32Lt cs = _
      unfold execU32Lt
      rw [hstack]; simp [ha, hb, MidenState.withStack]
    · exact ⟨by simp only [MidenState.withStack, List.map_cons, Expr.eval,
          List.cons_append], hmem, hframes, hadv⟩

theorem execInstruction_sound_u32Lte
    (ss : State) (cs : MidenState)
    (σ : Assignment) (rest : List Felt)
    (ss' : State) (preconds : List Precondition)
    (hmodels : ss.models cs σ rest)
    (hexec : execInstruction ss .u32Lte = some (ss', preconds))
    (hpreconds : ∀ p ∈ preconds, p.holds σ) :
    ∃ cs', MidenLean.execInstruction cs .u32Lte = some cs' ∧ ss'.models cs' σ rest := by
  obtain ⟨hstack, hmem, hframes, hadv⟩ := hmodels
  simp only [execInstruction] at hexec
  match hstk : ss.stack with
  | [] | [_] => simp [hstk] at hexec
  | b :: a :: tail =>
    simp only [hstk] at hexec
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hexec)
    rw [hstk, List.map_cons, List.map_cons, List.cons_append, List.cons_append] at hstack
    have ha : (a.eval σ).isU32 = true :=
      hpreconds (.isU32 a) (by simp)
    have hb : (b.eval σ).isU32 = true :=
      hpreconds (.isU32 b) (by simp)
    refine ⟨cs.withStack ((if (a.eval σ).val ≤ (b.eval σ).val then (1 : Felt) else 0) ::
                          tail.map (Expr.eval σ) ++ rest), ?_, ?_⟩
    · change execU32Lte cs = _
      unfold execU32Lte
      rw [hstack]; simp [ha, hb, MidenState.withStack]
    · exact ⟨by simp only [MidenState.withStack, List.map_cons, Expr.eval,
          List.cons_append], hmem, hframes, hadv⟩

theorem execInstruction_sound_u32Gt
    (ss : State) (cs : MidenState)
    (σ : Assignment) (rest : List Felt)
    (ss' : State) (preconds : List Precondition)
    (hmodels : ss.models cs σ rest)
    (hexec : execInstruction ss .u32Gt = some (ss', preconds))
    (hpreconds : ∀ p ∈ preconds, p.holds σ) :
    ∃ cs', MidenLean.execInstruction cs .u32Gt = some cs' ∧ ss'.models cs' σ rest := by
  obtain ⟨hstack, hmem, hframes, hadv⟩ := hmodels
  simp only [execInstruction] at hexec
  match hstk : ss.stack with
  | [] | [_] => simp [hstk] at hexec
  | b :: a :: tail =>
    simp only [hstk] at hexec
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hexec)
    rw [hstk, List.map_cons, List.map_cons, List.cons_append, List.cons_append] at hstack
    have ha : (a.eval σ).isU32 = true :=
      hpreconds (.isU32 a) (by simp)
    have hb : (b.eval σ).isU32 = true :=
      hpreconds (.isU32 b) (by simp)
    refine ⟨cs.withStack ((if (a.eval σ).val > (b.eval σ).val then (1 : Felt) else 0) ::
                          tail.map (Expr.eval σ) ++ rest), ?_, ?_⟩
    · change execU32Gt cs = _
      unfold execU32Gt
      rw [hstack]; simp [ha, hb, MidenState.withStack]
    · exact ⟨by simp only [MidenState.withStack, List.map_cons, Expr.eval,
          List.cons_append], hmem, hframes, hadv⟩

theorem execInstruction_sound_u32Gte
    (ss : State) (cs : MidenState)
    (σ : Assignment) (rest : List Felt)
    (ss' : State) (preconds : List Precondition)
    (hmodels : ss.models cs σ rest)
    (hexec : execInstruction ss .u32Gte = some (ss', preconds))
    (hpreconds : ∀ p ∈ preconds, p.holds σ) :
    ∃ cs', MidenLean.execInstruction cs .u32Gte = some cs' ∧ ss'.models cs' σ rest := by
  obtain ⟨hstack, hmem, hframes, hadv⟩ := hmodels
  simp only [execInstruction] at hexec
  match hstk : ss.stack with
  | [] | [_] => simp [hstk] at hexec
  | b :: a :: tail =>
    simp only [hstk] at hexec
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hexec)
    rw [hstk, List.map_cons, List.map_cons, List.cons_append, List.cons_append] at hstack
    have ha : (a.eval σ).isU32 = true :=
      hpreconds (.isU32 a) (by simp)
    have hb : (b.eval σ).isU32 = true :=
      hpreconds (.isU32 b) (by simp)
    refine ⟨cs.withStack ((if (a.eval σ).val ≥ (b.eval σ).val then (1 : Felt) else 0) ::
                          tail.map (Expr.eval σ) ++ rest), ?_, ?_⟩
    · change execU32Gte cs = _
      unfold execU32Gte
      rw [hstack]; simp [ha, hb, MidenState.withStack]
    · exact ⟨by simp only [MidenState.withStack, List.map_cons, Expr.eval,
          List.cons_append], hmem, hframes, hadv⟩

theorem execInstruction_sound_u32Min
    (ss : State) (cs : MidenState)
    (σ : Assignment) (rest : List Felt)
    (ss' : State) (preconds : List Precondition)
    (hmodels : ss.models cs σ rest)
    (hexec : execInstruction ss .u32Min = some (ss', preconds))
    (hpreconds : ∀ p ∈ preconds, p.holds σ) :
    ∃ cs', MidenLean.execInstruction cs .u32Min = some cs' ∧ ss'.models cs' σ rest := by
  obtain ⟨hstack, hmem, hframes, hadv⟩ := hmodels
  simp only [execInstruction] at hexec
  match hstk : ss.stack with
  | [] | [_] => simp [hstk] at hexec
  | b :: a :: tail =>
    simp only [hstk] at hexec
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hexec)
    rw [hstk, List.map_cons, List.map_cons, List.cons_append, List.cons_append] at hstack
    have ha : (a.eval σ).isU32 = true :=
      hpreconds (.isU32 a) (by simp)
    have hb : (b.eval σ).isU32 = true :=
      hpreconds (.isU32 b) (by simp)
    refine ⟨cs.withStack ((if (a.eval σ).val ≤ (b.eval σ).val then a.eval σ else b.eval σ) ::
                          tail.map (Expr.eval σ) ++ rest), ?_, ?_⟩
    · change execU32Min cs = _
      unfold execU32Min
      rw [hstack]; simp [ha, hb, MidenState.withStack]
    · exact ⟨by simp only [MidenState.withStack, List.map_cons, Expr.eval,
          List.cons_append], hmem, hframes, hadv⟩

theorem execInstruction_sound_u32Max
    (ss : State) (cs : MidenState)
    (σ : Assignment) (rest : List Felt)
    (ss' : State) (preconds : List Precondition)
    (hmodels : ss.models cs σ rest)
    (hexec : execInstruction ss .u32Max = some (ss', preconds))
    (hpreconds : ∀ p ∈ preconds, p.holds σ) :
    ∃ cs', MidenLean.execInstruction cs .u32Max = some cs' ∧ ss'.models cs' σ rest := by
  obtain ⟨hstack, hmem, hframes, hadv⟩ := hmodels
  simp only [execInstruction] at hexec
  match hstk : ss.stack with
  | [] | [_] => simp [hstk] at hexec
  | b :: a :: tail =>
    simp only [hstk] at hexec
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hexec)
    rw [hstk, List.map_cons, List.map_cons, List.cons_append, List.cons_append] at hstack
    have ha : (a.eval σ).isU32 = true :=
      hpreconds (.isU32 a) (by simp)
    have hb : (b.eval σ).isU32 = true :=
      hpreconds (.isU32 b) (by simp)
    refine ⟨cs.withStack ((if (a.eval σ).val ≥ (b.eval σ).val then a.eval σ else b.eval σ) ::
                          tail.map (Expr.eval σ) ++ rest), ?_, ?_⟩
    · change execU32Max cs = _
      unfold execU32Max
      rw [hstack]; simp [ha, hb, MidenState.withStack]
    · exact ⟨by simp only [MidenState.withStack, List.map_cons, Expr.eval,
          List.cons_append], hmem, hframes, hadv⟩

-- Word ops (multi-element indexed access via getElem?)

set_option maxHeartbeats 800000 in
theorem execInstruction_sound_dupw
    (n : Fin 4) (ss : State) (cs : MidenState)
    (σ : Assignment) (rest : List Felt)
    (ss' : State) (preconds : List Precondition)
    (hmodels : ss.models cs σ rest)
    (hexec : execInstruction ss (.dupw n) = some (ss', preconds))
    (hpreconds : ∀ p ∈ preconds, p.holds σ) :
    ∃ cs', MidenLean.execInstruction cs (.dupw n) = some cs' ∧ ss'.models cs' σ rest := by
  obtain ⟨hstack, hmem, hframes, hadv⟩ := hmodels
  simp only [execInstruction] at hexec
  set base := n.val * 4 with hbase_def
  match hga : ss.stack[base]?, hgb : ss.stack[base + 1]?,
        hgc : ss.stack[base + 2]?, hgd : ss.stack[base + 3]? with
  | some a, some b, some c, some d =>
    simp only [hga, hgb, hgc, hgd] at hexec
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hexec)
    have hna : base < ss.stack.length := getElem?_some_lt _ _ _ hga
    have hnb : base + 1 < ss.stack.length := getElem?_some_lt _ _ _ hgb
    have hnc : base + 2 < ss.stack.length := getElem?_some_lt _ _ _ hgc
    have hnd : base + 3 < ss.stack.length := getElem?_some_lt _ _ _ hgd
    have hva : ss.stack[base] = a := getElem_of_getElem?_some _ _ _ hga
    have hvb : ss.stack[base + 1] = b := getElem_of_getElem?_some _ _ _ hgb
    have hvc : ss.stack[base + 2] = c := getElem_of_getElem?_some _ _ _ hgc
    have hvd : ss.stack[base + 3] = d := getElem_of_getElem?_some _ _ _ hgd
    refine ⟨cs.withStack (a.eval σ :: b.eval σ :: c.eval σ :: d.eval σ :: cs.stack), ?_, ?_⟩
    · simp only [MidenLean.execInstruction, execDupw, hbase_def, hstack]
      rw [getElem?_map_append_left (Expr.eval σ) ss.stack rest base hna,
          getElem?_map_append_left (Expr.eval σ) ss.stack rest (base + 1) hnb,
          getElem?_map_append_left (Expr.eval σ) ss.stack rest (base + 2) hnc,
          getElem?_map_append_left (Expr.eval σ) ss.stack rest (base + 3) hnd]
      rw [hva, hvb, hvc, hvd]
    · exact ⟨by simp only [MidenState.withStack, List.map_cons, hstack]; rfl, hmem, hframes, hadv⟩
  | _, _, _, _ =>
    simp only [hga, hgb, hgc, hgd] at hexec
    split at hexec
    next a' b' c' d' =>
      obtain ⟨rfl, rfl⟩ := hexec
      have hna : base < ss.stack.length := getElem?_some_lt _ _ _ hga
      have hnb : base + 1 < ss.stack.length := getElem?_some_lt _ _ _ hgb
      have hnc : base + 2 < ss.stack.length := getElem?_some_lt _ _ _ hgc
      have hnd : base + 3 < ss.stack.length := getElem?_some_lt _ _ _ hgd
      have hva : ss.stack[base] = a' := getElem_of_getElem?_some _ _ _ hga
      have hvb : ss.stack[base + 1] = b' := getElem_of_getElem?_some _ _ _ hgb
      have hvc : ss.stack[base + 2] = c' := getElem_of_getElem?_some _ _ _ hgc
      have hvd : ss.stack[base + 3] = d' := getElem_of_getElem?_some _ _ _ hgd
      refine ⟨cs.withStack (a'.eval σ :: b'.eval σ :: c'.eval σ :: d'.eval σ :: cs.stack), ?_, ?_⟩
      · simp only [MidenLean.execInstruction, execDupw, hstack]
        rw [getElem?_map_append_left (Expr.eval σ) ss.stack rest base hna,
            getElem?_map_append_left (Expr.eval σ) ss.stack rest (base + 1) hnb,
            getElem?_map_append_left (Expr.eval σ) ss.stack rest (base + 2) hnc,
            getElem?_map_append_left (Expr.eval σ) ss.stack rest (base + 3) hnd]
        rw [hva, hvb, hvc, hvd]
      · exact ⟨by simp only [MidenState.withStack, List.map_cons, hstack]; rfl, hmem, hframes, hadv⟩
    next h =>
      exact absurd hexec (by simp)

set_option maxHeartbeats 1600000 in
theorem execInstruction_sound_swapw
    (n : Fin 4) (ss : State) (cs : MidenState)
    (σ : Assignment) (rest : List Felt)
    (ss' : State) (preconds : List Precondition)
    (hmodels : ss.models cs σ rest)
    (hexec : execInstruction ss (.swapw n) = some (ss', preconds))
    (hpreconds : ∀ p ∈ preconds, p.holds σ) :
    ∃ cs', MidenLean.execInstruction cs (.swapw n) = some cs' ∧ ss'.models cs' σ rest := by
  obtain ⟨hstack, hmem, hframes, hadv⟩ := hmodels
  simp only [execInstruction] at hexec
  -- Split on the if (n.val == 0) condition inside hexec
  split at hexec
  · -- n = 0: identity case
    rename_i h0
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hexec)
    exact ⟨cs,
      by simp [MidenLean.execInstruction, execSwapw, h0],
      hstack, hmem, hframes, hadv⟩
  · -- n ≠ 0: 8-element swap
    -- Split on the 8-way match inside hexec
    split at hexec
    · -- all 8 getElem? are some (a0..a3 at 0..3, b0..b3 at n*4..n*4+3)
      rename_i h0 _ _ _ _ _ _ _ _ a0 a1 a2 a3 b0 b1 b2 b3 hg0 hg1 hg2 hg3 hgb0 hgb1 hgb2 hgb3
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hexec)
      have h0lt : 0 < ss.stack.length := getElem?_some_lt _ _ _ hg0
      have h1lt : 1 < ss.stack.length := getElem?_some_lt _ _ _ hg1
      have h2lt : 2 < ss.stack.length := getElem?_some_lt _ _ _ hg2
      have h3lt : 3 < ss.stack.length := getElem?_some_lt _ _ _ hg3
      have hb0lt : n.val * 4 < ss.stack.length := getElem?_some_lt _ _ _ hgb0
      have hb1lt : n.val * 4 + 1 < ss.stack.length := getElem?_some_lt _ _ _ hgb1
      have hb2lt : n.val * 4 + 2 < ss.stack.length := getElem?_some_lt _ _ _ hgb2
      have hb3lt : n.val * 4 + 3 < ss.stack.length := getElem?_some_lt _ _ _ hgb3
      have hv0 : ss.stack[0] = a0 := getElem_of_getElem?_some _ _ _ hg0
      have hv1 : ss.stack[1] = a1 := getElem_of_getElem?_some _ _ _ hg1
      have hv2 : ss.stack[2] = a2 := getElem_of_getElem?_some _ _ _ hg2
      have hv3 : ss.stack[3] = a3 := getElem_of_getElem?_some _ _ _ hg3
      have hvb0 : ss.stack[n.val * 4] = b0 := getElem_of_getElem?_some _ _ _ hgb0
      have hvb1 : ss.stack[n.val * 4 + 1] = b1 := getElem_of_getElem?_some _ _ _ hgb1
      have hvb2 : ss.stack[n.val * 4 + 2] = b2 := getElem_of_getElem?_some _ _ _ hgb2
      have hvb3 : ss.stack[n.val * 4 + 3] = b3 := getElem_of_getElem?_some _ _ _ hgb3
      refine ⟨cs.withStack ((cs.stack.set 0 (b0.eval σ) |>.set 1 (b1.eval σ) |>.set 2 (b2.eval σ)
                             |>.set 3 (b3.eval σ) |>.set (n.val * 4) (a0.eval σ)
                             |>.set (n.val * 4 + 1) (a1.eval σ)
                             |>.set (n.val * 4 + 2) (a2.eval σ)
                             |>.set (n.val * 4 + 3) (a3.eval σ))), ?_, ?_⟩
      · simp only [MidenLean.execInstruction, execSwapw]
        split
        · -- n == 0 case (contradicts h0)
          rename_i h0eq; exact absurd h0eq h0
        · -- n ≠ 0 case
          rw [hstack,
              getElem?_map_append_left (Expr.eval σ) ss.stack rest 0 h0lt,
              getElem?_map_append_left (Expr.eval σ) ss.stack rest 1 h1lt,
              getElem?_map_append_left (Expr.eval σ) ss.stack rest 2 h2lt,
              getElem?_map_append_left (Expr.eval σ) ss.stack rest 3 h3lt,
              getElem?_map_append_left (Expr.eval σ) ss.stack rest (n.val * 4) hb0lt,
              getElem?_map_append_left (Expr.eval σ) ss.stack rest (n.val * 4 + 1) hb1lt,
              getElem?_map_append_left (Expr.eval σ) ss.stack rest (n.val * 4 + 2) hb2lt,
              getElem?_map_append_left (Expr.eval σ) ss.stack rest (n.val * 4 + 3) hb3lt]
          rw [hv0, hv1, hv2, hv3, hvb0, hvb1, hvb2, hvb3]
      · refine ⟨?_, hmem, hframes, hadv⟩
        unfold MidenState.withStack
        rw [hstack,
            set_map_append_left _ _ _ (n.val * 4 + 3) a3 (by simp [List.length_set]; exact hb3lt),
            set_map_append_left _ _ _ (n.val * 4 + 2) a2 (by simp [List.length_set]; exact hb2lt),
            set_map_append_left _ _ _ (n.val * 4 + 1) a1 (by simp [List.length_set]; exact hb1lt),
            set_map_append_left _ _ _ (n.val * 4) a0 (by simp [List.length_set]; exact hb0lt),
            set_map_append_left _ _ _ 3 b3 (by simp [List.length_set]; exact h3lt),
            set_map_append_left _ _ _ 2 b2 (by simp [List.length_set]; exact h2lt),
            set_map_append_left _ _ _ 1 b1 (by simp [List.length_set]; exact h1lt),
            set_map_append_left _ _ _ 0 b0 h0lt]
    · -- not all some: contradiction
      exact absurd hexec (by simp)

set_option maxHeartbeats 800000 in
theorem execInstruction_sound_movupw
    (n : Nat) (ss : State) (cs : MidenState)
    (σ : Assignment) (rest : List Felt)
    (ss' : State) (preconds : List Precondition)
    (hmodels : ss.models cs σ rest)
    (hexec : execInstruction ss (.movupw n) = some (ss', preconds))
    (hpreconds : ∀ p ∈ preconds, p.holds σ) :
    ∃ cs', MidenLean.execInstruction cs (.movupw n) = some cs' ∧ ss'.models cs' σ rest := by
  obtain ⟨hstack, hmem, hframes, hadv⟩ := hmodels
  simp only [execInstruction] at hexec
  by_cases hrange : 2 ≤ n ∧ n ≤ 3
  · have htrue : (decide (2 ≤ n) && decide (n ≤ 3)) = true := by
      simp only [Bool.and_eq_true, decide_eq_true_eq]; exact hrange
    simp only [htrue, ite_true] at hexec
    set base := n * 4 with hbase_def
    by_cases hlen : ss.stack.length < base + 4
    · simp [hlen] at hexec
    · push_neg at hlen
      rw [if_neg (by omega)] at hexec
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hexec)
      have hle : base + 4 ≤ ss.stack.length := hlen
      refine ⟨cs.withStack (((ss.stack.map (Expr.eval σ)).drop base).take 4 ++
                              (ss.stack.map (Expr.eval σ)).take base ++
                              (ss.stack.map (Expr.eval σ)).drop (base + 4) ++ rest), ?_, ?_⟩
      · change execMovupw n cs = _
        unfold execMovupw
        have : ¬(n < 2) := by omega
        have : ¬(n > 3) := by omega
        simp only [show (n < 2 || n > 3) = false by simp_all [Bool.or_eq_true, decide_eq_true_eq],
                    ite_false]
        rw [hstack]
        have hle' : base + 4 ≤ (ss.stack.map (Expr.eval σ) ++ rest).length := by simp; omega
        simp only [MidenState.withStack]
        congr 1
        rw [List.take_append_of_le_length (by simp; omega),
            List.drop_append_of_le_length (by simp; omega)]
        rw [List.take_append_of_le_length (by simp [List.length_drop]; omega),
            List.drop_append_of_le_length (by simp; omega)]
        simp only [List.append_assoc, hbase_def]
        simp; omega
      · exact ⟨by simp only [MidenState.withStack,
            List.map_append, List.map_take, List.map_drop, List.append_assoc], hmem, hframes, hadv⟩
  · have hfalse : (decide (2 ≤ n) && decide (n ≤ 3)) = false := by
      simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega
    simp [hfalse] at hexec

set_option maxHeartbeats 800000 in
theorem execInstruction_sound_movdnw
    (n : Nat) (ss : State) (cs : MidenState)
    (σ : Assignment) (rest : List Felt)
    (ss' : State) (preconds : List Precondition)
    (hmodels : ss.models cs σ rest)
    (hexec : execInstruction ss (.movdnw n) = some (ss', preconds))
    (hpreconds : ∀ p ∈ preconds, p.holds σ) :
    ∃ cs', MidenLean.execInstruction cs (.movdnw n) = some cs' ∧ ss'.models cs' σ rest := by
  obtain ⟨hstack, hmem, hframes, hadv⟩ := hmodels
  simp only [execInstruction] at hexec
  by_cases hrange : 2 ≤ n ∧ n ≤ 3
  · have htrue : (decide (2 ≤ n) && decide (n ≤ 3)) = true := by
      simp only [Bool.and_eq_true, decide_eq_true_eq]; exact hrange
    simp only [htrue, ite_true] at hexec
    by_cases hlen : ss.stack.length < (n + 1) * 4
    · simp [hlen] at hexec
    · push_neg at hlen
      rw [if_neg (by omega)] at hexec
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hexec)
      have hle : (n + 1) * 4 ≤ ss.stack.length := hlen
      refine ⟨cs.withStack (((ss.stack.map (Expr.eval σ)).drop 4).take (n * 4) ++
                              (ss.stack.map (Expr.eval σ)).take 4 ++
                              ((ss.stack.map (Expr.eval σ)).drop 4).drop (n * 4) ++ rest), ?_, ?_⟩
      · change execMovdnw n cs = _
        unfold execMovdnw
        have : ¬(n < 2) := by omega
        have : ¬(n > 3) := by omega
        simp only [show (n < 2 || n > 3) = false by simp_all [Bool.or_eq_true, decide_eq_true_eq],
                    ite_false]
        rw [hstack]
        have hle' : (n + 1) * 4 ≤ (ss.stack.map (Expr.eval σ) ++ rest).length := by simp; omega
        simp only [MidenState.withStack]
        congr 1
        rw [List.take_append_of_le_length (by simp; omega),
            List.drop_append_of_le_length (by simp; omega)]
        rw [List.take_append_of_le_length (by simp [List.length_drop]; omega),
            List.drop_append_of_le_length (by simp [List.length_drop]; omega)]
        simp [List.append_assoc]
        omega
      · exact ⟨by simp only [MidenState.withStack,
            List.map_append, List.map_take, List.map_drop, List.append_assoc], hmem, hframes, hadv⟩
  · have hfalse : (decide (2 ≤ n) && decide (n ≤ 3)) = false := by
      simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega
    simp [hfalse] at hexec

end MidenLean.Symbolic
