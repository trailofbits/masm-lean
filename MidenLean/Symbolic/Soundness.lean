import MidenLean.Symbolic.Exec
import MidenLean.Symbolic.Helpers
import MidenLean.Proofs.Fuel

/-!
# Symbolic Execution Soundness

Three-tier soundness stack:

* `execInstruction_sound` — each supported instruction agrees with the
  concrete step (per-instruction helpers live in `Helpers.lean`);
* `execBlock_sound` — lifts this to straight-line basic blocks;
* `execOps_sound` — extends it to op lists containing `exec` calls, given
  `Spec.sound` witnesses for every callee in the symbolic `ProcEnv`.

Both block-level theorems share a single fold induction over `execOp`
(`foldlM_execOp_sound`): `execBlock_sound` is derived from it through the
executor bridge `execOps_map_inst_eq_execBlock`, which identifies `execBlock`
with `execOps` on instruction-only op lists under the empty symbolic
environment.

Direction of the guarantee: symbolic success implies concrete success with a
matching (`models`) state, provided all collected preconditions hold. A
symbolic `some` result can therefore never diverge silently from the concrete
semantics; unsupported ops return `none` and fail loudly at tactic time.

Trust caveat: `Expr.eval` intentionally shares its arithmetic helper
definitions with `Concrete/Exec.lean`, so these theorems validate the
symbolic/concrete translation — not the fidelity of the concrete model to
the Miden VM itself.
-/

namespace MidenLean.Symbolic

-- Helper lemmas: provided by Helpers.lean
-- (getElem?_map_append_left, set_map_append_left,
--  eraseIdx_map_append_left, isBool_guard)

-- Per-instruction soundness

-- Helper: drop case
private theorem execInstruction_sound_drop
    (ss : State) (cs : Concrete.State)
    (σ : Assignment) (rest : List Felt)
    (ss' : State) (preconds : List Precondition)
    (hmodels : ss.models cs σ rest)
    (hexec : execInstruction ss .drop = some (ss', preconds))
    (hpreconds : ∀ p ∈ preconds, p.holds σ) :
    ∃ cs', MidenLean.execInstruction cs .drop = some cs' ∧ ss'.models cs' σ rest := by
  obtain ⟨hstack, hmem, hframes, hadv⟩ := hmodels
  unfold execInstruction at hexec
  match hstk : ss.stack with
  | [] => simp [hstk] at hexec
  | x :: tail =>
    simp only [hstk] at hexec
    have heq := Option.some.inj hexec
    have hss : ss' = { ss with stack := tail } := (congrArg Prod.fst heq).symm
    have hpc : preconds = [] := (congrArg Prod.snd heq).symm
    subst hss; subst hpc
    rw [hstk, List.map_cons] at hstack
    exact ⟨cs.withStack (tail.map (Expr.eval σ) ++ rest),
      by simp only [MidenLean.execInstruction, execDrop, hstack]; rfl,
      ⟨by simp only [Concrete.State.withStack], hmem, hframes, hadv⟩⟩

-- Helper: dup case
private theorem execInstruction_sound_dup
    (n : Fin 16) (ss : State) (cs : Concrete.State)
    (σ : Assignment) (rest : List Felt)
    (ss' : State) (preconds : List Precondition)
    (hmodels : ss.models cs σ rest)
    (hexec : execInstruction ss (.dup n) = some (ss', preconds))
    (hpreconds : ∀ p ∈ preconds, p.holds σ) :
    ∃ cs', MidenLean.execInstruction cs (.dup n) = some cs' ∧ ss'.models cs' σ rest := by
  obtain ⟨hstack, hmem, hframes, hadv⟩ := hmodels
  unfold execInstruction at hexec
  match hget : ss.stack[n.val]? with
  | none => simp [hget] at hexec
  | some v =>
    simp only [hget] at hexec
    have heq := Option.some.inj hexec
    have hss : ss' = { ss with stack := v :: ss.stack } := (congrArg Prod.fst heq).symm
    have hpc : preconds = [] := (congrArg Prod.snd heq).symm
    subst hss; subst hpc
    obtain ⟨hn, hval⟩ := List.getElem?_eq_some_iff.mp hget
    refine ⟨cs.withStack (v.eval σ :: cs.stack), ?_, ?_⟩
    · simp only [MidenLean.execInstruction, execDup, hstack,
          getElem?_map_append_left _ _ _ _ hn]
      rw [hval]
    · exact ⟨by simp only [Concrete.State.withStack, List.map_cons, List.cons_append, hstack],
             hmem, hframes, hadv⟩

-- Helper: swap case
private theorem execInstruction_sound_swap
    (n : Fin 16) (ss : State) (cs : Concrete.State)
    (σ : Assignment) (rest : List Felt)
    (ss' : State) (preconds : List Precondition)
    (hmodels : ss.models cs σ rest)
    (hexec : execInstruction ss (.swap n) = some (ss', preconds))
    (hpreconds : ∀ p ∈ preconds, p.holds σ) :
    ∃ cs', MidenLean.execInstruction cs (.swap n) = some cs' ∧ ss'.models cs' σ rest := by
  obtain ⟨hstack, hmem, hframes, hadv⟩ := hmodels
  unfold execInstruction at hexec
  by_cases h0 : n.val = 0
  · have hbeq : (n.val == 0) = true := by simp [h0]
    simp only [hbeq, ite_true] at hexec
    have heq := Option.some.inj hexec
    have hss : ss' = ss := (congrArg Prod.fst heq).symm
    have hpc : preconds = [] := (congrArg Prod.snd heq).symm
    subst hss; subst hpc
    exact ⟨cs,
      by simp only [MidenLean.execInstruction, execSwap, hbeq, ite_true],
      hstack, hmem, hframes, hadv⟩
  · have hne : (n.val == 0) = false := by simp [h0]
    simp only [hne] at hexec
    match hget0 : ss.stack[0]?, hgetn : ss.stack[n.val]? with
    | some top, some nth =>
      simp only [hget0, hgetn] at hexec
      have heq := Option.some.inj hexec
      have hss : ss' = { ss with stack := (ss.stack.set 0 nth).set n.val top } :=
        (congrArg Prod.fst heq).symm
      have hpc : preconds = [] := (congrArg Prod.snd heq).symm
      subst hss; subst hpc
      obtain ⟨h0lt, hval0⟩ := List.getElem?_eq_some_iff.mp hget0
      obtain ⟨hnlt, hvaln⟩ := List.getElem?_eq_some_iff.mp hgetn
      refine ⟨cs.withStack ((cs.stack.set 0 (nth.eval σ)).set n.val (top.eval σ)), ?_, ?_⟩
      · simp only [MidenLean.execInstruction, execSwap, hne]
        rw [hstack,
            getElem?_map_append_left _ _ _ 0 h0lt,
            getElem?_map_append_left _ _ _ n.val hnlt]
        rw [hval0, hvaln]
        rfl
      · constructor
        · simp only [Concrete.State.withStack]
          rw [hstack,
              set_map_append_left (Expr.eval σ) (ss.stack.set 0 nth) rest n.val top
                (by rw [List.length_set]; exact hnlt),
              set_map_append_left (Expr.eval σ) ss.stack rest 0 nth h0lt]
        · exact ⟨hmem, hframes, hadv⟩
    | some _, none | none, some _ | none, none =>
      simp [hget0, hgetn] at hexec

-- Helper: add case
private theorem execInstruction_sound_add
    (ss : State) (cs : Concrete.State)
    (σ : Assignment) (rest : List Felt)
    (ss' : State) (preconds : List Precondition)
    (hmodels : ss.models cs σ rest)
    (hexec : execInstruction ss .add = some (ss', preconds))
    (hpreconds : ∀ p ∈ preconds, p.holds σ) :
    ∃ cs', MidenLean.execInstruction cs .add = some cs' ∧ ss'.models cs' σ rest := by
  obtain ⟨hstack, hmem, hframes, hadv⟩ := hmodels
  unfold execInstruction at hexec
  match hstk : ss.stack with
  | [] | [_] => simp [hstk] at hexec
  | b :: a :: tail =>
    simp only [hstk] at hexec
    have heq := Option.some.inj hexec
    have hss : ss' = { ss with stack := .add a b :: tail } := (congrArg Prod.fst heq).symm
    have hpc : preconds = [] := (congrArg Prod.snd heq).symm
    subst hss; subst hpc
    rw [hstk, List.map_cons, List.map_cons] at hstack
    exact ⟨cs.withStack ((a.eval σ + b.eval σ) :: tail.map (Expr.eval σ) ++ rest),
      by simp only [MidenLean.execInstruction, execAdd, hstack]; rfl,
      ⟨by simp only [Concrete.State.withStack, List.map_cons, Expr.eval], hmem, hframes, hadv⟩⟩

-- Helper: sub case
private theorem execInstruction_sound_sub
    (ss : State) (cs : Concrete.State)
    (σ : Assignment) (rest : List Felt)
    (ss' : State) (preconds : List Precondition)
    (hmodels : ss.models cs σ rest)
    (hexec : execInstruction ss .sub = some (ss', preconds))
    (hpreconds : ∀ p ∈ preconds, p.holds σ) :
    ∃ cs', MidenLean.execInstruction cs .sub = some cs' ∧ ss'.models cs' σ rest := by
  obtain ⟨hstack, hmem, hframes, hadv⟩ := hmodels
  unfold execInstruction at hexec
  match hstk : ss.stack with
  | [] | [_] => simp [hstk] at hexec
  | b :: a :: tail =>
    simp only [hstk] at hexec
    have heq := Option.some.inj hexec
    have hss : ss' = { ss with stack := .sub a b :: tail } := (congrArg Prod.fst heq).symm
    have hpc : preconds = [] := (congrArg Prod.snd heq).symm
    subst hss; subst hpc
    rw [hstk, List.map_cons, List.map_cons] at hstack
    exact ⟨cs.withStack ((a.eval σ - b.eval σ) :: tail.map (Expr.eval σ) ++ rest),
      by simp only [MidenLean.execInstruction, execSub, hstack]; rfl,
      ⟨by simp only [Concrete.State.withStack, List.map_cons, Expr.eval], hmem, hframes, hadv⟩⟩

-- Helper: mul case
private theorem execInstruction_sound_mul
    (ss : State) (cs : Concrete.State)
    (σ : Assignment) (rest : List Felt)
    (ss' : State) (preconds : List Precondition)
    (hmodels : ss.models cs σ rest)
    (hexec : execInstruction ss .mul = some (ss', preconds))
    (hpreconds : ∀ p ∈ preconds, p.holds σ) :
    ∃ cs', MidenLean.execInstruction cs .mul = some cs' ∧ ss'.models cs' σ rest := by
  obtain ⟨hstack, hmem, hframes, hadv⟩ := hmodels
  unfold execInstruction at hexec
  match hstk : ss.stack with
  | [] | [_] => simp [hstk] at hexec
  | b :: a :: tail =>
    simp only [hstk] at hexec
    have heq := Option.some.inj hexec
    have hss : ss' = { ss with stack := .mul a b :: tail } := (congrArg Prod.fst heq).symm
    have hpc : preconds = [] := (congrArg Prod.snd heq).symm
    subst hss; subst hpc
    rw [hstk, List.map_cons, List.map_cons] at hstack
    exact ⟨cs.withStack ((a.eval σ * b.eval σ) :: tail.map (Expr.eval σ) ++ rest),
      by simp only [MidenLean.execInstruction, execMul, hstack]; rfl,
      ⟨by simp only [Concrete.State.withStack, List.map_cons, Expr.eval], hmem, hframes, hadv⟩⟩

-- Helper: u32WidenAdd case
private theorem execInstruction_sound_u32WidenAdd
    (ss : State) (cs : Concrete.State)
    (σ : Assignment) (rest : List Felt)
    (ss' : State) (preconds : List Precondition)
    (hmodels : ss.models cs σ rest)
    (hexec : execInstruction ss .u32WidenAdd = some (ss', preconds))
    (hpreconds : ∀ p ∈ preconds, p.holds σ) :
    ∃ cs', MidenLean.execInstruction cs .u32WidenAdd = some cs' ∧ ss'.models cs' σ rest := by
  obtain ⟨hstack, hmem, hframes, hadv⟩ := hmodels
  unfold execInstruction at hexec
  match hstk : ss.stack with
  | [] | [_] => simp [hstk] at hexec
  | b :: a :: tail =>
    simp only [hstk] at hexec
    have heq := Option.some.inj hexec
    have hss : ss' = { ss with stack := .u32AddLo a b :: .u32AddHi a b :: tail } :=
      (congrArg Prod.fst heq).symm
    have hpc : preconds = [.isU32 a, .isU32 b] := (congrArg Prod.snd heq).symm
    subst hss
    rw [hstk, List.map_cons, List.map_cons, List.cons_append, List.cons_append] at hstack
    have ha : (a.eval σ).isU32 = true :=
      hpreconds (.isU32 a) (by rw [hpc]; simp)
    have hb : (b.eval σ).isU32 = true :=
      hpreconds (.isU32 b) (by rw [hpc]; simp)
    refine ⟨cs.withStack (Felt.ofNat (((a.eval σ).val + (b.eval σ).val) % u32Max) ::
                          Felt.ofNat (((a.eval σ).val + (b.eval σ).val) / u32Max) ::
                          tail.map (Expr.eval σ) ++ rest), ?_, ?_⟩
    · simp only [MidenLean.execInstruction, execU32WidenAdd, hstack, ha, hb,
          Bool.not_true, Bool.false_or, u32WideAdd, Concrete.State.withStack]
      rfl
    · exact ⟨by simp only [Concrete.State.withStack, List.map_cons, Expr.eval, List.cons_append],
             hmem, hframes, hadv⟩

-- Helper: eq case
private theorem execInstruction_sound_eq
    (ss : State) (cs : Concrete.State)
    (σ : Assignment) (rest : List Felt)
    (ss' : State) (preconds : List Precondition)
    (hmodels : ss.models cs σ rest)
    (hexec : execInstruction ss .eq = some (ss', preconds))
    (hpreconds : ∀ p ∈ preconds, p.holds σ) :
    ∃ cs', MidenLean.execInstruction cs .eq = some cs' ∧ ss'.models cs' σ rest := by
  obtain ⟨hstack, hmem, hframes, hadv⟩ := hmodels
  unfold execInstruction at hexec
  match hstk : ss.stack with
  | [] | [_] => simp [hstk] at hexec
  | b :: a :: tail =>
    simp only [hstk] at hexec
    have heq := Option.some.inj hexec
    have hss : ss' = { ss with stack := .feltEq a b :: tail } := (congrArg Prod.fst heq).symm
    have hpc : preconds = [] := (congrArg Prod.snd heq).symm
    subst hss; subst hpc
    rw [hstk, List.map_cons, List.map_cons] at hstack
    exact ⟨cs.withStack ((if a.eval σ == b.eval σ then (1 : Felt) else 0) :: tail.map (Expr.eval σ) ++ rest),
      by simp only [MidenLean.execInstruction, execEq, hstack]; rfl,
      ⟨by simp only [Concrete.State.withStack, List.map_cons, Expr.eval], hmem, hframes, hadv⟩⟩

-- Helper: and case
private theorem execInstruction_sound_and
    (ss : State) (cs : Concrete.State)
    (σ : Assignment) (rest : List Felt)
    (ss' : State) (preconds : List Precondition)
    (hmodels : ss.models cs σ rest)
    (hexec : execInstruction ss .and = some (ss', preconds))
    (hpreconds : ∀ p ∈ preconds, p.holds σ) :
    ∃ cs', MidenLean.execInstruction cs .and = some cs' ∧ ss'.models cs' σ rest := by
  obtain ⟨hstack, hmem, hframes, hadv⟩ := hmodels
  unfold execInstruction at hexec
  match hstk : ss.stack with
  | [] | [_] => simp [hstk] at hexec
  | b :: a :: tail =>
    simp only [hstk] at hexec
    have heq := Option.some.inj hexec
    have hss : ss' = { ss with stack := .feltAnd a b :: tail } := (congrArg Prod.fst heq).symm
    have hpc : preconds = [.isBool a, .isBool b] := (congrArg Prod.snd heq).symm
    subst hss
    rw [hstk, List.map_cons, List.map_cons] at hstack
    have ha : (a.eval σ).isBool = true :=
      isBool_guard _ (hpreconds (.isBool a) (by rw [hpc]; simp))
    have hb : (b.eval σ).isBool = true :=
      isBool_guard _ (hpreconds (.isBool b) (by rw [hpc]; simp))
    have hguard : ((a.eval σ).isBool && (b.eval σ).isBool) = true := by rw [ha, hb]; rfl
    refine ⟨cs.withStack ((a.eval σ * b.eval σ) :: tail.map (Expr.eval σ) ++ rest), ?_, ?_⟩
    · change execAnd cs = _
      unfold execAnd
      rw [hstack]; simp [hguard, Concrete.State.withStack]
    · exact ⟨by simp only [Concrete.State.withStack, List.map_cons, Expr.eval], hmem, hframes, hadv⟩

-- Helper: u32WidenAdd3 case
private theorem execInstruction_sound_u32WidenAdd3
    (ss : State) (cs : Concrete.State)
    (σ : Assignment) (rest : List Felt)
    (ss' : State) (preconds : List Precondition)
    (hmodels : ss.models cs σ rest)
    (hexec : execInstruction ss .u32WidenAdd3 = some (ss', preconds))
    (hpreconds : ∀ p ∈ preconds, p.holds σ) :
    ∃ cs', MidenLean.execInstruction cs .u32WidenAdd3 = some cs' ∧ ss'.models cs' σ rest := by
  obtain ⟨hstack, hmem, hframes, hadv⟩ := hmodels
  unfold execInstruction at hexec
  match hstk : ss.stack with
  | [] | [_] | [_, _] => simp [hstk] at hexec
  | c :: b :: a :: tail =>
    simp only [hstk] at hexec
    have heq := Option.some.inj hexec
    have hss : ss' = { ss with stack := .u32Add3Lo a b c :: .u32Add3Hi a b c :: tail } :=
      (congrArg Prod.fst heq).symm
    have hpc : preconds = [.isU32 a, .isU32 b, .isU32 c] := (congrArg Prod.snd heq).symm
    subst hss
    rw [hstk, List.map_cons, List.map_cons, List.map_cons] at hstack
    have ha : (a.eval σ).isU32 = true :=
      hpreconds (.isU32 a) (by rw [hpc]; simp)
    have hb : (b.eval σ).isU32 = true :=
      hpreconds (.isU32 b) (by rw [hpc]; simp)
    have hc : (c.eval σ).isU32 = true :=
      hpreconds (.isU32 c) (by rw [hpc]; simp)
    refine ⟨cs.withStack (Felt.ofNat (((a.eval σ).val + (b.eval σ).val + (c.eval σ).val) % u32Max) ::
                          Felt.ofNat (((a.eval σ).val + (b.eval σ).val + (c.eval σ).val) / u32Max) ::
                          tail.map (Expr.eval σ) ++ rest), ?_, ?_⟩
    · change execU32WidenAdd3 cs = _
      unfold execU32WidenAdd3
      rw [hstack]; simp [ha, hb, hc, u32WideAdd3, Concrete.State.withStack]
    · exact ⟨by simp only [Concrete.State.withStack, List.map_cons, Expr.eval, List.cons_append],
             hmem, hframes, hadv⟩

-- Helper: u32OverflowSub case
private theorem execInstruction_sound_u32OverflowSub
    (ss : State) (cs : Concrete.State)
    (σ : Assignment) (rest : List Felt)
    (ss' : State) (preconds : List Precondition)
    (hmodels : ss.models cs σ rest)
    (hexec : execInstruction ss .u32OverflowSub = some (ss', preconds))
    (hpreconds : ∀ p ∈ preconds, p.holds σ) :
    ∃ cs', MidenLean.execInstruction cs .u32OverflowSub = some cs' ∧ ss'.models cs' σ rest := by
  obtain ⟨hstack, hmem, hframes, hadv⟩ := hmodels
  unfold execInstruction at hexec
  match hstk : ss.stack with
  | [] | [_] => simp [hstk] at hexec
  | b :: a :: tail =>
    simp only [hstk] at hexec
    have heq := Option.some.inj hexec
    have hss : ss' = { ss with stack := .u32SubBorrow a b :: .u32SubDiff a b :: tail } :=
      (congrArg Prod.fst heq).symm
    have hpc : preconds = [.isU32 a, .isU32 b] := (congrArg Prod.snd heq).symm
    subst hss
    rw [hstk, List.map_cons, List.map_cons] at hstack
    have ha : (a.eval σ).isU32 = true :=
      hpreconds (.isU32 a) (by rw [hpc]; simp)
    have hb : (b.eval σ).isU32 = true :=
      hpreconds (.isU32 b) (by rw [hpc]; simp)
    refine ⟨cs.withStack (Felt.ofNat (u32OverflowingSub (a.eval σ).val (b.eval σ).val).1 ::
                          Felt.ofNat (u32OverflowingSub (a.eval σ).val (b.eval σ).val).2 ::
                          tail.map (Expr.eval σ) ++ rest), ?_, ?_⟩
    · change execU32OverflowSub cs = _
      unfold execU32OverflowSub
      rw [hstack]; simp [ha, hb, Concrete.State.withStack]
    · exact ⟨by simp only [Concrete.State.withStack, List.map_cons, Expr.eval, List.cons_append],
             hmem, hframes, hadv⟩

-- Helper: movup case
private theorem execInstruction_sound_movup
    (n : Nat) (ss : State) (cs : Concrete.State)
    (σ : Assignment) (rest : List Felt)
    (ss' : State) (preconds : List Precondition)
    (hmodels : ss.models cs σ rest)
    (hexec : execInstruction ss (.movup n) = some (ss', preconds))
    (hpreconds : ∀ p ∈ preconds, p.holds σ) :
    ∃ cs', MidenLean.execInstruction cs (.movup n) = some cs' ∧ ss'.models cs' σ rest := by
  obtain ⟨hstack, hmem, hframes, hadv⟩ := hmodels
  -- Simplify hexec from the symbolic side
  simp only [execInstruction] at hexec
  by_cases hrange : 2 ≤ n ∧ n ≤ 15
  · have htrue : (decide (2 ≤ n) && decide (n ≤ 15)) = true := by
      simp only [Bool.and_eq_true, decide_eq_true_eq]; exact hrange
    simp only [htrue, ite_true] at hexec
    match hget : ss.stack[n]? with
    | none => simp [hget] at hexec
    | some v =>
      simp only [hget] at hexec
      have heq := Option.some.inj hexec
      have hss : ss' = { ss with stack := v :: ss.stack.eraseIdx n } := (congrArg Prod.fst heq).symm
      have hpc : preconds = [] := (congrArg Prod.snd heq).symm
      subst hss; subst hpc
      obtain ⟨hn, hval⟩ := List.getElem?_eq_some_iff.mp hget
      refine ⟨cs.withStack (v.eval σ :: (ss.stack.eraseIdx n).map (Expr.eval σ) ++ rest), ?_, ?_⟩
      · change execMovup n cs = _
        unfold execMovup
        have : ¬(n < 2) := by omega
        have : ¬(n > 15) := by omega
        simp_all [removeNth, getElem?_map_append_left _ _ _ _ hn,
            eraseIdx_map_append_left _ _ _ _ hn, Concrete.State.withStack]
      · exact ⟨by simp only [Concrete.State.withStack, List.map_cons], hmem, hframes, hadv⟩
  · have hfalse : (decide (2 ≤ n) && decide (n ≤ 15)) = false := by
      simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega
    simp [hfalse] at hexec

-- Helper: movdn case
private theorem execInstruction_sound_movdn
    (n : Nat) (ss : State) (cs : Concrete.State)
    (σ : Assignment) (rest : List Felt)
    (ss' : State) (preconds : List Precondition)
    (hmodels : ss.models cs σ rest)
    (hexec : execInstruction ss (.movdn n) = some (ss', preconds))
    (hpreconds : ∀ p ∈ preconds, p.holds σ) :
    ∃ cs', MidenLean.execInstruction cs (.movdn n) = some cs' ∧ ss'.models cs' σ rest := by
  obtain ⟨hstack, hmem, hframes, hadv⟩ := hmodels
  simp only [execInstruction] at hexec
  by_cases hrange : 2 ≤ n ∧ n ≤ 15
  · have htrue : (decide (2 ≤ n) && decide (n ≤ 15)) = true := by
      simp only [Bool.and_eq_true, decide_eq_true_eq]; exact hrange
    simp only [htrue, ite_true] at hexec
    match hstk : ss.stack with
    | [] => simp [hstk] at hexec
    | top :: srest =>
      simp only [hstk] at hexec
      set p := srest.splitAt n with hp_def
      have hpsplit : p = srest.splitAt n := hp_def
      by_cases hlen : p.1.length == n
      · simp only [hlen, ite_true] at hexec
        have heq := Option.some.inj hexec
        have hss : ss' = { ss with stack := p.1 ++ [top] ++ p.2 } := (congrArg Prod.fst heq).symm
        have hpc : preconds = [] := (congrArg Prod.snd heq).symm
        subst hss; subst hpc
        have hsplit := @List.splitAt_eq _ n srest
        rw [← hpsplit] at hsplit
        have hlen_eq : p.1.length = n := by
          have := beq_iff_eq.mp hlen; omega
        have hstack' : cs.stack = Expr.eval σ top :: srest.map (Expr.eval σ) ++ rest := by
          rw [hstack, hstk, List.map_cons]
        refine ⟨cs.withStack (insertAt (srest.map (Expr.eval σ) ++ rest) n (top.eval σ)), ?_, ?_⟩
        · change execMovdn n cs = _
          unfold execMovdn
          have : ¬(n < 2) := by omega
          have : ¬(n > 15) := by omega
          simp_all [insertAt, Concrete.State.withStack]
        · constructor
          · simp only [Concrete.State.withStack]
            unfold insertAt
            simp only [List.map_append, List.map_cons, List.map_nil]
            have hp1 : p.1 = List.take n srest := congrArg Prod.fst hsplit
            have hp2 : p.2 = List.drop n srest := congrArg Prod.snd hsplit
            rw [hp1, hp2, List.map_take, List.map_drop]
            have hle : n ≤ srest.length := by
              have h1 : (List.take n srest).length = n := by rw [← hp1]; omega
              rw [List.length_take] at h1; omega
            have hle' : n ≤ (srest.map (Expr.eval σ)).length := by simp [hle]
            rw [List.take_append_of_le_length hle', List.drop_append_of_le_length hle']
            simp [List.append_assoc]
          · exact ⟨hmem, hframes, hadv⟩
      · simp [hlen] at hexec
  · have hfalse : (decide (2 ≤ n) && decide (n ≤ 15)) = false := by
      simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega
    simp [hfalse] at hexec

/-- Per-instruction soundness: if symbolic execution succeeds on instruction i
    with all preconditions satisfied, then concrete execution also succeeds
    and the resulting state models the symbolic result. -/
theorem execInstruction_sound
    (i : Instruction) (ss : State) (cs : Concrete.State)
    (σ : Assignment) (rest : List Felt)
    (ss' : State) (preconds : List Precondition)
    (hmodels : ss.models cs σ rest)
    (hexec : execInstruction ss i = some (ss', preconds))
    (hpreconds : ∀ p ∈ preconds, p.holds σ) :
    ∃ cs', MidenLean.execInstruction cs i = some cs'
      ∧ ss'.models cs' σ rest := by
  match i with
  | .drop =>
    exact execInstruction_sound_drop ss cs σ rest ss' preconds hmodels hexec hpreconds
  | .dup n =>
    exact execInstruction_sound_dup n ss cs σ rest ss' preconds hmodels hexec hpreconds
  | .swap n =>
    exact execInstruction_sound_swap n ss cs σ rest ss' preconds hmodels hexec hpreconds
  | .add =>
    exact execInstruction_sound_add ss cs σ rest ss' preconds hmodels hexec hpreconds
  | .sub =>
    exact execInstruction_sound_sub ss cs σ rest ss' preconds hmodels hexec hpreconds
  | .mul =>
    exact execInstruction_sound_mul ss cs σ rest ss' preconds hmodels hexec hpreconds
  | .u32WidenAdd =>
    exact execInstruction_sound_u32WidenAdd ss cs σ rest ss' preconds hmodels hexec hpreconds
  | .eq =>
    exact execInstruction_sound_eq ss cs σ rest ss' preconds hmodels hexec hpreconds
  | .and =>
    exact execInstruction_sound_and ss cs σ rest ss' preconds hmodels hexec hpreconds
  | .u32WidenAdd3 =>
    exact execInstruction_sound_u32WidenAdd3 ss cs σ rest ss' preconds hmodels hexec hpreconds
  | .u32OverflowSub =>
    exact execInstruction_sound_u32OverflowSub ss cs σ rest ss' preconds hmodels hexec hpreconds
  | .movup n =>
    exact execInstruction_sound_movup n ss cs σ rest ss' preconds hmodels hexec hpreconds
  | .movdn n =>
    exact execInstruction_sound_movdn n ss cs σ rest ss' preconds hmodels hexec hpreconds
  -- Batch 1: stack ops, field arithmetic/comparison
  | .nop =>
    exact execInstruction_sound_nop ss cs σ rest ss' preconds hmodels hexec hpreconds
  | .padw =>
    exact execInstruction_sound_padw ss cs σ rest ss' preconds hmodels hexec hpreconds
  | .push v =>
    exact execInstruction_sound_push v ss cs σ rest ss' preconds hmodels hexec hpreconds
  | .pushList vs =>
    exact execInstruction_sound_pushList vs ss cs σ rest ss' preconds hmodels hexec hpreconds
  | .dropw =>
    exact execInstruction_sound_dropw ss cs σ rest ss' preconds hmodels hexec hpreconds
  | .swapdw =>
    exact execInstruction_sound_swapdw ss cs σ rest ss' preconds hmodels hexec hpreconds
  | .reversew =>
    exact execInstruction_sound_reversew ss cs σ rest ss' preconds hmodels hexec hpreconds
  | .addImm v =>
    exact execInstruction_sound_addImm v ss cs σ rest ss' preconds hmodels hexec hpreconds
  | .subImm v =>
    exact execInstruction_sound_subImm v ss cs σ rest ss' preconds hmodels hexec hpreconds
  | .mulImm v =>
    exact execInstruction_sound_mulImm v ss cs σ rest ss' preconds hmodels hexec hpreconds
  | .neg =>
    exact execInstruction_sound_neg ss cs σ rest ss' preconds hmodels hexec hpreconds
  | .incr =>
    exact execInstruction_sound_incr ss cs σ rest ss' preconds hmodels hexec hpreconds
  | .eqImm v =>
    exact execInstruction_sound_eqImm v ss cs σ rest ss' preconds hmodels hexec hpreconds
  | .neq =>
    exact execInstruction_sound_neq ss cs σ rest ss' preconds hmodels hexec hpreconds
  | .neqImm v =>
    exact execInstruction_sound_neqImm v ss cs σ rest ss' preconds hmodels hexec hpreconds
  | .lt =>
    exact execInstruction_sound_lt ss cs σ rest ss' preconds hmodels hexec hpreconds
  | .lte =>
    exact execInstruction_sound_lte ss cs σ rest ss' preconds hmodels hexec hpreconds
  | .gt =>
    exact execInstruction_sound_gt ss cs σ rest ss' preconds hmodels hexec hpreconds
  | .gte =>
    exact execInstruction_sound_gte ss cs σ rest ss' preconds hmodels hexec hpreconds
  | .isOdd =>
    exact execInstruction_sound_isOdd ss cs σ rest ss' preconds hmodels hexec hpreconds
  -- Batch 2: boolean ops, field div/inv, assertions, u32 assertions/conversions
  | .or =>
    exact execInstruction_sound_or ss cs σ rest ss' preconds hmodels hexec hpreconds
  | .xor =>
    exact execInstruction_sound_xor ss cs σ rest ss' preconds hmodels hexec hpreconds
  | .not =>
    exact execInstruction_sound_not ss cs σ rest ss' preconds hmodels hexec hpreconds
  | .div =>
    exact execInstruction_sound_div ss cs σ rest ss' preconds hmodels hexec hpreconds
  | .divImm v =>
    exact execInstruction_sound_divImm v ss cs σ rest ss' preconds hmodels hexec hpreconds
  | .inv =>
    exact execInstruction_sound_inv ss cs σ rest ss' preconds hmodels hexec hpreconds
  | .pow2 =>
    exact execInstruction_sound_pow2 ss cs σ rest ss' preconds hmodels hexec hpreconds
  | .assert =>
    exact execInstruction_sound_assert ss cs σ rest ss' preconds hmodels hexec hpreconds
  | .assertWithError msg =>
    exact execInstruction_sound_assertWithError msg ss cs σ rest ss' preconds hmodels hexec hpreconds
  | .assertz =>
    exact execInstruction_sound_assertz ss cs σ rest ss' preconds hmodels hexec hpreconds
  | .assertzWithError msg =>
    exact execInstruction_sound_assertzWithError msg ss cs σ rest ss' preconds hmodels hexec hpreconds
  | .assertEq =>
    exact execInstruction_sound_assertEq ss cs σ rest ss' preconds hmodels hexec hpreconds
  | .assertEqWithError msg =>
    exact execInstruction_sound_assertEqWithError msg ss cs σ rest ss' preconds hmodels hexec hpreconds
  | .assertEqw =>
    exact execInstruction_sound_assertEqw ss cs σ rest ss' preconds hmodels hexec hpreconds
  | .eqw =>
    exact execInstruction_sound_eqw ss cs σ rest ss' preconds hmodels hexec hpreconds
  | .u32Assert =>
    exact execInstruction_sound_u32Assert ss cs σ rest ss' preconds hmodels hexec hpreconds
  | .u32Assert2 =>
    exact execInstruction_sound_u32Assert2 ss cs σ rest ss' preconds hmodels hexec hpreconds
  | .u32AssertW =>
    exact execInstruction_sound_u32AssertW ss cs σ rest ss' preconds hmodels hexec hpreconds
  | .u32Cast =>
    exact execInstruction_sound_u32Cast ss cs σ rest ss' preconds hmodels hexec hpreconds
  | .u32Split =>
    exact execInstruction_sound_u32Split ss cs σ rest ss' preconds hmodels hexec hpreconds
  -- Batch 3: u32 arithmetic
  | .u32OverflowAdd =>
    exact execInstruction_sound_u32OverflowAdd ss cs σ rest ss' preconds hmodels hexec hpreconds
  | .u32WrappingAdd =>
    exact execInstruction_sound_u32WrappingAdd ss cs σ rest ss' preconds hmodels hexec hpreconds
  | .u32OverflowAdd3 =>
    exact execInstruction_sound_u32OverflowAdd3 ss cs σ rest ss' preconds hmodels hexec hpreconds
  | .u32WrappingAdd3 =>
    exact execInstruction_sound_u32WrappingAdd3 ss cs σ rest ss' preconds hmodels hexec hpreconds
  | .u32WrappingSub =>
    exact execInstruction_sound_u32WrappingSub ss cs σ rest ss' preconds hmodels hexec hpreconds
  | .u32WidenMul =>
    exact execInstruction_sound_u32WidenMul ss cs σ rest ss' preconds hmodels hexec hpreconds
  | .u32WrappingMul =>
    exact execInstruction_sound_u32WrappingMul ss cs σ rest ss' preconds hmodels hexec hpreconds
  | .u32WidenMadd =>
    exact execInstruction_sound_u32WidenMadd ss cs σ rest ss' preconds hmodels hexec hpreconds
  | .u32WrappingMadd =>
    exact execInstruction_sound_u32WrappingMadd ss cs σ rest ss' preconds hmodels hexec hpreconds
  | .u32DivMod =>
    exact execInstruction_sound_u32DivMod ss cs σ rest ss' preconds hmodels hexec hpreconds
  | .u32Div =>
    exact execInstruction_sound_u32Div ss cs σ rest ss' preconds hmodels hexec hpreconds
  | .u32Mod =>
    exact execInstruction_sound_u32Mod ss cs σ rest ss' preconds hmodels hexec hpreconds
  -- Batch 4: u32 bitwise, shift/rotate, comparison
  | .u32And =>
    exact execInstruction_sound_u32And ss cs σ rest ss' preconds hmodels hexec hpreconds
  | .u32Or =>
    exact execInstruction_sound_u32Or ss cs σ rest ss' preconds hmodels hexec hpreconds
  | .u32Xor =>
    exact execInstruction_sound_u32Xor ss cs σ rest ss' preconds hmodels hexec hpreconds
  | .u32Not =>
    exact execInstruction_sound_u32Not ss cs σ rest ss' preconds hmodels hexec hpreconds
  | .u32Popcnt =>
    exact execInstruction_sound_u32Popcnt ss cs σ rest ss' preconds hmodels hexec hpreconds
  | .u32Clz =>
    exact execInstruction_sound_u32Clz ss cs σ rest ss' preconds hmodels hexec hpreconds
  | .u32Ctz =>
    exact execInstruction_sound_u32Ctz ss cs σ rest ss' preconds hmodels hexec hpreconds
  | .u32Clo =>
    exact execInstruction_sound_u32Clo ss cs σ rest ss' preconds hmodels hexec hpreconds
  | .u32Cto =>
    exact execInstruction_sound_u32Cto ss cs σ rest ss' preconds hmodels hexec hpreconds
  | .u32Shl =>
    exact execInstruction_sound_u32Shl ss cs σ rest ss' preconds hmodels hexec hpreconds
  | .u32Shr =>
    exact execInstruction_sound_u32Shr ss cs σ rest ss' preconds hmodels hexec hpreconds
  | .u32Rotl =>
    exact execInstruction_sound_u32Rotl ss cs σ rest ss' preconds hmodels hexec hpreconds
  | .u32Rotr =>
    exact execInstruction_sound_u32Rotr ss cs σ rest ss' preconds hmodels hexec hpreconds
  | .u32ShlImm n =>
    exact execInstruction_sound_u32ShlImm n ss cs σ rest ss' preconds hmodels hexec hpreconds
  | .u32ShrImm n =>
    exact execInstruction_sound_u32ShrImm n ss cs σ rest ss' preconds hmodels hexec hpreconds
  | .u32RotlImm n =>
    exact execInstruction_sound_u32RotlImm n ss cs σ rest ss' preconds hmodels hexec hpreconds
  | .u32RotrImm n =>
    exact execInstruction_sound_u32RotrImm n ss cs σ rest ss' preconds hmodels hexec hpreconds
  | .u32Lt =>
    exact execInstruction_sound_u32Lt ss cs σ rest ss' preconds hmodels hexec hpreconds
  | .u32Lte =>
    exact execInstruction_sound_u32Lte ss cs σ rest ss' preconds hmodels hexec hpreconds
  | .u32Gt =>
    exact execInstruction_sound_u32Gt ss cs σ rest ss' preconds hmodels hexec hpreconds
  | .u32Gte =>
    exact execInstruction_sound_u32Gte ss cs σ rest ss' preconds hmodels hexec hpreconds
  | .u32Min =>
    exact execInstruction_sound_u32Min ss cs σ rest ss' preconds hmodels hexec hpreconds
  | .u32Max =>
    exact execInstruction_sound_u32Max ss cs σ rest ss' preconds hmodels hexec hpreconds
  -- Complex stack ops
  | .dupw n =>
    exact execInstruction_sound_dupw n ss cs σ rest ss' preconds hmodels hexec hpreconds
  | .swapw n =>
    exact execInstruction_sound_swapw n ss cs σ rest ss' preconds hmodels hexec hpreconds
  | .movupw n =>
    exact execInstruction_sound_movupw n ss cs σ rest ss' preconds hmodels hexec hpreconds
  | .movdnw n =>
    exact execInstruction_sound_movdnw n ss cs σ rest ss' preconds hmodels hexec hpreconds
  -- Batch 5: emitImm (trivial: always succeeds, state unchanged)
  | .emitImm _ =>
    obtain ⟨hstack, hmem, hframes, hadv⟩ := hmodels
    simp only [execInstruction] at hexec
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hexec)
    exact ⟨cs, by simp only [MidenLean.execInstruction], hstack, hmem, hframes, hadv⟩
  -- emit (requires ≥ 1 element on stack, state unchanged)
  | .emit =>
    obtain ⟨hstack, hmem, hframes, hadv⟩ := hmodels
    simp only [execInstruction] at hexec
    match hstk : ss.stack with
    | [] => simp [hstk] at hexec
    | a :: tail =>
      simp only [hstk] at hexec
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hexec)
      refine ⟨cs, ?_, hstack, hmem, hframes, hadv⟩
      simp only [MidenLean.execInstruction, execEmit]
      rw [hstk, List.map_cons] at hstack; rw [hstack]; rfl
  -- locLoad idx
  | .locLoad idx =>
    obtain ⟨hstack, hmem, hframes, hadv⟩ := hmodels
    simp only [execInstruction] at hexec
    match hfr : ss.frames with
    | [] => simp [hfr] at hexec
    | frame :: frest =>
      simp only [hfr] at hexec
      by_cases hidx : idx < frame.numLocals
      · simp only [hidx, ite_true] at hexec
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hexec)
        refine ⟨cs.withStack (cs.memory (frame.localAddr idx) :: cs.stack), ?_, ?_⟩
        · simp only [MidenLean.execInstruction, execLocLoad, Concrete.State.readLocal?,
              Concrete.State.localAddr?, hframes, hfr, hidx, ite_true,
              Concrete.State.withStack, hstack]; rfl
        · unfold State.models
          refine ⟨?_, hmem, ?_, hadv⟩
          · simp only [Concrete.State.withStack, List.map_cons, List.cons_append, hstack]
            rw [hmem (frame.localAddr idx)]
          · simp only [Concrete.State.withStack, hframes, hfr]
      · simp [hidx] at hexec
  -- locStore idx
  | .locStore idx =>
    obtain ⟨hstack, hmem, hframes, hadv⟩ := hmodels
    simp only [execInstruction] at hexec
    match hstk : ss.stack, hfr : ss.frames with
    | [], _ => simp [hstk] at hexec
    | _, [] => simp [hfr] at hexec
    | v :: tail, frame :: frest =>
      simp only [hstk, hfr] at hexec
      by_cases hidx : idx < frame.numLocals
      · simp only [hidx, ite_true] at hexec
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hexec)
        let addr := frame.localAddr idx
        refine ⟨(cs.writeMemory addr (v.eval σ)).withStack (tail.map (Expr.eval σ) ++ rest), ?_, ?_⟩
        · simp only [MidenLean.execInstruction, execLocStore, Concrete.State.writeLocal?,
              Concrete.State.localAddr?, hframes, hfr, hidx, ite_true,
              Concrete.State.writeMemory, Concrete.State.withStack]
          rw [hstk, List.map_cons] at hstack; rw [hstack]; rfl
        · refine ⟨by simp only [Concrete.State.withStack], ?_, ?_, ?_⟩
          · intro a; simp only [Concrete.State.withStack, Concrete.State.writeMemory]
            split <;> [rfl; exact hmem a]
          · simp only [Concrete.State.withStack, Concrete.State.writeMemory]; rw [hframes, hfr]
          · simp only [Concrete.State.withStack, Concrete.State.writeMemory]; exact hadv
      · simp [hidx] at hexec
  -- locaddr idx
  | .locaddr idx =>
    obtain ⟨hstack, hmem, hframes, hadv⟩ := hmodels
    simp only [execInstruction] at hexec
    match hfr : ss.frames with
    | [] => simp [hfr] at hexec
    | frame :: frest =>
      simp only [hfr] at hexec
      by_cases hidx : idx < frame.numLocals
      · simp only [hidx, ite_true] at hexec
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hexec)
        refine ⟨cs.withStack (Felt.ofNat (frame.localAddr idx) :: cs.stack), ?_, ?_⟩
        · simp only [MidenLean.execInstruction, execLocAddr, Concrete.State.localAddr?,
              hframes, hfr, hidx, ite_true, Concrete.State.withStack, hstack]; rfl
        · unfold State.models
          refine ⟨?_, hmem, ?_, hadv⟩
          · simp only [Concrete.State.withStack, List.map_cons, Expr.eval, List.cons_append, hstack]
          · simp only [Concrete.State.withStack, hframes, hfr]
      · simp [hidx] at hexec
  -- memLoadImm addr
  | .memLoadImm addr =>
    obtain ⟨hstack, hmem, hframes, hadv⟩ := hmodels
    simp only [execInstruction] at hexec
    by_cases haddr : addr ≥ u32Max
    · simp [haddr] at hexec
    · have hlt : ¬(addr ≥ u32Max) := haddr
      simp only [hlt, ite_false] at hexec
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hexec)
      refine ⟨cs.withStack (cs.memory addr :: cs.stack), ?_, ?_⟩
      · simp only [MidenLean.execInstruction, execMemLoadImm, hlt, ite_false,
            Concrete.State.withStack, hstack]
      · refine ⟨?_, hmem, hframes, hadv⟩
        simp only [Concrete.State.withStack, List.map_cons, List.cons_append, hstack]
        rw [hmem addr]
  -- memStoreImm addr
  | .memStoreImm addr =>
    obtain ⟨hstack, hmem, hframes, hadv⟩ := hmodels
    simp only [execInstruction] at hexec
    match hstk : ss.stack with
    | [] => simp [hstk] at hexec
    | v :: tail =>
      simp only [hstk] at hexec
      by_cases haddr : addr ≥ u32Max
      · simp [haddr] at hexec
      · have hlt : ¬(addr ≥ u32Max) := haddr
        simp only [hlt, ite_false] at hexec
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hexec)
        refine ⟨(cs.writeMemory addr (v.eval σ)).withStack (tail.map (Expr.eval σ) ++ rest), ?_, ?_⟩
        · simp only [MidenLean.execInstruction, execMemStoreImm, Concrete.State.writeMemory,
              Concrete.State.withStack]
          rw [hstk, List.map_cons] at hstack; rw [hstack]; simp [hlt]
        · refine ⟨by simp only [Concrete.State.withStack], ?_, ?_, ?_⟩
          · intro a; simp only [Concrete.State.withStack, Concrete.State.writeMemory]
            split <;> [rfl; exact hmem a]
          · simp only [Concrete.State.withStack, Concrete.State.writeMemory, hframes]
          · simp only [Concrete.State.withStack, Concrete.State.writeMemory, hadv]
  -- advPush n
  | .advPush n =>
    obtain ⟨hstack, hmem, hframes, hadv⟩ := hmodels
    simp only [execInstruction] at hexec
    by_cases hlen : ss.advice.length < n
    · simp [hlen] at hexec
    · have hge : ¬(ss.advice.length < n) := hlen
      simp only [hge, ite_false] at hexec
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hexec)
      refine ⟨(cs.withAdvice (cs.advice.drop n)).withStack
               ((cs.advice.take n).reverse ++ cs.stack), ?_, ?_⟩
      · simp only [MidenLean.execInstruction, execAdvPush]
        rw [hadv]; simp only [List.length_map, hge, ite_false,
            Concrete.State.withAdvice, Concrete.State.withStack, hstack]
      · unfold State.models; refine ⟨?_, ?_, ?_, ?_⟩
        · simp only [Concrete.State.withStack, Concrete.State.withAdvice,
              List.map_reverse, List.map_append, List.map_take, hstack]
          rw [hadv, List.append_assoc]
        · intro a; simp only [Concrete.State.withStack, Concrete.State.withAdvice]; exact hmem a
        · simp only [Concrete.State.withStack, Concrete.State.withAdvice, hframes]
        · simp only [Concrete.State.withStack, Concrete.State.withAdvice]
          rw [hadv, List.map_drop]
  -- advLoadW
  | .advLoadW =>
    obtain ⟨hstack, hmem, hframes, hadv⟩ := hmodels
    simp only [execInstruction] at hexec
    match hstk : ss.stack with
    | _ :: _ :: _ :: _ :: srest =>
      simp only [hstk] at hexec
      by_cases hlen : ss.advice.length < 4
      · simp [hlen] at hexec
      · have hge : ¬(ss.advice.length < 4) := hlen
        simp only [hge, ite_false] at hexec
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hexec)
        refine ⟨(cs.withAdvice (cs.advice.drop 4)).withStack
                 (cs.advice.take 4 ++ srest.map (Expr.eval σ) ++ rest), ?_, ?_⟩
        · rw [hstk, List.map_cons, List.map_cons, List.map_cons, List.map_cons] at hstack
          simp only [MidenLean.execInstruction, execAdvLoadW, hstack, hadv,
              List.length_map, hge, ite_false, Concrete.State.withAdvice, Concrete.State.withStack,
              List.cons_append, List.append_assoc]
        · unfold State.models; refine ⟨?_, ?_, ?_, ?_⟩
          · simp only [Concrete.State.withStack, Concrete.State.withAdvice,
                List.map_append, List.map_take]
            rw [hadv]
          · intro a; simp only [Concrete.State.withStack, Concrete.State.withAdvice]; exact hmem a
          · simp only [Concrete.State.withStack, Concrete.State.withAdvice, hframes]
          · simp only [Concrete.State.withStack, Concrete.State.withAdvice]
            rw [hadv, List.map_drop]
    | [] | [_] | [_, _] | [_, _, _] => simp [hstk] at hexec
  -- memLoadwBeImm addr (big-endian word load from static address)
  | .memLoadwBeImm addr =>
    obtain ⟨hstack, hmem, hframes, hadv⟩ := hmodels
    simp only [execInstruction] at hexec
    match hstk : ss.stack with
    | _ :: _ :: _ :: _ :: srest =>
      simp only [hstk] at hexec
      by_cases haddr : addr ≥ u32Max ∨ addr % 4 ≠ 0
      · rcases haddr with hge | hmod
        · simp [hge] at hexec
        · simp [hmod] at hexec
      · push_neg at haddr
        obtain ⟨hlt, hmod⟩ := haddr
        simp [hlt, hmod] at hexec
        obtain ⟨rfl, rfl⟩ := hexec
        refine ⟨cs.withStack (cs.memory (addr + 3) :: cs.memory (addr + 2) ::
          cs.memory (addr + 1) :: cs.memory addr :: srest.map (Expr.eval σ) ++ rest), ?_, ?_⟩
        · rw [hstk, List.map_cons, List.map_cons, List.map_cons, List.map_cons] at hstack
          simp only [MidenLean.execInstruction, execMemLoadwBeImm, hstack, Concrete.State.withStack]
          simp [hlt, hmod]
        · refine ⟨?_, hmem, hframes, hadv⟩
          simp only [Concrete.State.withStack, List.map_cons, List.cons_append]
          rw [hmem addr, hmem (addr + 1), hmem (addr + 2), hmem (addr + 3)]
    | [] | [_] | [_, _] | [_, _, _] => simp [hstk] at hexec
  -- memLoadwLeImm addr (little-endian word load from static address)
  | .memLoadwLeImm addr =>
    obtain ⟨hstack, hmem, hframes, hadv⟩ := hmodels
    simp only [execInstruction] at hexec
    match hstk : ss.stack with
    | _ :: _ :: _ :: _ :: srest =>
      simp only [hstk] at hexec
      by_cases haddr : addr ≥ u32Max ∨ addr % 4 ≠ 0
      · rcases haddr with hge | hmod
        · simp [hge] at hexec
        · simp [hmod] at hexec
      · push_neg at haddr
        obtain ⟨hlt, hmod⟩ := haddr
        simp [hlt, hmod] at hexec
        obtain ⟨rfl, rfl⟩ := hexec
        refine ⟨cs.withStack (cs.memory addr :: cs.memory (addr + 1) ::
          cs.memory (addr + 2) :: cs.memory (addr + 3) :: srest.map (Expr.eval σ) ++ rest), ?_, ?_⟩
        · rw [hstk, List.map_cons, List.map_cons, List.map_cons, List.map_cons] at hstack
          simp only [MidenLean.execInstruction, execMemLoadwLeImm, hstack, Concrete.State.withStack]
          simp [hlt, hmod]
        · refine ⟨?_, hmem, hframes, hadv⟩
          simp only [Concrete.State.withStack, List.map_cons, List.cons_append]
          rw [hmem addr, hmem (addr + 1), hmem (addr + 2), hmem (addr + 3)]
    | [] | [_] | [_, _] | [_, _, _] => simp [hstk] at hexec
  -- memStorewBeImm addr (big-endian word store to static address)
  | .memStorewBeImm addr =>
    obtain ⟨hstack, hmem, hframes, hadv⟩ := hmodels
    simp only [execInstruction] at hexec
    match hstk : ss.stack with
    | e0 :: e1 :: e2 :: e3 :: srest =>
      simp only [hstk] at hexec
      by_cases haddr : addr ≥ u32Max ∨ addr % 4 ≠ 0
      · rcases haddr with hge | hmod
        · simp [hge] at hexec
        · simp [hmod] at hexec
      · push_neg at haddr
        obtain ⟨hlt, hmod⟩ := haddr
        simp [hlt, hmod] at hexec
        obtain ⟨rfl, rfl⟩ := hexec
        refine ⟨(((cs.writeMemory addr (e3.eval σ)).writeMemory (addr + 1) (e2.eval σ)).writeMemory
          (addr + 2) (e1.eval σ) |>.writeMemory (addr + 3) (e0.eval σ)).withStack
          (e0.eval σ :: e1.eval σ :: e2.eval σ :: e3.eval σ ::
          srest.map (Expr.eval σ) ++ rest), ?_, ?_⟩
        · rw [hstk, List.map_cons, List.map_cons, List.map_cons, List.map_cons] at hstack
          simp only [MidenLean.execInstruction, execMemStorewBeImm, hstack,
              Concrete.State.writeMemory, Concrete.State.withStack]
          simp [hlt, hmod]
        · refine ⟨by simp only [Concrete.State.withStack, List.map_cons, List.cons_append], ?_, ?_, ?_⟩
          · intro a; simp only [Concrete.State.withStack, Concrete.State.writeMemory]
            split_ifs <;> simp_all
          · simp only [Concrete.State.withStack, Concrete.State.writeMemory, hframes]
          · simp only [Concrete.State.withStack, Concrete.State.writeMemory, hadv]
    | [] | [_] | [_, _] | [_, _, _] => simp [hstk] at hexec
  -- memStorewLeImm addr (little-endian word store to static address)
  | .memStorewLeImm addr =>
    obtain ⟨hstack, hmem, hframes, hadv⟩ := hmodels
    simp only [execInstruction] at hexec
    match hstk : ss.stack with
    | e0 :: e1 :: e2 :: e3 :: srest =>
      simp only [hstk] at hexec
      by_cases haddr : addr ≥ u32Max ∨ addr % 4 ≠ 0
      · rcases haddr with hge | hmod
        · simp [hge] at hexec
        · simp [hmod] at hexec
      · push_neg at haddr
        obtain ⟨hlt, hmod⟩ := haddr
        simp [hlt, hmod] at hexec
        obtain ⟨rfl, rfl⟩ := hexec
        refine ⟨(((cs.writeMemory addr (e0.eval σ)).writeMemory (addr + 1) (e1.eval σ)).writeMemory
          (addr + 2) (e2.eval σ) |>.writeMemory (addr + 3) (e3.eval σ)).withStack
          (e0.eval σ :: e1.eval σ :: e2.eval σ :: e3.eval σ ::
          srest.map (Expr.eval σ) ++ rest), ?_, ?_⟩
        · rw [hstk, List.map_cons, List.map_cons, List.map_cons, List.map_cons] at hstack
          simp only [MidenLean.execInstruction, execMemStorewLeImm, hstack,
              Concrete.State.writeMemory, Concrete.State.withStack]
          simp [hlt, hmod]
        · refine ⟨by simp only [Concrete.State.withStack, List.map_cons, List.cons_append], ?_, ?_, ?_⟩
          · intro a; simp only [Concrete.State.withStack, Concrete.State.writeMemory]
            split_ifs <;> simp_all
          · simp only [Concrete.State.withStack, Concrete.State.writeMemory, hframes]
          · simp only [Concrete.State.withStack, Concrete.State.writeMemory, hadv]
    | [] | [_] | [_, _] | [_, _, _] => simp [hstk] at hexec
  -- locLoadwBe idx (big-endian word load from local frame)
  | .locLoadwBe idx =>
    obtain ⟨hstack, hmem, hframes, hadv⟩ := hmodels
    simp only [execInstruction] at hexec
    match hstk : ss.stack, hfr : ss.frames with
    | _ :: _ :: _ :: _ :: srest, frame :: frest =>
      simp only [hstk, hfr, currentFrame, List.head?] at hexec
      by_cases hguard : idx % 4 ≠ 0 ∨ idx + 4 > frame.numLocals
      · rcases hguard with hmod | hgt
        · simp [hmod] at hexec
        · simp [hgt] at hexec
      · push_neg at hguard
        obtain ⟨hmod, hle⟩ := hguard
        simp [hmod, hle] at hexec
        obtain ⟨rfl, rfl⟩ := hexec
        refine ⟨cs.withStack (cs.memory (frame.localAddr idx + 3) ::
          cs.memory (frame.localAddr idx + 2) :: cs.memory (frame.localAddr idx + 1) ::
          cs.memory (frame.localAddr idx) :: srest.map (Expr.eval σ) ++ rest), ?_, ?_⟩
        · rw [hstk, List.map_cons, List.map_cons, List.map_cons, List.map_cons] at hstack
          simp only [MidenLean.execInstruction, execLocLoadwBe, hstack, currentFrame,
              hframes, hfr, List.head?, Concrete.State.withStack]
          simp [hmod, hle]
        · unfold State.models
          refine ⟨?_, ?_, ?_, ?_⟩
          · simp only [Concrete.State.withStack, List.map_cons, List.cons_append]
            rw [hmem, hmem, hmem, hmem]
          · intro a; exact hmem a
          · simp only [Concrete.State.withStack]; rw [hframes, hfr]
          · simp only [Concrete.State.withStack]; exact hadv
    | [], _ => simp [hstk] at hexec
    | [_], _ => simp [hstk] at hexec
    | [_, _], _ => simp [hstk] at hexec
    | [_, _, _], _ => simp [hstk] at hexec
    | _ :: _ :: _ :: _ :: _, [] =>
      simp [hstk, hfr, currentFrame, List.head?] at hexec
  -- locLoadwLe idx (little-endian word load from local frame)
  | .locLoadwLe idx =>
    obtain ⟨hstack, hmem, hframes, hadv⟩ := hmodels
    simp only [execInstruction] at hexec
    match hstk : ss.stack, hfr : ss.frames with
    | _ :: _ :: _ :: _ :: srest, frame :: frest =>
      simp only [hstk, hfr, currentFrame, List.head?] at hexec
      by_cases hguard : idx % 4 ≠ 0 ∨ idx + 4 > frame.numLocals
      · rcases hguard with hmod | hgt
        · simp [hmod] at hexec
        · simp [hgt] at hexec
      · push_neg at hguard
        obtain ⟨hmod, hle⟩ := hguard
        simp [hmod, hle] at hexec
        obtain ⟨rfl, rfl⟩ := hexec
        refine ⟨cs.withStack (cs.memory (frame.localAddr idx) ::
          cs.memory (frame.localAddr idx + 1) :: cs.memory (frame.localAddr idx + 2) ::
          cs.memory (frame.localAddr idx + 3) :: srest.map (Expr.eval σ) ++ rest), ?_, ?_⟩
        · rw [hstk, List.map_cons, List.map_cons, List.map_cons, List.map_cons] at hstack
          simp only [MidenLean.execInstruction, execLocLoadwLe, hstack, currentFrame,
              hframes, hfr, List.head?, Concrete.State.withStack]
          simp [hmod, hle]
        · unfold State.models
          refine ⟨?_, ?_, ?_, ?_⟩
          · simp only [Concrete.State.withStack, List.map_cons, List.cons_append]
            rw [hmem, hmem, hmem, hmem]
          · intro a; exact hmem a
          · simp only [Concrete.State.withStack]; rw [hframes, hfr]
          · simp only [Concrete.State.withStack]; exact hadv
    | [], _ => simp [hstk] at hexec
    | [_], _ => simp [hstk] at hexec
    | [_, _], _ => simp [hstk] at hexec
    | [_, _, _], _ => simp [hstk] at hexec
    | _ :: _ :: _ :: _ :: _, [] =>
      simp [hstk, hfr, currentFrame, List.head?] at hexec
  -- locStorewBe idx (big-endian word store to local frame)
  | .locStorewBe idx =>
    obtain ⟨hstack, hmem, hframes, hadv⟩ := hmodels
    simp only [execInstruction] at hexec
    match hstk : ss.stack, hfr : ss.frames with
    | e0 :: e1 :: e2 :: e3 :: srest, frame :: frest =>
      simp only [hstk, hfr, currentFrame, List.head?] at hexec
      by_cases hguard : idx % 4 ≠ 0 ∨ idx + 4 > frame.numLocals
      · rcases hguard with hmod | hgt
        · simp [hmod] at hexec
        · simp [hgt] at hexec
      · push_neg at hguard
        obtain ⟨hmod, hle⟩ := hguard
        simp [hmod, hle] at hexec
        obtain ⟨rfl, rfl⟩ := hexec
        refine ⟨(((cs.writeMemory (frame.localAddr idx) (e3.eval σ)).writeMemory
          (frame.localAddr idx + 1) (e2.eval σ)).writeMemory (frame.localAddr idx + 2) (e1.eval σ)
          |>.writeMemory (frame.localAddr idx + 3) (e0.eval σ)).withStack
          (e0.eval σ :: e1.eval σ :: e2.eval σ :: e3.eval σ ::
          srest.map (Expr.eval σ) ++ rest), ?_, ?_⟩
        · rw [hstk, List.map_cons, List.map_cons, List.map_cons, List.map_cons] at hstack
          simp only [MidenLean.execInstruction, execLocStorewBe, hstack, currentFrame,
              hframes, hfr, List.head?, Concrete.State.writeMemory, Concrete.State.withStack]
          simp [hmod, hle]
        · unfold State.models
          refine ⟨by simp only [Concrete.State.withStack, List.map_cons, List.cons_append], ?_, ?_, ?_⟩
          · intro a; simp only [Concrete.State.withStack, Concrete.State.writeMemory]
            split_ifs <;> simp_all
          · simp only [Concrete.State.withStack, Concrete.State.writeMemory]; rw [hframes, hfr]
          · simp only [Concrete.State.withStack, Concrete.State.writeMemory]; exact hadv
    | [], _ => simp [hstk] at hexec
    | [_], _ => simp [hstk] at hexec
    | [_, _], _ => simp [hstk] at hexec
    | [_, _, _], _ => simp [hstk] at hexec
    | _ :: _ :: _ :: _ :: _, [] =>
      simp [hstk, hfr, currentFrame, List.head?] at hexec
  -- locStorewLe idx (little-endian word store to local frame)
  | .locStorewLe idx =>
    obtain ⟨hstack, hmem, hframes, hadv⟩ := hmodels
    simp only [execInstruction] at hexec
    match hstk : ss.stack, hfr : ss.frames with
    | e0 :: e1 :: e2 :: e3 :: srest, frame :: frest =>
      simp only [hstk, hfr, currentFrame, List.head?] at hexec
      by_cases hguard : idx % 4 ≠ 0 ∨ idx + 4 > frame.numLocals
      · rcases hguard with hmod | hgt
        · simp [hmod] at hexec
        · simp [hgt] at hexec
      · push_neg at hguard
        obtain ⟨hmod, hle⟩ := hguard
        simp [hmod, hle] at hexec
        obtain ⟨rfl, rfl⟩ := hexec
        refine ⟨(((cs.writeMemory (frame.localAddr idx) (e0.eval σ)).writeMemory
          (frame.localAddr idx + 1) (e1.eval σ)).writeMemory (frame.localAddr idx + 2) (e2.eval σ)
          |>.writeMemory (frame.localAddr idx + 3) (e3.eval σ)).withStack
          (e0.eval σ :: e1.eval σ :: e2.eval σ :: e3.eval σ ::
          srest.map (Expr.eval σ) ++ rest), ?_, ?_⟩
        · rw [hstk, List.map_cons, List.map_cons, List.map_cons, List.map_cons] at hstack
          simp only [MidenLean.execInstruction, execLocStorewLe, hstack, currentFrame,
              hframes, hfr, List.head?, Concrete.State.writeMemory, Concrete.State.withStack]
          simp [hmod, hle]
        · unfold State.models
          refine ⟨by simp only [Concrete.State.withStack, List.map_cons, List.cons_append], ?_, ?_, ?_⟩
          · intro a; simp only [Concrete.State.withStack, Concrete.State.writeMemory]
            split_ifs <;> simp_all
          · simp only [Concrete.State.withStack, Concrete.State.writeMemory]; rw [hframes, hfr]
          · simp only [Concrete.State.withStack, Concrete.State.writeMemory]; exact hadv
    | [], _ => simp [hstk] at hexec
    | [_], _ => simp [hstk] at hexec
    | [_, _], _ => simp [hstk] at hexec
    | [_, _, _], _ => simp [hstk] at hexec
    | _ :: _ :: _ :: _ :: _, [] =>
      simp [hstk, hfr, currentFrame, List.head?] at hexec
  -- Conditional swap/drop
  | .cswap =>
    exact execInstruction_sound_cswap ss cs σ rest ss' preconds hmodels hexec hpreconds
  | .cswapw =>
    exact execInstruction_sound_cswapw ss cs σ rest ss' preconds hmodels hexec hpreconds
  | .cdrop =>
    exact execInstruction_sound_cdrop ss cs σ rest ss' preconds hmodels hexec hpreconds
  | .cdropw =>
    exact execInstruction_sound_cdropw ss cs σ rest ss' preconds hmodels hexec hpreconds
  -- U32 type tests
  | .u32Test =>
    exact execInstruction_sound_u32Test ss cs σ rest ss' preconds hmodels hexec hpreconds
  | .u32TestW =>
    exact execInstruction_sound_u32TestW ss cs σ rest ss' preconds hmodels hexec hpreconds
  -- Instructions that return none in execInstruction (unsupported symbolically)
  | .memLoad | .memStore
  | .memLoadwBe | .memStorewBe
  | .memLoadwLe | .memStorewLe
  | .exec _ =>
    simp [execInstruction] at hexec

-- Block-level soundness: `execBlock_sound` is stated below, after the
-- `execOp` fold induction it is derived from (see `execOps_map_inst_eq_execBlock`).

-- ============================================================================
-- Bridge: execProcedure → Concrete.execBlock (generalized)
-- ============================================================================

/-- Boolean predicate: is this instruction an `exec` call? -/
def isExecInst : Instruction → Bool
  | .exec _ => true
  | _ => false

/-- For a non-`exec` instruction, opStep at any env and fuel equals execInstruction. -/
private theorem opStep_inst_non_exec
    (env : MidenLean.ProcEnv) (fuel : Nat) (s : Concrete.State) (i : Instruction)
    (hi : isExecInst i = false) :
    MidenLean.opStep env fuel s (.inst i) = MidenLean.execInstruction s i := by
  unfold MidenLean.opStep
  cases i with
  | exec _ => simp [isExecInst] at hi
  | _ => rfl

/-- Under the empty concrete environment, `opStep` agrees with the concrete
    `execInstruction` on every instruction — including `exec`, where both
    fail with `none`. -/
private theorem opStep_inst_emptyEnv
    (fuel : Nat) (s : Concrete.State) (i : Instruction) :
    MidenLean.opStep MidenLean.emptyEnv fuel s (.inst i) =
    MidenLean.execInstruction s i := by
  cases i <;> rfl

/-- foldlM of opStep over (insts.map Op.inst) equals Concrete.execBlock
    whenever opStep agrees with the concrete execInstruction on every listed
    instruction (e.g. no `exec` calls, or the empty environment). -/
private theorem foldlM_opStep_eq_concreteExecBlock
    (env : MidenLean.ProcEnv) (fuel : Nat)
    (insts : List Instruction) (s : Concrete.State)
    (hagree : ∀ i ∈ insts, ∀ st, MidenLean.opStep env fuel st (.inst i) =
      MidenLean.execInstruction st i) :
    (insts.map Op.inst).foldlM (MidenLean.opStep env fuel) s =
    Concrete.execBlock insts s := by
  induction insts generalizing s with
  | nil => rfl
  | cons i rest ih =>
    simp only [List.map_cons, List.foldlM, bind, Bind.bind, Option.bind,
               Concrete.execBlock]
    rw [hagree i (List.mem_cons_self ..) s]
    match MidenLean.execInstruction s i with
    | none => rfl
    | some s' =>
      exact ih s' (fun j hj st => hagree j (List.mem_cons_of_mem _ hj) st)

/-- The pointwise-agreement premise of `foldlM_opStep_eq_concreteExecBlock`,
    discharged from a no-`exec` hypothesis. -/
private theorem opStep_agree_of_noexec
    (env : MidenLean.ProcEnv) (fuel : Nat) (insts : List Instruction)
    (hnoexec : insts.all (fun i => !isExecInst i) = true) :
    ∀ i ∈ insts, ∀ st, MidenLean.opStep env fuel st (.inst i) =
      MidenLean.execInstruction st i := fun i hi st =>
  opStep_inst_non_exec env fuel st i
    (Bool.not_eq_true' _ ▸ List.all_eq_true.mp hnoexec i hi)

/-- For a basic block with numLocals = 0,
    execProcedure reduces to Concrete.execBlock. -/
theorem execProcedure_basic_block_zero
    (env : MidenLean.ProcEnv) (fuel : Nat) (s : Concrete.State)
    (insts : List Instruction) (name : String) (ops : List Op)
    (hops : ops = insts.map Op.inst)
    (hfuel : fuel > 0)
    (hnoexec : insts.all (fun i => !isExecInst i) = true) :
    MidenLean.execProcedure env fuel s ⟨name, 0, ops⟩ =
    Concrete.execBlock insts s := by
  obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 1 := ⟨fuel - 1, by omega⟩
  rw [MidenLean.execProcedure_succ_zero]
  rw [hops]
  exact foldlM_opStep_eq_concreteExecBlock env n insts s
    (opStep_agree_of_noexec env n insts hnoexec)

/-- For a basic block with numLocals > 0,
    execProcedure reduces to frame-push + Concrete.execBlock + frame-pop. -/
theorem execProcedure_basic_block_locals
    (env : MidenLean.ProcEnv) (fuel : Nat) (s : Concrete.State)
    (insts : List Instruction) (name : String) (k : Nat) (ops : List Op)
    (hops : ops = insts.map Op.inst)
    (hfuel : fuel > 0)
    (hnoexec : insts.all (fun i => !isExecInst i) = true) :
    MidenLean.execProcedure env fuel s ⟨name, k + 1, ops⟩ =
    let aligned := MidenLean.alignLocals (k + 1)
    let frame : MidenLean.LocalFrame := { base := MidenLean.localsBase s.frames,
                                           numLocals := k + 1,
                                           alignedNumLocals := aligned }
    let s' := { s with frames := frame :: s.frames }
    match Concrete.execBlock insts s' with
    | some r => some { r with frames := s.frames }
    | none => none := by
  obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 1 := ⟨fuel - 1, by omega⟩
  show MidenLean.execProcedure env (n + 1) s ⟨name, k + 1, ops⟩ = _
  rw [MidenLean.execProcedure_succ_locals]
  simp only []
  rw [hops]
  rw [foldlM_opStep_eq_concreteExecBlock env n insts _
    (opStep_agree_of_noexec env n insts hnoexec)]
  rfl

/-- Symbolic execInstruction never modifies the frames field. -/
private theorem execInstruction_preserves_frames
    (ss : State) (i : Instruction) (ss' : State) (pc : List Precondition)
    (h : execInstruction ss i = some (ss', pc)) :
    ss'.frames = ss.frames := by
  -- Every handler in `execInstruction` either fails (`none`) or succeeds with
  -- a state built by `{ ss with stack/memory/advice := _ }`, never rewriting
  -- `.frames`.  So after exposing each handler's branches with `split`, a
  -- branch is either `none = some _` (closed by `cases h`) or `some (s', pc')
  -- = some (ss', pc)` (injected and substituted by `cases h`), after which
  -- `s'.frames = ss.frames` holds definitionally.
  unfold execInstruction at h
  cases i <;> simp only [] at h <;>
    (repeat' split at h) <;>
    cases h <;> rfl

/-- foldlM of execBlockStep preserves frames. -/
private theorem foldlM_execBlockStep_preserves_frames
    (insts : List Instruction) (s : State) (acc : List Precondition)
    (fs : State) (fp : List Precondition)
    (hf : insts.foldlM execBlockStep (s, acc) = some (fs, fp)) :
    fs.frames = s.frames := by
  induction insts generalizing s acc fs fp with
  | nil =>
    simp only [List.foldlM] at hf
    exact (congrArg (fun p => p.1.frames) (Option.some.inj hf)).symm
  | cons i rest ih =>
    simp only [List.foldlM, bind, Bind.bind, Option.bind, execBlockStep] at hf
    match hstep : execInstruction s i with
    | none => simp [hstep] at hf
    | some (s1, pc1) =>
      simp only [hstep] at hf
      have hfr := execInstruction_preserves_frames s i s1 pc1 hstep
      have := ih s1 (pc1.reverse ++ acc) fs fp hf
      rw [this, hfr]

/-- Symbolic execBlock never modifies the frames field. -/
theorem execBlock_preserves_frames
    (insts : List Instruction) (ss : State)
    (result : BlockResult)
    (h : execBlock insts ss = some result) :
    result.state.frames = ss.frames := by
  unfold execBlock at h
  match hfold : insts.foldlM execBlockStep (ss, []) with
  | none => simp [hfold] at h
  | some (final_ss, final_preconds) =>
    simp only [hfold, Option.some.injEq] at h
    have hstate : result.state = final_ss := (congrArg BlockResult.state h).symm
    rw [hstate]
    exact foldlM_execBlockStep_preserves_frames insts ss [] final_ss final_preconds hfold

-- Bridge: execProcedure emptyEnv → Concrete.execBlock

-- ============================================================================
-- Call-site soundness: Spec.sound, execOp_sound, execOps_sound
-- ============================================================================

/-- A Spec is sound w.r.t. a concrete procedure at a given minimum fuel level:
    whenever the symbolic spec succeeds and its preconditions hold, the concrete
    execution also succeeds and models the symbolic result for any fuel ≥ minFuel. -/
def Spec.sound (spec : Spec) (env : MidenLean.ProcEnv) (minFuel : Nat)
    (callee : Procedure) : Prop :=
  ∀ ss cs σ rest result fuel,
    fuel ≥ minFuel →
    spec.transform ss = some result →
    ss.models cs σ rest →
    (∀ p ∈ result.preconditions, p.holds σ) →
    ∃ cs', MidenLean.execProcedure env fuel cs callee = some cs'
      ∧ result.state.models cs' σ rest

/-- For a non-`exec` instruction, execOp delegates to the symbolic execInstruction. -/
private theorem execOp_inst_non_exec
    (senv : ProcEnv) (acc : BlockResult) (i : Instruction)
    (hi : ∀ t, i ≠ .exec t) :
    execOp senv acc (.inst i) =
      (execInstruction acc.state i).bind fun ⟨s', preconds⟩ =>
        some { state := s', preconditions := acc.preconditions ++ preconds } := by
  unfold execOp
  cases i with
  | exec t => exact absurd rfl (hi t)
  | _ => rfl

/-- Exec case of `execOp_preconds_prefix`: on an `exec` op the output
    accumulates all input preconditions. -/
private theorem execOp_exec_preconds_prefix
    (senv : ProcEnv) (acc acc' : BlockResult) (target : String)
    (h : execOp senv acc (.inst (.exec target)) = some acc')
    (p : Precondition) (hp : p ∈ acc.preconditions) :
    p ∈ acc'.preconditions := by
  simp only [execOp] at h
  match hsenv : senv target with
  | some spec =>
    simp only [hsenv] at h
    match htrans : spec.transform acc.state with
    | some result =>
      simp only [htrans] at h
      rw [← Option.some.inj h]; exact List.mem_append_left _ hp
    | none => simp [htrans] at h
  | none => simp [hsenv] at h

/-- Exec case of `execOp_sound`: an `exec` op is sound provided the target's
    symbolic spec is backed by a sound concrete callee. -/
private theorem execOp_exec_sound
    (senv : ProcEnv) (env : MidenLean.ProcEnv) (minFuel : Nat)
    (target : String) (acc acc' : BlockResult) (cs : Concrete.State)
    (σ : Assignment) (rest : List Felt)
    (hmodels : acc.state.models cs σ rest)
    (hstep : execOp senv acc (.inst (.exec target)) = some acc')
    (hpreconds : ∀ p ∈ acc'.preconditions, p.holds σ)
    (hcallee : ∀ spec : Spec, senv target = some spec →
      ∃ callee, env target = some callee ∧ spec.sound env minFuel callee) :
    ∃ cs', MidenLean.opStep env minFuel cs (.inst (.exec target)) = some cs'
      ∧ acc'.state.models cs' σ rest := by
  simp only [execOp] at hstep
  match hsenv : senv target with
  | some spec =>
    simp only [hsenv] at hstep
    match htrans : spec.transform acc.state with
    | some result =>
      simp only [htrans] at hstep
      have heq := Option.some.inj hstep
      obtain ⟨callee, henv, hsound⟩ := hcallee spec hsenv
      have hresult_preconds : ∀ p ∈ result.preconditions, p.holds σ := fun p hp => by
        rw [← heq] at hpreconds; exact hpreconds p (List.mem_append_right _ hp)
      obtain ⟨cs', hconc, hmod⟩ := hsound acc.state cs σ rest result minFuel
        (Nat.le_refl _) htrans hmodels hresult_preconds
      exact ⟨cs', by unfold MidenLean.opStep; simp only [henv]; exact hconc,
        by rw [← heq]; exact hmod⟩
    | none => simp [htrans] at hstep
  | none => simp [hsenv] at hstep

/-- If execOp succeeds, the output accumulates all input preconditions. -/
private theorem execOp_preconds_prefix
    (senv : ProcEnv) (acc acc' : BlockResult) (op : Op)
    (h : execOp senv acc op = some acc')
    (p : Precondition) (hp : p ∈ acc.preconditions) :
    p ∈ acc'.preconditions := by
  match op with
  | .inst (.exec target) =>
    exact execOp_exec_preconds_prefix senv acc acc' target h p hp
  | .inst i =>
    by_cases hi : ∃ t, i = .exec t
    · obtain ⟨t, rfl⟩ := hi
      exact execOp_exec_preconds_prefix senv acc acc' t h p hp
    · push_neg at hi
      rw [execOp_inst_non_exec senv acc i hi] at h
      match hexec : execInstruction acc.state i with
      | some (s', preconds) =>
        simp only [hexec] at h
        rw [← Option.some.inj h]; exact List.mem_append_left _ hp
      | none => simp [hexec] at h
  | .ifElse _ _ | .repeat _ _ | .whileTrue _ => simp [execOp] at h

/-- Helper: preconditions from the final result of foldlM over execOp include
    all preconditions from any intermediate accumulator. -/
private theorem foldlM_execOp_preconds_subset
    (senv : ProcEnv) (ops : List Op) (acc result : BlockResult)
    (hfold : ops.foldlM (execOp senv) acc = some result)
    (p : Precondition) (hp : p ∈ acc.preconditions) : p ∈ result.preconditions := by
  induction ops generalizing acc with
  | nil =>
    simp [List.foldlM] at hfold; rw [← hfold]; exact hp
  | cons op rest ih =>
    simp only [List.foldlM, bind, Bind.bind, Option.bind] at hfold
    match hstep : execOp senv acc op with
    | none => simp [hstep] at hfold
    | some acc' =>
      simp only [hstep] at hfold
      exact ih acc' hfold (execOp_preconds_prefix senv acc acc' op hstep p hp)

/-- Per-op soundness: if execOp succeeds symbolically, all callees are sound
    (and every symbolic callee has a concrete counterpart), and the accumulator
    models the concrete state, then the concrete op-step also succeeds and the
    result models the new concrete state. -/
private theorem execOp_sound
    (senv : ProcEnv) (env : MidenLean.ProcEnv) (minFuel : Nat)
    (op : Op) (acc acc' : BlockResult) (cs : Concrete.State)
    (σ : Assignment) (rest : List Felt)
    (hmodels : acc.state.models cs σ rest)
    (hstep : execOp senv acc op = some acc')
    (hpreconds : ∀ p ∈ acc'.preconditions, p.holds σ)
    (hcallees : ∀ name (spec : Spec),
      senv name = some spec →
      ∃ callee, env name = some callee ∧ spec.sound env minFuel callee) :
    ∃ cs', MidenLean.opStep env minFuel cs op = some cs'
      ∧ acc'.state.models cs' σ rest := by
  match op with
  | .inst (.exec target) =>
    -- `exec` case: use Spec.sound via hcallees
    exact execOp_exec_sound senv env minFuel target acc acc' cs σ rest
      hmodels hstep hpreconds (fun spec => hcallees target spec)
  | .inst i =>
    -- Non-`exec` instruction case: check if i is .exec (overlap with first case)
    by_cases hi : ∃ t, i = .exec t
    · -- i = .exec t: same as the `exec` case above
      obtain ⟨t, rfl⟩ := hi
      exact execOp_exec_sound senv env minFuel t acc acc' cs σ rest
        hmodels hstep hpreconds (fun spec => hcallees t spec)
    · -- i is not .exec: execOp delegates to execInstruction
      push_neg at hi
      rw [execOp_inst_non_exec senv acc i hi] at hstep
      match hexec : execInstruction acc.state i with
      | some (s', preconds) =>
        simp only [hexec] at hstep
        have heq := Option.some.inj hstep
        have hpreconds' : ∀ p ∈ preconds, p.holds σ := fun p hp => by
          rw [← heq] at hpreconds; exact hpreconds p (List.mem_append_right _ hp)
        obtain ⟨cs', hconc, hmod⟩ :=
          execInstruction_sound i acc.state cs σ rest s' preconds hmodels hexec hpreconds'
        refine ⟨cs', ?_, by rw [← heq]; exact hmod⟩
        unfold MidenLean.opStep
        cases i with
        | exec t => exact absurd rfl (hi t)
        | _ => exact hconc
      | none => simp [hexec] at hstep
  | .ifElse _ _ | .repeat _ _ | .whileTrue _ =>
    simp [execOp] at hstep

/-- Generalized fold soundness: if foldlM of execOp over ops starting from acc
    produces result, and all preconditions hold, then the concrete foldlM of
    opStep also succeeds. -/
private theorem foldlM_execOp_sound
    (senv : ProcEnv) (env : MidenLean.ProcEnv) (minFuel : Nat)
    (ops : List Op) (acc result : BlockResult)
    (cs : Concrete.State) (σ : Assignment) (rest : List Felt)
    (hmodels : acc.state.models cs σ rest)
    (hfold : ops.foldlM (execOp senv) acc = some result)
    (hpreconds : ∀ p ∈ result.preconditions, p.holds σ)
    (hcallees : ∀ name (spec : Spec),
      senv name = some spec →
      ∃ callee, env name = some callee ∧ spec.sound env minFuel callee) :
    ∃ cs', ops.foldlM (MidenLean.opStep env minFuel) cs = some cs'
      ∧ result.state.models cs' σ rest := by
  induction ops generalizing acc cs with
  | nil =>
    simp [List.foldlM] at hfold
    exact ⟨cs, rfl, hfold ▸ hmodels⟩
  | cons op rest_ops ih =>
    simp only [List.foldlM, bind, Bind.bind, Option.bind] at hfold ⊢
    match hstep : execOp senv acc op with
    | none => simp [hstep] at hfold
    | some acc_mid =>
      simp only [hstep] at hfold
      have hpc_mid : ∀ p ∈ acc_mid.preconditions, p.holds σ := fun p hp =>
        hpreconds p (foldlM_execOp_preconds_subset senv rest_ops acc_mid result hfold p hp)
      obtain ⟨cs_mid, hconc_mid, hmod_mid⟩ :=
        execOp_sound senv env minFuel op acc acc_mid cs σ rest
          hmodels hstep hpc_mid hcallees
      rw [hconc_mid]
      exact ih acc_mid cs_mid hmod_mid hfold

-- ============================================================================
-- Executor bridge: execBlock is execOps on instruction-only ops with no
-- symbolic callees.  This lets `execBlock_sound` reuse the `execOp` fold
-- induction instead of a second, parallel induction over `execBlockStep`.
-- ============================================================================

/-- Fold correspondence between the two symbolic executors: folding `execOp`
    under the empty symbolic environment over `insts.map Op.inst` matches
    folding `execBlockStep` over `insts`, up to the reversed-precondition
    accumulator encoding used by `execBlock`. -/
private theorem foldlM_execOp_eq_foldlM_execBlockStep
    (insts : List Instruction) (st : State) (pcs : List Precondition) :
    (insts.map Op.inst).foldlM (execOp fun _ => none)
        { state := st, preconditions := pcs.reverse } =
      (insts.foldlM execBlockStep (st, pcs)).map
        (fun acc => { state := acc.1, preconditions := acc.2.reverse }) := by
  induction insts generalizing st pcs with
  | nil => rfl
  | cons i rest ih =>
    simp only [List.map_cons, List.foldlM, bind, Bind.bind, Option.bind, execBlockStep]
    by_cases hi : ∃ t, i = .exec t
    · -- Both executors fail on `exec` under the empty environment.
      obtain ⟨t, rfl⟩ := hi
      rfl
    · push_neg at hi
      rw [execOp_inst_non_exec (fun _ => none) _ i hi]
      match hexec : execInstruction st i with
      | none => rfl
      | some (s', pc) =>
        simp only [Option.bind]
        have hrev : pcs.reverse ++ pc = (pc.reverse ++ pcs).reverse := by
          simp
        rw [hrev]
        exact ih s' (pc.reverse ++ pcs)

/-- On instruction-only op lists with no symbolic procedure environment,
    `execOps` coincides with the primitive block executor `execBlock`. -/
theorem execOps_map_inst_eq_execBlock (insts : List Instruction) (s : State) :
    execOps (fun _ => none) (insts.map .inst) s = execBlock insts s := by
  unfold execOps execBlock
  have h := foldlM_execOp_eq_foldlM_execBlockStep insts s []
  simp only [List.reverse_nil] at h
  rw [h]
  cases insts.foldlM execBlockStep (s, []) <;> rfl

/-- Block-level soundness: if symbolic execution of a straight-line block
    succeeds with all collected preconditions satisfied, then concrete
    execution also succeeds and the result models the symbolic state.
    Derived from the `execOp` fold induction via the executor bridge. -/
theorem execBlock_sound
    (insts : List Instruction) (ss : State) (cs : Concrete.State)
    (σ : Assignment) (rest : List Felt) (result : BlockResult)
    (hmodels : ss.models cs σ rest)
    (hresult : execBlock insts ss = some result)
    (hpreconds : ∀ p ∈ result.preconditions, p.holds σ) :
    ∃ cs', Concrete.execBlock insts cs = some cs'
      ∧ result.state.models cs' σ rest := by
  rw [← execOps_map_inst_eq_execBlock] at hresult
  unfold execOps at hresult
  obtain ⟨cs', hfold, hmod⟩ :=
    foldlM_execOp_sound (fun _ => none) MidenLean.emptyEnv 0
      (insts.map .inst) { state := ss, preconditions := [] } result cs σ rest
      hmodels hresult hpreconds (fun _ _ h => nomatch h)
  refine ⟨cs', ?_, hmod⟩
  rw [← foldlM_opStep_eq_concreteExecBlock MidenLean.emptyEnv 0 insts cs
    (fun i _ st => opStep_inst_emptyEnv 0 st i)]
  exact hfold

/-- Extended soundness: if all callees in the symbolic ProcEnv are sound
    (and every symbolic callee has a concrete counterpart),
    then execOps is sound. The conclusion is stated in terms of execProcedure
    applied to the op list wrapped as a procedure with numLocals = 0. -/
theorem execOps_sound
    (senv : ProcEnv) (env : MidenLean.ProcEnv) (minFuel : Nat)
    (ops : List Op) (ss : State) (cs : Concrete.State)
    (σ : Assignment) (rest : List Felt) (result : BlockResult)
    (hmodels : ss.models cs σ rest)
    (hresult : execOps senv ops ss = some result)
    (hpreconds : ∀ p ∈ result.preconditions, p.holds σ)
    (hcallees : ∀ name (spec : Spec),
      senv name = some spec →
      ∃ callee, env name = some callee ∧ spec.sound env minFuel callee) :
    ∃ cs', MidenLean.execProcedure env (minFuel + 1) cs (Procedure.ofOps ops) = some cs'
      ∧ result.state.models cs' σ rest := by
  -- execOps unfolds to foldlM (execOp senv) over the initial accumulator
  unfold execOps at hresult
  -- execProcedure at fuel (minFuel + 1) with Procedure.ofOps (numLocals = 0)
  -- unfolds to foldlM (opStep env minFuel)
  have hunfold : MidenLean.execProcedure env (minFuel + 1) cs (Procedure.ofOps ops)
      = ops.foldlM (MidenLean.opStep env minFuel) cs := by
    unfold Procedure.ofOps MidenLean.execProcedure; rfl
  rw [hunfold]
  exact foldlM_execOp_sound senv env minFuel ops
    { state := ss, preconditions := [] } result cs σ rest
    hmodels hresult hpreconds hcallees

end MidenLean.Symbolic
