import MidenLean.Symbolic.Exec
import MidenLean.Symbolic.Helpers
import MidenLean.Proofs.Fuel

/-!
# Symbolic Execution Soundness

Proves that if the symbolic executor succeeds on a basic block and all
collected preconditions hold, then the concrete executor also succeeds
and the result models the symbolic output.

All instruction cases in `execInstruction_sound` are complete — per-instruction
helpers live in `Helpers.lean`.
-/

namespace MidenLean.Symbolic

-- Helper lemmas: provided by Helpers.lean
-- (getElem?_map_append_left, set_map_append_left, getElem?_some_lt,
--  getElem_of_getElem?_some, eraseIdx_map_append_left, isBool_guard)

-- Per-instruction soundness

-- Helper: drop case
private theorem execInstruction_sound_drop
    (ss : State) (cs : MidenState)
    (σ : Assignment) (rest : List Felt)
    (ss' : State) (preconds : List Precondition)
    (hmodels : cs.stack = ss.stack.map (Expr.eval σ) ++ rest)
    (hexec : execInstruction ss .drop = some (ss', preconds))
    (hpreconds : ∀ p ∈ preconds, p.holds σ) :
    ∃ cs', MidenLean.execInstruction cs .drop = some cs' ∧ ss'.models cs' σ rest := by
  unfold execInstruction at hexec
  match hstk : ss.stack with
  | [] => simp [hstk] at hexec
  | x :: tail =>
    simp only [hstk] at hexec
    have heq := Option.some.inj hexec
    have hss : ss' = { stack := tail } := (congrArg Prod.fst heq).symm
    have hpc : preconds = [] := (congrArg Prod.snd heq).symm
    subst hss; subst hpc
    rw [hstk, List.map_cons] at hmodels
    exact ⟨cs.withStack (tail.map (Expr.eval σ) ++ rest),
      by simp only [MidenLean.execInstruction, execDrop, hmodels]; rfl,
      by simp only [State.models, MidenState.withStack]⟩

-- Helper: dup case
private theorem execInstruction_sound_dup
    (n : Fin 16) (ss : State) (cs : MidenState)
    (σ : Assignment) (rest : List Felt)
    (ss' : State) (preconds : List Precondition)
    (hmodels : cs.stack = ss.stack.map (Expr.eval σ) ++ rest)
    (hexec : execInstruction ss (.dup n) = some (ss', preconds))
    (hpreconds : ∀ p ∈ preconds, p.holds σ) :
    ∃ cs', MidenLean.execInstruction cs (.dup n) = some cs' ∧ ss'.models cs' σ rest := by
  unfold execInstruction at hexec
  match hget : ss.stack[n.val]? with
  | none => simp [hget] at hexec
  | some v =>
    simp only [hget] at hexec
    have heq := Option.some.inj hexec
    have hss : ss' = { stack := v :: ss.stack } := (congrArg Prod.fst heq).symm
    have hpc : preconds = [] := (congrArg Prod.snd heq).symm
    subst hss; subst hpc
    have hn : n.val < ss.stack.length := getElem?_some_lt _ _ _ hget
    have hval : ss.stack[n.val] = v := getElem_of_getElem?_some _ _ _ hget
    refine ⟨cs.withStack (v.eval σ :: cs.stack), ?_, ?_⟩
    · simp only [MidenLean.execInstruction, execDup, hmodels,
          getElem?_map_append_left _ _ _ _ hn]
      rw [hval]
    · simp only [State.models, MidenState.withStack, List.map_cons, hmodels]
      rfl

-- Helper: swap case
private theorem execInstruction_sound_swap
    (n : Fin 16) (ss : State) (cs : MidenState)
    (σ : Assignment) (rest : List Felt)
    (ss' : State) (preconds : List Precondition)
    (hmodels : cs.stack = ss.stack.map (Expr.eval σ) ++ rest)
    (hexec : execInstruction ss (.swap n) = some (ss', preconds))
    (hpreconds : ∀ p ∈ preconds, p.holds σ) :
    ∃ cs', MidenLean.execInstruction cs (.swap n) = some cs' ∧ ss'.models cs' σ rest := by
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
      by simp only [State.models, hmodels]⟩
  · have hne : (n.val == 0) = false := by simp [h0]
    simp only [hne] at hexec
    match hget0 : ss.stack[0]?, hgetn : ss.stack[n.val]? with
    | some top, some nth =>
      simp only [hget0, hgetn] at hexec
      have heq := Option.some.inj hexec
      have hss : ss' = { stack := (ss.stack.set 0 nth).set n.val top } :=
        (congrArg Prod.fst heq).symm
      have hpc : preconds = [] := (congrArg Prod.snd heq).symm
      subst hss; subst hpc
      have h0lt : (0 : Nat) < ss.stack.length := getElem?_some_lt _ _ _ hget0
      have hnlt : n.val < ss.stack.length := getElem?_some_lt _ _ _ hgetn
      have hval0 : ss.stack[0] = top := getElem_of_getElem?_some _ _ _ hget0
      have hvaln : ss.stack[n.val] = nth := getElem_of_getElem?_some _ _ _ hgetn
      refine ⟨cs.withStack ((cs.stack.set 0 (nth.eval σ)).set n.val (top.eval σ)), ?_, ?_⟩
      · simp only [MidenLean.execInstruction, execSwap, hne]
        rw [hmodels,
            getElem?_map_append_left _ _ _ 0 h0lt,
            getElem?_map_append_left _ _ _ n.val hnlt]
        rw [hval0, hvaln]
        rfl
      · unfold State.models MidenState.withStack
        rw [hmodels,
            set_map_append_left (Expr.eval σ) (ss.stack.set 0 nth) rest n.val top
              (by rw [List.length_set]; exact hnlt),
            set_map_append_left (Expr.eval σ) ss.stack rest 0 nth h0lt]
    | some _, none | none, some _ | none, none =>
      simp [hget0, hgetn] at hexec

-- Helper: add case
private theorem execInstruction_sound_add
    (ss : State) (cs : MidenState)
    (σ : Assignment) (rest : List Felt)
    (ss' : State) (preconds : List Precondition)
    (hmodels : cs.stack = ss.stack.map (Expr.eval σ) ++ rest)
    (hexec : execInstruction ss .add = some (ss', preconds))
    (hpreconds : ∀ p ∈ preconds, p.holds σ) :
    ∃ cs', MidenLean.execInstruction cs .add = some cs' ∧ ss'.models cs' σ rest := by
  unfold execInstruction at hexec
  match hstk : ss.stack with
  | [] | [_] => simp [hstk] at hexec
  | b :: a :: tail =>
    simp only [hstk] at hexec
    have heq := Option.some.inj hexec
    have hss : ss' = { stack := .add a b :: tail } := (congrArg Prod.fst heq).symm
    have hpc : preconds = [] := (congrArg Prod.snd heq).symm
    subst hss; subst hpc
    rw [hstk, List.map_cons, List.map_cons] at hmodels
    exact ⟨cs.withStack ((a.eval σ + b.eval σ) :: tail.map (Expr.eval σ) ++ rest),
      by simp only [MidenLean.execInstruction, execAdd, hmodels]; rfl,
      by simp only [State.models, MidenState.withStack, List.map_cons, Expr.eval]⟩

-- Helper: sub case
private theorem execInstruction_sound_sub
    (ss : State) (cs : MidenState)
    (σ : Assignment) (rest : List Felt)
    (ss' : State) (preconds : List Precondition)
    (hmodels : cs.stack = ss.stack.map (Expr.eval σ) ++ rest)
    (hexec : execInstruction ss .sub = some (ss', preconds))
    (hpreconds : ∀ p ∈ preconds, p.holds σ) :
    ∃ cs', MidenLean.execInstruction cs .sub = some cs' ∧ ss'.models cs' σ rest := by
  unfold execInstruction at hexec
  match hstk : ss.stack with
  | [] | [_] => simp [hstk] at hexec
  | b :: a :: tail =>
    simp only [hstk] at hexec
    have heq := Option.some.inj hexec
    have hss : ss' = { stack := .sub a b :: tail } := (congrArg Prod.fst heq).symm
    have hpc : preconds = [] := (congrArg Prod.snd heq).symm
    subst hss; subst hpc
    rw [hstk, List.map_cons, List.map_cons] at hmodels
    exact ⟨cs.withStack ((a.eval σ - b.eval σ) :: tail.map (Expr.eval σ) ++ rest),
      by simp only [MidenLean.execInstruction, execSub, hmodels]; rfl,
      by simp only [State.models, MidenState.withStack, List.map_cons, Expr.eval]⟩

-- Helper: mul case
private theorem execInstruction_sound_mul
    (ss : State) (cs : MidenState)
    (σ : Assignment) (rest : List Felt)
    (ss' : State) (preconds : List Precondition)
    (hmodels : cs.stack = ss.stack.map (Expr.eval σ) ++ rest)
    (hexec : execInstruction ss .mul = some (ss', preconds))
    (hpreconds : ∀ p ∈ preconds, p.holds σ) :
    ∃ cs', MidenLean.execInstruction cs .mul = some cs' ∧ ss'.models cs' σ rest := by
  unfold execInstruction at hexec
  match hstk : ss.stack with
  | [] | [_] => simp [hstk] at hexec
  | b :: a :: tail =>
    simp only [hstk] at hexec
    have heq := Option.some.inj hexec
    have hss : ss' = { stack := .mul a b :: tail } := (congrArg Prod.fst heq).symm
    have hpc : preconds = [] := (congrArg Prod.snd heq).symm
    subst hss; subst hpc
    rw [hstk, List.map_cons, List.map_cons] at hmodels
    exact ⟨cs.withStack ((a.eval σ * b.eval σ) :: tail.map (Expr.eval σ) ++ rest),
      by simp only [MidenLean.execInstruction, execMul, hmodels]; rfl,
      by simp only [State.models, MidenState.withStack, List.map_cons, Expr.eval]⟩

-- Helper: u32WidenAdd case
private theorem execInstruction_sound_u32WidenAdd
    (ss : State) (cs : MidenState)
    (σ : Assignment) (rest : List Felt)
    (ss' : State) (preconds : List Precondition)
    (hmodels : cs.stack = ss.stack.map (Expr.eval σ) ++ rest)
    (hexec : execInstruction ss .u32WidenAdd = some (ss', preconds))
    (hpreconds : ∀ p ∈ preconds, p.holds σ) :
    ∃ cs', MidenLean.execInstruction cs .u32WidenAdd = some cs' ∧ ss'.models cs' σ rest := by
  unfold execInstruction at hexec
  match hstk : ss.stack with
  | [] | [_] => simp [hstk] at hexec
  | b :: a :: tail =>
    simp only [hstk] at hexec
    have heq := Option.some.inj hexec
    have hss : ss' = { stack := .u32AddLo a b :: .u32AddHi a b :: tail } :=
      (congrArg Prod.fst heq).symm
    have hpc : preconds = [.isU32 a, .isU32 b] := (congrArg Prod.snd heq).symm
    subst hss
    rw [hstk, List.map_cons, List.map_cons, List.cons_append, List.cons_append] at hmodels
    have ha : (a.eval σ).isU32 = true :=
      hpreconds (.isU32 a) (by rw [hpc]; simp)
    have hb : (b.eval σ).isU32 = true :=
      hpreconds (.isU32 b) (by rw [hpc]; simp)
    refine ⟨cs.withStack (Felt.ofNat (((a.eval σ).val + (b.eval σ).val) % u32Max) ::
                          Felt.ofNat (((a.eval σ).val + (b.eval σ).val) / u32Max) ::
                          tail.map (Expr.eval σ) ++ rest), ?_, ?_⟩
    · simp only [MidenLean.execInstruction, execU32WidenAdd, hmodels, ha, hb,
          Bool.not_true, Bool.false_or, u32WideAdd, MidenState.withStack]
      rfl
    · simp only [State.models, MidenState.withStack, List.map_cons, Expr.eval,
          List.cons_append]

-- Helper: eq case
private theorem execInstruction_sound_eq
    (ss : State) (cs : MidenState)
    (σ : Assignment) (rest : List Felt)
    (ss' : State) (preconds : List Precondition)
    (hmodels : cs.stack = ss.stack.map (Expr.eval σ) ++ rest)
    (hexec : execInstruction ss .eq = some (ss', preconds))
    (hpreconds : ∀ p ∈ preconds, p.holds σ) :
    ∃ cs', MidenLean.execInstruction cs .eq = some cs' ∧ ss'.models cs' σ rest := by
  unfold execInstruction at hexec
  match hstk : ss.stack with
  | [] | [_] => simp [hstk] at hexec
  | b :: a :: tail =>
    simp only [hstk] at hexec
    have heq := Option.some.inj hexec
    have hss : ss' = { stack := .feltEq a b :: tail } := (congrArg Prod.fst heq).symm
    have hpc : preconds = [] := (congrArg Prod.snd heq).symm
    subst hss; subst hpc
    rw [hstk, List.map_cons, List.map_cons] at hmodels
    exact ⟨cs.withStack ((if a.eval σ == b.eval σ then (1 : Felt) else 0) :: tail.map (Expr.eval σ) ++ rest),
      by simp only [MidenLean.execInstruction, execEq, hmodels]; rfl,
      by simp only [State.models, MidenState.withStack, List.map_cons, Expr.eval]⟩

-- Helper: and case
private theorem execInstruction_sound_and
    (ss : State) (cs : MidenState)
    (σ : Assignment) (rest : List Felt)
    (ss' : State) (preconds : List Precondition)
    (hmodels : cs.stack = ss.stack.map (Expr.eval σ) ++ rest)
    (hexec : execInstruction ss .and = some (ss', preconds))
    (hpreconds : ∀ p ∈ preconds, p.holds σ) :
    ∃ cs', MidenLean.execInstruction cs .and = some cs' ∧ ss'.models cs' σ rest := by
  unfold execInstruction at hexec
  match hstk : ss.stack with
  | [] | [_] => simp [hstk] at hexec
  | b :: a :: tail =>
    simp only [hstk] at hexec
    have heq := Option.some.inj hexec
    have hss : ss' = { stack := .feltAnd a b :: tail } := (congrArg Prod.fst heq).symm
    have hpc : preconds = [.isBool a, .isBool b] := (congrArg Prod.snd heq).symm
    subst hss
    rw [hstk, List.map_cons, List.map_cons] at hmodels
    have ha : (a.eval σ).isBool = true :=
      isBool_guard _ (hpreconds (.isBool a) (by rw [hpc]; simp))
    have hb : (b.eval σ).isBool = true :=
      isBool_guard _ (hpreconds (.isBool b) (by rw [hpc]; simp))
    have hguard : ((a.eval σ).isBool && (b.eval σ).isBool) = true := by rw [ha, hb]; rfl
    refine ⟨cs.withStack ((a.eval σ * b.eval σ) :: tail.map (Expr.eval σ) ++ rest), ?_, ?_⟩
    · change execAnd cs = _
      unfold execAnd
      rw [hmodels]; simp [hguard, MidenState.withStack]
    · simp only [State.models, MidenState.withStack, List.map_cons, Expr.eval]

-- Helper: u32WidenAdd3 case
private theorem execInstruction_sound_u32WidenAdd3
    (ss : State) (cs : MidenState)
    (σ : Assignment) (rest : List Felt)
    (ss' : State) (preconds : List Precondition)
    (hmodels : cs.stack = ss.stack.map (Expr.eval σ) ++ rest)
    (hexec : execInstruction ss .u32WidenAdd3 = some (ss', preconds))
    (hpreconds : ∀ p ∈ preconds, p.holds σ) :
    ∃ cs', MidenLean.execInstruction cs .u32WidenAdd3 = some cs' ∧ ss'.models cs' σ rest := by
  unfold execInstruction at hexec
  match hstk : ss.stack with
  | [] | [_] | [_, _] => simp [hstk] at hexec
  | c :: b :: a :: tail =>
    simp only [hstk] at hexec
    have heq := Option.some.inj hexec
    have hss : ss' = { stack := .u32Add3Lo a b c :: .u32Add3Hi a b c :: tail } :=
      (congrArg Prod.fst heq).symm
    have hpc : preconds = [.isU32 a, .isU32 b, .isU32 c] := (congrArg Prod.snd heq).symm
    subst hss
    rw [hstk, List.map_cons, List.map_cons, List.map_cons] at hmodels
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
      rw [hmodels]; simp [ha, hb, hc, u32WideAdd3, MidenState.withStack]
    · simp only [State.models, MidenState.withStack, List.map_cons, Expr.eval,
          List.cons_append]

-- Helper: u32OverflowSub case
private theorem execInstruction_sound_u32OverflowSub
    (ss : State) (cs : MidenState)
    (σ : Assignment) (rest : List Felt)
    (ss' : State) (preconds : List Precondition)
    (hmodels : cs.stack = ss.stack.map (Expr.eval σ) ++ rest)
    (hexec : execInstruction ss .u32OverflowSub = some (ss', preconds))
    (hpreconds : ∀ p ∈ preconds, p.holds σ) :
    ∃ cs', MidenLean.execInstruction cs .u32OverflowSub = some cs' ∧ ss'.models cs' σ rest := by
  unfold execInstruction at hexec
  match hstk : ss.stack with
  | [] | [_] => simp [hstk] at hexec
  | b :: a :: tail =>
    simp only [hstk] at hexec
    have heq := Option.some.inj hexec
    have hss : ss' = { stack := .u32SubBorrow a b :: .u32SubDiff a b :: tail } :=
      (congrArg Prod.fst heq).symm
    have hpc : preconds = [.isU32 a, .isU32 b] := (congrArg Prod.snd heq).symm
    subst hss
    rw [hstk, List.map_cons, List.map_cons] at hmodels
    have ha : (a.eval σ).isU32 = true :=
      hpreconds (.isU32 a) (by rw [hpc]; simp)
    have hb : (b.eval σ).isU32 = true :=
      hpreconds (.isU32 b) (by rw [hpc]; simp)
    refine ⟨cs.withStack (Felt.ofNat (u32OverflowingSub (a.eval σ).val (b.eval σ).val).1 ::
                          Felt.ofNat (u32OverflowingSub (a.eval σ).val (b.eval σ).val).2 ::
                          tail.map (Expr.eval σ) ++ rest), ?_, ?_⟩
    · change execU32OverflowSub cs = _
      unfold execU32OverflowSub
      rw [hmodels]; simp [ha, hb, MidenState.withStack]
    · simp only [State.models, MidenState.withStack, List.map_cons, Expr.eval,
          List.cons_append]

-- Helper: movup case
private theorem execInstruction_sound_movup
    (n : Nat) (ss : State) (cs : MidenState)
    (σ : Assignment) (rest : List Felt)
    (ss' : State) (preconds : List Precondition)
    (hmodels : cs.stack = ss.stack.map (Expr.eval σ) ++ rest)
    (hexec : execInstruction ss (.movup n) = some (ss', preconds))
    (hpreconds : ∀ p ∈ preconds, p.holds σ) :
    ∃ cs', MidenLean.execInstruction cs (.movup n) = some cs' ∧ ss'.models cs' σ rest := by
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
      have hss : ss' = { stack := v :: ss.stack.eraseIdx n } := (congrArg Prod.fst heq).symm
      have hpc : preconds = [] := (congrArg Prod.snd heq).symm
      subst hss; subst hpc
      have hn : n < ss.stack.length := getElem?_some_lt _ _ _ hget
      have hval : ss.stack[n] = v := getElem_of_getElem?_some _ _ _ hget
      refine ⟨cs.withStack (v.eval σ :: (ss.stack.eraseIdx n).map (Expr.eval σ) ++ rest), ?_, ?_⟩
      · change execMovup n cs = _
        unfold execMovup
        have : ¬(n < 2) := by omega
        have : ¬(n > 15) := by omega
        simp_all [removeNth, getElem?_map_append_left _ _ _ _ hn,
            eraseIdx_map_append_left _ _ _ _ hn, MidenState.withStack]
      · simp only [State.models, MidenState.withStack, List.map_cons]
  · have hfalse : (decide (2 ≤ n) && decide (n ≤ 15)) = false := by
      simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega
    simp [hfalse] at hexec

-- Helper: movdn case
set_option maxHeartbeats 800000 in
private theorem execInstruction_sound_movdn
    (n : Nat) (ss : State) (cs : MidenState)
    (σ : Assignment) (rest : List Felt)
    (ss' : State) (preconds : List Precondition)
    (hmodels : cs.stack = ss.stack.map (Expr.eval σ) ++ rest)
    (hexec : execInstruction ss (.movdn n) = some (ss', preconds))
    (hpreconds : ∀ p ∈ preconds, p.holds σ) :
    ∃ cs', MidenLean.execInstruction cs (.movdn n) = some cs' ∧ ss'.models cs' σ rest := by
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
        have hss : ss' = { stack := p.1 ++ [top] ++ p.2 } := (congrArg Prod.fst heq).symm
        have hpc : preconds = [] := (congrArg Prod.snd heq).symm
        subst hss; subst hpc
        have hsplit := @List.splitAt_eq _ n srest
        rw [← hpsplit] at hsplit
        have hlen_eq : p.1.length = n := by
          have := beq_iff_eq.mp hlen; omega
        have hmodels' : cs.stack = Expr.eval σ top :: srest.map (Expr.eval σ) ++ rest := by
          rw [hmodels, hstk, List.map_cons]
        refine ⟨cs.withStack (insertAt (srest.map (Expr.eval σ) ++ rest) n (top.eval σ)), ?_, ?_⟩
        · change execMovdn n cs = _
          unfold execMovdn
          have : ¬(n < 2) := by omega
          have : ¬(n > 15) := by omega
          simp_all [insertAt, MidenState.withStack]
        · simp only [State.models, MidenState.withStack]
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
      · simp [hlen] at hexec
  · have hfalse : (decide (2 ≤ n) && decide (n ≤ 15)) = false := by
      simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega
    simp [hfalse] at hexec

set_option maxHeartbeats 400000 in
/-- Per-instruction soundness: if symbolic execution succeeds on instruction i
    with all preconditions satisfied, then concrete execution also succeeds
    and the resulting state models the symbolic result. -/
theorem execInstruction_sound
    (i : Instruction) (ss : State) (cs : MidenState)
    (σ : Assignment) (rest : List Felt)
    (ss' : State) (preconds : List Precondition)
    (hmodels : ss.models cs σ rest)
    (hexec : execInstruction ss i = some (ss', preconds))
    (hpreconds : ∀ p ∈ preconds, p.holds σ) :
    ∃ cs', MidenLean.execInstruction cs i = some cs'
      ∧ ss'.models cs' σ rest := by
  unfold State.models at hmodels
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
  -- Instructions that return none in execInstruction (unsupported symbolically)
  | .cswap | .cswapw | .cdrop | .cdropw
  | .u32Test | .u32TestW
  | .memLoad | .memLoadImm _ | .memStore | .memStoreImm _
  | .memLoadwBe | .memLoadwBeImm _ | .memStorewBe | .memStorewBeImm _
  | .memLoadwLe | .memLoadwLeImm _ | .memStorewLe | .memStorewLeImm _
  | .locLoad _ | .locStore _ | .locLoadwBe _ | .locLoadwLe _
  | .locStorewBe _ | .locStorewLe _ | .locaddr _
  | .advPush _ | .advLoadW
  | .emit | .emitImm _
  | .exec _ =>
    simp [execInstruction] at hexec

-- Block-level soundness

private theorem foldlM_preconds_subset
    (insts : List Instruction) (ss : State) (acc : List Precondition)
    (final_ss : State) (final_preconds : List Precondition)
    (hfold : insts.foldlM execBlockStep (ss, acc) = some (final_ss, final_preconds))
    (p : Precondition) (hp : p ∈ acc) : p ∈ final_preconds := by
  induction insts generalizing ss acc with
  | nil =>
    simp [List.foldlM] at hfold
    rw [← hfold.2]; exact hp
  | cons i rest ih =>
    simp only [List.foldlM, bind, Bind.bind, Option.bind] at hfold
    unfold execBlockStep at hfold
    match hstep : execInstruction ss i with
    | none => simp [hstep] at hfold
    | some (ss1, pc1) =>
      simp only [hstep] at hfold
      exact ih ss1 (pc1.reverse ++ acc) hfold (List.mem_append_right _ hp)

private theorem foldlM_sound
    (insts : List Instruction) (ss : State) (cs : MidenState)
    (σ : Assignment) (rest : List Felt) (acc : List Precondition)
    (final_ss : State) (final_preconds : List Precondition)
    (hmodels : ss.models cs σ rest)
    (hfold : insts.foldlM execBlockStep (ss, acc) = some (final_ss, final_preconds))
    (hpreconds : ∀ p ∈ final_preconds, p.holds σ) :
    ∃ cs', concreteExecBlock insts cs = some cs'
      ∧ final_ss.models cs' σ rest := by
  induction insts generalizing ss cs acc with
  | nil =>
    simp [List.foldlM] at hfold
    obtain ⟨rfl, _⟩ := hfold
    exact ⟨cs, rfl, hmodels⟩
  | cons i rest_insts ih =>
    simp only [List.foldlM, bind, Bind.bind, Option.bind] at hfold
    unfold execBlockStep at hfold
    match hstep : execInstruction ss i with
    | none => simp [hstep] at hfold
    | some (ss1, pc1) =>
      simp only [hstep] at hfold
      have hpc1 : ∀ p ∈ pc1, p.holds σ := by
        intro p hp
        apply hpreconds
        exact foldlM_preconds_subset rest_insts ss1 (pc1.reverse ++ acc)
          final_ss final_preconds hfold p
          (List.mem_append_left _ (List.mem_reverse.mpr hp))
      obtain ⟨cs1, hconc1, hmod1⟩ :=
        execInstruction_sound i ss cs σ rest ss1 pc1 hmodels hstep hpc1
      obtain ⟨cs', hconc', hmod'⟩ :=
        ih ss1 cs1 (pc1.reverse ++ acc) hmod1 hfold
      refine ⟨cs', ?_, hmod'⟩
      unfold concreteExecBlock at hconc' ⊢
      simp only [List.foldlM, bind, Bind.bind, Option.bind, hconc1]
      exact hconc'

theorem execBlock_sound
    (insts : List Instruction) (ss : State) (cs : MidenState)
    (σ : Assignment) (rest : List Felt) (result : BlockResult)
    (hmodels : ss.models cs σ rest)
    (hresult : execBlock insts ss = some result)
    (hpreconds : ∀ p ∈ result.preconditions, p.holds σ) :
    ∃ cs', concreteExecBlock insts cs = some cs'
      ∧ result.state.models cs' σ rest := by
  unfold execBlock at hresult
  match hfold : insts.foldlM execBlockStep (ss, []) with
  | none => simp [hfold] at hresult
  | some (final_ss, final_preconds) =>
    simp only [hfold, Option.some.injEq] at hresult
    have hstate : result.state = final_ss :=
      (congrArg BlockResult.state hresult).symm
    have hpc : result.preconditions = final_preconds.reverse :=
      (congrArg BlockResult.preconditions hresult).symm
    rw [hstate]
    exact foldlM_sound insts ss cs σ rest [] final_ss final_preconds hmodels
      hfold (fun p hp => hpreconds p (hpc ▸ List.mem_reverse.mpr hp))

-- Bridge: exec → concreteExecBlock

/-- The Op-level closure from execWithEnv agrees with execInstruction
    on Op.inst i when env returns none for all targets. -/
private theorem exec_closure_inst
    (env : MidenLean.ProcEnv) (fuel : Nat) (s : MidenState) (i : Instruction)
    (henv : ∀ t, env t = none) :
    (match (Op.inst i : Op) with
     | .inst (.exec target) =>
       match env target with
       | some callee => execWithEnv env fuel s callee
       | none => none
     | .inst i => MidenLean.execInstruction s i
     | .ifElse thenBlk elseBlk =>
       match s.stack with
       | cond :: rest =>
         if cond.val == 1 then execWithEnv env fuel (s.withStack rest) thenBlk
         else if cond.val == 0 then execWithEnv env fuel (s.withStack rest) elseBlk
         else none
       | _ => none
     | .repeat count body => execWithEnv.doRepeat env fuel count body s
     | .whileTrue body => execWithEnv.doWhile env fuel fuel body s)
    = MidenLean.execInstruction s i := by
  cases i with
  | exec target => simp [henv, MidenLean.execInstruction]
  | _ => rfl

/-- For any closure that maps Op.inst i to execInstruction s i,
    foldlM over insts.map Op.inst equals concreteExecBlock. -/
private theorem foldlM_map_inst
    (f : MidenState → Op → Option MidenState)
    (hf : ∀ s i, f s (.inst i) = MidenLean.execInstruction s i)
    (insts : List Instruction) (s : MidenState) :
    (insts.map Op.inst).foldlM (fun st op => f st op) s =
    concreteExecBlock insts s := by
  induction insts generalizing s with
  | nil => rfl
  | cons i rest ih =>
    simp only [List.map_cons, List.foldlM, bind, Bind.bind, Option.bind,
               concreteExecBlock]
    rw [hf]
    match MidenLean.execInstruction s i with
    | none => rfl
    | some s' => exact ih s'

/-- For a basic block (all Op.inst, numLocals = 0),
    `exec` reduces to `concreteExecBlock`. -/
theorem exec_basic_block
    (fuel : Nat) (s : MidenState) (insts : List Instruction)
    (proc : Procedure)
    (hbody : proc.body = insts.map Op.inst)
    (hlocals : proc.numLocals = 0)
    (hfuel : fuel > 0) :
    exec fuel s proc = concreteExecBlock insts s := by
  obtain ⟨name, numLocals, ops⟩ := proc
  simp only at hbody hlocals
  subst hlocals; subst hbody
  obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 1 := ⟨fuel - 1, by omega⟩
  unfold exec execWithEnv
  simp only
  exact foldlM_map_inst _ (fun s i =>
    exec_closure_inst _ n s i (fun _ => rfl)) insts s

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
    ∃ cs', MidenLean.execWithEnv env fuel cs callee = some cs'
      ∧ result.state.models cs' σ rest

/-- For a non-exec instruction, execOp delegates to the symbolic execInstruction. -/
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

/-- If execOp succeeds, the output accumulates all input preconditions. -/
private theorem execOp_preconds_prefix
    (senv : ProcEnv) (acc acc' : BlockResult) (op : Op)
    (h : execOp senv acc op = some acc')
    (p : Precondition) (hp : p ∈ acc.preconditions) :
    p ∈ acc'.preconditions := by
  match op with
  | .inst (.exec target) =>
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
  | .inst i =>
    by_cases hi : ∃ t, i = .exec t
    · obtain ⟨t, rfl⟩ := hi
      simp only [execOp] at h
      match hsenv : senv t with
      | some spec =>
        simp only [hsenv] at h
        match htrans : spec.transform acc.state with
        | some result =>
          simp only [htrans] at h
          rw [← Option.some.inj h]; exact List.mem_append_left _ hp
        | none => simp [htrans] at h
      | none => simp [hsenv] at h
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
    (op : Op) (acc acc' : BlockResult) (cs : MidenState)
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
    -- exec case: use Spec.sound via hcallees
    simp only [execOp] at hstep
    match hsenv : senv target with
    | some spec =>
      simp only [hsenv] at hstep
      match htrans : spec.transform acc.state with
      | some result =>
        simp only [htrans] at hstep
        have heq := Option.some.inj hstep
        obtain ⟨callee, henv, hsound⟩ := hcallees target spec hsenv
        have hresult_preconds : ∀ p ∈ result.preconditions, p.holds σ := fun p hp => by
          rw [← heq] at hpreconds; exact hpreconds p (List.mem_append_right _ hp)
        obtain ⟨cs', hconc, hmod⟩ := hsound acc.state cs σ rest result minFuel
          (Nat.le_refl _) htrans hmodels hresult_preconds
        exact ⟨cs', by unfold MidenLean.opStep; simp only [henv]; exact hconc,
          by rw [← heq]; exact hmod⟩
      | none => simp [htrans] at hstep
    | none => simp [hsenv] at hstep
  | .inst i =>
    -- Non-exec instruction case: check if i is .exec (overlap with first case)
    by_cases hi : ∃ t, i = .exec t
    · -- i = .exec t: same as exec case above
      obtain ⟨t, rfl⟩ := hi
      simp only [execOp] at hstep
      match hsenv : senv t with
      | some spec =>
        simp only [hsenv] at hstep
        match htrans : spec.transform acc.state with
        | some result =>
          simp only [htrans] at hstep
          have heq := Option.some.inj hstep
          obtain ⟨callee, henv, hsound⟩ := hcallees t spec hsenv
          have hresult_preconds : ∀ p ∈ result.preconditions, p.holds σ := fun p hp => by
            rw [← heq] at hpreconds; exact hpreconds p (List.mem_append_right _ hp)
          obtain ⟨cs', hconc, hmod⟩ := hsound acc.state cs σ rest result minFuel
            (Nat.le_refl _) htrans hmodels hresult_preconds
          exact ⟨cs', by unfold MidenLean.opStep; simp only [henv]; exact hconc,
            by rw [← heq]; exact hmod⟩
        | none => simp [htrans] at hstep
      | none => simp [hsenv] at hstep
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
    (cs : MidenState) (σ : Assignment) (rest : List Felt)
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

/-- Extended soundness: if all callees in the symbolic ProcEnv are sound
    (and every symbolic callee has a concrete counterpart),
    then execOps is sound. The conclusion is stated in terms of execWithEnv
    applied to the op list wrapped as a procedure with numLocals = 0. -/
theorem execOps_sound
    (senv : ProcEnv) (env : MidenLean.ProcEnv) (minFuel : Nat)
    (ops : List Op) (ss : State) (cs : MidenState)
    (σ : Assignment) (rest : List Felt) (result : BlockResult)
    (hmodels : ss.models cs σ rest)
    (hresult : execOps senv ops ss = some result)
    (hpreconds : ∀ p ∈ result.preconditions, p.holds σ)
    (hcallees : ∀ name (spec : Spec),
      senv name = some spec →
      ∃ callee, env name = some callee ∧ spec.sound env minFuel callee) :
    ∃ cs', MidenLean.execWithEnv env (minFuel + 1) cs (Procedure.ofOps ops) = some cs'
      ∧ result.state.models cs' σ rest := by
  -- execOps unfolds to foldlM (execOp senv) over the initial accumulator
  unfold execOps at hresult
  -- execWithEnv at fuel (minFuel + 1) with Procedure.ofOps (numLocals = 0)
  -- unfolds to foldlM (opStep env minFuel)
  have hunfold : MidenLean.execWithEnv env (minFuel + 1) cs (Procedure.ofOps ops)
      = ops.foldlM (MidenLean.opStep env minFuel) cs := by
    unfold Procedure.ofOps MidenLean.execWithEnv; rfl
  rw [hunfold]
  exact foldlM_execOp_sound senv env minFuel ops
    { state := ss, preconditions := [] } result cs σ rest
    hmodels hresult hpreconds hcallees

end MidenLean.Symbolic
