import MidenLean.Symbolic.SimpAttrs
import MidenLean.Symbolic.Soundness
import MidenLean.Proofs.Helpers
import MidenLean.Proofs.Fuel
import MidenLean.Generated.U64

/-!
# Symbolic Reflection

End-to-end use of the symbolic block executor to prove correctness of
real MASM procedures. Two reflection theorems:
1. `reflect_with_env_zero` for procedures with numLocals = 0
2. `reflect_with_env_locals` for procedures with numLocals > 0
-/

namespace MidenLean.Symbolic.Reflect

open MidenLean
open MidenLean.Symbolic

/-- The concrete assignment used by tactic-facing reflection wrappers. -/
abbrev concreteAssignment : Assignment := fun _ => 0

/-- Concrete literal symbolic state matching a concrete stack prefix, memory,
    frames, and advice. -/
def concreteState (stackPrefix : List Felt) (mem : Nat → Felt)
    (frames : List MidenLean.LocalFrame) (adv : List Felt) : State :=
  { stack := stackPrefix.map Expr.lit
    memory := fun addr => Expr.lit (mem addr)
    frames := frames
    advice := adv.map Expr.lit }

/-! ### `miden_reflect_norm` bank

The lemmas tagged `@[miden_reflect_norm]` below canonicalize the terms produced by
reflection, so that the cleanup phase of `miden_reflect` / `miden_vcg` can close
the residual goal. Symbolic execution leaves behind `Expr.eval` applications over
the trivial `concreteAssignment`, projections out of `concreteState` /
`concreteStateWithLocals`, and `Precondition.holds` obligations; this bank pushes
`eval` through the term structure, collapses literal-carrying `Expr` nodes back to
`Felt` arithmetic, and rewrites boolean flags into the propositions they encode.

Most lemmas are `@[simp]` as well; the few that are scoped to
`miden_reflect_norm` only are flagged where they occur. The two state
constructors these lemmas project out of are defined inline in this section.
-/

/-- The local-memory base of an empty frame stack is `0`. -/
@[simp, miden_reflect_norm] theorem localsBase_nil : MidenLean.localsBase [] = 0 := rfl

/-- The local-memory base above a frame stack sits past the top frame. -/
@[simp, miden_reflect_norm] theorem localsBase_cons
    (f : MidenLean.LocalFrame) (fs : List MidenLean.LocalFrame) :
    MidenLean.localsBase (f :: fs) = f.base + f.alignedNumLocals := rfl

/-- Concrete literal symbolic state for the `numLocals > 0` reflection path.
    It pre-pushes the fresh local frame that `execProcedure` would allocate. -/
def concreteStateWithLocals (stackPrefix : List Felt) (mem : Nat → Felt)
    (frames : List MidenLean.LocalFrame) (adv : List Felt)
    (numLocals : Nat) : State :=
  let aligned := MidenLean.alignLocals numLocals
  let frame : MidenLean.LocalFrame :=
    { base := MidenLean.localsBase frames, numLocals, alignedNumLocals := aligned }
  { stack := stackPrefix.map Expr.lit
    memory := fun addr => Expr.lit (mem addr)
    frames := frame :: frames
    advice := adv.map Expr.lit }

/-- Project the frame stack out of a `concreteState`. -/
@[simp, miden_reflect_norm] theorem concreteState_frames
    (stackPrefix : List Felt) (mem : Nat → Felt)
    (frames : List MidenLean.LocalFrame) (adv : List Felt) :
    (concreteState stackPrefix mem frames adv).frames = frames := rfl

/-- Project the symbolic stack out of a `concreteState`. -/
@[simp, miden_reflect_norm] theorem concreteState_stack
    (stackPrefix : List Felt) (mem : Nat → Felt)
    (frames : List MidenLean.LocalFrame) (adv : List Felt) :
    (concreteState stackPrefix mem frames adv).stack = stackPrefix.map Expr.lit := rfl

/-- Project the advice stack out of a `concreteState`. -/
@[simp, miden_reflect_norm] theorem concreteState_advice
    (stackPrefix : List Felt) (mem : Nat → Felt)
    (frames : List MidenLean.LocalFrame) (adv : List Felt) :
    (concreteState stackPrefix mem frames adv).advice = adv.map Expr.lit := rfl

/-- Project the frame stack out of a `concreteStateWithLocals`, exposing the
    pre-pushed local frame. -/
@[simp, miden_reflect_norm] theorem concreteStateWithLocals_frames
    (stackPrefix : List Felt) (mem : Nat → Felt)
    (frames : List MidenLean.LocalFrame) (adv : List Felt) (numLocals : Nat) :
    (concreteStateWithLocals stackPrefix mem frames adv numLocals).frames =
      { base := MidenLean.localsBase frames, numLocals,
        alignedNumLocals := MidenLean.alignLocals numLocals } :: frames := rfl

/-- Evaluating a list of literals (in composed form) recovers the original list. -/
@[simp, miden_reflect_norm] theorem map_eval_lit_comp_zero (xs : List Felt) :
    List.map ((Expr.eval (fun _ => 0)) ∘ Expr.lit) xs = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [Expr.eval, ih]

/-- Evaluating a literal-mapped list recovers the original list. -/
@[miden_reflect_norm] theorem map_eval_lit_concrete (xs : List Felt) :
    List.map (Expr.eval concreteAssignment) (xs.map Expr.lit) = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [Expr.eval, ih]

/-- A memory read out of a `concreteState` evaluates to the concrete memory value. -/
@[simp, miden_reflect_norm] theorem eval_concreteState_memory
    (stackPrefix : List Felt) (mem : Nat → Felt)
    (frames : List MidenLean.LocalFrame) (adv : List Felt) (addr : Nat) :
    ((concreteState stackPrefix mem frames adv).memory addr).eval concreteAssignment = mem addr := by
  simp [concreteState, Expr.eval]

/-- A memory read out of a `concreteStateWithLocals` evaluates to the concrete
    memory value. -/
@[simp, miden_reflect_norm] theorem eval_concreteStateWithLocals_memory
    (stackPrefix : List Felt) (mem : Nat → Felt)
    (frames : List MidenLean.LocalFrame) (adv : List Felt)
    (numLocals : Nat) (addr : Nat) :
    ((concreteStateWithLocals stackPrefix mem frames adv numLocals).memory addr).eval
        concreteAssignment = mem addr := by
  simp [concreteStateWithLocals, Expr.eval]

/-- Push `Expr.eval` through a Lean-level conditional between two expressions. -/
@[simp, miden_reflect_norm] theorem eval_if_concreteAssignment
    (c : Prop) [Decidable c] (t e : Expr) :
    Expr.eval concreteAssignment (if c then t else e) =
      if c then Expr.eval concreteAssignment t else Expr.eval concreteAssignment e := by
  by_cases h : c <;> simp [h]

/-- An `Expr.ite` guarded by the literal `0` takes its else branch. -/
@[simp, miden_reflect_norm] theorem eval_ite_zero_concrete (a b : Expr) :
    Expr.eval concreteAssignment (.ite (.lit 0) a b) = Expr.eval concreteAssignment b := by
  change (if (((0 : Felt).val == 1) = true) then Expr.eval concreteAssignment a
      else Expr.eval concreteAssignment b) = Expr.eval concreteAssignment b
  simp

/-- An `Expr.ite` guarded by the literal `1` takes its then branch. -/
@[simp, miden_reflect_norm] theorem eval_ite_one_concrete (a b : Expr) :
    Expr.eval concreteAssignment (.ite (.lit 1) a b) = Expr.eval concreteAssignment a := by
  change (if (((1 : Felt).val == 1) = true) then Expr.eval concreteAssignment a
      else Expr.eval concreteAssignment b) = Expr.eval concreteAssignment a
  simp

/-- A literal `feltEq` flag is `1` exactly when the two literals agree. -/
@[simp, miden_reflect_norm] theorem eval_feltEq_lit_concrete_eq_one_iff
    (a b : Felt) :
    Expr.eval concreteAssignment ((Expr.lit a).feltEq (Expr.lit b)) = 1 ↔ a = b := by
  by_cases h : a = b <;> simp [Expr.eval, h]

/-- A literal `feltEq` flag is `0` exactly when the two literals differ. -/
@[simp, miden_reflect_norm] theorem eval_feltEq_lit_concrete_eq_zero_iff
    (a b : Felt) :
    Expr.eval concreteAssignment ((Expr.lit a).feltEq (Expr.lit b)) = 0 ↔ a ≠ b := by
  by_cases h : a = b <;> simp [Expr.eval, h]

/-- `val`-level version of `eval_feltEq_lit_concrete_eq_one_iff`. -/
@[simp, miden_reflect_norm] theorem val_eval_feltEq_lit_concrete_eq_one_iff
    (a b : Felt) :
    (Expr.eval concreteAssignment ((Expr.lit a).feltEq (Expr.lit b))).val = 1 ↔ a = b := by
  by_cases h : a = b <;> simp [Expr.eval, h]

/-- `val`-level version of `eval_feltEq_lit_concrete_eq_zero_iff`. -/
@[miden_reflect_norm] theorem val_eval_feltEq_lit_concrete_eq_zero_iff
    (a b : Felt) :
    (Expr.eval concreteAssignment ((Expr.lit a).feltEq (Expr.lit b))).val = 0 ↔ a ≠ b := by
  by_cases h : a = b <;> simp [Expr.eval, h]

/-- A literal `feltAnd` evaluates to the product of the two literals. -/
@[simp, miden_reflect_norm] theorem eval_feltAnd_lit_concrete
    (a b : Felt) :
    Expr.eval concreteAssignment ((Expr.lit a).feltAnd (Expr.lit b)) = a * b := by
  simp [Expr.eval]

/-- An `isBool` precondition on a literal reduces to a `0`/`1` disjunction. -/
@[simp, miden_reflect_norm] theorem holds_isBool_lit_concrete
    (a : Felt) :
    Precondition.holds (.isBool (.lit a)) concreteAssignment ↔ a = 0 ∨ a = 1 := by
  simp [Precondition.holds, Expr.eval]

/-- An `isBool` precondition on a literal `feltAnd` reduces to a `0`/`1`
    disjunction about the product. -/
@[simp, miden_reflect_norm] theorem holds_isBool_feltAnd_lit_concrete
    (a b : Felt) :
    Precondition.holds (.isBool ((Expr.lit a).feltAnd (Expr.lit b))) concreteAssignment ↔
      a * b = 0 ∨ a * b = 1 := by
  simp [Precondition.holds, Expr.eval]

/-! ### Widening-add carry chains

The `u32WidenAdd` / `u32WidenAdd3` handlers push a `Lo` node and a `Hi` node that
each embed the same operand subtrees, so along a carry chain the carry expression
reappears at every limb, and each limb consumes the previous carry as
`(Expr.eval σ carry).val` — a `ZMod.val ∘ Felt.ofNat` round-trip.

Unfolding `Expr.eval` alone cannot eliminate those round-trips, for two
independent reasons. `Expr.eval` spells the modulus `u32Max` while the round-trip
lemmas in `miden_val` / `miden_bound` are keyed on `2 ^ 32` and the goal side is
normalized to the literal `4294967296` (by `Nat.reducePow` in the default `simp`
set), so no spelling matches; and the general conditional route,
`felt_ofNat_val_lt`, needs a `< GOLDILOCKS_PRIME` side condition that the
discharger cannot establish for a nested carry. Nothing collapses, `simp`
re-traverses the duplicated subtrees, and the cost per chain depth measured
0.02s / 0.2s / 4.8s / >110s for depths 1–4 — the depth-4
`u128::overflowing_add` chain exceeded 4M heartbeats.

The eight lemmas below collapse one carry level in a single rewrite with no side
condition: the `.val` of a widening-add node is *unconditionally* below the
prime, because the operands are `Felt`s (so their sum is below `3 * (p - 1)`,
and dividing by `2 ^ 32` or reducing mod `2 ^ 32` lands well below `p`).

Two details matter:

* They are registered as **pre**-order (`↓`) rewrites. `simp` rewrites
  bottom-up, so by the time it reaches `(Expr.eval σ carry).val` the inner
  `Expr.eval` has already been unfolded to `Felt.ofNat …` and the fused
  `val`-of-`eval` pattern no longer matches. Firing before the descent is what
  keeps each level to one rewrite.
* The right-hand sides spell the modulus `2 ^ 32`, not `u32Max`, so that the
  usual literal normalization lands on the same form as the user's statement.

Scoped to `miden_reflect_norm` / `miden_val` rather than `@[simp]`: they are
normalization steps for reflected goals, not facts wanted in unrelated proofs. -/

/-- Evaluate the low word of a two-operand widening add. -/
@[miden_reflect_norm ↓, miden_val ↓] theorem eval_u32AddLo (σ : Assignment) (x y : Expr) :
    Expr.eval σ (x.u32AddLo y) =
      Felt.ofNat (((x.eval σ).val + (y.eval σ).val) % 2 ^ 32) := rfl

/-- Evaluate the carry of a two-operand widening add. -/
@[miden_reflect_norm ↓, miden_val ↓] theorem eval_u32AddHi (σ : Assignment) (x y : Expr) :
    Expr.eval σ (x.u32AddHi y) =
      Felt.ofNat (((x.eval σ).val + (y.eval σ).val) / 2 ^ 32) := rfl

/-- Evaluate the low word of a three-operand widening add. -/
@[miden_reflect_norm ↓, miden_val ↓] theorem eval_u32Add3Lo (σ : Assignment) (x y z : Expr) :
    Expr.eval σ (x.u32Add3Lo y z) =
      Felt.ofNat (((x.eval σ).val + (y.eval σ).val + (z.eval σ).val) % 2 ^ 32) := rfl

/-- Evaluate the carry of a three-operand widening add. -/
@[miden_reflect_norm ↓, miden_val ↓] theorem eval_u32Add3Hi (σ : Assignment) (x y z : Expr) :
    Expr.eval σ (x.u32Add3Hi y z) =
      Felt.ofNat (((x.eval σ).val + (y.eval σ).val + (z.eval σ).val) / 2 ^ 32) := rfl

/-- The low word of a two-operand widening add round-trips through `Felt`. -/
@[miden_reflect_norm ↓, miden_val ↓] theorem val_eval_u32AddLo (σ : Assignment) (x y : Expr) :
    (Expr.eval σ (x.u32AddLo y)).val = ((x.eval σ).val + (y.eval σ).val) % 2 ^ 32 := by
  rw [eval_u32AddLo]
  exact felt_ofNat_val_lt _ (u32_mod_lt_prime _)

/-- The carry of a two-operand widening add round-trips through `Felt`. -/
@[miden_reflect_norm ↓, miden_val ↓] theorem val_eval_u32AddHi (σ : Assignment) (x y : Expr) :
    (Expr.eval σ (x.u32AddHi y)).val = ((x.eval σ).val + (y.eval σ).val) / 2 ^ 32 := by
  rw [eval_u32AddHi]
  exact felt_ofNat_val_lt _ (sum_div_2_32_lt_prime _ _)

/-- The low word of a three-operand widening add round-trips through `Felt`. -/
@[miden_reflect_norm ↓, miden_val ↓] theorem val_eval_u32Add3Lo (σ : Assignment) (x y z : Expr) :
    (Expr.eval σ (x.u32Add3Lo y z)).val =
      ((x.eval σ).val + (y.eval σ).val + (z.eval σ).val) % 2 ^ 32 := by
  rw [eval_u32Add3Lo]
  exact felt_ofNat_val_lt _ (u32_mod_lt_prime _)

/-- The carry of a three-operand widening add round-trips through `Felt`. -/
@[miden_reflect_norm ↓, miden_val ↓] theorem val_eval_u32Add3Hi (σ : Assignment) (x y z : Expr) :
    (Expr.eval σ (x.u32Add3Hi y z)).val =
      ((x.eval σ).val + (y.eval σ).val + (z.eval σ).val) / 2 ^ 32 := by
  rw [eval_u32Add3Hi]
  exact felt_ofNat_val_lt _ (sum3_div_2_32_lt_prime _ _ _)

/-! ### Borrow-propagation chains

`u32OverflowSub` is the mirror image of `u32WidenAdd`: it pushes a
`.u32SubBorrow` node and a `.u32SubDiff` node sharing the same operand subtrees,
so a multi-limb subtraction threads the borrow expression through every limb and
consumes it as `(Expr.eval σ borrow).val` — the same `ZMod.val ∘ Felt.ofNat`
round-trip that gated the widening-add carry chains.

The failure mode is the more visible half of the add diagnosis: because
`u32OverflowingSub` is an opaque `if`, `simp` cannot make *any* progress on
`(Felt.ofNat (u32OverflowingSub _ _).2).val`, so it does not slow down with
depth, it simply gives up with the round-trips intact at every depth. The
conditional route `felt_ofNat_val_lt` is unavailable for the same reason as
before: its `< GOLDILOCKS_PRIME` side condition is not something the discharger
can establish for a nested borrow.

The six lemmas below collapse one borrow level per rewrite with no side
condition. Both components are *unconditionally* below the prime once the
operands come from `Felt`s: the borrow is `0` or `1`, and the difference is
either `a - b ≤ a < p` or, in the underflow branch, at most `2 ^ 32 - 1`
(Nat-truncated `u32Max - b + a` with `a < b`).

Registration follows the add family exactly, and for the same two reasons:
**pre**-order (`↓`) so the fused `val`-of-`eval` pattern is seen before `simp`
descends and unfolds the inner `Expr.eval`, and right-hand sides spelling
`u32OverflowingSub` — the form the manual statements and the `miden_bound`
lemmas already use — rather than the unfolded `if`. -/

/-- Evaluate the difference of an overflowing subtract. -/
@[miden_reflect_norm ↓, miden_val ↓] theorem eval_u32SubDiff (σ : Assignment) (x y : Expr) :
    Expr.eval σ (x.u32SubDiff y) =
      Felt.ofNat (u32OverflowingSub (x.eval σ).val (y.eval σ).val).2 := rfl

/-- Evaluate the borrow of an overflowing subtract. -/
@[miden_reflect_norm ↓, miden_val ↓] theorem eval_u32SubBorrow (σ : Assignment) (x y : Expr) :
    Expr.eval σ (x.u32SubBorrow y) =
      Felt.ofNat (u32OverflowingSub (x.eval σ).val (y.eval σ).val).1 := rfl

/-- Evaluate a wrapping subtract, which keeps only the difference. -/
@[miden_reflect_norm ↓, miden_val ↓] theorem eval_u32WSub (σ : Assignment) (x y : Expr) :
    Expr.eval σ (x.u32WSub y) =
      Felt.ofNat (u32OverflowingSub (x.eval σ).val (y.eval σ).val).2 := rfl

/-- The difference of an overflowing subtract round-trips through `Felt`. -/
@[miden_reflect_norm ↓, miden_val ↓] theorem val_eval_u32SubDiff (σ : Assignment) (x y : Expr) :
    (Expr.eval σ (x.u32SubDiff y)).val =
      (u32OverflowingSub (x.eval σ).val (y.eval σ).val).2 := by
  rw [eval_u32SubDiff]
  exact felt_ofNat_val_lt _
    (u32_overflow_sub_snd_lt _ _ (felt_val_lt_prime _) (felt_val_lt_prime _))

/-- The borrow of an overflowing subtract round-trips through `Felt`. -/
@[miden_reflect_norm ↓, miden_val ↓] theorem val_eval_u32SubBorrow (σ : Assignment) (x y : Expr) :
    (Expr.eval σ (x.u32SubBorrow y)).val =
      (u32OverflowingSub (x.eval σ).val (y.eval σ).val).1 := by
  rw [eval_u32SubBorrow]
  exact felt_ofNat_val_lt _ (u32_overflow_sub_fst_lt _ _)

/-- A wrapping subtract round-trips through `Felt`. -/
@[miden_reflect_norm ↓, miden_val ↓] theorem val_eval_u32WSub (σ : Assignment) (x y : Expr) :
    (Expr.eval σ (x.u32WSub y)).val =
      (u32OverflowingSub (x.eval σ).val (y.eval σ).val).2 := by
  rw [eval_u32WSub]
  exact felt_ofNat_val_lt _
    (u32_overflow_sub_snd_lt _ _ (felt_val_lt_prime _) (felt_val_lt_prime _))

/-! The next two lemmas are scoped to `miden_reflect_norm` only: as global
`@[simp]` lemmas they would silently rewrite `clo`/`cto` spellings in unrelated
manual proofs. -/

/-- Rewrite leading-ones counting into leading-zeros counting on the complement. -/
@[miden_reflect_norm] theorem u32CountLeadingOnes_eq (n : Nat) :
    u32CountLeadingOnes n = u32CountLeadingZeros (u32Max - 1 - n) := rfl

/-- Rewrite trailing-ones counting into trailing-zeros counting on the complement. -/
@[miden_reflect_norm] theorem u32CountTrailingOnes_eq (n : Nat) :
    u32CountTrailingOnes n = u32CountTrailingZeros (n ^^^ (u32Max - 1)) := rfl

/-- Turn a `Decidable.rec` with branch-independent results back into an `ite`;
    scoped to `miden_reflect_norm` to keep it out of unrelated `simp` calls. -/
@[miden_reflect_norm] theorem decidable_rec_const
    {P : Prop} [inst : Decidable P] {α : Sort*} (e t : α) :
    @Decidable.rec P (fun _ => α) (fun _ => e) (fun _ => t) inst =
    if P then t else e := by
  cases inst with
  | isFalse h => simp [h]
  | isTrue h => simp [h]

/-- Fuse nested boolean flags into a single flag guarded by a conjunction. -/
@[simp, miden_reflect_norm] theorem ite_then_ite_one_zero_and (p q : Prop)
    [Decidable p] [Decidable q] :
    (if p then (if q then (1 : Felt) else 0) else 0) =
      if p ∧ q then (1 : Felt) else 0 := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

/-! ### Modelling lemmas

The reflected literal states model the concrete states they were built from, for
any stack suffix `rest`. These discharge the `models` side conditions of the
soundness theorems below.
-/

@[simp] theorem concreteState_models
    (stackPrefix rest : List Felt) (mem : Nat → Felt)
    (frames : List MidenLean.LocalFrame) (adv : List Felt) :
    (concreteState stackPrefix mem frames adv).models
      ⟨stackPrefix ++ rest, mem, frames, adv⟩ (fun _ => 0) rest := by
  refine ⟨?_, ?_, rfl, ?_⟩
  · simp [concreteState]
  · intro addr
    simp [concreteState, Expr.eval]
  · simp [concreteState]

@[simp] theorem concreteStateWithLocals_models
    (stackPrefix rest : List Felt) (mem : Nat → Felt)
    (frames : List MidenLean.LocalFrame) (adv : List Felt)
    (numLocals : Nat) :
    (concreteStateWithLocals stackPrefix mem frames adv numLocals).models
      (let aligned := MidenLean.alignLocals numLocals
       let frame : MidenLean.LocalFrame :=
         { base := MidenLean.localsBase frames, numLocals, alignedNumLocals := aligned }
       ⟨stackPrefix ++ rest, mem, frame :: frames, adv⟩) (fun _ => 0) rest := by
  refine ⟨?_, ?_, rfl, ?_⟩
  · simp [concreteStateWithLocals]
  · intro addr
    simp [concreteStateWithLocals, Expr.eval]
  · simp [concreteStateWithLocals]

/-- Reflection for procedures with numLocals = 0.
    Memory, frames, and advice pass through based on the symbolic execution result. -/
theorem reflect_with_env_zero
    (insts : List Instruction) (name : String) (ops : List MidenLean.Op)
    (env : MidenLean.ProcEnv) (fuel : Nat)
    (stack : List Felt) (mem : Nat → Felt)
    (frames : List MidenLean.LocalFrame) (adv : List Felt)
    (rest : List Felt)
    (σ : Assignment)
    (initSS : State)
    (result : BlockResult)
    (hops : ops = insts.map MidenLean.Op.inst)
    (hfuel : fuel > 0)
    (hnoexec : insts.all (fun i => !isExecInst i) = true)
    (hmodels : initSS.models ⟨stack, mem, frames, adv⟩ σ rest)
    (hresult : execBlock insts initSS = some result)
    (hpreconds : ∀ p ∈ result.preconditions, p.holds σ) :
    MidenLean.execProcedure env fuel ⟨stack, mem, frames, adv⟩ ⟨name, 0, ops⟩ =
    some ⟨result.state.stack.map (Expr.eval σ) ++ rest,
          fun addr => (result.state.memory addr).eval σ,
          result.state.frames,
          result.state.advice.map (Expr.eval σ)⟩ := by
  rw [execProcedure_basic_block_zero env fuel ⟨stack, mem, frames, adv⟩ insts name ops
      hops hfuel hnoexec]
  obtain ⟨cs', hconc, hmod⟩ :=
    execBlock_sound insts initSS ⟨stack, mem, frames, adv⟩ σ rest result
      hmodels hresult hpreconds
  rw [hconc]
  unfold State.models at hmod
  obtain ⟨hstk, hmem, hfr, hadv⟩ := hmod
  congr 1
  cases cs'
  simp only [MidenLean.Concrete.State.mk.injEq] at hstk hmem hfr hadv ⊢
  exact ⟨hstk, funext hmem, hfr, hadv⟩

/-- Reflection for procedures with numLocals > 0.
    Frame is pushed before execution and popped after. -/
theorem reflect_with_env_locals
    (insts : List Instruction) (name : String) (k : Nat) (ops : List MidenLean.Op)
    (env : MidenLean.ProcEnv) (fuel : Nat)
    (stack : List Felt) (mem : Nat → Felt)
    (frames : List MidenLean.LocalFrame) (adv : List Felt)
    (rest : List Felt)
    (σ : Assignment)
    (initSS : State)
    (result : BlockResult)
    (hops : ops = insts.map MidenLean.Op.inst)
    (hfuel : fuel > 0)
    (hnoexec : insts.all (fun i => !isExecInst i) = true)
    (hmodels : initSS.models
      (let aligned := MidenLean.alignLocals (k + 1)
       let frame : MidenLean.LocalFrame :=
         { base := MidenLean.localsBase frames, numLocals := k + 1, alignedNumLocals := aligned }
       ⟨stack, mem, frame :: frames, adv⟩) σ rest)
    (hresult : execBlock insts initSS = some result)
    (hpreconds : ∀ p ∈ result.preconditions, p.holds σ) :
    MidenLean.execProcedure env fuel ⟨stack, mem, frames, adv⟩ ⟨name, k + 1, ops⟩ =
    some ⟨result.state.stack.map (Expr.eval σ) ++ rest,
          fun addr => (result.state.memory addr).eval σ,
          frames,
          result.state.advice.map (Expr.eval σ)⟩ := by
  cases frames with
  | nil =>
    rw [execProcedure_basic_block_locals env fuel ⟨stack, mem, [], adv⟩ insts name k ops
        hops hfuel hnoexec]
    dsimp only []
    obtain ⟨cs', hconc, hmod⟩ :=
      execBlock_sound insts initSS _ σ rest result
        hmodels hresult hpreconds
    rw [hconc]
    unfold State.models at hmod
    obtain ⟨hstk, hmem, _, hadv⟩ := hmod
    cases cs' with | mk s m f a =>
    simp only [] at hstk hmem hadv ⊢
    subst hstk; subst hadv
    exact congrArg some (by congr 1; exact funext hmem)
  | cons f rest_frames =>
    rw [execProcedure_basic_block_locals env fuel ⟨stack, mem, f :: rest_frames, adv⟩ insts name k ops
        hops hfuel hnoexec]
    dsimp only []
    obtain ⟨cs', hconc, hmod⟩ :=
      execBlock_sound insts initSS _ σ rest result
        hmodels hresult hpreconds
    rw [hconc]
    unfold State.models at hmod
    obtain ⟨hstk, hmem, _, hadv⟩ := hmod
    cases cs' with | mk s m fr a =>
    simp only [] at hstk hmem hadv ⊢
    subst hstk; subst hadv
    exact congrArg some (by congr 1; exact funext hmem)

/-- Tactic-facing zero-locals reflection wrapper for a fully concrete initial
    symbolic state. This hides the `State.models` setup proof. -/
theorem reflect_with_env_zero_concrete
    (insts : List Instruction) (name : String) (ops : List MidenLean.Op)
    (env : MidenLean.ProcEnv) (fuel : Nat)
    (stackPrefix rest : List Felt) (mem : Nat → Felt)
    (frames : List MidenLean.LocalFrame) (adv : List Felt)
    (result : BlockResult)
    (hops : ops = insts.map MidenLean.Op.inst)
    (hfuel : fuel > 0)
    (hnoexec : insts.all (fun i => !isExecInst i) = true)
    (hresult : execBlock insts (concreteState stackPrefix mem frames adv) = some result)
    (hpreconds : ∀ p ∈ result.preconditions, p.holds (fun _ => 0)) :
    MidenLean.execProcedure env fuel ⟨stackPrefix ++ rest, mem, frames, adv⟩ ⟨name, 0, ops⟩ =
    some ⟨result.state.stack.map (Expr.eval (fun _ => 0)) ++ rest,
          fun addr => (result.state.memory addr).eval (fun _ => 0),
          frames,
          result.state.advice.map (Expr.eval (fun _ => 0))⟩ := by
  have hmain :=
    reflect_with_env_zero insts name ops env fuel
      (stackPrefix ++ rest) mem frames adv
      rest
      (fun _ => 0)
      (concreteState stackPrefix mem frames adv)
      result
      hops hfuel hnoexec
      (concreteState_models stackPrefix rest mem frames adv)
      hresult hpreconds
  have hframes :
      result.state.frames = frames := by
    simpa [concreteState] using
      execBlock_preserves_frames insts (concreteState stackPrefix mem frames adv) result hresult
  simpa [hframes] using hmain

/-- Tactic-facing positive-locals reflection wrapper for a fully concrete
    initial symbolic state. This hides the `State.models` setup proof. -/
theorem reflect_with_env_locals_concrete
    (insts : List Instruction) (name : String) (k : Nat) (ops : List MidenLean.Op)
    (env : MidenLean.ProcEnv) (fuel : Nat)
    (stackPrefix rest : List Felt) (mem : Nat → Felt)
    (frames : List MidenLean.LocalFrame) (adv : List Felt)
    (result : BlockResult)
    (hops : ops = insts.map MidenLean.Op.inst)
    (hfuel : fuel > 0)
    (hnoexec : insts.all (fun i => !isExecInst i) = true)
    (hresult : execBlock insts (concreteStateWithLocals stackPrefix mem frames adv (k + 1)) = some result)
    (hpreconds : ∀ p ∈ result.preconditions, p.holds (fun _ => 0)) :
    MidenLean.execProcedure env fuel ⟨stackPrefix ++ rest, mem, frames, adv⟩ ⟨name, k + 1, ops⟩ =
    some ⟨result.state.stack.map (Expr.eval (fun _ => 0)) ++ rest,
          fun addr => (result.state.memory addr).eval (fun _ => 0),
          frames,
          result.state.advice.map (Expr.eval (fun _ => 0))⟩ := by
  simpa [concreteStateWithLocals] using
    reflect_with_env_locals insts name k ops env fuel
      (stackPrefix ++ rest) mem frames adv
      rest
      (fun _ => 0)
      (concreteStateWithLocals stackPrefix mem frames adv (k + 1))
      result
      hops hfuel hnoexec
      (concreteStateWithLocals_models stackPrefix rest mem frames adv (k + 1))
      hresult hpreconds

/-- Proc-generic zero-locals reflection wrapper. This lets the tactic apply
    reflection directly to named procedure constants rather than requiring the
    goal to already expose `⟨name, 0, body⟩` syntactically. -/
theorem reflect_proc_with_env_zero_concrete
    (proc : Procedure) (insts : List Instruction) (ops : List MidenLean.Op)
    (env : MidenLean.ProcEnv) (fuel : Nat)
    (stackPrefix rest : List Felt) (mem : Nat → Felt)
    (frames : List MidenLean.LocalFrame) (adv : List Felt)
    (result : BlockResult)
    (hbody : proc.body = ops)
    (hlocals : proc.numLocals = 0)
    (hops : ops = insts.map MidenLean.Op.inst)
    (hfuel : fuel > 0)
    (hnoexec : insts.all (fun i => !isExecInst i) = true)
    (hresult : execBlock insts (concreteState stackPrefix mem frames adv) = some result)
    (hpreconds : ∀ p ∈ result.preconditions, p.holds (fun _ => 0)) :
    MidenLean.execProcedure env fuel ⟨stackPrefix ++ rest, mem, frames, adv⟩ proc =
    some ⟨result.state.stack.map (Expr.eval (fun _ => 0)) ++ rest,
          fun addr => (result.state.memory addr).eval (fun _ => 0),
          frames,
          result.state.advice.map (Expr.eval (fun _ => 0))⟩ := by
  cases proc with
  | mk name numLocals body =>
      simp only at hbody hlocals
      subst body
      subst numLocals
      simpa using
        reflect_with_env_zero_concrete insts name ops env fuel
          stackPrefix rest mem frames adv result
          hops hfuel hnoexec hresult hpreconds

/-- Proc-generic positive-locals reflection wrapper. -/
theorem reflect_proc_with_env_locals_concrete
    (proc : Procedure) (insts : List Instruction) (ops : List MidenLean.Op)
    (env : MidenLean.ProcEnv) (fuel : Nat)
    (stackPrefix rest : List Felt) (mem : Nat → Felt)
    (frames : List MidenLean.LocalFrame) (adv : List Felt)
    (k : Nat) (result : BlockResult)
    (hbody : proc.body = ops)
    (hlocals : proc.numLocals = k + 1)
    (hops : ops = insts.map MidenLean.Op.inst)
    (hfuel : fuel > 0)
    (hnoexec : insts.all (fun i => !isExecInst i) = true)
    (hresult : execBlock insts (concreteStateWithLocals stackPrefix mem frames adv (k + 1)) = some result)
    (hpreconds : ∀ p ∈ result.preconditions, p.holds (fun _ => 0)) :
    MidenLean.execProcedure env fuel ⟨stackPrefix ++ rest, mem, frames, adv⟩ proc =
    some ⟨result.state.stack.map (Expr.eval (fun _ => 0)) ++ rest,
          fun addr => (result.state.memory addr).eval (fun _ => 0),
          frames,
          result.state.advice.map (Expr.eval (fun _ => 0))⟩ := by
  cases proc with
  | mk name numLocals body =>
      simp only at hbody hlocals
      subst body
      subst numLocals
      simpa using
        reflect_with_env_locals_concrete insts name k ops env fuel
          stackPrefix rest mem frames adv result
          (hops := hops) (hfuel := hfuel) (hnoexec := hnoexec)
          (hresult := hresult) (hpreconds := hpreconds)

/-- Proc-generic zero-locals wrapper that accepts an arbitrary concrete stack
    expression together with the definitional decomposition used for reflection. -/
theorem reflect_proc_with_env_zero_stack
    (proc : Procedure) (insts : List Instruction) (ops : List MidenLean.Op)
    (env : MidenLean.ProcEnv) (fuel : Nat)
    (stack stackPrefix rest : List Felt) (mem : Nat → Felt)
    (frames : List MidenLean.LocalFrame) (adv : List Felt)
    (result : BlockResult)
    (hstack : stack = stackPrefix ++ rest)
    (hbody : proc.body = ops)
    (hlocals : proc.numLocals = 0)
    (hops : ops = insts.map MidenLean.Op.inst)
    (hfuel : fuel > 0)
    (hnoexec : insts.all (fun i => !isExecInst i) = true)
    (hresult : execBlock insts (concreteState stackPrefix mem frames adv) = some result)
    (hpreconds : ∀ p ∈ result.preconditions, p.holds (fun _ => 0)) :
    MidenLean.execProcedure env fuel ⟨stack, mem, frames, adv⟩ proc =
    some ⟨result.state.stack.map (Expr.eval (fun _ => 0)) ++ rest,
          fun addr => (result.state.memory addr).eval (fun _ => 0),
          frames,
          result.state.advice.map (Expr.eval (fun _ => 0))⟩ := by
  subst hstack
  exact reflect_proc_with_env_zero_concrete proc insts ops env fuel
    stackPrefix rest mem frames adv result
    hbody hlocals hops hfuel hnoexec hresult hpreconds

/-- Proc-generic positive-locals wrapper with an explicit stack decomposition. -/
theorem reflect_proc_with_env_locals_stack
    (proc : Procedure) (insts : List Instruction) (ops : List MidenLean.Op)
    (env : MidenLean.ProcEnv) (fuel : Nat)
    (stack stackPrefix rest : List Felt) (mem : Nat → Felt)
    (frames : List MidenLean.LocalFrame) (adv : List Felt)
    (k : Nat) (result : BlockResult)
    (hstack : stack = stackPrefix ++ rest)
    (hbody : proc.body = ops)
    (hlocals : proc.numLocals = k + 1)
    (hops : ops = insts.map MidenLean.Op.inst)
    (hfuel : fuel > 0)
    (hnoexec : insts.all (fun i => !isExecInst i) = true)
    (hresult : execBlock insts (concreteStateWithLocals stackPrefix mem frames adv (k + 1)) = some result)
    (hpreconds : ∀ p ∈ result.preconditions, p.holds (fun _ => 0)) :
    MidenLean.execProcedure env fuel ⟨stack, mem, frames, adv⟩ proc =
    some ⟨result.state.stack.map (Expr.eval (fun _ => 0)) ++ rest,
          fun addr => (result.state.memory addr).eval (fun _ => 0),
          frames,
          result.state.advice.map (Expr.eval (fun _ => 0))⟩ := by
  subst hstack
  exact reflect_proc_with_env_locals_concrete proc insts ops env fuel
    stackPrefix rest mem frames adv k result
    hbody hlocals hops hfuel hnoexec hresult hpreconds

/-!
Generic straight-line reflection over `execProcedure`, with optional call
summaries carried by `ReflectEnv`.
-/

/-- Proof-facing symbolic summary for a named callee at a fixed minimum fuel. -/
structure ReflectSpec (env : MidenLean.ProcEnv) (minFuel : Nat) (name : String) where
  callee : Procedure
  spec : MidenLean.Symbolic.Spec
  hlookup : env name = some callee
  sound : spec.sound env minFuel callee

/-- Proof-facing symbolic environment used by `miden_reflect`.
    The `minFuel` index matches the concrete subcall fuel used by `opStep`. -/
abbrev ReflectEnv (env : MidenLean.ProcEnv) (minFuel : Nat) :=
  (name : String) → Option (ReflectSpec env minFuel name)

/-- Empty reflection environment for no-call procedures. -/
def ReflectEnv.empty {env : MidenLean.ProcEnv} {minFuel : Nat} : ReflectEnv env minFuel := fun _ => none

/-- Forget the soundness proofs and expose only the symbolic summaries. -/
def ReflectEnv.toSymbolic {env : MidenLean.ProcEnv} {minFuel : Nat}
    (Γ : ReflectEnv env minFuel) : MidenLean.Symbolic.ProcEnv :=
  fun name => (Γ name).map fun rs => rs.spec

@[simp] theorem ReflectEnv.toSymbolic_empty
    {env : MidenLean.ProcEnv} {minFuel : Nat} (name : String) :
    (ReflectEnv.empty (env := env) (minFuel := minFuel)).toSymbolic name = none := by
  simp [ReflectEnv.toSymbolic, ReflectEnv.empty]

/-- The callee-soundness premise required by `execOps_sound` follows from a
    `ReflectEnv`. -/
theorem ReflectEnv.toSymbolic_sound {env : MidenLean.ProcEnv} {minFuel : Nat}
    (Γ : ReflectEnv env minFuel) :
    ∀ name (spec : MidenLean.Symbolic.Spec),
      Γ.toSymbolic name = some spec →
      ∃ callee, env name = some callee ∧ spec.sound env minFuel callee := by
  intro name spec hspec
  unfold ReflectEnv.toSymbolic at hspec
  cases hΓ : Γ name with
  | none =>
      simp [hΓ] at hspec
  | some rs =>
      have hrs : rs.spec = spec := by
        simpa [hΓ] using hspec
      subst spec
      exact ⟨rs.callee, rs.hlookup, rs.sound⟩

/-- Symbolic execution of a whole straight-line procedure, including local-frame
    allocation/pop for `numLocals > 0`. -/
def execProcedure (senv : MidenLean.Symbolic.ProcEnv) (proc : Procedure) (s : State) :
    Option BlockResult :=
  match proc.numLocals with
  | 0 =>
      execOps senv proc.body s
  | k + 1 =>
      let aligned := MidenLean.alignLocals (k + 1)
      let frame : MidenLean.LocalFrame := { base := MidenLean.localsBase s.frames,
                                            numLocals := k + 1, alignedNumLocals := aligned }
      let s' := { s with frames := frame :: s.frames }
      match execOps senv proc.body s' with
      | some result =>
          some { result with state := { result.state with frames := s.frames } }
      | none => none

/-- Turn a procedure into a symbolic summary relative to a `ReflectEnv`. -/
def procSpec {env : MidenLean.ProcEnv} {minFuel : Nat}
    (Γ : ReflectEnv env minFuel) (proc : Procedure) : MidenLean.Symbolic.Spec where
  transform := execProcedure (Γ.toSymbolic) proc

private theorem models_pushFrame
    (ss : State) (cs : Concrete.State) (σ : Assignment) (rest : List Felt)
    (frame : MidenLean.LocalFrame)
    (hmodels : ss.models cs σ rest) :
    ({ ss with frames := frame :: ss.frames }).models
      ({ cs with frames := frame :: cs.frames }) σ rest := by
  rcases hmodels with ⟨hstk, hmem, hframes, hadv⟩
  exact ⟨hstk, hmem, by simp [hframes], hadv⟩

private theorem models_restoreFrames
    (ss : State) (cs : Concrete.State) (σ : Assignment) (rest : List Felt)
    (frames : List MidenLean.LocalFrame)
    (hmodels : ss.models cs σ rest) :
    ({ ss with frames := frames }).models
      ({ cs with frames := frames }) σ rest := by
  rcases hmodels with ⟨hstk, hmem, _, hadv⟩
  exact ⟨hstk, hmem, rfl, hadv⟩

/-- Soundness for `execProcedure` at the exact concrete fuel budget
    `minFuel + 1`. -/
theorem execProcedure_sound
    (senv : MidenLean.Symbolic.ProcEnv) (env : MidenLean.ProcEnv) (minFuel : Nat)
    (proc : Procedure) (ss : State) (cs : Concrete.State)
    (σ : Assignment) (rest : List Felt) (result : BlockResult)
    (hmodels : ss.models cs σ rest)
    (hresult : execProcedure senv proc ss = some result)
    (hpreconds : ∀ p ∈ result.preconditions, p.holds σ)
    (hcallees : ∀ name (spec : MidenLean.Symbolic.Spec),
      senv name = some spec →
      ∃ callee, env name = some callee ∧ spec.sound env minFuel callee) :
    ∃ cs', MidenLean.execProcedure env (minFuel + 1) cs proc = some cs'
      ∧ result.state.models cs' σ rest := by
  cases proc with
  | mk name numLocals body =>
      cases numLocals with
      | zero =>
          simp only [execProcedure] at hresult
          obtain ⟨cs', hconc, hmod⟩ :=
            execOps_sound senv env minFuel body ss cs σ rest result
              hmodels hresult hpreconds hcallees
          have hconc' :
              MidenLean.execProcedure env (minFuel + 1) cs
                { name := name, numLocals := 0, body := body } = some cs' := by
            rw [MidenLean.execProcedure_body_eq env (minFuel + 1) cs
                { name := name, numLocals := 0, body := body } body rfl rfl]
            simpa [MidenLean.execProcedure_ofOps] using hconc
          exact ⟨cs', hconc', hmod⟩
      | succ k =>
          let aligned := MidenLean.alignLocals (k + 1)
          let base := MidenLean.localsBase ss.frames
          let frame : MidenLean.LocalFrame := { base, numLocals := k + 1, alignedNumLocals := aligned }
          let ss' : State := { ss with frames := frame :: ss.frames }
          have hframes0 : cs.frames = ss.frames := by
            rcases hmodels with ⟨_, _, hframes0, _⟩
            exact hframes0
          let cbase := MidenLean.localsBase cs.frames
          let cframe : MidenLean.LocalFrame :=
            { base := cbase, numLocals := k + 1, alignedNumLocals := MidenLean.alignLocals (k + 1) }
          let cs' : Concrete.State := { cs with frames := cframe :: cs.frames }
          have hcbase : cbase = base := by
            unfold cbase base
            rw [hframes0]
          have haligned : MidenLean.alignLocals (k + 1) = aligned := by rfl
          have hcframe : cframe = frame := by
            simp [cframe, frame, hcbase, haligned]
          have hmodels' : ss'.models cs' σ rest := by
            simpa [ss', cs', hcframe] using
              (models_pushFrame ss cs σ rest frame hmodels)
          cases hexecOps : execOps senv body ss' with
          | none =>
              simp [execProcedure, aligned, base, frame, ss', hexecOps] at hresult
          | some bodyResult =>
              simp only [execProcedure, hexecOps, Option.some.injEq, aligned, ss', base,
                frame] at hresult
              subst result
              obtain ⟨csMid, hconcBody, hmodBody⟩ :=
                execOps_sound senv env minFuel body ss' cs' σ rest bodyResult
                  hmodels' hexecOps hpreconds hcallees
              have hconcProc :
                  MidenLean.execProcedure env (minFuel + 1) cs
                    { name := name, numLocals := k + 1, body := body } =
                  some { csMid with frames := cs.frames } := by
                have hconcBody' :
                    MidenLean.execProcedure env (minFuel + 1) cs' body = some csMid := by
                  simpa [MidenLean.execProcedure_ofOps] using hconcBody
                rw [MidenLean.execProcedure_body_eq_withLocals env (minFuel + 1) cs
                    { name := name, numLocals := k + 1, body := body } body k rfl rfl]
                simpa [cs', cframe, cbase] using
                  congrArg
                    (fun x =>
                      match x with
                      | some r => some { r with frames := cs.frames }
                      | none => none)
                    hconcBody'
              refine ⟨{ csMid with frames := cs.frames }, hconcProc, ?_⟩
              simpa [hframes0] using
                models_restoreFrames bodyResult.state csMid σ rest cs.frames hmodBody

/-- A procedure executed symbolically against a `ReflectEnv` yields a sound
    summary for the next-higher concrete fuel level. -/
theorem procSpec_sound {env : MidenLean.ProcEnv} {minFuel : Nat}
    (Γ : ReflectEnv env minFuel) (proc : Procedure) :
    (procSpec Γ proc).sound env (minFuel + 1) proc := by
  intro ss cs σ rest result fuel hfuel hresult hmodels hpreconds
  obtain ⟨cs', hbase, hmod⟩ :=
    execProcedure_sound (senv := Γ.toSymbolic) (env := env) (minFuel := minFuel)
      proc ss cs σ rest result hmodels hresult hpreconds (ReflectEnv.toSymbolic_sound Γ)
  exact ⟨cs', MidenLean.execProcedure_fuel_mono hfuel hbase, hmod⟩

/-- Build a proof-carrying reflection environment directly from a reducible
    concrete `ProcEnv`, bounded by both the minimum concrete subcall fuel and
    a hard recursion-depth cap.

    `maxDepth` limits how many nested layers of callee summaries are produced.
    Once the depth cap is reached, the environment falls back to
    `ReflectEnv.empty`, forcing the reflection tactic to use a registered
    `_exec` summary or fail. The cap prevents the kernel from unfolding the
    full `minFuel` levels of nested `procSpec` calls during type checking,
    which otherwise exhausts the stack on large `ProcEnv`s such as
    `u128ProcEnv` (17 procedures × default fuel ≈ 30 yields ~424K nested
    `List.rec` unfoldings).

    A typical caller chain in the core library is at most depth 3
    (rotl → shl → wrapping_mul), so a depth cap of `8` is generous and safe. -/
def ReflectEnv.ofConcrete (env : MidenLean.ProcEnv) (maxDepth : Nat) :
    (minFuel : Nat) → ReflectEnv env minFuel
  | 0 => ReflectEnv.empty
  | n + 1 =>
      match maxDepth with
      | 0 => ReflectEnv.empty
      | maxDepth' + 1 => fun name =>
          match hlookup : env name with
          | some proc =>
              some
                { callee := proc
                  spec := procSpec (ReflectEnv.ofConcrete env maxDepth' n) proc
                  hlookup := hlookup
                  sound := by
                    simpa using
                      (procSpec_sound
                        (Γ := ReflectEnv.ofConcrete env maxDepth' n) (proc := proc)) }
          | none => none

@[simp] theorem ReflectEnv.toSymbolic_ofConcrete_minFuel_zero
    (env : MidenLean.ProcEnv) (maxDepth : Nat) (name : String) :
    (ReflectEnv.ofConcrete env maxDepth 0).toSymbolic name = none := by
  simp [ReflectEnv.ofConcrete]

@[simp] theorem ReflectEnv.toSymbolic_ofConcrete_maxDepth_zero
    (env : MidenLean.ProcEnv) (n : Nat) (name : String) :
    (ReflectEnv.ofConcrete env 0 (n + 1)).toSymbolic name = none := by
  simp [ReflectEnv.ofConcrete]

@[simp] theorem ReflectEnv.toSymbolic_ofConcrete_succ
    (env : MidenLean.ProcEnv) (maxDepth n : Nat) (name : String) :
    (ReflectEnv.ofConcrete env (maxDepth + 1) (n + 1)).toSymbolic name =
      Option.map (fun proc => procSpec (ReflectEnv.ofConcrete env maxDepth n) proc) (env name) := by
  dsimp only [ReflectEnv.toSymbolic, ReflectEnv.ofConcrete]
  split <;> simp [*]

/-- Procedure-level reflection over a fully concrete symbolic state, using an
    explicit `ReflectEnv` for direct callees. -/
theorem reflect_proc_concrete_using
    (proc : Procedure) (env : MidenLean.ProcEnv) (fuel : Nat)
    (Γ : ReflectEnv env (fuel - 1))
    (stackPrefix rest : List Felt) (mem : Nat → Felt)
    (frames : List MidenLean.LocalFrame) (adv : List Felt)
    (result : BlockResult)
    (hfuel : fuel > 0)
    (hresult : execProcedure (Γ.toSymbolic) proc
      (concreteState stackPrefix mem frames adv) = some result)
    (hpreconds : ∀ p ∈ result.preconditions, p.holds concreteAssignment) :
    MidenLean.execProcedure env fuel ⟨stackPrefix ++ rest, mem, frames, adv⟩ proc =
    some ⟨result.state.stack.map (Expr.eval concreteAssignment) ++ rest,
          fun addr => (result.state.memory addr).eval concreteAssignment,
          result.state.frames,
          result.state.advice.map (Expr.eval concreteAssignment)⟩ := by
  have hmain :=
    execProcedure_sound (senv := Γ.toSymbolic) (env := env) (minFuel := fuel - 1)
      proc (concreteState stackPrefix mem frames adv)
      ⟨stackPrefix ++ rest, mem, frames, adv⟩ concreteAssignment rest result
      (concreteState_models stackPrefix rest mem frames adv)
      hresult hpreconds (ReflectEnv.toSymbolic_sound Γ)
  obtain ⟨cs', hconc, hmod⟩ := hmain
  have hconc' :
      MidenLean.execProcedure env fuel ⟨stackPrefix ++ rest, mem, frames, adv⟩ proc = some cs' := by
    have hfuel' : fuel - 1 + 1 = fuel := by omega
    simpa [hfuel'] using hconc
  rw [hconc']
  unfold State.models at hmod
  obtain ⟨hstk, hmem, hframes, hadv⟩ := hmod
  cases cs'
  simp only [Option.some.injEq, MidenLean.Concrete.State.mk.injEq] at hstk hmem hframes hadv ⊢
  exact ⟨hstk, funext hmem, hframes, hadv⟩

/-- Procedure-level reflection over a fully concrete symbolic state with no
    callee summaries. -/
theorem reflect_proc_concrete
    (proc : Procedure) (env : MidenLean.ProcEnv) (fuel : Nat)
    (stackPrefix rest : List Felt) (mem : Nat → Felt)
    (frames : List MidenLean.LocalFrame) (adv : List Felt)
    (result : BlockResult)
    (hfuel : fuel > 0)
    (hresult : execProcedure ((ReflectEnv.empty (env := env) (minFuel := fuel - 1)).toSymbolic) proc
      (concreteState stackPrefix mem frames adv) = some result)
    (hpreconds : ∀ p ∈ result.preconditions, p.holds concreteAssignment) :
    MidenLean.execProcedure env fuel ⟨stackPrefix ++ rest, mem, frames, adv⟩ proc =
    some ⟨result.state.stack.map (Expr.eval concreteAssignment) ++ rest,
          fun addr => (result.state.memory addr).eval concreteAssignment,
          result.state.frames,
          result.state.advice.map (Expr.eval concreteAssignment)⟩ := by
  exact reflect_proc_concrete_using proc env fuel
    (Γ := ReflectEnv.empty (env := env) (minFuel := fuel - 1))
    stackPrefix rest mem frames adv result hfuel hresult hpreconds

/-- Procedure-level reflection with an explicit stack decomposition. -/
theorem reflect_proc_stack_using
    (proc : Procedure) (env : MidenLean.ProcEnv) (fuel : Nat)
    (Γ : ReflectEnv env (fuel - 1))
    (stack stackPrefix rest : List Felt) (mem : Nat → Felt)
    (frames : List MidenLean.LocalFrame) (adv : List Felt)
    (result : BlockResult)
    (hstack : stack = stackPrefix ++ rest)
    (hfuel : fuel > 0)
    (hresult : execProcedure (Γ.toSymbolic) proc
      (concreteState stackPrefix mem frames adv) = some result)
    (hpreconds : ∀ p ∈ result.preconditions, p.holds concreteAssignment) :
    MidenLean.execProcedure env fuel ⟨stack, mem, frames, adv⟩ proc =
    some ⟨result.state.stack.map (Expr.eval concreteAssignment) ++ rest,
          fun addr => (result.state.memory addr).eval concreteAssignment,
          result.state.frames,
          result.state.advice.map (Expr.eval concreteAssignment)⟩ := by
  subst hstack
  exact reflect_proc_concrete_using proc env fuel Γ
    stackPrefix rest mem frames adv result hfuel hresult hpreconds

/-- Procedure-level reflection with an explicit stack decomposition and no
    callee summaries. -/
theorem reflect_proc_stack
    (proc : Procedure) (env : MidenLean.ProcEnv) (fuel : Nat)
    (stack stackPrefix rest : List Felt) (mem : Nat → Felt)
    (frames : List MidenLean.LocalFrame) (adv : List Felt)
    (result : BlockResult)
    (hstack : stack = stackPrefix ++ rest)
    (hfuel : fuel > 0)
    (hresult : execProcedure ((ReflectEnv.empty (env := env) (minFuel := fuel - 1)).toSymbolic) proc
      (concreteState stackPrefix mem frames adv) = some result)
    (hpreconds : ∀ p ∈ result.preconditions, p.holds concreteAssignment) :
    MidenLean.execProcedure env fuel ⟨stack, mem, frames, adv⟩ proc =
    some ⟨result.state.stack.map (Expr.eval concreteAssignment) ++ rest,
          fun addr => (result.state.memory addr).eval concreteAssignment,
          result.state.frames,
          result.state.advice.map (Expr.eval concreteAssignment)⟩ := by
  subst hstack
  exact reflect_proc_concrete proc env fuel
    stackPrefix rest mem frames adv result hfuel hresult hpreconds

/-- Procedure-level reflection for theorem goals over a concrete `s` with a
    stack-decomposition hypothesis, using an explicit `ReflectEnv`. -/
theorem reflect_proc_state_using
    (proc : Procedure) (env : MidenLean.ProcEnv) (fuel : Nat)
    (Γ : ReflectEnv env (fuel - 1))
    (s : MidenLean.Concrete.State) (stackPrefix rest : List Felt)
    (result : BlockResult)
    (hstack : s.stack = stackPrefix ++ rest)
    (hfuel : fuel > 0)
    (hresult : execProcedure (Γ.toSymbolic) proc
      (concreteState stackPrefix s.memory s.frames s.advice) = some result)
    (hpreconds : ∀ p ∈ result.preconditions, p.holds concreteAssignment) :
    MidenLean.execProcedure env fuel s proc =
    some ⟨result.state.stack.map (Expr.eval concreteAssignment) ++ rest,
          fun addr => (result.state.memory addr).eval concreteAssignment,
          result.state.frames,
          result.state.advice.map (Expr.eval concreteAssignment)⟩ := by
  cases s with
  | mk stack mem frames adv =>
      simp only at hstack ⊢
      subst hstack
      exact reflect_proc_stack_using proc env fuel Γ
        (stack := stackPrefix ++ rest)
        stackPrefix rest mem frames adv result rfl hfuel hresult hpreconds

/-- Procedure-level reflection for theorem goals over a concrete `s` with a
    stack-decomposition hypothesis and no callee summaries. -/
theorem reflect_proc_state
    (proc : Procedure) (env : MidenLean.ProcEnv) (fuel : Nat)
    (s : MidenLean.Concrete.State) (stackPrefix rest : List Felt)
    (result : BlockResult)
    (hstack : s.stack = stackPrefix ++ rest)
    (hfuel : fuel > 0)
    (hresult : execProcedure ((ReflectEnv.empty (env := env) (minFuel := fuel - 1)).toSymbolic) proc
      (concreteState stackPrefix s.memory s.frames s.advice) = some result)
    (hpreconds : ∀ p ∈ result.preconditions, p.holds concreteAssignment) :
    MidenLean.execProcedure env fuel s proc =
    some ⟨result.state.stack.map (Expr.eval concreteAssignment) ++ rest,
          fun addr => (result.state.memory addr).eval concreteAssignment,
          result.state.frames,
          result.state.advice.map (Expr.eval concreteAssignment)⟩ := by
  cases s with
  | mk stack mem frames adv =>
      simp only at hstack ⊢
      subst hstack
      exact reflect_proc_stack proc env fuel
        (stack := stackPrefix ++ rest)
        stackPrefix rest mem frames adv result rfl hfuel hresult hpreconds

end MidenLean.Symbolic.Reflect

-- The shared lemma/unfold set used by every reflection cleanup ladder
-- (`miden_finish_reflection`, `finalizeCleanupGoals`, `cleanupExecSummaryGoals`).
-- Registered once here so the ladders can say `simp [miden_cleanup, ...]`
-- instead of each repeating the full list.
attribute [miden_cleanup]
  and_assoc and_left_comm and_comm
  MidenLean.Concrete.State.withStack
  MidenLean.Symbolic.Precondition.holds
  MidenLean.Symbolic.Expr.eval
  MidenLean.Symbolic.Reflect.concreteAssignment
  MidenLean.Symbolic.Reflect.concreteState
  MidenLean.Symbolic.Reflect.concreteStateWithLocals
  MidenLean.LocalFrame.localAddr
