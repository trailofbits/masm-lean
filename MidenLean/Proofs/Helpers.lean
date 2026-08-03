import MidenLean.Concrete.Exec
import MidenLean.Proofs.SimpAttrs
import MidenLean.Symbolic.SimpAttrs

/-!
# Shared proof helpers

Small reusable lemmas consumed both by the manual procedure proofs under
`MidenLean/Proofs/` and by the cleanup ladders of the `miden_*` tactics
(`miden_arith`, `miden_finish_reflection`, `miden_vcg`, `miden_reflect`).

The file is organized into five groups:

* **state projections** — how `Concrete.State.withStack` and
  `Concrete.State.writeMemory` interact with the individual state fields;
* **`ite` normalization** — pushing conditionals inwards so that state-valued,
  `Option`-valued, and `Felt`-valued branches collapse into one canonical shape;
* **execution decomposition** — splitting `execProcedure` over appended op
  lists, singleton `exec` calls, `ifElse` blocks, and local-frame allocation;
* **`Felt` values and arithmetic bounds** — `val`/`isU32` facts and round-trip
  lemmas, mostly tagged `@[miden_bound]` for the bound-discharging ladder;
* **local frames** — `LocalFrame.localAddr` comparison lemmas that let memory
  reads through the `ite` chains produced by `loc_store*` be resolved by `simp`.

Most lemmas carry `@[simp]`, `@[miden_bound]`, or `@[miden_reflect_norm]`, so
they are normally applied automatically rather than named in a proof.
-/

namespace MidenLean

/-! ### State projections

Field-level reduction lemmas for the two state constructors used by the
instruction semantics. All of them hold by `rfl` and are `@[simp]` so that
goals about a rewritten state reduce to goals about its fields.
-/

/-- `withStack` replaces the stack. -/
@[simp] theorem Concrete.State.withStack_stack (s : Concrete.State) (stk : List Felt) :
    (s.withStack stk).stack = stk := rfl

/-- `withStack` leaves memory untouched. -/
@[simp] theorem Concrete.State.withStack_memory (s : Concrete.State) (stk : List Felt) :
    (s.withStack stk).memory = s.memory := rfl

/-- `withStack` leaves the advice provider untouched. -/
@[simp] theorem Concrete.State.withStack_advice (s : Concrete.State) (stk : List Felt) :
    (s.withStack stk).advice = s.advice := rfl

/-- Consecutive stack replacements collapse to the last one. -/
@[simp] theorem Concrete.State.withStack_withStack (s : Concrete.State) (stk1 stk2 : List Felt) :
    (s.withStack stk1).withStack stk2 = s.withStack stk2 := rfl

/-- `withStack` leaves the local-frame stack untouched. -/
@[simp] theorem Concrete.State.withStack_frames (s : Concrete.State) (stk : List Felt) :
    (s.withStack stk).frames = s.frames := rfl

/-- A memory write leaves the stack untouched. -/
@[simp] theorem Concrete.State.writeMemory_stack (s : Concrete.State) (addr : Nat) (v : Felt) :
    (s.writeMemory addr v).stack = s.stack := rfl

/-- A memory write updates exactly the written address. -/
@[simp] theorem Concrete.State.writeMemory_memory (s : Concrete.State) (addr : Nat) (v : Felt) :
    (s.writeMemory addr v).memory = fun a => if a = addr then v else s.memory a := rfl

/-- A memory write leaves the local-frame stack untouched. -/
@[simp] theorem Concrete.State.writeMemory_frames (s : Concrete.State) (addr : Nat) (v : Felt) :
    (s.writeMemory addr v).frames = s.frames := rfl

/-- A memory write leaves the advice provider untouched. -/
@[simp] theorem Concrete.State.writeMemory_advice (s : Concrete.State) (addr : Nat) (v : Felt) :
    (s.writeMemory addr v).advice = s.advice := rfl

/-- Two writes to the same address collapse to the later one. -/
@[simp] theorem Concrete.State.writeMemory_overwrite (s : Concrete.State) (addr : Nat) (v w : Felt) :
    (s.writeMemory addr v).writeMemory addr w = s.writeMemory addr w := by
  simp only [Concrete.State.writeMemory, Concrete.State.mk.injEq, and_self, and_true, true_and]
  funext a; split <;> simp

/-! ### `ite` normalization for states and options

Branches that differ only in the value they carry are pushed inwards, so that a
conditional over states or `Option`s becomes a single state (or `some`) carrying
a conditional value. This keeps later projection and `simp` steps from having to
case split.
-/

/-- Push a conditional between two `withStack` states into the stack argument. -/
@[simp, miden_reflect_norm] theorem Concrete.State.ite_withStack
    (p : Prop) [Decidable p] (s : Concrete.State) (stk1 stk2 : List Felt) :
    (if p then s.withStack stk1 else s.withStack stk2) =
      s.withStack (if p then stk1 else stk2) := by
  by_cases hp : p <;> simp [hp]

/-- Push a conditional between two `some` values into the payload. -/
@[simp, miden_reflect_norm] theorem ite_some
    {α : Type} (p : Prop) [Decidable p] (x y : α) :
    (if p then some x else some y : Option α) = some (if p then x else y) := by
  by_cases hp : p <;> simp [hp]

/-! ### Execution decomposition

Lemmas that break an `execProcedure` goal into smaller pieces: sequential
composition of op lists, resolution of a singleton `exec` call, reduction of a
singleton `ifElse` block, and the body/local-frame view of a `Procedure`.
-/

/-- Execute a concatenation of op lists in two phases under a procedure environment. -/
theorem execProcedure_append (env : ProcEnv) (fuel : Nat) (s : Concrete.State) (xs ys : List Op) :
    execProcedure env fuel s (xs ++ ys) = (do
      let s' ← execProcedure env fuel s xs
      execProcedure env fuel s' ys) := by
  cases fuel with
  | zero =>
      unfold execProcedure
      simp
  | succ fuel' =>
      simp [execProcedure, Procedure.ofOps]

/-- Equality-oriented append decomposition for `execProcedure`. -/
theorem execProcedure_append_eq
    (env : ProcEnv) (fuel : Nat) (s : Concrete.State)
    (xs ys : List Op) (s' s'' : Concrete.State)
    (hexec₁ : execProcedure env fuel s xs = some s')
    (hexec₂ : execProcedure env fuel s' ys = some s'') :
    execProcedure env fuel s (xs ++ ys) = some s'' := by
  rw [execProcedure_append, hexec₁]
  simp [hexec₂]

/-- Execute a singleton `.exec` op by jumping directly to the resolved callee.
    This is the bridge used by theorem-backed call summaries in `miden_reflect`
    and `miden_vcg`. -/
theorem execProcedure_singleton_exec_eq
    (env : ProcEnv) (fuel : Nat) (s : Concrete.State)
    (target : String) (callee : Procedure)
    (hlookup : env target = some callee) :
    execProcedure env (fuel + 1) s [Op.inst (.exec target)] =
      execProcedure env fuel s callee := by
  simp [execProcedure, Procedure.ofOps, hlookup]

/-- State-level singleton `.exec` bridge for arbitrary positive fuel.
    This is convenient for tactic-driven rewrites on nested call sites, where
    the ambient goal often exposes `execProcedure env fuel s [exec "..."]`
    directly rather than a syntactic `(fuel + 1)` shape. -/
theorem execProcedure_singleton_exec_state
    (env : ProcEnv) (fuel : Nat) (s : Concrete.State)
    (target : String) (callee : Procedure)
    (hlookup : env target = some callee)
    (hfuel : fuel > 0) :
    execProcedure env fuel s [Op.inst (.exec target)] =
      execProcedure env (fuel - 1) s callee := by
  cases fuel with
  | zero => omega
  | succ fuel' =>
      simp [execProcedure, Procedure.ofOps, hlookup]

/-- Execute a concatenation of op lists in two phases under a procedure environment. -/
theorem execOps_append (env : ProcEnv) (fuel : Nat) (s : Concrete.State) (xs ys : List Op) :
    execOps env fuel s (xs ++ ys) = (do
      let s' ← execOps env fuel s xs
      execOps env fuel s' ys) := by
  simpa [execOps] using execProcedure_append env fuel s xs ys

/-- Execute a concatenation of straight-line op lists in two phases. -/
theorem exec_append (fuel : Nat) (s : Concrete.State) (xs ys : List Op) :
    execProcedure emptyEnv fuel s (xs ++ ys) = (do
      let s' ← execProcedure emptyEnv fuel s xs
      execProcedure emptyEnv fuel s' ys) := by
  simpa [emptyEnv] using execOps_append (env := fun _ => none) fuel s xs ys

/-! ### `Felt` values

The two literal `val` computations that the `ifElse` reduction lemmas below rely
on when inspecting a boolean condition sitting on top of the stack.
-/

/-- The `val` of the zero field element is `0`. -/
@[simp] theorem Felt.val_zero' : (0 : Felt).val = 0 := rfl

/-- The `val` of the one field element is `1`. -/
@[simp] theorem Felt.val_one' : (1 : Felt).val = 1 := ZMod.val_one _

/-- Reduce a singleton `.ifElse` op when the condition on the stack is `1`. -/
theorem execProcedure_ifElse_one
    (env : ProcEnv) (fuel : Nat)
    (rest : List Felt) (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (thenBlk elseBlk : List Op) :
    execProcedure env (fuel + 2)
      ⟨(1 : Felt) :: rest, mem, frames, adv⟩
      ([.ifElse thenBlk elseBlk] : List Op) =
    execProcedure env (fuel + 1) ⟨rest, mem, frames, adv⟩ thenBlk := by
  conv_lhs => unfold execProcedure
  simp only [Procedure.ofOps, List.foldlM, Concrete.State.withStack]
  dsimp only [bind, Bind.bind, Option.bind, pure, Pure.pure]
  have hv1 : (1 : Felt).val = 1 := Felt.val_one'
  have hbeq : ((1 : Nat) == 1) = true := by decide
  simp only [hv1, hbeq, ↓reduceIte]
  cases execProcedure env (fuel + 1) ⟨rest, mem, frames, adv⟩ thenBlk <;> rfl

/-- Reduce a singleton `.ifElse` op when the condition on the stack is `0`. -/
theorem execProcedure_ifElse_zero
    (env : ProcEnv) (fuel : Nat)
    (rest : List Felt) (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (thenBlk elseBlk : List Op) :
    execProcedure env (fuel + 2)
      ⟨(0 : Felt) :: rest, mem, frames, adv⟩
      ([.ifElse thenBlk elseBlk] : List Op) =
    execProcedure env (fuel + 1) ⟨rest, mem, frames, adv⟩ elseBlk := by
  conv_lhs => unfold execProcedure
  simp only [Procedure.ofOps, List.foldlM, Concrete.State.withStack]
  dsimp only [bind, Bind.bind, Option.bind, pure, Pure.pure]
  have hv0 : (0 : Felt).val = 0 := Felt.val_zero'
  have hneq : ((0 : Nat) == 1) = false := by decide
  have hbeq : ((0 : Nat) == 0) = true := by decide
  simp only [hv0, hneq, hbeq, ↓reduceIte]
  cases execProcedure env (fuel + 1) ⟨rest, mem, frames, adv⟩ elseBlk <;> rfl

/-- State-level version of `execProcedure_ifElse_one` for arbitrary positive fuel. -/
theorem execProcedure_ifElse_state_one
    (env : ProcEnv) (fuel : Nat) (s : Concrete.State)
    (rest : List Felt) (thenBlk elseBlk : List Op)
    (hs : s.stack = (1 : Felt) :: rest)
    (hfuel : fuel > 0) :
    execProcedure env fuel s ([.ifElse thenBlk elseBlk] : List Op) =
    execProcedure env (fuel - 1) (s.withStack rest) thenBlk := by
  cases fuel with
  | zero => omega
  | succ fuel' =>
      obtain ⟨stack, mem, frames, adv⟩ := s
      simp only [Concrete.State.withStack] at hs ⊢
      subst hs
      have hv1 : (1 : Felt).val = 1 := Felt.val_one'
      simp [execProcedure, Procedure.ofOps, List.foldlM, bind, Bind.bind, Option.bind,
        Pure.pure, hv1, Concrete.State.withStack]
      cases execProcedure env fuel' { stack := rest, memory := mem, frames := frames, advice := adv } thenBlk <;> rfl

/-- State-level version of `execProcedure_ifElse_zero` for arbitrary positive fuel. -/
theorem execProcedure_ifElse_state_zero
    (env : ProcEnv) (fuel : Nat) (s : Concrete.State)
    (rest : List Felt) (thenBlk elseBlk : List Op)
    (hs : s.stack = (0 : Felt) :: rest)
    (hfuel : fuel > 0) :
    execProcedure env fuel s ([.ifElse thenBlk elseBlk] : List Op) =
    execProcedure env (fuel - 1) (s.withStack rest) elseBlk := by
  cases fuel with
  | zero => omega
  | succ fuel' =>
      obtain ⟨stack, mem, frames, adv⟩ := s
      simp only [Concrete.State.withStack] at hs ⊢
      subst hs
      have hv0 : (0 : Felt).val = 0 := Felt.val_zero'
      have hneq : ((0 : Nat) == 1) = false := by decide
      simp [execProcedure, Procedure.ofOps, List.foldlM, bind, Bind.bind, Option.bind,
        Pure.pure, hv0, hneq, Concrete.State.withStack]
      cases execProcedure env fuel' { stack := rest, memory := mem, frames := frames, advice := adv } elseBlk <;> rfl

/-- Reduce a singleton `.ifElse` whose stack condition is `if p then 1 else 0`. -/
theorem execProcedure_ifElse_bool_ite
    (env : ProcEnv) (fuel : Nat) (s : Concrete.State)
    (rest : List Felt) (thenBlk elseBlk : List Op)
    (p : Prop) [Decidable p]
    (hs : s.stack = (if p then (1 : Felt) else 0) :: rest)
    (hfuel : fuel > 0) :
    execProcedure env fuel s ([.ifElse thenBlk elseBlk] : List Op) =
    (if p then
      execProcedure env (fuel - 1) (s.withStack rest) thenBlk
    else
      execProcedure env (fuel - 1) (s.withStack rest) elseBlk) := by
  by_cases hp : p
  · simp [hp]
    exact execProcedure_ifElse_state_one env fuel s rest thenBlk elseBlk
      (by simpa [hp] using hs) hfuel
  · simp [hp]
    exact execProcedure_ifElse_state_zero env fuel s rest thenBlk elseBlk
      (by simpa [hp] using hs) hfuel

/-- Reduce a singleton `.ifElse` whose stack condition is `if p then 0 else 1`. -/
theorem execProcedure_ifElse_bool_ite_neg
    (env : ProcEnv) (fuel : Nat) (s : Concrete.State)
    (rest : List Felt) (thenBlk elseBlk : List Op)
    (p : Prop) [Decidable p]
    (hs : s.stack = (if p then (0 : Felt) else 1) :: rest)
    (hfuel : fuel > 0) :
    execProcedure env fuel s ([.ifElse thenBlk elseBlk] : List Op) =
    (if p then
      execProcedure env (fuel - 1) (s.withStack rest) elseBlk
    else
      execProcedure env (fuel - 1) (s.withStack rest) thenBlk) := by
  by_cases hp : p
  · simp [hp]
    exact execProcedure_ifElse_state_zero env fuel s rest thenBlk elseBlk
      (by simpa [hp] using hs) hfuel
  · simp [hp]
    exact execProcedure_ifElse_state_one env fuel s rest thenBlk elseBlk
      (by simpa [hp] using hs) hfuel

/-- Rewrite `execProcedure` on a Procedure whose body equals a given op list.
    Requires `numLocals = 0` so the RHS (via `List Op → Procedure` coercion) has
    the same frame-allocation behavior as the LHS. -/
theorem execProcedure_body_eq (env : ProcEnv) (fuel : Nat) (s : Concrete.State)
    (proc : Procedure) (ops : List Op) (h : proc.body = ops) (h0 : proc.numLocals = 0) :
    execProcedure env fuel s proc = execProcedure env fuel s ops := by
  obtain ⟨name, numLocals, body⟩ := proc
  simp only at h h0; subst h; subst h0
  cases fuel <;> simp [execProcedure, Procedure.ofOps]

/-- Rewrite `execProcedure emptyEnv` on a Procedure whose body equals a given op list.
    Requires `numLocals = 0`. -/
theorem exec_body_eq (fuel : Nat) (s : Concrete.State)
    (proc : Procedure) (ops : List Op) (h : proc.body = ops) (h0 : proc.numLocals = 0) :
    execProcedure emptyEnv fuel s proc = execProcedure emptyEnv fuel s ops := by
  simp [execProcedure_body_eq _ _ _ _ _ h h0]

/-- Frame base for a new allocation on top of the current frame stack. -/
def nextFrameBase (frames : List LocalFrame) : Nat :=
  match frames with
  | [] => 0
  | f :: _ => f.base + f.alignedNumLocals

/-- Rewrite `execProcedure` on a Procedure with `numLocals > 0` as:
    allocate a frame, run the body ops (via the `numLocals = 0` path), pop the frame.

    This is the primary entry point for proofs about procedures that use local memory.
    After applying this lemma, the body execution can be chunked using
    `execProcedure_body_eq` and `execProcedure_append` as usual. -/
theorem execProcedure_body_eq_withLocals (env : ProcEnv) (fuel : Nat) (s : Concrete.State)
    (proc : Procedure) (ops : List Op) (n : Nat)
    (hbody : proc.body = ops) (hlocals : proc.numLocals = n + 1) :
    let numLocals := n + 1
    let aligned := alignLocals numLocals
    let base := nextFrameBase s.frames
    let frame : LocalFrame := { base, numLocals, alignedNumLocals := aligned }
    let s' := { s with frames := frame :: s.frames }
    execProcedure env fuel s proc =
      match execProcedure env fuel s' ops with
      | some r => some { r with frames := s.frames }
      | none => none := by
  obtain ⟨name, numLocals, body⟩ := proc
  simp only at hbody hlocals; subst hbody; subst hlocals
  cases fuel with
  | zero => simp [execProcedure]
  | succ fuel' =>
    simp only [execProcedure, Procedure.ofOps, nextFrameBase, alignLocals, Nat.succ_eq_add_one]
    rfl

/-! ### `ite` normalization for boolean `Felt` values

MASM comparison instructions leave `if p then 1 else 0` on the stack. These
lemmas recognize that shape: they identify it as boolean, fuse products of two
such flags into a conjunction, and turn `= 0` / `= 1` tests (on the element or on
its `val`) back into the underlying proposition.
-/

/-- An `if _ then 1 else 0` flag is a boolean field element. -/
@[simp] theorem Felt.isBool_ite_bool (p : Bool) :
    Felt.isBool (if p then (1 : Felt) else 0) = true := by
  cases p <;> simp [Felt.isBool, Felt.val_one']

/-- A boolean flag equals `1` exactly when its condition holds. -/
@[miden_reflect_norm] theorem Felt.ite_prop_eq_one_iff
    (p : Prop) [Decidable p] :
    (if p then (1 : Felt) else 0) = 1 ↔ p := by
  by_cases hp : p <;> simp [hp]

/-- A boolean flag equals `0` exactly when its condition fails. -/
@[miden_reflect_norm] theorem Felt.ite_prop_eq_zero_iff
    (p : Prop) [Decidable p] :
    (if p then (1 : Felt) else 0) = 0 ↔ ¬p := by
  by_cases hp : p <;> simp [hp]

/-- `val`-level version of `Felt.ite_prop_eq_one_iff`. -/
@[simp, miden_reflect_norm] theorem Felt.val_ite_prop_eq_one_iff
    (p : Prop) [Decidable p] :
    (if p then (1 : Felt) else 0).val = 1 ↔ p := by
  by_cases hp : p <;> simp [hp]

/-- `val`-level version of `Felt.ite_prop_eq_zero_iff`. -/
@[miden_reflect_norm] theorem Felt.val_ite_prop_eq_zero_iff
    (p : Prop) [Decidable p] :
    (if p then (1 : Felt) else 0).val = 0 ↔ ¬p := by
  by_cases hp : p <;> simp [hp]

/-! ### Arithmetic bounds and value recovery

`@[miden_bound]` lemmas feeding the side-goal ladder used by `miden_arith` and
the reflection tactics: `Felt.ofNat` round trips below the Goldilocks prime,
`isU32` propagation through the u32 helper operations, and the no-wrap
conditions under which `Felt` arithmetic agrees with `Nat` arithmetic.
-/

/-- The borrow (first component) of u32OverflowingSub is a boolean:
    1 when a < b, 0 otherwise. -/
theorem u32OverflowingSub_borrow_ite (a b : Nat) :
    Felt.ofNat (u32OverflowingSub a b).1 =
    if decide (a < b) then (1 : Felt) else 0 := by
  unfold u32OverflowingSub Felt.ofNat
  split
  · simp [decide_eq_false (show ¬(a < b) by omega)]
  · simp [decide_eq_true (show a < b by omega)]

/-- Felt.ofNat n has val = n when n < GOLDILOCKS_PRIME. -/
@[miden_bound] theorem felt_ofNat_val_lt (n : Nat) (h : n < GOLDILOCKS_PRIME) :
    (Felt.ofNat n).val = n := by
  unfold Felt.ofNat
  simp only [Felt, GOLDILOCKS_PRIME] at *
  rw [ZMod.val_natCast]
  exact Nat.mod_eq_of_lt h

/-- Unconditional companion to `felt_ofNat_val_lt`: embedding into `Felt` and
    reading `val` back reduces mod the prime. Deliberately *not* tagged into any
    `simp` set — as a rewrite it would compete with the conditional round-trip
    lemmas and turn every recovered value into a `% GOLDILOCKS_PRIME` term.
    It is used explicitly, to flatten residual goals for `omega`. -/
theorem felt_ofNat_val_mod (n : Nat) : (Felt.ofNat n).val = n % GOLDILOCKS_PRIME := by
  unfold Felt.ofNat
  exact ZMod.val_natCast (n := GOLDILOCKS_PRIME) n

/-- Every `Felt` has `val` below the Goldilocks prime. -/
@[miden_bound] theorem felt_val_lt_prime (a : Felt) : a.val < GOLDILOCKS_PRIME :=
  ZMod.val_lt a

/-- Every u32 value is below the Goldilocks prime. -/
@[miden_bound] theorem u32_val_lt_prime (n : Nat) (h : n < 2^32) : n < GOLDILOCKS_PRIME := by
  unfold GOLDILOCKS_PRIME; omega

/-- A u32-truncated value is below the Goldilocks prime. -/
@[miden_bound] theorem u32_mod_lt_prime (n : Nat) : n % 2^32 < GOLDILOCKS_PRIME := by
  unfold GOLDILOCKS_PRIME; omega

/-- The carry of a `Felt` sum is below the Goldilocks prime. -/
@[miden_bound] theorem sum_div_2_32_lt_prime (a b : Felt) :
    (a.val + b.val) / 2^32 < GOLDILOCKS_PRIME := by
  have ha := felt_val_lt_prime a
  have hb := felt_val_lt_prime b
  unfold GOLDILOCKS_PRIME at *; omega

/-- The carry of a three-way `Felt` sum is below the Goldilocks prime. -/
@[miden_bound] theorem sum3_div_2_32_lt_prime (a b c : Felt) :
    (a.val + b.val + c.val) / 2^32 < GOLDILOCKS_PRIME := by
  have ha := felt_val_lt_prime a
  have hb := felt_val_lt_prime b
  have hc := felt_val_lt_prime c
  unfold GOLDILOCKS_PRIME at *; omega

/-- The borrow of `u32OverflowingSub` is below the Goldilocks prime. -/
@[miden_bound] theorem u32_overflow_sub_fst_lt (a b : Nat) :
    (u32OverflowingSub a b).1 < GOLDILOCKS_PRIME := by
  unfold u32OverflowingSub
  split <;> simp [GOLDILOCKS_PRIME]

/-- The difference computed by `u32OverflowingSub` stays below the prime when its
    inputs do. -/
@[miden_bound] theorem u32_overflow_sub_snd_lt (a b : Nat)
    (ha : a < GOLDILOCKS_PRIME) (hb : b < GOLDILOCKS_PRIME) :
    (u32OverflowingSub a b).2 < GOLDILOCKS_PRIME := by
  unfold u32OverflowingSub
  split
  · simp; omega
  · simp [u32Max, GOLDILOCKS_PRIME] at *; omega

/-- Embedding a value below `2^32` into `Felt` yields a u32 element. -/
@[miden_bound] theorem felt_ofNat_isU32_of_lt (n : Nat) (h : n < 2^32) :
    (Felt.ofNat n).isU32 = true := by
  simp only [Felt.isU32, decide_eq_true_eq]
  have hp : n < GOLDILOCKS_PRIME := by unfold GOLDILOCKS_PRIME; omega
  rw [felt_ofNat_val_lt n hp]; exact h

/-- The borrow of `u32OverflowingSub` is a u32 element. -/
@[miden_bound] theorem u32OverflowingSub_fst_isU32 (a b : Nat) :
    (Felt.ofNat (u32OverflowingSub a b).1).isU32 = true := by
  unfold u32OverflowingSub
  split <;> simp [felt_ofNat_isU32_of_lt]

/-- The difference computed by `u32OverflowingSub` is a u32 element. -/
@[miden_bound] theorem u32OverflowingSub_snd_isU32 (a b : Nat)
    (ha : a < 2^32) (hb : b < 2^32) :
    (Felt.ofNat (u32OverflowingSub a b).2).isU32 = true := by
  apply felt_ofNat_isU32_of_lt
  unfold u32OverflowingSub u32Max; split <;> omega

/-- A u32-truncated value embeds to a u32 element. -/
@[miden_bound] theorem u32_mod_isU32 (n : Nat) :
    (Felt.ofNat (n % 2^32)).isU32 = true := by
  apply felt_ofNat_isU32_of_lt; omega

/-- The carry of a sum of two u32 elements is a u32 element. -/
@[miden_bound] theorem u32_div_2_32_isU32 (a b : Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true) :
    (Felt.ofNat ((a.val + b.val) / 2^32)).isU32 = true := by
  apply felt_ofNat_isU32_of_lt
  simp only [Felt.isU32, decide_eq_true_eq] at ha hb; omega

/-- The high limb of a product of two u32 elements is a u32 element. -/
@[miden_bound] theorem u32_prod_div_isU32 (a b : Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true) :
    (Felt.ofNat (a.val * b.val / 2^32)).isU32 = true := by
  apply felt_ofNat_isU32_of_lt
  simp only [Felt.isU32, decide_eq_true_eq] at ha hb
  have h3 : a.val * b.val ≤ (2^32 - 1) * (2^32 - 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  calc a.val * b.val / 2^32
      ≤ (2^32 - 1) * (2^32 - 1) / 2^32 := Nat.div_le_div_right h3
    _ < 2^32 := by decide

/-- The high limb of a product of two u32 elements is below the Goldilocks prime. -/
@[miden_bound] theorem u32_prod_div_lt_prime (a b : Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true) :
    a.val * b.val / 2^32 < GOLDILOCKS_PRIME := by
  simp only [Felt.isU32, decide_eq_true_eq] at ha hb
  have h3 : a.val * b.val ≤ (2^32 - 1) * (2^32 - 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  calc a.val * b.val / 2^32
      ≤ (2^32 - 1) * (2^32 - 1) / 2^32 := Nat.div_le_div_right h3
    _ < GOLDILOCKS_PRIME := by unfold GOLDILOCKS_PRIME; decide

/-! #### `Felt` arithmetic round trips

Conditions under which a `Felt` operation agrees with the corresponding `Nat`
operation, used to bridge between the field-level semantics and the `Nat`-level
specifications in the correctness statements.
-/

/-- Felt addition round-trips when the sum stays below the prime. -/
@[miden_bound] theorem felt_add_val_no_wrap (a b : Felt)
    (h : a.val + b.val < GOLDILOCKS_PRIME) :
    (a + b).val = a.val + b.val := by
  show (a + b).val = a.val + b.val
  rw [ZMod.val_add]
  exact Nat.mod_eq_of_lt h

/-- Felt subtraction round-trips when a ≥ b (no underflow). -/
@[miden_bound] theorem felt_sub_val_no_wrap (a b : Felt)
    (hab : b.val ≤ a.val) :
    (a - b).val = a.val - b.val := by
  show (a - b).val = a.val - b.val
  rw [ZMod.val_sub (by exact hab)]

/-- Felt multiplication round-trips when the product stays below the prime. -/
@[miden_bound] theorem felt_mul_val_no_wrap (a b : Felt)
    (h : a.val * b.val < GOLDILOCKS_PRIME) :
    (a * b).val = a.val * b.val := by
  show (a * b).val = a.val * b.val
  rw [ZMod.val_mul]
  exact Nat.mod_eq_of_lt h

/-- u32OverflowingSub result round-trips through Felt.ofNat when inputs are u32. -/
@[miden_bound] theorem u32OverflowingSub_snd_val (a b : Nat)
    (ha : a < 2^32) (hb : b < 2^32) :
    (Felt.ofNat (u32OverflowingSub a b).2).val = (u32OverflowingSub a b).2 := by
  apply felt_ofNat_val_lt
  apply u32_val_lt_prime
  unfold u32OverflowingSub u32Max; split <;> omega

/-- u32OverflowingSub subtraction result is zero iff inputs are equal (for u32 inputs). -/
theorem u32OverflowingSub_snd_eq_zero_iff (a b : Nat)
    (ha : a < 2^32) (hb : b < 2^32) :
    (u32OverflowingSub a b).2 = 0 ↔ a = b := by
  unfold u32OverflowingSub u32Max; split <;> (constructor <;> intro h <;> omega)

/-- Two Felt values are equal when they have the same val. -/
theorem felt_eq_ofNat_of_val_eq (a : Felt) (n : Nat) (h : a.val = n)
    (hn : n < GOLDILOCKS_PRIME) : a = Felt.ofNat n := by
  unfold Felt.ofNat
  have : (n : Felt).val = n := ZMod.val_cast_of_lt hn
  exact_mod_cast Fin.val_injective (by omega : a.val = (n : Felt).val)

/-- Felt.ofNat 0 is beq-equal to 0. -/
theorem felt_ofNat_beq_zero (n : Nat) (h : n = 0) :
    (Felt.ofNat n == (0 : Felt)) = true := by
  subst h; simp [Felt.ofNat]

/-- A Felt product is beq-equal to 0 when the Nat product is 0. -/
theorem felt_mul_beq_zero (a b : Felt) (h : a.val * b.val = 0)
    (hlt : a.val * b.val < GOLDILOCKS_PRIME) :
    ((a * b : Felt) == (0 : Felt)) = true := by
  rw [beq_iff_eq]
  have hmul : (a * b).val = 0 := by rw [felt_mul_val_no_wrap a b hlt]; exact h
  have hzero : (0 : Felt).val = 0 := Felt.val_zero'
  exact_mod_cast Fin.val_injective (by omega : (a * b).val = (0 : Felt).val)

/-! ### Local frames

`LocalFrame.localAddr` comparison lemmas. They are critical for resolving memory
reads through the if-then-else chains produced by `locStorewBe`: since
`localAddr idx = LOCAL_MEM_BASE + base + idx`, address equality reduces to offset
equality, which `simp`/`omega` can then decide.
-/

/-- Compare two offset local addresses by their offsets. -/
@[simp] theorem LocalFrame.localAddr_add_eq_localAddr_add_iff
    (frame : LocalFrame) (i k j l : Nat) :
    (frame.localAddr i + k = frame.localAddr j + l) ↔ (i + k = j + l) := by
  unfold localAddr; omega

/-- Compare a local address with an offset local address by their offsets. -/
@[simp] theorem LocalFrame.localAddr_eq_localAddr_add_iff
    (frame : LocalFrame) (i j l : Nat) :
    (frame.localAddr i = frame.localAddr j + l) ↔ (i = j + l) := by
  unfold localAddr; omega

/-- Compare an offset local address with a local address by their offsets. -/
@[simp] theorem LocalFrame.localAddr_add_eq_localAddr_iff
    (frame : LocalFrame) (i k j : Nat) :
    (frame.localAddr i + k = frame.localAddr j) ↔ (i + k = j) := by
  unfold localAddr; omega

/-- Two local addresses in the same frame are equal exactly when their indices are. -/
@[simp] theorem LocalFrame.localAddr_eq_localAddr_iff
    (frame : LocalFrame) (i j : Nat) :
    (frame.localAddr i = frame.localAddr j) ↔ (i = j) := by
  unfold localAddr; omega

end MidenLean
