import MidenLean.Semantics

namespace MidenLean

-- ============================================================================
-- MidenState projection lemmas
-- ============================================================================

@[simp] theorem MidenState.withStack_stack (s : MidenState) (stk : List Felt) :
    (s.withStack stk).stack = stk := rfl

@[simp] theorem MidenState.withStack_memory (s : MidenState) (stk : List Felt) :
    (s.withStack stk).memory = s.memory := rfl

@[simp] theorem MidenState.withStack_locals (s : MidenState) (stk : List Felt) :
    (s.withStack stk).locals = s.locals := rfl

@[simp] theorem MidenState.withStack_advice (s : MidenState) (stk : List Felt) :
    (s.withStack stk).advice = s.advice := rfl

@[simp] theorem MidenState.withStack_withStack (s : MidenState) (stk1 stk2 : List Felt) :
    (s.withStack stk1).withStack stk2 = s.withStack stk2 := rfl

-- ============================================================================
-- Felt value lemmas
-- ============================================================================

@[simp] theorem Felt.val_zero' : (0 : Felt).val = 0 := rfl

set_option maxHeartbeats 400000 in
@[simp] theorem Felt.val_one' : (1 : Felt).val = 1 := by native_decide

-- ============================================================================
-- Felt boolean lemmas
-- ============================================================================

@[simp] theorem Felt.isBool_ite_bool (p : Bool) :
    Felt.isBool (if p then (1 : Felt) else 0) = true := by
  cases p <;> simp [Felt.isBool, Felt.val_one']

@[simp] theorem Felt.ite_mul_ite (p q : Bool) :
    (if p then (1 : Felt) else 0) * (if q then (1 : Felt) else 0) =
    if (p && q) then (1 : Felt) else 0 := by
  cases p <;> cases q <;> simp

end MidenLean
