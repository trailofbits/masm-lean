# Vivisect Correctness Analysis: masm-lean

Date: 2026-03-19 (run 12, post-memory-refactor)

## Target: core-semantics

### MidenState (State.lean)

**Assumptions:** None -- this is a data definition.

**Invariants:**
- `memory : Nat -> Word` maps each address to a 4-felt
  tuple. Default is `Word.zero = (0, 0, 0, 0)`.
  Lines 43, 32.
- `locals : Nat -> Word` same structure for procedure
  locals. Line 46.
- `stack : List Felt` unbounded, head = top of stack.
  Line 38.
- `wellFormed` (line 122-124) states `16 <= len <= 2^16`
  but is not enforced in the type.

**Guarantees:**
- `writeMemory` (line 65-68) produces a new state where
  exactly one address maps to the new word; all other
  addresses unchanged.
- `writeMemoryElem0` (line 73-79) writes only element 0
  of the word at the given address, preserving elements
  1-3 from the original word.
- `writeLocal` / `writeLocalElem0` mirror the memory
  write helpers for local slots.

**Dependencies:** Felt (Mathlib ZMod), Word (tuple).

**Preliminary category:** Good

---

### execMemLoad / execMemLoadImm (Semantics.lean:809-819)

**Assumptions:**
- Address < u32Max (checked, returns none otherwise).
Lines 812, 818.

**Invariants:** Does not modify memory or locals.

**Guarantees:**
- Reads `(s.memory addr).1` -- element 0 of the word.
  This matches Rust's `op_mload` which reads `word[0]`.
- `execMemLoad`: consumes address from stack, pushes
  value. Stack: [addr, ...] -> [word[0], ...].
- `execMemLoadImm`: pushes value without consuming
  anything. Stack: [...] -> [word[0], ...].

**Dependencies:** MidenState.memory, Word.

**Preliminary category:** Good

---

### execMemStore / execMemStoreImm (Semantics.lean:821-834)

**Assumptions:**
- Address < u32Max (checked). Lines 824, 832.

**Invariants:** Only element 0 of the target word is
modified; elements 1-3 preserved via writeMemoryElem0.

**Guarantees:**
- `execMemStore`: consumes address and value. Stack:
  [addr, value, ...] -> [...]. Writes value to
  mem[addr][0].
- `execMemStoreImm`: consumes value only. Stack:
  [value, ...] -> [...]. Writes value to
  mem[addr][0].
- Both match Rust's `op_mstore` behavior.

**Dependencies:** MidenState.writeMemoryElem0.

**Preliminary category:** Good

---

### execMemStorewLe / execMemStorewLeImm (Semantics.lean:857-876)

**Assumptions:**
- Address < u32Max (checked). Lines 861, 872.
- Stack has address + 4 elements (pattern match).

**Invariants:** Writes full word (e0, e1, e2, e3)
where e0 = stack[0] after address. Element ordering
matches Rust's `op_mstorew` (stack[0] -> word[0]).

**Guarantees:**
- Stack: [addr, e0, e1, e2, e3, ...] ->
  [e0, e1, e2, e3, ...] (address consumed, word
  elements remain).
- Memory: word at addr = (e0, e1, e2, e3).
- Matches Rust VM's op_mstorew exactly.

**Dependencies:** MidenState.writeMemory.

**Preliminary category:** Good

---

### execMemStorewBe / execMemStorewBeImm (Semantics.lean:836-855)

**Assumptions:**
- Address < u32Max (checked). Lines 840, 851.

**Invariants:** Stores word with reversed element
order: (e3, e2, e1, e0). Stack elements remain in
original order on the stack.

**Guarantees:**
- Stack: [addr, e0, e1, e2, e3, ...] ->
  [e0, e1, e2, e3, ...].
- Memory: word at addr = (e3, e2, e1, e0).
- This does NOT match Rust's op_mstorew; it is a
  big-endian variant for user code.

**Dependencies:** MidenState.writeMemory.

**Preliminary category:** Good (Be variant is a
modeling convenience, Le matches Rust)

---

### execMemLoadwLe / execMemLoadwBe (Semantics.lean:878-918)

**Assumptions:**
- Address < u32Max (checked).
- Stack has address + 4 dummy elements (pattern match).

**Invariants:** Reads full word from memory, pushes
elements onto stack.

**Guarantees:**
- Le: [addr, _, _, _, _, ...] ->
  [w[0], w[1], w[2], w[3], ...]. Matches Rust's
  op_mloadw.
- Be: [addr, _, _, _, _, ...] ->
  [w[3], w[2], w[1], w[0], ...]. Reversed order.
- Le round-trips with StorewLe; Be round-trips with
  StorewBe. Verified by tests at
  Tests/Semantics.lean:1219-1257.

**Dependencies:** MidenState.memory, Word accessors.

**Preliminary category:** Good

---

### execLocLoad / execLocStore (Semantics.lean:923-932)

**Assumptions:**
- No address range check (locals are unlimited).
  This diverges from Rust where local count is
  bounded by procedure metadata.

**Invariants:**
- locLoad reads element 0 of local word.
- locStore writes element 0 via writeLocalElem0.

**Guarantees:**
- Matches Rust's compiled local access pattern
  (loc_load reads word[0], loc_store writes word[0]).

**Dependencies:** MidenState.locals, writeLocalElem0.

**Preliminary category:** Good

---

### execAdvPush / execAdvLoadW (Semantics.lean:951-970)

**Assumptions:**
- Advice stack has sufficient elements (checked).
  Lines 952, 965.

**Invariants:**
- advPush reverses taken elements (correct: models
  N sequential ADVPOP operations).
- advLoadW does NOT reverse (correct: overwrites top
  4 stack elements with word from advice).

**Guarantees:**
- advPush: [a1,...,aN] from advice -> stack gets
  [aN,...,a1, ...rest] (reversed).
- advLoadW: [a1,a2,a3,a4] from advice -> stack gets
  [a1,a2,a3,a4, ...rest] (not reversed).
- Both match Rust VM behavior. Regression tests at
  Tests/Semantics.lean:786-790.

**Dependencies:** MidenState.advice.

**Preliminary category:** Good

---

### execEmit / emitImm (Semantics.lean:977-981, 1104-1105)

**Assumptions:**
- emit: stack must be non-empty (pattern match).

**Invariants:**
- Records event ID in s.events list.

**Guarantees:**
- emit: reads top stack element as event ID, appends
  to events. Stack unchanged.
- emitImm: records the immediate argument as event ID.
  Stack unchanged.
- Both now functional (previously no-op).

**Dependencies:** MidenState.events.

**Preliminary category:** Good

---

## Target: generated-procs

### store_word_u32s_le (Generated/Word.lean:12-28)

**Assumptions:**
- Stack: [x0, x1, x2, x3, addr, ...rest]
- addr + 4 < u32Max

**Invariants:** Splits 4 felts into 8 u32 limbs via
u32Split, stores as two words at addr and addr+4.

**Guarantees:**
- Memory at addr: (x0.lo32, x0.hi32, x1.lo32, x1.hi32)
- Memory at addr+4: (x2.lo32, x2.hi32, x3.lo32, x3.hi32)
- Stack: rest (all consumed).
- Proved correct: StoreWordU32sLe.lean theorem.

**Dependencies:** memStorewLe, u32Split, addImm.

**Preliminary category:** Good

---

## Target: proofs

### StoreWordU32sLe proof (Proofs/Word/StoreWordU32sLe.lean)

**Assumptions:**
- addr.val + 4 < u32Max (explicit hypothesis)
- (addr + 4 : Felt).val = addr.val + 4 (no overflow)

**Invariants:** Proof correctly uses word-addressed
memory model (Nat -> Word). Output state has a
2-level if/then/else for memory at addr and addr+4.

**Guarantees:**
- Theorem is machine-checked (no sorry, no axiom).
- Output memory function correctly maps addr to
  (x0.lo32, x0.hi32, x1.lo32, x1.hi32) and addr+4
  to (x2.lo32, x2.hi32, x3.lo32, x3.hi32).

**Dependencies:** stepMemStorewLe, stepU32Split,
stepDropw, exec_append.

**Preliminary category:** Good

---

## Cross-function analysis

### writeMemoryElem0 -> execMemLoad roundtrip

Does storing via writeMemoryElem0 then loading via
execMemLoad return the stored value?

writeMemoryElem0 sets element 0 to v:
  (v, old.2.1, old.2.2.1, old.2.2.2)
execMemLoad reads element 0: (memory addr).1

So (memory addr).1 = v. Correct roundtrip. MATCHED.

### writeMemory -> execMemLoadwLe roundtrip

writeMemory sets full word: (e0, e1, e2, e3).
execMemLoadwLe reads: w.1 :: w.2.1 :: w.2.2.1 ::
  w.2.2.2 = e0 :: e1 :: e2 :: e3.

Correct roundtrip. MATCHED.

### writeMemory -> execMemLoadwBe roundtrip

writeMemory sets: (e0, e1, e2, e3).
execMemLoadwBe reads: w.2.2.2 :: w.2.2.1 :: w.2.1 ::
  w.1 = e3 :: e2 :: e1 :: e0.

This returns elements in reversed order. For Be
round-trip, StorewBe must be used (stores
(e3, e2, e1, e0)), then LoadwBe reads back as
e0 :: e1 :: e2 :: e3. Correct paired round-trip.
MATCHED.

### StorewLe -> LoadwLe vs StorewBe -> LoadwBe

StorewLe stores (e0,e1,e2,e3), LoadwLe returns
e0,e1,e2,e3. Round-trip preserves order. MATCHED.

StorewBe stores (e3,e2,e1,e0), LoadwBe returns
e0,e1,e2,e3 (reverses back). MATCHED.

Cross-variant: StorewLe then LoadwBe returns
e3,e2,e1,e0 (reversed). StorewBe then LoadwLe
returns e3,e2,e1,e0 (reversed). These cross-variant
accesses intentionally reverse. MATCHED.

### memStore -> memStorewLe interaction

memStore writes only element 0 of a word.
memStorewLe writes all 4 elements. If a word is
written via memStorewLe then element 0 is overwritten
via memStore, the result is (new_v, e1, e2, e3).
This matches Rust's behavior. MATCHED.

## Misuse Resistance Baseline

The primary API for external use is `exec` /
`execWithEnv` / `execWithProcs`. These are pure
functions with no side effects. Misuse is limited to:

1. Constructing invalid states (e.g., negative stack
   depth) -- mitigated by wellFormed predicate.
2. Using Be variants where Le is intended (or vice
   versa) -- documented, type-safe (same type).
3. Mixing memory access patterns (element vs word) --
   now coherent since both access the same Word.
4. Unbounded local indices -- no range check, but
   this is a Lean modeling simplification (Rust
   bounds-checks at compile time via procedure
   metadata).

No exported symbol has a caller-obvious misuse that
produces silently wrong results. The Be/Le naming
is the closest to a misuse risk, but the naming is
clear and documented.
