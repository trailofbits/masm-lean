/-
  Cross-validation tests: run MASM library procedures through our
  Lean semantics model and verify outputs match miden-vm test vectors.

  These tests are NOT imported by MidenLean.lean because they execute
  multi-instruction procedures at #eval time (expensive). Run with:
    lake build MidenLean.Tests.CrossValidation
-/
import MidenLean.Semantics
import MidenLean.Proofs.U64
import MidenLean.Generated.U64

namespace MidenLean.Tests.CrossValidation

open MidenLean

private def mkState (stk : List Felt) : MidenState :=
  MidenState.ofStack stk

private def mkStateAdv (stk : List Felt) (adv : List Felt) : MidenState :=
  MidenState.ofStackAdvice stk adv

-- Complete u64 ProcEnv for testing
private def testU64ProcEnv : ProcEnv := fun name =>
  match name with
  | "overflowing_add" => some Miden.Core.U64.overflowing_add
  | "wrapping_add" => some Miden.Core.U64.wrapping_add
  | "gt" => some Miden.Core.U64.gt
  | "lt" => some Miden.Core.U64.lt
  | "lte" => some Miden.Core.U64.lte
  | "gte" => some Miden.Core.U64.gte
  | "eq" => some Miden.Core.U64.eq
  | "neq" => some Miden.Core.U64.neq
  | "eqz" => some Miden.Core.U64.eqz
  | "min" => some Miden.Core.U64.min
  | "max" => some Miden.Core.U64.max
  | "and" => some Miden.Core.U64.and
  | "or" => some Miden.Core.U64.or
  | "xor" => some Miden.Core.U64.xor
  | "shl" => some Miden.Core.U64.shl
  | "shr" => some Miden.Core.U64.shr
  | "rotl" => some Miden.Core.U64.rotl
  | "rotr" => some Miden.Core.U64.rotr
  | "clz" => some Miden.Core.U64.clz
  | "ctz" => some Miden.Core.U64.ctz
  | "clo" => some Miden.Core.U64.clo
  | "cto" => some Miden.Core.U64.cto
  | "divmod" => some Miden.Core.U64.divmod
  | "div" => some Miden.Core.U64.div
  | "mod" => some Miden.Core.U64.mod
  | "widening_mul" => some Miden.Core.U64.widening_mul
  | "wrapping_mul" => some Miden.Core.U64.wrapping_mul
  | "overflowing_sub" => some Miden.Core.U64.overflowing_sub
  | "wrapping_sub" => some Miden.Core.U64.wrapping_sub
  | _ => none

private def runU64 (proc : List Op) (stk : List Felt)
    (fuel := 100) : Option MidenState :=
  execWithEnv testU64ProcEnv fuel (mkState stk) proc

-- ============================================================================
-- Cross-validation: miden-vm u64_mod.rs test vectors
-- ============================================================================

-- wrapping_add (u64_mod.rs line 32-52)
-- a=0x00000002_00000005, b=0x00000001_00000003 -> [8,3]
#eval do
  let r := runU64 Miden.Core.U64.wrapping_add [5, 2, 3, 1]
  match r with
  | some s =>
    unless s.stack.take 2 == [8, 3] do
      panic! "CROSS-VAL wrapping_add: [5,2,3,1] should give [8,3]"
  | none => panic! "wrapping_add should not fail"

-- lt (u64_mod.rs line 270-288)
#eval do
  let check (stk : List Felt) (expected : Felt) (msg : String) : IO Unit := do
    match runU64 Miden.Core.U64.lt stk with
    | some s =>
      unless s.stack[0]! == expected do panic! msg
    | none => panic! s!"{msg}: should not fail"
  check [0,0,0,0] 0 "CROSS-VAL lt: 0<0=false"
  check [1,0,0,0] 1 "CROSS-VAL lt: 0<1=true"
  check [0,0,1,0] 0 "CROSS-VAL lt: 1<0=false"

-- lte (u64_mod.rs line 290-316)
#eval do
  let check (stk : List Felt) (expected : Felt) (msg : String) : IO Unit := do
    match runU64 Miden.Core.U64.lte stk with
    | some s =>
      unless s.stack[0]! == expected do panic! msg
    | none => panic! s!"{msg}: should not fail"
  check [0,0,0,0] 1 "CROSS-VAL lte: 0<=0=true"
  check [1,0,0,0] 1 "CROSS-VAL lte: 0<=1=true"
  check [0,0,1,0] 0 "CROSS-VAL lte: 1<=0=false"

-- gt (u64_mod.rs line 318-336)
#eval do
  let check (stk : List Felt) (expected : Felt) (msg : String) : IO Unit := do
    match runU64 Miden.Core.U64.gt stk with
    | some s =>
      unless s.stack[0]! == expected do panic! msg
    | none => panic! s!"{msg}: should not fail"
  check [0,0,0,0] 0 "CROSS-VAL gt: 0>0=false"
  check [1,0,0,0] 0 "CROSS-VAL gt: 0>1=false"
  check [0,0,1,0] 1 "CROSS-VAL gt: 1>0=true"

-- gte (u64_mod.rs line 338-364)
#eval do
  let check (stk : List Felt) (expected : Felt) (msg : String) : IO Unit := do
    match runU64 Miden.Core.U64.gte stk with
    | some s =>
      unless s.stack[0]! == expected do panic! msg
    | none => panic! s!"{msg}: should not fail"
  check [0,0,0,0] 1 "CROSS-VAL gte: 0>=0=true"
  check [1,0,0,0] 0 "CROSS-VAL gte: 0>=1=false"
  check [0,0,1,0] 1 "CROSS-VAL gte: 1>=0=true"

-- min (u64_mod.rs line 366-384)
#eval do
  let check (stk : List Felt) (exp : List Felt) (msg : String) : IO Unit := do
    match runU64 Miden.Core.U64.min stk with
    | some s =>
      unless s.stack.take 2 == exp do panic! msg
    | none => panic! s!"{msg}: should not fail"
  check [0,0,0,0] [0,0] "CROSS-VAL min: min(0,0)=0"
  check [1,0,2,0] [1,0] "CROSS-VAL min: min(1,2)=1"
  check [3,0,2,0] [2,0] "CROSS-VAL min: min(3,2)=2"

-- max (u64_mod.rs line 386-404)
#eval do
  let check (stk : List Felt) (exp : List Felt) (msg : String) : IO Unit := do
    match runU64 Miden.Core.U64.max stk with
    | some s =>
      unless s.stack.take 2 == exp do panic! msg
    | none => panic! s!"{msg}: should not fail"
  check [0,0,0,0] [0,0] "CROSS-VAL max: max(0,0)=0"
  check [1,0,2,0] [2,0] "CROSS-VAL max: max(1,2)=2"
  check [3,0,2,0] [3,0] "CROSS-VAL max: max(3,2)=3"

-- eq (u64_mod.rs line 406-432)
#eval do
  let check (stk : List Felt) (expected : Felt) (msg : String) : IO Unit := do
    match runU64 Miden.Core.U64.eq stk with
    | some s =>
      unless s.stack[0]! == expected do panic! msg
    | none => panic! s!"{msg}: should not fail"
  check [0,0,0,0] 1 "CROSS-VAL eq: 0==0=true"
  check [0,0,1,0] 0 "CROSS-VAL eq: 0==1=false"
  check [1,0,0,0] 0 "CROSS-VAL eq: 1==0=false"

-- neq (u64_mod.rs line 434-460)
#eval do
  let check (stk : List Felt) (expected : Felt) (msg : String) : IO Unit := do
    match runU64 Miden.Core.U64.neq stk with
    | some s =>
      unless s.stack[0]! == expected do panic! msg
    | none => panic! s!"{msg}: should not fail"
  check [0,0,0,0] 0 "CROSS-VAL neq: 0!=0=false"
  check [0,0,1,0] 1 "CROSS-VAL neq: 0!=1=true"
  check [1,0,0,0] 1 "CROSS-VAL neq: 1!=0=true"

-- eqz (u64_mod.rs line 462-483)
#eval do
  let check (stk : List Felt) (expected : Felt) (msg : String) : IO Unit := do
    match runU64 Miden.Core.U64.eqz stk with
    | some s =>
      unless s.stack[0]! == expected do panic! msg
    | none => panic! s!"{msg}: should not fail"
  check [0,0] 1 "CROSS-VAL eqz: 0==0 true"
  check [1,0] 0 "CROSS-VAL eqz: 1!=0 false"

-- divmod (u64_mod.rs line 526-549)
-- a=123, b=10 => q=12, r=3
open Miden.Core.U64 in
open MidenLean.Proofs in
#eval do
  let stk := [(10:Felt), 0, 123, 0]
  let adv := [(0:Felt), 12, 0, 3]
  let s := mkStateAdv stk adv
  let r := execWithEnv u64ProcEnv 50 s divmod
  match r with
  | some s' =>
    unless s'.stack == [3, 0, 12, 0] do
      panic! "CROSS-VAL divmod 123/10: expected [3,0,12,0]"
  | none => panic! "CROSS-VAL divmod 123/10 should not fail"

-- clz (u64_mod.rs line 1207-1231): a=0 -> 64
#eval do
  match runU64 Miden.Core.U64.clz [0, 0] with
  | some s =>
    unless s.stack[0]! == (64 : Felt) do panic! "CROSS-VAL clz(0)=64"
  | none => panic! "clz should not fail"

-- ctz (u64_mod.rs line 1258-1281): a=0 -> 64
#eval do
  match runU64 Miden.Core.U64.ctz [0, 0] with
  | some s =>
    unless s.stack[0]! == (64 : Felt) do panic! "CROSS-VAL ctz(0)=64"
  | none => panic! "ctz should not fail"

-- clo: a=0xffffffffffffffff -> 64
#eval do
  let maxu32 : Felt := Felt.ofNat (2^32 - 1)
  match runU64 Miden.Core.U64.clo [maxu32, maxu32] with
  | some s =>
    unless s.stack[0]! == (64 : Felt) do panic! "CROSS-VAL clo(max)=64"
  | none => panic! "clo should not fail"

-- cto: a=0xffffffffffffffff -> 64
#eval do
  let maxu32 : Felt := Felt.ofNat (2^32 - 1)
  match runU64 Miden.Core.U64.cto [maxu32, maxu32] with
  | some s =>
    unless s.stack[0]! == (64 : Felt) do panic! "CROSS-VAL cto(max)=64"
  | none => panic! "cto should not fail"

-- shl: a=1, shift=32 -> (lo=0,hi=1)
#eval do
  match runU64 Miden.Core.U64.shl [32, 1, 0, 5] with
  | some s =>
    unless s.stack.take 3 == [0, 1, 5] do panic! "CROSS-VAL shl 1<<32"
  | none => panic! "shl should not fail"

-- shr: a=0x100000001, shift=1 -> (lo=2^31,hi=0)
#eval do
  match runU64 Miden.Core.U64.shr [1, 1, 1, 99] with
  | some s =>
    unless s.stack.take 3 == [Felt.ofNat (2^31), 0, 99] do
      panic! "CROSS-VAL shr 0x100000001>>1"
  | none => panic! "shr should not fail"

end MidenLean.Tests.CrossValidation
