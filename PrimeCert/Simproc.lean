/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import PrimeCert.SmallPrimes
import Qq

/-! # Simproc for automatic primality certification

A `simproc` that recognizes `Nat.Prime n` for numeric literals and automatically
constructs Pocklington certificates. The witness (factorization of `n-1`, primitive root)
is computed in untrusted elaboration-time code; the proof term is kernel-checked via
`pocklington_certifyKR`.
-/

open Lean Meta Qq

namespace PrimeCert.Simproc

/-- Trial-division factorization. Returns array of (prime, exponent) pairs. -/
partial def trialFactor (n : Nat) : Array (Nat × Nat) :=
  go n #[] 2
where
  nextD (d : Nat) : Nat := if d == 2 then 3 else d + 2
  go (n : Nat) (acc : Array (Nat × Nat)) (d : Nat) : Array (Nat × Nat) :=
    if n ≤ 1 then acc
    else if d * d > n then
      acc.push (n, 1)  -- n is prime
    else if n % d == 0 then
      let (n', e) := extractFactor n d 0
      go n' (acc.push (d, e)) (nextD d)
    else
      go n acc (nextD d)
  extractFactor (n p e : Nat) : Nat × Nat :=
    if n % p == 0 then extractFactor (n / p) p (e + 1)
    else (n, e)

/-- Check if `a` is a primitive root mod `n` for the Pocklington test. -/
def isPrimitiveRoot (n a : Nat) (primeFactors : Array Nat) : Bool :=
  powModTR' a (n - 1) n == 1 &&
  primeFactors.all fun p =>
    let r := powModTR' a ((n - 1) / p) n
    Nat.gcd (if r == 0 then n else r - 1) n == 1

/-- Find a primitive root mod `n` by trying 2, 3, 4, ... -/
partial def findPrimitiveRoot (n : Nat) (primeFactors : Array Nat) : MetaM Nat := do
  for a in List.range (n - 1) |>.map (· + 2) do
    if isPrimitiveRoot n a primeFactors then return a
  throwError "no primitive root found for {n}"

/-- Build the F₁ expression and PocklingtonPred proof from factorization.
Uses raw `mkAppN` to avoid elaboration-time type checking of `eagerReflBoolTrue`
(since `powModTR` is noncomputable and can only be reduced by the kernel). -/
private def buildPocklingtonPred (N root : Q(ℕ)) (factors : Array (Nat × Nat))
    (dict : Meta.PrimeDict) : MetaM (Q(ℕ) × Expr) := do
  if factors.size == 0 then
    return (mkNatLit 1, mkConst ``PocklingtonPred.one)
  let (p0, e0) := factors[0]!
  let hp0 ← dict.getM p0
  let pred0 := if e0 == 1 then
    mkAppN (mkConst ``PocklingtonPred.base)
      #[N, root, mkNatLit p0, hp0, eagerReflBoolTrue, eagerReflBoolTrue]
  else
    mkAppN (mkConst ``PocklingtonPred.base_pow)
      #[N, root, mkNatLit p0, mkNatLit e0, hp0, eagerReflBoolTrue, eagerReflBoolTrue]
  let f1_0 : Q(ℕ) := if e0 == 1 then mkNatLit p0
    else mkApp2 (mkConst ``Nat.pow) (mkNatLit p0) (mkNatLit e0)
  let mut pred := pred0
  let mut f1E := f1_0
  for i in [1:factors.size] do
    let (p, e) := factors[i]!
    let hp ← dict.getM p
    if e == 1 then
      pred := mkAppN (mkConst ``PocklingtonPred.step)
        #[N, root, f1E, mkNatLit p, hp, pred, eagerReflBoolTrue, eagerReflBoolTrue]
      f1E := mkApp2 (mkConst ``Nat.mul) f1E (mkNatLit p)
    else
      pred := mkAppN (mkConst ``PocklingtonPred.step_pow)
        #[N, root, f1E, mkNatLit p, mkNatLit e, hp, pred,
          eagerReflBoolTrue, eagerReflBoolTrue]
      f1E := mkApp2 (mkConst ``Nat.mul) f1E
        (mkApp2 (mkConst ``Nat.pow) (mkNatLit p) (mkNatLit e))
  return (f1E, pred)

/-- Recursively certify `Nat.Prime n`, returning an updated dict and a proof expression. -/
partial def certifyPrime (n : Nat) (dict : Meta.PrimeDict) : MetaM (Meta.PrimeDict × Expr) := do
  if let some proof := dict.get? n then
    return (dict, proof)
  if n ≤ 2300 then
    if Nat.Prime n then
      let name : Name := (`PrimeCert).str s!"prime_{n}"
      let proof := mkConst name
      return (dict.insert n proof, proof)
    else
      throwError "{n} is not prime"
  unless Nat.Prime n do throwError "{n} is not prime"
  let factors := trialFactor (n - 1)
  let primeFactors := factors.map (·.1)
  let root ← findPrimitiveRoot n primeFactors
  let mut curDict := dict
  for (p, _) in factors do
    let (dict', _) ← certifyPrime p curDict
    curDict := dict'
  let nE : Q(ℕ) := mkNatLit n
  let rootE : Q(ℕ) := mkNatLit root
  let (f1E, pockPred) ← buildPocklingtonPred nE rootE factors curDict
  let proof := mkAppN (mkConst ``pocklington_certifyKR)
    #[nE, rootE, f1E, pockPred, eagerReflBoolTrue, eagerReflBoolTrue,
      eagerReflBoolTrue, eagerReflBoolTrue]
  return (curDict.insert n proof, proof)

/-- Simproc that automatically proves `Nat.Prime n` for numeric literals
by computing Pocklington certificates at elaboration time. -/
simproc_decl natPrimeCert (Nat.Prime _) := fun e => do
  unless e.isAppOfArity ``Nat.Prime 1 do return .continue
  let arg := e.appArg!
  let some n := arg.nat? | return .continue
  let (_, proof) ← certifyPrime n ∅
  -- Need to type-check the proof so the kernel verifies it
  let proofType ← inferType proof
  let expectedType := mkApp (mkConst ``Nat.Prime) arg
  unless ← isDefEq proofType expectedType do
    throwError "proof type mismatch: expected {expectedType}, got {proofType}"
  return .done { expr := q(True), proof? := some (← mkAppM ``eq_true #[proof]) }

end PrimeCert.Simproc
