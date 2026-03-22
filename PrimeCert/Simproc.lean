/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import PrimeCert.SmallPrimes
import PrimeCert.Pocklington3
import Qq

/-! # Simproc for automatic primality certification

A `simproc` that recognizes `Nat.Prime n` for numeric literals and automatically
constructs Pocklington certificates. The witness (factorization of `n-1`, primitive root)
is computed in untrusted elaboration-time code; the proof term is kernel-checked via
`pocklington3_certKR` (cube-root Pocklington) or `pocklington_certifyKR` (classic).
-/

open Lean Meta Qq

namespace PrimeCert.Simproc

/-! ## Untrusted elaboration-time utilities -/

/-- Trial-division factorization. Returns array of (prime, exponent) pairs. -/
partial def trialFactor (n : Nat) : Array (Nat × Nat) :=
  go n #[] 2
where
  go (n : Nat) (acc : Array (Nat × Nat)) (d : Nat) : Array (Nat × Nat) :=
    if n ≤ 1 then acc
    else if d * d > n then
      acc.push (n, 1)
    else if n % d == 0 then
      let (n', e) := extractFactor n d 0
      go n' (acc.push (d, e)) (if d == 2 then 3 else d + 2)
    else
      go n acc (if d == 2 then 3 else d + 2)
  extractFactor (n p e : Nat) : Nat × Nat :=
    if n % p == 0 then extractFactor (n / p) p (e + 1)
    else (n, e)

/-- Extract the 2-adic valuation of `n`. Returns `(e, odd)` where `n = 2^e * odd`. -/
partial def extract2 (n : Nat) : Nat × Nat :=
  go n 0
where
  go (n e : Nat) : Nat × Nat :=
    if n % 2 == 0 && n > 0 then go (n / 2) (e + 1) else (e, n)

/-- Factor `n` partially: extract odd prime factors until the product exceeds `bound`.
Returns `(factored_pairs, remaining_cofactor)`. -/
partial def partialFactor (n : Nat) (bound : Nat) : Array (Nat × Nat) × Nat :=
  go n #[] 1 3
where
  go (n : Nat) (acc : Array (Nat × Nat)) (prod : Nat) (d : Nat) : Array (Nat × Nat) × Nat :=
    if prod > bound then (acc, n)
    else if n ≤ 1 then (acc, 1)
    else if d * d > n then
      (acc.push (n, 1), 1)
    else if n % d == 0 then
      let (n', e) := extractFactor n d 0
      go n' (acc.push (d, e)) (prod * d ^ e) (d + 2)
    else
      go n acc prod (d + 2)
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
  let mut a := 2
  while a < n do
    if isPrimitiveRoot n a primeFactors then return a
    a := a + 1
  throwError "no primitive root found for {n}"

/-- Compute the sieve bound `m` for pock3: the smallest m ≥ 1 such that
for all `1 ≤ l < m`, `l*F+1` does not divide `N`. We stop when `(m*F+1)² > N`. -/
partial def computeSieveBound (n F : Nat) : Nat :=
  go 1
where
  go (m : Nat) : Nat :=
    let lF1 := m * F + 1
    if lF1 * lF1 > n then m
    else if n % lF1 == 0 then m + 1  -- shouldn't happen for prime N, but be safe
    else go (m + 1)

/-- Find a `Pocklington3CertMode` for given `r, s`. -/
def findCertMode (r s : Nat) (dict : Meta.PrimeDict) :
    MetaM Expr := do
  if s == 0 then
    return mkConst ``PrimeCert.Pocklington3CertMode.zero
  if r ^ 2 < 8 * s then
    return mkConst ``PrimeCert.Pocklington3CertMode.lt
  -- Find a prime p > 2 where r²-8s is a QNR mod p (Euler criterion)
  let val := r ^ 2 - 8 * s
  let smallPrimes := #[3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67,
    71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157,
    163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241,
    251, 257, 263, 269, 271, 277, 281, 283]
  for p in smallPrimes do
    if powModTR' val (p / 2) p == p - 1 then
      let hp ← dict.getM p
      let pE := mkNatLit p
      return mkApp2 (mkConst ``PrimeCert.Pocklington3CertMode.prime) pE hp
  throwError "could not find non-square certificate mode for r={r}, s={s}"

/-! ## Proof term construction -/

/-- Build the `F'` list expression (`List PrimePow`) for pock3 from odd factors. -/
private def buildPrimePowList (oddFactors : Array (Nat × Nat)) (dict : Meta.PrimeDict) :
    MetaM Expr := do
  let mut listE : Expr := mkApp (mkConst ``List.nil [.zero]) (mkConst ``PrimeCert.PrimePow)
  for i in List.range oddFactors.size |>.reverse do
    let (p, e) := oddFactors[i]!
    let hp ← dict.getM p
    let ppE := mkAppN (mkConst ``PrimeCert.PrimePow.mk)
      #[mkNatLit p, mkNatLit e, hp, eagerReflBoolTrue]
    listE := mkAppN (mkConst ``List.cons [.zero]) #[mkConst ``PrimeCert.PrimePow, ppE, listE]
  return listE

/-- Build the F₁ expression and PocklingtonPred proof from factorization (classic Pocklington). -/
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

/-! ## Main certification logic -/

/-- Main entry point: recursively certify `Nat.Prime n`. -/
partial def certifyPrime (n : Nat) (dict : Meta.PrimeDict) :
    MetaM (Meta.PrimeDict × Expr) := do
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
  -- Use pock3 (cube-root variant) for primes > 2300
  certifyPrimePock3 n dict
where
  /-- Certify using pock3 (cube-root Pocklington). Only needs F > N^(1/3). -/
  certifyPrimePock3 (n : Nat) (dict : Meta.PrimeDict) :
      MetaM (Meta.PrimeDict × Expr) := do
    let nm1 := n - 1
    -- Split n-1 = 2^e * oddPart
    let (e, oddPart) := extract2 nm1
    if e == 0 then
      throwError "pock3 requires N-1 to be even (N must be odd), but N={n}"
    -- We need F = 2^e * (odd factored part) > N^(1/3)
    -- Using sqrt(n) as a conservative bound for cube root
    let cubeRootBound := Nat.sqrt n
    let twoE := 2 ^ e
    -- Factor odd part until product of odd factors > cubeRootBound / 2^e
    let neededOddProduct := cubeRootBound / twoE + 1
    let (oddFactors, _) := partialFactor oddPart neededOddProduct
    let oddProduct := oddFactors.foldl (fun acc (p, exp) => acc * p ^ exp) 1
    let bigF := twoE * oddProduct
    -- All prime factors of F (including 2)
    let allPrimeFactors := #[2] ++ oddFactors.map (·.1)
    -- Find primitive root
    let root ← findPrimitiveRoot n allPrimeFactors
    -- Compute R, r, s for the non-square certificate
    let bigR := nm1 / bigF
    let twoF := 2 * bigF
    let r := bigR % twoF
    let s := bigR / twoF
    -- Sieve bound
    let m := computeSieveBound n bigF
    -- Check bound inequality: s*2 + m² < (2F + r) * m + 2
    unless s * 2 + m ^ 2 < (2 * bigF + r) * m + 2 do
      throwError "pock3 bound check failed for N={n}, F={bigF}, m={m}, r={r}, s={s}"
    -- Recursively certify all odd prime factors of F
    let mut curDict := dict
    for (p, _) in oddFactors do
      let (dict', _) ← certifyPrime p curDict
      curDict := dict'
    -- Ensure 2 is in the dict
    if curDict.get? 2 |>.isNone then
      curDict := curDict.insert 2 (mkConst ((`PrimeCert).str "prime_2"))
    -- Find cert mode
    let modeE ← findCertMode r s curDict
    -- Build proof term
    let nE : Q(ℕ) := mkNatLit n
    let rootE : Q(ℕ) := mkNatLit root
    let mE : Q(ℕ) := mkNatLit m
    let eE : Q(ℕ) := mkNatLit e
    let f'E ← buildPrimePowList oddFactors curDict
    let proof := mkAppN (mkConst ``PrimeCert.pocklington3_certKR)
      #[nE, rootE, mE, eE, f'E, modeE, eagerReflBoolTrue]
    return (curDict.insert n proof, proof)

/-- Simproc that automatically proves `Nat.Prime n` for numeric literals
by computing Pocklington certificates at elaboration time. -/
simproc_decl natPrimeCert (Nat.Prime _) := fun e => do
  unless e.isAppOfArity ``Nat.Prime 1 do return .continue
  let arg := e.appArg!
  let some n := arg.nat? | return .continue
  let (_, proof) ← certifyPrime n ∅
  -- Construct `@eq_true (Nat.Prime n) proof` directly to avoid triggering
  -- kernel reduction during elaboration-time isDefEq checks.
  let propE := mkApp (mkConst ``Nat.Prime) arg
  let eqTrueProof := mkApp2 (mkConst ``eq_true) propE proof
  return .done { expr := q(True), proof? := some eqTrueProof }

/-- Find an odd prime `w` such that `val` is a quadratic non-residue mod `w`. -/
def findQNRWitness (val : Nat) : MetaM Nat := do
  for w in [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61,
            67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137,
            139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199] do
    if Nat.Prime w && powModTR' val (w / 2) w == w - 1 then
      return w
  throwError "no QNR witness found for {val}"

structure CertState where
  smalls : Array Nat := #[]
  steps : Array String := #[]
  visited : Std.HashSet Nat := {}

/-- Generate a `prime_cert%` syntax string by computing pock3 certificates.
Mirrors the Python script's logic exactly. -/
partial def genCert (p : Nat) (st : CertState) : MetaM CertState := do
  if p ≤ 2300 then
    return { st with smalls := st.smalls.push p }
  if st.visited.contains p then return st
  let st := { st with visited := st.visited.insert p }
  let nm1 := p - 1
  let (e, oddPart) := extract2 nm1
  -- Cube root bound
  let mut target := 1
  while (target + 1) ^ 3 ≤ p do target := target + 1
  target := target + 2
  -- Factor odd part minimally
  let (oddFactors, _) := partialFactor oddPart (target / (2 ^ e) + 1)
  let oddProduct := oddFactors.foldl (fun acc (pe : Nat × Nat) => acc * pe.1 ^ pe.2) 1
  let bigF := (2 ^ e) * oddProduct
  let allPrimeFactors := #[2] ++ oddFactors.map (·.1)
  let root ← findPrimitiveRoot p allPrimeFactors
  let bigR := nm1 / bigF
  let twoF := 2 * bigF
  let r := bigR % twoF
  let s := bigR / twoF
  let m := computeSieveBound p bigF
  -- Find mode
  let (mode, st1) ←
    if s == 0 then pure ("0", st)
    else if r ^ 2 < 8 * s then pure ("<", st)
    else do
      let val := r ^ 2 - 8 * s
      let w ← findQNRWitness val
      pure (toString w, { st with smalls := st.smalls.push w })
  -- Recurse on factor primes
  let mut cur := st1
  for i in List.range oddFactors.size do
    cur ← genCert (oddFactors[i]!).1 cur
  -- Build step string
  let pp (b exp : Nat) : String := if exp == 1 then toString b else s!"{b} ^ {exp}"
  let fStr := String.intercalate " * "
    ([pp 2 e] ++ oddFactors.toList.map (fun (q, exp) => pp q exp))
  return { cur with steps := cur.steps.push s!"({p}, {root}, {m}, {mode}, {fStr})" }

open Lean in
/-- Term elaborator that generates `prime_cert%` syntax and elaborates it.
Computes the certificate at elaboration time, then expands to `prime_cert%`
which handles kernel checking efficiently. -/
elab "prime_cert_auto%" n:num : term => do
  let nVal := n.getNat
  let st ← genCert nVal {}
  let smallsDedup := st.smalls.toList.eraseDups.mergeSort (· < ·)
  let smallStr := String.intercalate "; " (smallsDedup.map toString)
  let stepsStr := String.intercalate "; " st.steps.toList
  let src := if st.steps.isEmpty then
    s!"prime_cert% [small \{{smallStr}}]"
  else
    s!"prime_cert% [small \{{smallStr}}, pock3 \{{stepsStr}}]"
  let env ← getEnv
  let stx ← match Parser.runParserCategory env `term src with
    | .ok stx => pure stx
    | .error e => throwError "parse error: {e}"
  let nE := mkNatLit nVal
  let expectedType := mkApp (mkConst ``Nat.Prime) nE
  Elab.Term.elabTerm (stx := stx) (expectedType? := some expectedType)

end PrimeCert.Simproc
