import PrimeCert.Simproc

open PrimeCert.Simproc

-- Small prime (uses existing declaration)
example : Nat.Prime 7 := by simp [natPrimeCert]

-- Prime just above the 2300 small-prime threshold
example : Nat.Prime 2311 := by simp [natPrimeCert]

-- Larger prime
example : Nat.Prime 100003 := by simp [natPrimeCert]

-- 6-digit prime
example : Nat.Prime 999983 := by simp [natPrimeCert]

-- 7-digit prime
example : Nat.Prime 1000003 := by simp [natPrimeCert]
