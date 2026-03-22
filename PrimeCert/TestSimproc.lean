import PrimeCert.Simproc

open PrimeCert.Simproc

-- Small prime
example : Nat.Prime 7 := by prime_cert_tac
example : Nat.Prime 2311 := by prime_cert_tac
example : Nat.Prime 100003 := by prime_cert_tac
example : Nat.Prime 1000003 := by prime_cert_tac
example : Nat.Prime 10000019 := by prime_cert_tac
example : Nat.Prime 100000007 := by prime_cert_tac

-- 10-digit — takes ~60s for kernel checking
example : Nat.Prime 1000000009 := by prime_cert_tac
