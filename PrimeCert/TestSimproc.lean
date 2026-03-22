import PrimeCert.Simproc

open PrimeCert.Simproc

example : Nat.Prime 7 := prime_cert_auto% 7
example : Nat.Prime 2311 := prime_cert_auto% 2311
example : Nat.Prime 100003 := prime_cert_auto% 100003
example : Nat.Prime 1000003 := prime_cert_auto% 1000003
example : Nat.Prime 10000019 := prime_cert_auto% 10000019
example : Nat.Prime 100000007 := prime_cert_auto% 100000007
example : Nat.Prime 1000000009 := prime_cert_auto% 1000000009
example : Nat.Prime 100000000003 := prime_cert_auto% 100000000003
example : Nat.Prime 100000000000031 := prime_cert_auto% 100000000000031
