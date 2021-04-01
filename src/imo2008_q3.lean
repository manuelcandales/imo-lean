/-
Copyright (c) 2021 Manuel Candales. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manuel Candales
-/
import data.nat.prime
import data.real.sqrt

/-!
# IMO 2008 Q3
Prove that there exist infinitely many positive integers n such that n^2+1 has a prime
divisor which is greater than 2n + √(2n).
-/

theorem imo2008_q3 :
∀ N : ℕ, ∃ n : ℕ, n > N ∧ ∃ p : ℕ, nat.prime p ∧ p ∣ n^2 + 1 ∧ real.sqrt(2*n) + 2*n < p :=
begin
  sorry
end
