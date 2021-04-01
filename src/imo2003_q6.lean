/-
Copyright (c) 2021 Manuel Candales. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manuel Candales
-/
import data.nat.basic
import data.nat.prime

open nat

/-!
# IMO 2003 Q6
Let p be a prime number. Prove that there exists a prime number q such that for every natural n,
the number n^p - p is not divisible by q.

# Solution
TODO
-/

theorem imo2003_q6 (p : ℕ) (hp : prime p) : ∃ q : ℕ, prime q ∧ ∀ n : ℕ, ¬ (q ∣ n^p - p) :=
begin
  sorry,
end
