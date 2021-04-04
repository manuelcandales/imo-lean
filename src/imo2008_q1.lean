/-
Copyright (c) 2021 Manuel Candales. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manuel Candales
-/
import data.real.basic
import data.real.sqrt

open real

/-!
# IMO 2008 Q1
Find all functions `f : (0,∞) → (0,∞)` (so, `f` is a function from the positive real
numbers to the positive real numbers) such that
      ```
      (f(w)^2 + f(x)^2)/(f(y^2) + f(z^2)) = (w^2 + x^2)/(y^2 + z^2)
      ```
for all positive real numbers `w`, `x`, `y`, `z`, satisfying `wx = yz`.

# Solution
The desired theorem is that either `f = λ x, x` or `f = λ x, 1/x`
-/

theorem imo2008_q1
  (f : ℝ → ℝ)
  (H₁ : ∀ x > 0, f(x) > 0)
  (H₂ : ∀ w x y z : ℝ, 0 < w → 0 < x → 0 < y → 0 < z →
        (f(w)^2 + f(x)^2)/(f(y^2) + f(z^2)) = (w^2 + x^2)/(y^2 + z^2)) :
  ∀ x, 0 < x → (f(x) = x ∨ f(x) = 1/x) :=
begin
  sorry,
end
