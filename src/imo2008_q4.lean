/-
Copyright (c) 2021 Manuel Candales. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manuel Candales
-/
import data.real.basic
import data.real.sqrt

open real

/-!
# IMO 2008 Q4
Find all functions `f : (0,∞) → (0,∞)` (so, `f` is a function from the positive real
numbers to the positive real numbers) such that
      ```
      (f(w)^2 + f(x)^2)/(f(y^2) + f(z^2)) = (w^2 + x^2)/(y^2 + z^2)
      ```
for all positive real numbers `w`, `x`, `y`, `z`, satisfying `wx = yz`.

# Solution
The desired theorem is that either `f = λ x, x` or `f = λ x, 1/x`
-/

theorem imo2008_q4
  (f : ℝ → ℝ)
  (H₁ : ∀ x > 0, f(x) > 0)
  (H₂ : ∀ w x y z : ℝ, 0 < w → 0 < x → 0 < y → 0 < z →
        (f(w)^2 + f(x)^2)/(f(y^2) + f(z^2)) = (w^2 + x^2)/(y^2 + z^2)) :
  (∀ x > 0, f(x) = x) ∨ (∀ x > 0, f(x) = 1/x) :=
begin
  have h₀ : f(1) ≠ 0, { specialize H₁ 1 zero_lt_one, exact ne_of_gt H₁ },

  have h₁ : f(1) = 1,
  { specialize H₂ 1 1 1 1 zero_lt_one zero_lt_one zero_lt_one zero_lt_one,
    norm_num at H₂,
    rw [(two_mul (f(1)^2)).symm, (two_mul (f 1)).symm] at H₂,
    rw mul_div_mul_left (f(1)^2) (f 1) two_ne_zero at H₂,
    rwa ← (div_eq_iff h₀).mpr (pow_two (f 1)) },

  have h₂ : ∀ x > 0, (f x - x) * (f x - 1/x) = 0,
  { intros x hx,
    specialize H₂ 1 x (sqrt x) (sqrt x) zero_lt_one hx (sqrt_pos.mpr hx) (sqrt_pos.mpr hx),
    rw [h₁, (one_pow 2), (sqr_sqrt (le_of_lt hx)), (two_mul (f x)).symm, (two_mul x).symm] at H₂,
    have hx_ne_0 : x ≠ 0 := ne_of_gt hx,
    have hfx_ne_0 : (f x) ≠ 0, { specialize H₁ x hx, exact ne_of_gt H₁ },
    field_simp at H₂,

    have h1 : (2 * x) * ((f x - x) * (f x - 1/x)) = 0,
    { calc  (2*x) * ((f x - x) * (f x - 1/x))
          = 2 * (f x - x) * (x * f x - x * 1/x)   : by ring
      ... = 2 * (f x - x) * (x * f x - 1)         : by rw (mul_div_cancel_left 1 hx_ne_0)
      ... = ((1+f(x)^2)*(2*x) - (1+x^2)*(2*f(x))) : by ring
      ... = 0                                     : sub_eq_zero.mpr H₂ },

    have h2x_ne_0 : 2*x ≠ 0 := mul_ne_zero two_ne_zero hx_ne_0,

    calc  ((f x - x) * (f x - 1/x))
        = (2*x) * ((f x - x) * (f x - 1/x)) / (2*x) : (mul_div_cancel_left _ h2x_ne_0).symm
    ... = 0                                         : by { rw h1, exact zero_div (2*x) } },

  have h₃ : ∀ x > 0, f(x) = x ∨ f(x) = 1/x,
  { rintros x hx,
    obtain h := zero_eq_mul.mp (h₂ x hx).symm,
    cases h with hp hq,
    left, linarith [hp],
    right, linarith [hq] },

  by_contradiction,
  obtain ⟨hp₁, hq₁⟩ := not_or_distrib.mp h,

  obtain ⟨x, hp₂⟩ := not_forall.mp hp₁,
  obtain ⟨hx, hp₃⟩ := not_imp.mp hp₂,
  obtain hp₄ := or.resolve_left (h₃ x hx) hp₃, -- f(x) = 1/x

  obtain ⟨y, hq₂⟩ := not_forall.mp hq₁,
  obtain ⟨hy, hq₃⟩ := not_imp.mp hq₂,
  obtain hq₄ := or.resolve_right (h₃ y hy) hq₃, -- f(y) = y

  sorry,
end
