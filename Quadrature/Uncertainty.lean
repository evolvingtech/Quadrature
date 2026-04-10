/-
Copyright (c) 2026 Loren Abdulezer / Evolving Technologies Corporation
Licensed under the Apache License, Version 2.0
-/
import Mathlib


namespace Quadrature

/-! ## Uncertainty Squaring -/

-- Shows squaring the quadrature sum returns the sum of squares: (√(δX² + δY²))² = δX² + δY²
theorem uncertainty_sq {δX δY : ℝ} (h : 0 ≤ δX ^ 2 + δY ^ 2) :
    (√(δX ^ 2 + δY ^ 2)) ^ 2 = δX ^ 2 + δY ^ 2 := Real.sq_sqrt h


/-! ## Linear vs Quadrature Sum -/

-- Proves the quadrature sum is strictly less than the linear sum: √(δX² + δY²) < δX + δY
theorem linear_vs_quadrature {δX δY : ℝ} (hδX : 0 < δX) (hδY : 0 < δY) :
    √(δX ^ 2 + δY ^ 2) < δX + δY := by
  have h4 : 0 ≤ δX ^ 2 + δY ^ 2 := by positivity
  have h5 : δX ^ 2 + δY ^ 2 < (δX + δY) ^ 2 := by
    have : 2 * δX * δY > 0 := by linarith [mul_pos hδX hδY]
    calc
      δX ^ 2 + δY ^ 2 < δX ^ 2 + 2 * δX * δY + δY ^ 2 := by linarith
      _ = (δX + δY) ^ 2 := by ring
  have h6 : 0 ≤ δX + δY := le_of_lt (by linarith)
  calc
    √(δX ^ 2 + δY ^ 2) < √((δX + δY) ^ 2) := Real.sqrt_lt_sqrt h4 h5
  _ = δX + δY := Real.sqrt_sq h6


/-! ## Uncertainty Multiplication -/

-- For positive X, Y: removes absolute value in product uncertainty: |X·Y|·√(δX²+δY²) = X·Y·√(δX²+δY²)
theorem uncertainty_mul {X Y δX δY : ℝ} (hX : 0 < X) (hY : 0 < Y) :
    |X * Y| * √(δX ^ 2 + δY ^ 2) = X * Y * √(δX ^ 2 + δY ^ 2) := by
  have h1 : |X| = X := abs_of_nonneg hX.le
  have h2 : |Y| = Y := abs_of_nonneg hY.le
  have h3 : |X * Y| = X * Y := by
    calc
      |X * Y| = |X| * |Y| := abs_mul X Y
      _ = X * Y := by rw [h1, h2]
  rw [h3]


/-! ## Uncertainty Formulas -/

-- Exact uncertainty for scalar multiplication: if q = A * x, then δq = |A| * δx
-- The uncertainty in A*x equals |A| times the uncertainty in x
theorem uncertainty_mul_exact {A x : ℝ} (hA : 0 ≤ A) (hx : 0 < x) :
    |A * x| = A * x := by
  have h1 : |A * x| = |A| * |x| := abs_mul A x
  have h2 : |x| = x := abs_of_pos hx
  have h3 : |A| = A := abs_of_nonneg hA
  rw [h1, h2, h3]


-- Power rule: for q = x^2, relative uncertainty relates to absolute
-- This shows |x^2| = x^2 when x > 0
theorem uncertainty_power_two {x : ℝ} (hx : 0 < x) :
    |x ^ 2| = x ^ 2 := by
  have h1 : 0 < x ^ 2 := by positivity
  exact abs_of_pos h1

end Quadrature

#min_imports
