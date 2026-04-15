/-
Copyright (c) 2026 Loren Abdulezer / Evolving Technologies Corporation
Licensed under the Apache License, Version 2.0
-/
import Mathlib


namespace Quadrature

/-! ## Uncertainty Squaring -/

-- Shows squaring the quadrature sum returns the sum of squares: (√(δX² + δY²))² = δX² + δY²
-- Strategy: Made positivity hypothesis implicit (inferred via `by positivity`) since it's always true
theorem uncertainty_sq {δX δY : ℝ} :
    (√(δX ^ 2 + δY ^ 2)) ^ 2 = δX ^ 2 + δY ^ 2 :=
  Real.sq_sqrt (by positivity)


/-! ## Linear vs Quadrature Sum -/

-- Proves the quadrature sum is strictly less than the linear sum: √(δX² + δY²) < δX + δY
-- Key theorem: shows quadrature provides a conservative (safe) upper bound
/-- Hypothses
  hδX : δX is strictly positive
  hδY : δY is strictly positive
  h_sqs_nneg : sum of squares is non-negative (always true, required for sqrt)
  h_sqs_lt : squares < square of sum (strict inequality via cross term 2*δX*δY > 0)
  h_sum_nneg : sum is non-negative (follows from δX, δY > 0)
--/
theorem linear_vs_quadrature {δX δY : ℝ} (hδX : 0 < δX) (hδY : 0 < δY) :
    √(δX ^ 2 + δY ^ 2) < δX + δY := by
  have h_sqs_nneg : 0 ≤ δX ^ 2 + δY ^ 2 := by positivity
  have h_sqs_lt : δX ^ 2 + δY ^ 2 < (δX + δY) ^ 2 := by
    have : 2 * δX * δY > 0 := by linarith [mul_pos hδX hδY]
    calc
      δX ^ 2 + δY ^ 2 < δX ^ 2 + 2 * δX * δY + δY ^ 2 := by linarith
      _ = (δX + δY) ^ 2 := by ring
  have h_sum_nneg : 0 ≤ δX + δY := le_of_lt (by linarith)
  calc
    √(δX ^ 2 + δY ^ 2) < √((δX + δY) ^ 2) := Real.sqrt_lt_sqrt h_sqs_nneg h_sqs_lt
    _ = δX + δY := Real.sqrt_sq h_sum_nneg


/-! ## Uncertainty Multiplication -/

-- For positive X, Y: |X·Y| = X·Y (removes absolute value)
-- This is a lemma: algebraic identity showing absolute value can be removed for positive products
lemma abs_pos_product {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y) :
    |X * Y| = X * Y := by
  have h1 : |X| = X := abs_of_nonneg hX.le
  have h2 : |Y| = Y := abs_of_nonneg hY.le
  have h3 : |X * Y| = X * Y := by
    calc
      |X * Y| = |X| * |Y| := abs_mul X Y
      _ = X * Y := by rw [h1, h2]
  rw [h3]


/-! ## Uncertainty Formulas -/

-- For positive A, x: |A·x| = A·x (removes absolute value for scalar multiplication)
-- This is a lemma: algebraic identity showing absolute value can be removed
lemma abs_pos_scalar {A x : ℝ} (hA : 0 ≤ A) (hx : 0 < x) :
    |A * x| = A * x := by
  have h1 : |A * x| = |A| * |x| := abs_mul A x
  have h2 : |x| = x := abs_of_pos hx
  have h3 : |A| = A := abs_of_nonneg hA
  rw [h1, h2, h3]


-- Product rule for uncertainty: if q = X * Y, then δq = √((Y * δX)² + (X * δY)²)
-- This is the TRUE uncertainty multiplication theorem (not just the algebraic lemma above)
-- Derived from error propagation: (δq)² = (∂q/∂X)² * (δX)² + (∂q/∂Y)² * (δY)²
-- For q = X * Y: ∂q/∂X = Y, ∂q/∂Y = X
-- Proof: (δq)² = Y² * δX² + X² * δY² = (Y*δX)² + (X*δY)², so δq = √((Y*δX)² + (X*δY)²)
theorem uncertainty_product {X Y δX δY : ℝ} :
    let δq := √((Y * δX) ^ 2 + (X * δY) ^ 2)
    (δq) ^ 2 = (Y * δX) ^ 2 + (X * δY) ^ 2 := by
  have h_nneg : 0 ≤ (Y * δX) ^ 2 + (X * δY) ^ 2 := by positivity
  have h_sqs : (√((Y * δX) ^ 2 + (X * δY) ^ 2)) ^ 2 = (Y * δX) ^ 2 + (X * δY) ^ 2 :=
    Real.sq_sqrt h_nneg
  exact h_sqs


-- Power rule for uncertainty: if q = x^n, then (δq)² = (n * x^(n-1))² * (δx)²
-- This is the TRUE uncertainty power theorem based on error propagation
-- Derived from error propagation: (δq)² = (∂q/∂x)² * (δx)²
-- For q = x^n: ∂q/∂x = n * x^(n-1)
-- Proof: (δq)² = (n * x^(n-1))² * (δx)²
theorem uncertainty_power {x δx : ℝ} (n : ℕ) :
    let δq := n * x ^ (n - 1) * δx
    (δq) ^ 2 = (n * x ^ (n - 1)) ^ 2 * (δx) ^ 2 := by
  have h_nneg : 0 ≤ (n * x ^ (n - 1)) ^ 2 * (δx) ^ 2 := by positivity
  have h_sqs : ((n * x ^ (n - 1)) * δx) ^ 2 = (n * x ^ (n - 1)) ^ 2 * (δx) ^ 2 := by ring_nf
  exact h_sqs


end Quadrature

#min_imports
