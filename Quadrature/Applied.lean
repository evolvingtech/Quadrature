/-
Copyright (c) 2026 Loren Abdulezer / Evolving Technologies Corporation
Licensed under the Apache License, Version 2.0
-/
import Mathlib
import Quadrature.Uncertainty

namespace Applied

-- APPLIED APPROACH WITH SUBTYPE: Values constrained to be positive

----------------------------------------------------------------------
-- ACTUAL VALUES: Using Subtype to guarantee positivity
----------------------------------------------------------------------

-- δX_val : ℝ constrained to be > 0
def δX_val : {x : ℝ // 0 < x} := ⟨10000.1, by norm_num⟩

-- δY_val : ℝ constrained to be > 0
def δY_val : {x : ℝ // 0 < x} := ⟨30000, by norm_num⟩

-- Project to ℝ for computations (using .1 to access the value)
def δX_val_real : ℝ := δX_val.1
def δY_val_real : ℝ := δY_val.1

def δX_val_float : Float := 10000.1
def δY_val_float : Float := 30000

def combined_revenue : ℝ := 100000 + 172500
def combined_revenue_float : Float := 100000 + 172500

----------------------------------------------------------------------
-- COMPUTATIONS using PosReal values
----------------------------------------------------------------------

-- Real computation (for theorems) - extract .1 to get ℝ
noncomputable def combined_uncertainty : ℝ := √(δX_val_real ^ 2 + δY_val_real ^ 2)
def linear_sum : ℝ := δX_val_real + δY_val_real

-- Float computation (for runtime)
def combined_uncertainty_approx : Float :=
  Float.sqrt (δX_val_float * δX_val_float + δY_val_float * δY_val_float)
def linear_sum_float : Float := δX_val_float + δY_val_float

----------------------------------------------------------------------
-- THEOREMS: No separate positivity lemmas needed!
-- The type guarantees positivity - extract with .2
----------------------------------------------------------------------

theorem uncertainty_sq_applied :
    (combined_uncertainty) ^ 2 = δX_val_real ^ 2 + δY_val_real ^ 2 :=
  Quadrature.uncertainty_sq (by positivity)

-- Extract positivity proofs using .2 (the property of the subtype)
theorem linear_vs_quadrature_applied :
    combined_uncertainty < linear_sum :=
  Quadrature.linear_vs_quadrature δX_val.2 δY_val.2

----------------------------------------------------------------------
-- RUNTIME VERIFICATION
----------------------------------------------------------------------

#eval combined_uncertainty_approx    -- ~31622.81
#eval combined_revenue_float         -- 272500
#eval linear_sum_float              -- 40000.1
#eval combined_uncertainty_approx < linear_sum_float  -- true

end Applied

#min_imports
