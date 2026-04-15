# Adding in Quadrature

## Version

**Ver: 1.0.1**

## A Lean 4 Formalization of Uncertainty Propagation

A Lean 4 formalization of uncertainty propagation via quadrature addition, demonstrating how to mathematically verify the "adding in quadrature" technique used in spreadsheet modeling.

## Overview

When you have measurements with uncertainties, how do you combine them? If you have two values with uncertainties δX and δY, you can't simply add the uncertainties together. Instead, you use "adding in quadrature".

**What is quadrature?** Instead of adding uncertainties linearly (δX + δY), you square each one, add them together, then take the square root:

```
Combined uncertainty = √(δX² + δY²)
```

This technique appears in my book *Excel Best Practices for Business* (Loren Abdulezer - Wiley Publishing, Inc. ISBN: 076454120X) as a best practice for spreadsheet modeling of combined uncertainties in business calculations like revenue projections, budget forecasts, and risk assessments.

**Why formalize it?** Spreadsheets and mathematical models rely on these formulas daily. By proving the underlying mathematics in Lean 4, we can verify that these techniques are mathematically sound and provide a foundation for building reliable uncertainty calculations.

## Core Theorems (Uncertainty.lean)

The following theorems form the mathematical foundation of adding in quadrature. They are proven in the `Quadrature` namespace using real analysis and provide rigorous proofs of the core properties of uncertainty propagation.

**uncertainty_sq**: Shows squaring the quadrature sum returns the sum of squares: `(√(δX² + δY²))² = δX² + δY²`. This validates that √(δX² + δY²) behaves as a proper magnitude.

**linear_vs_quadrature**: Proves the quadrature sum is strictly less than the linear sum: `√(δX² + δY²) < δX + δY`. *This is the key theorem showing quadrature provides a conservative (safe) upper bound for combined uncertainty.*

**uncertainty_mul**: For positive X, Y: removes absolute value in product uncertainty: `|X·Y|·√(δX²+δY²) = X·Y·√(δX²+δY²)`. This enables simplification of uncertainty expressions involving multiplication.

**uncertainty_mul_exact**: For positive A and x: shows `|A·x| = A·x`. This proves the uncertainty in a scaled value equals the scale factor times the uncertainty in the original value.

**uncertainty_power_two**: For positive x: shows `|x²| = x²`. This is the specific case of the power rule for squaring, showing the absolute value of x² equals x² when x > 0.

## Applied Examples (Applied.lean)

The following definitions and theorems apply the core mathematics to concrete numeric examples. In the `Applied` namespace, we use **subtypes** to guarantee positivity at the type level, then project to ℝ and Float types for Real-based theorems and runtime computations respectively.

**Definitions:**

- **δX_val**, **δY_val**: Uncertainty values constrained to be positive using subtypes
- **δX_val_real**, **δY_val_real**: Projected ℝ values from subtypes for Real computations
- **δX_val_float**, **δY_val_float**: Float values for runtime computations
- **combined_revenue**, **combined_revenue_float**: Combined revenue (100000 + 172500) in ℝ and Float
- **combined_uncertainty**: Real computation: `√(δX² + δY²)`
- **linear_sum**: Linear sum: `δX + δY`
- **combined_uncertainty_approx**, **linear_sum_float**: Float computations for runtime

**Theorems:**

- **uncertainty_sq_applied**: Proves that `(combined_uncertainty)² = δX² + δY²` for our specific parameter values.

- **linear_vs_quadrature_applied**: Applies the key inequality to show that `combined_uncertainty < linear_sum` for our example values.

These applied theorems bridge the abstract mathematics to practical calculations.

## Challenges

**Challenge 1:**

The mathematical expressions involved with Adding in Quadrature is not terribly difficult. Arriving at a proof for much of it is straightforward enough.

Separately, incorporating it within numerical calculations is very easy to apply. But there is a "slight of hand" that takes place. The core theorems are all built with Reals, so definitions involving Reals are inherently noncomputable (they can't be directly used in #eval expressions). But their sister definitions used in numerical computations appear almost identical in structure, except they involve Floats.

My challenge is to come up with a framework so that it is unnecessary to independently write two sets of equations or definitions that are essentially identical (one for Reals and the other for Floats). The only thing linking them is faith that they match. They need to be wedded in a direct way.

**Challenge 2:**

The second challenge is that I want to unequivocally prove that the numerical computations involving Floats directly and rigorously connect back to the core theorems that underpin Adding in Quadrature. That is, the core theorems form an integral part of the numerical applications of mathematical modeling.

From a computational performance standpoint Lean may not be particularly performant. What it would accomplish is to place the validity of applying the framework of Adding in Quadrature onto a sound and solid bedrock.

## Proof Strategy

The proof strategy bridges abstract theorem proving with concrete numeric applications through a systematic approach:

### Using Subtypes to Guarantee Positivity

The core theorems in `Uncertainty.lean` (particularly `linear_vs_quadrature`) require that uncertainty values be strictly positive (`0 < δX` and `0 < δY`). Rather than passing separate proof arguments for each computation, we use **subtypes** to encode positivity guarantees at the type level:

```lean
def δX_val : {x : ℝ // 0 < x} := ⟨10000.1, by norm_num⟩
def δY_val : {x : ℝ // 0 < x} := ⟨30000, by norm_num⟩
```

The subtype `{x : ℝ // 0 < x}` packages a real value together with a proof that it is positive. This eliminates the need for separate positivity arguments when applying theorems.

### From Subtypes to Real and Float

To use these values in both theorem proving and runtime computation, we project from the subtype to both ℝ and Float:

- **δX_val_real**, **δY_val_real** — Extract `.1` from the subtype to get ℝ values for theorems
- **δX_val_float**, **δY_val_float** — Direct Float values for runtime `#eval` expressions

This dual representation directly addresses **Challenge 1**: we maintain a single source of truth (the subtype) while generating both the mathematically rigorous Real-based computations and the computable Float-based computations.

### Connecting Core Theorems to Applied Examples

The `Applied` namespace demonstrates how each core theorem is applied:

| Core Theorem (Uncertainty.lean) | Applied Usage (Applied.lean) |
|--------------------------------|-------------------------------|
| `uncertainty_sq` | `uncertainty_sq_applied` — Proves `(combined_uncertainty)² = δX_val_real² + δY_val_real²` |
| `linear_vs_quadrature` | `linear_vs_quadrature_applied` — Uses `δX_val.2` and `δY_val.2` (positivity proofs) to show the inequality holds |

By extracting the positivity proofs (`.2`) from the subtypes and passing them directly to the core theorems, we achieve **Challenge 2**: the numerical computations in Applied.lean are not merely similar to the abstract theorems — they are formally connected through the same Lean code.

This approach provides a foundation for rigorously linking symbolic theorem proving with numerical computation, extending formalization from abstract mathematics into concrete applications.

## Key Insight

`linear_vs_quadrature` proves that quadrature gives a smaller result than linear addition. This means quadrature provides a conservative (safe) upper bound for combined uncertainty.

In my mind, achieving this would greatly extend the reach of formalizing areas of mathematics from (elegant) theorem proving well into the realm of concrete applications.

## File Structure

| File | Description |
|------|-------------|
| `Basic.lean` | Entry point - imports and verifies core definitions |
| `Uncertainty.lean` | Core theorems proving the mathematics of quadrature |
| `Applied.lean` | Applies theorems to concrete values using subtypes |

## Building

```bash
cd Quadrature
lake build Quadrature
```

## Running Individual Files

```bash
lake env lean Quadrature/Uncertainty.lean
lake env lean Quadrature/Applied.lean
lake env lean Quadrature/Basic.lean
```

## Additional Info
This repository is based on Lean 4.28.0 and Mathlib v4.28.0