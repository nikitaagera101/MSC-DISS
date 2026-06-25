import Mathlib

open Polynomial

namespace PadicExamples

/-!
# Examples

A graded collection of statements about `ℚ_[p]` and `ℤ_[p]`, the `p`-adic numbers and
`p`-adic integers in mathlib.

Try to solve these exercises on paper first, and then write up the proofs here as
an exercise in finding the right library lemmas.
-/

/-- There is no square root of `p` in `ℚ_[p]`. -/
example {p : ℕ} [Fact p.Prime] (x : ℚ_[p]) : x ^ 2 ≠ p := by
  sorry

/-- Similarly, there is no square root of `p ^ 3` in `ℚ_[p]`. -/
example {p : ℕ} [Fact p.Prime] (x : ℚ_[p]) : x ^ 2 ≠ (p : ℚ_[p]) ^ 3 := by
  sorry

/-- `p` is not a unit in the `p`-adic integers. -/
example {p : ℕ} [Fact p.Prime] : ¬ IsUnit (p : ℤ_[p]) := by
  sorry

/-- The powers of `p` tend to `0` in `ℚ_[p]`. -/
example {p : ℕ} [Fact p.Prime] :
    Filter.Tendsto (fun n : ℕ => (p : ℚ_[p]) ^ n) Filter.atTop (nhds 0) := by
  sorry

local instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 3) := ⟨by norm_num⟩

/--`2` has a square root in `ℤ_[7]`.

This is an application of Hensel's lemma. -/
example : ∃ z : ℤ_[7], z ^ 2 = 2 := by
  sorry

/-- `2` has no square root in `ℤ_[3]`. -/
example : ¬ ∃ z : ℤ_[3], z ^ 2 = 2 := by
  sorry

/-- The geometric series `∑ pⁿ` converges in `ℚ_[p]` to `(1 - p)⁻¹`. Note that this is
false in `ℝ`. -/
example {p : ℕ} [Fact p.Prime] :
    ∑' n : ℕ, (p : ℚ_[p]) ^ n = (1 - (p : ℚ_[p]))⁻¹ := by
  sorry

/-- Every `p`-adic integer is the limit of a sequence of ordinary integers (`ℤ` is dense in
`ℤ_[p]`). -/
example {p : ℕ} [Fact p.Prime] (x : ℤ_[p]) :
    ∃ a : ℕ → ℤ, Filter.Tendsto (fun n => (a n : ℤ_[p])) Filter.atTop (nhds x) := by
  sorry

/-! A weird fact in `p`-adic analysis: a series `∑ f n` converges **iff** its terms tend
to `0`. This is not true in `ℝ` (e.g., the harmonic series). -/
example {p : ℕ} [Fact p.Prime] (f : ℕ → ℚ_[p]) :
    Summable f ↔ Filter.Tendsto f Filter.atTop (nhds 0) := by
  sorry

end PadicExamples
