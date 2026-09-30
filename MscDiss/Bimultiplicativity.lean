import MscDiss.PadicMachinery
import Mathlib.Tactic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.NumberTheory.Padics.Hensel

/- # SECTION 4 : THE EXPLICIT FORMULA FOR THE HILBERT SYMBOL AT p = 2 OR p ODD -/
/-
**(1) What this section does :** For `a = p^α u`, `b = p^β v` in `ℚ_pˣ` Serre's Theorem 1
gives the explicit formulae for the Hilbert symbol at p :
→ for `p ≠ 2` :  `(a,b) = (−1)^{αβ ε(p)} · (u/p)^β · (v/p)^α`
→ for `p = 2` :  `(a,b) = (−1)^{ε(u)ε(v) + α ω(v) + β ω(u)}`
where `(·/p)` denotes the Legendre symbol and `ε(u) = (u−1)/2`, `ω(u) = (u²−1)/8` mod 2
(Serre I.3.2). We define these right-hand sides as functions
`formulaOdd`, `formulaTwo : ℚ_pˣ → ℚ_pˣ → ℤˣ` and prove they are bimultiplicative and symmetric.
Sections 6–7 then equate them with the symbol of Section 2.

**(2) Why we need it :** Serre proves bilinearity of the Hilbert symbol (Thm 2) as a corollary of
Thm 1: the right-hand sides are bimultiplicative because they are built from characters. That is
exactly what happens here — `formulaOdd` inherits multiplicativity from the Legendre character
`quadraticCharUnits` and from `valuationUnits`, `unitPartZMod`, while `formulaTwo` inherits it
from `ε`, `ω` being homomorphisms. Sections 6–7 prove `hilbertSym = formulaOdd` and
`hilbertSym = formulaTwo`, and bimultiplicativity of the geometric symbol follows.

**(3) Design discussion :** Serre's `(−1)^{ε(p)}` is `(−1/p)` (Euler's criterion, Serre I.3.2
Thm 4), so the odd formula is written with `quadraticCharUnits p (−1)` in place of
`(−1)^{ε(p)}`. For `p = 2` the exponent lives in `ZMod 2` and `sgn : ZMod 2 → ℤˣ` converts it to a
sign. Defining these via Mathlib's quadratic characters and a sign homomorphism means most of
their properties are already in Mathlib and avoids long formulae crowding the tactic state.
-/

/- # 4.1 THE LEGENDRE SYMBOL AS A QUADRATIC CHARACTER -/

namespace Padic

variable {p : ℕ } [Fact p.Prime]

/--*Definition 4.1.1 : The Legendre symbol as the unit-valued quadratic character (ℤ/p)ˣ →* ℤˣ*--/
noncomputable def quadraticCharUnits (p : ℕ) [Fact p.Prime] : (ZMod p)ˣ →* ℤˣ :=
  (quadraticChar (ZMod p)).toUnitHom

/--*Lemma 4.1.1 : The Legendre symbol of a unit equals 1 iff it is a square in ℤ/p*--/
lemma quadraticCharUnits_eq_one_iff (w : (ZMod p)ˣ) :
    quadraticCharUnits p w = 1 ↔ IsSquare (w : ZMod p) := by
  rw [← quadraticChar_one_iff_isSquare w.ne_zero, ← Units.val_eq_one]
  unfold quadraticCharUnits
  simp

/--*Lemma 4.1.2 : The Legendre symbol of a unit equals -1 iff it is not a square in ℤ/p*--/
lemma quadraticCharUnits_eq_neg_one_iff (w : (ZMod p)ˣ) :
    quadraticCharUnits p w = -1 ↔ ¬ IsSquare (w : ZMod p) := by
  rw [← quadraticCharUnits_eq_one_iff]
  constructor
  · intro h h1
    simp_all
  · intro h
    rcases Int.units_eq_one_or (quadraticCharUnits p w) with h1 | h1
    · solve_by_elim
    · grind

/- # 4.2 THE EXPLICIT FORMULA FOR ODD p AND ITS PROPERTIES -/

/--*Definition 4.2.1 : Explicit formula for the Hilbert symbol at odd p (Serre III.1.2, Thm 1)*--/
noncomputable def formulaOdd (a b : ℚ_[p]ˣ) : ℤˣ :=
  quadraticCharUnits p (-1) ^ (valuationUnits a * valuationUnits b)
    * quadraticCharUnits p (unitPartZMod b) ^ valuationUnits a
    * quadraticCharUnits p (unitPartZMod a) ^ valuationUnits b

/--*Lemma 4.2.1 : formulaOdd is symmetric*--/
lemma formulaOdd_comm (a b : ℚ_[p]ˣ) : formulaOdd a b = formulaOdd b a := by
  unfold formulaOdd
  rw [mul_comm (valuationUnits a) (valuationUnits b)]
  ac_rfl

/--*Lemma 4.2.2 : formulaOdd is multiplicative in the first entry*--/
lemma formulaOdd_mul_left (a a' b : ℚ_[p]ˣ) :
    formulaOdd (a * a') b = formulaOdd a b * formulaOdd a' b := by
  unfold formulaOdd
  simp only [valuationUnits_mul, unitPartZMod_mul, map_mul, add_mul]
  have h1 : quadraticCharUnits p (-1) ^ (valuationUnits a * valuationUnits b
      + valuationUnits a' * valuationUnits b)
      = quadraticCharUnits p (-1) ^ (valuationUnits a * valuationUnits b)
        * quadraticCharUnits p (-1) ^ (valuationUnits a' * valuationUnits b) := zpow_add _ _ _
  have h2 : quadraticCharUnits p (unitPartZMod b) ^ (valuationUnits a + valuationUnits a')
      = quadraticCharUnits p (unitPartZMod b) ^ valuationUnits a
        * quadraticCharUnits p (unitPartZMod b) ^ valuationUnits a' := zpow_add _ _ _
  have h3 : (quadraticCharUnits p (unitPartZMod a) * quadraticCharUnits p (unitPartZMod a'))
      ^ valuationUnits b
      = quadraticCharUnits p (unitPartZMod a) ^ valuationUnits b
        * quadraticCharUnits p (unitPartZMod a') ^ valuationUnits b := mul_zpow _ _ _
  rw [h1, h2, h3]
  ac_rfl

/--*Lemma 4.2.3 : formulaOdd is multiplicative in the second entry*--/
lemma formulaOdd_mul_right (a b b' : ℚ_[p]ˣ) :
    formulaOdd a (b * b') = formulaOdd a b * formulaOdd a b' := by
  rw [formulaOdd_comm, formulaOdd_mul_left, formulaOdd_comm b a, formulaOdd_comm b' a]

/--*Lemma 4.2.4 : formulaOdd is bimultiplicative*--/
lemma formulaOdd_isSqBimult : IsSqBimult (formulaOdd (p := p)) :=
  ⟨formulaOdd_mul_left, formulaOdd_mul_right⟩

/--*Lemma 4.2.5 : Square invariance of formulaOdd in the first entry*--/
lemma formulaOdd_mul_sq_left (a c b : ℚ_[p]ˣ) : formulaOdd (a * c ^ 2) b = formulaOdd a b :=
  formulaOdd_isSqBimult.mul_sq_left a b c

/--*Lemma 4.2.6 : Square invariance of formulaOdd in the second entry*--/
lemma formulaOdd_mul_sq_right (a b c : ℚ_[p]ˣ) : formulaOdd a (b * c ^ 2) = formulaOdd a b :=
  formulaOdd_isSqBimult.mul_sq_right a b c

/- # 4.3 RESIDUES MOD 4 AND 8, AND ε, ω, sgn FOR THE p = 2 CASE -/

/--*Definition 4.3.1 : The residue mod 4 of the unit part of a 2-adic number*--/
private noncomputable def unitPartZMod4 (a : ℚ_[2]ˣ) : (ZMod 4)ˣ :=
  Units.map (PadicInt.toZModPow 2).toMonoidHom (unitPart a)

/--*Lemma 4.3.1 : The residue mod 4 viewed in ℤ/4 is the reduction mod 4 of the unit part*--/
lemma coe_unitPartZMod4 (a : ℚ_[2]ˣ) :
    ((unitPartZMod4 a : (ZMod 4)ˣ) : ZMod 4) = PadicInt.toZModPow 2 (unitPart a : ℤ_[2]) := rfl

/--*Lemma 4.3.2 : The residue mod 4 is multiplicative*--/
lemma unitPartZMod4_mul (a b : ℚ_[2]ˣ) :
    unitPartZMod4 (a * b) = unitPartZMod4 a * unitPartZMod4 b := by
  unfold unitPartZMod4
  rw [unitPart_mul, map_mul]

/--*Definition 4.3.2 : The residue mod 8 of the unit part of a 2-adic number*--/
private noncomputable def unitPartZMod8 (a : ℚ_[2]ˣ) : (ZMod 8)ˣ :=
  Units.map (PadicInt.toZModPow 3).toMonoidHom (unitPart a)

/--*Lemma 4.3.3 : The residue mod 8 viewed in ℤ/8 is the reduction mod 8 of the unit part*--/
lemma coe_unitPartZMod8 (a : ℚ_[2]ˣ) :
    ((unitPartZMod8 a : (ZMod 8)ˣ) : ZMod 8) = PadicInt.toZModPow 3 (unitPart a : ℤ_[2]) := rfl

/--*Lemma 4.3.4 : The residue mod 8 is multiplicative*--/
lemma unitPartZMod8_mul (a b : ℚ_[2]ˣ) :
    unitPartZMod8 (a * b) = unitPartZMod8 a * unitPartZMod8 b := by
  unfold unitPartZMod8
  rw [unitPart_mul, map_mul]

/--*Definition 4.3.3 : ε(a) ∈ ℤ/2, with ε(a) = 0 ↔ unit part of a ≡ 1 (mod 4)*--/
noncomputable def epsilon2 (a : ℚ_[2]ˣ) : ZMod 2 := if unitPartZMod4 a = 1 then 0 else 1

/--*Lemma 4.3.5 : Finite check on (ℤ/4)ˣ that ε is additive (Serre III.1.2)*--/
lemma epsilon2_aux : ∀ u v : (ZMod 4)ˣ,
    (if u * v = 1 then (0 : ZMod 2) else 1)
      = (if u = 1 then (0 : ZMod 2) else 1) + (if v = 1 then 0 else 1) := by
  decide

/--*Lemma 4.3.6 : ε is a homomorphism (ℚ_2ˣ, ·) → (ℤ/2, +)*--/
lemma epsilon2_mul (a b : ℚ_[2]ˣ) : epsilon2 (a * b) = epsilon2 a + epsilon2 b := by
  unfold epsilon2
  rw [unitPartZMod4_mul]
  exact epsilon2_aux (unitPartZMod4 a) (unitPartZMod4 b)

/--*Definition 4.3.4 : ω(a) ∈ ℤ/2, with ω(a) = 0 ↔ unit part of a ≡ ±1 (mod 8)*--/
noncomputable def omega2 (a : ℚ_[2]ˣ) : ZMod 2 :=
  if unitPartZMod8 a = 1 ∨ unitPartZMod8 a = -1 then 0 else 1

/--*Lemma 4.3.7 : Finite check on (ℤ/8)ˣ that ω is additive (Serre III.1.2)*--/
lemma omega2_aux : ∀ u v : (ZMod 8)ˣ,
    (if u * v = 1 ∨ u * v = -1 then (0 : ZMod 2) else 1)
      = (if u = 1 ∨ u = -1 then (0 : ZMod 2) else 1)
        + (if v = 1 ∨ v = -1 then (0 : ZMod 2) else 1) := by
  decide

/--*Lemma 4.3.8 : ω is a homomorphism (ℚ_2ˣ, ·) → (ℤ/2, +)*--/
lemma omega2_mul (a b : ℚ_[2]ˣ) : omega2 (a * b) = omega2 a + omega2 b := by
  unfold omega2
  rw [unitPartZMod8_mul]
  exact omega2_aux (unitPartZMod8 a) (unitPartZMod8 b)

/--*Definition 4.3.5 : The sign map (ℤ/2, +) → ({±1}, ·), t ↦ (−1)^t*--/
def sgn : ZMod 2 → ℤˣ := fun t => if t = 0 then 1 else -1

/--*Lemma 4.3.9 : sgn is a homomorphism, sgn (s + t) = sgn s · sgn t (sanity check)*--/
lemma sgn_add : ∀ s t : ZMod 2, sgn (s + t) = sgn s * sgn t := by decide

/- # 4.4 THE EXPLICIT FORMULA FOR p = 2 AND ITS PROPERTIES -/

/--*Definition 4.4.1 : Explicit formula for the Hilbert symbol at p = 2 (Serre III.1.2, Thm 1)*--/
noncomputable def formulaTwo (a b : ℚ_[2]ˣ) : ℤˣ :=
  sgn (epsilon2 a * epsilon2 b + (valuationUnits a : ZMod 2) * omega2 b
    + (valuationUnits b : ZMod 2) * omega2 a)

/--*Lemma 4.4.1 : formulaTwo is symmetric*--/
lemma formulaTwo_comm (a b : ℚ_[2]ˣ) : formulaTwo a b = formulaTwo b a := by
  unfold formulaTwo
  congr 1
  ring

/--*Lemma 4.4.2 : formulaTwo is multiplicative in the first entry*--/
lemma formulaTwo_mul_left (a a' b : ℚ_[2]ˣ) :
    formulaTwo (a * a') b = formulaTwo a b * formulaTwo a' b := by
  unfold formulaTwo
  rw [← sgn_add]
  congr 1
  rw [epsilon2_mul, omega2_mul, valuationUnits_mul]
  grind

/--*Lemma 4.4.3 : formulaTwo is multiplicative in the second entry*--/
lemma formulaTwo_mul_right (a b b' : ℚ_[2]ˣ) :
    formulaTwo a (b * b') = formulaTwo a b * formulaTwo a b' := by
  grind only [formulaTwo_comm, formulaTwo_mul_left]

/--*Lemma 4.4.4 : formulaTwo is bimultiplicative*--/
lemma formulaTwo_isSqBimult : IsSqBimult formulaTwo := ⟨formulaTwo_mul_left, formulaTwo_mul_right⟩

/--*Lemma 4.4.5 : Square invariance of formulaTwo in the first entry*--/
lemma formulaTwo_mul_sq_left (a c b : ℚ_[2]ˣ) : formulaTwo (a * c ^ 2) b = formulaTwo a b :=
  formulaTwo_isSqBimult.mul_sq_left a b c

/--*Lemma 4.4.6 : Square invariance of formulaTwo in the second entry*--/
lemma formulaTwo_mul_sq_right (a b c : ℚ_[2]ˣ) : formulaTwo a (b * c ^ 2) = formulaTwo a b :=
  formulaTwo_isSqBimult.mul_sq_right a b c


/- # SECTION 5 : FINAL MACHINERY — RESIDUES, HENSEL'S LEMMA, PRIMITIVE SOLUTIONS -/
/-
**(1) What this section does :** This section bridges the gap between the Hilbert symbol
(solvability of `z² = ax² + by²` over `ℚ_p`) and the explicit formulae (finite residue
computations). We achieve this in :
1) The reduction map `ℤ_p → ℤ/p` (and `ℤ/pⁿ`) against divisibility and the norm → Section 5.1
2) Hensel's lemma for `X² − u` (Serre II.2.2, Thm 1) → Section 5.2
3) Its consequences — a unit is a square iff its residue is (`p ≠ 2`, Serre II.3.3 Thm 3) and
   `u ≡ 1 (mod 8)` implies `u` is a square (`p = 2`, Serre II.3.3 Thm 4) → Section 5.3
4) The units case `z² = ux² + vy²` for `p ≠ 2` (Serre III.1.2, case (i)) → Section 5.4
5) From a `ℚ_p`-solution to a primitive `ℤ_p`-solution and back → Section 5.5

**(2) Why we need it :** The formulas of Section 4 are residue computations while the actual
symbol is a statement about `ℚ_p`. Every `⟸` direction in Sections 6–7 builds a `ℚ_p`-solution
from the explicit formula, which needs Hensel's lemma. Every `⟹` direction reduces a supposed
solution mod `p` or mod `8`, which needs the primitive solution lemma of Section 5.5 and the
reduction map of Section 5.1.

**(3) Design discussion :** Serre takes a primitive solution in `ℤ_p` (not all coordinates
divisible by `p`). We instead divide a solution by its coordinate of largest norm, which then
becomes `1`.
-/

/- # 5.1 THE REDUCTION MAP AND THE NORM -/

/--*Lemma 5.1.1 : The kernel of the reduction map ℤ_p → ℤ/p is the ideal generated by p*--/
lemma toZMod_eq_zero_iff_dvd (x : ℤ_[p]) : PadicInt.toZMod x = 0 ↔ (p : ℤ_[p]) ∣ x := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p,
    Ideal.mem_span_singleton]

/--*Lemma 5.1.2 : A p-adic integer in the kernel of reduction has norm < 1*--/
lemma norm_lt_one_of_toZMod_eq_zero {x : ℤ_[p]} (h : PadicInt.toZMod x = 0) : ‖x‖ < 1 := by
  grind only [toZMod_eq_zero_iff_dvd, PadicInt.norm_lt_one_iff_dvd]

/--*Lemma 5.1.3 : A p-adic integer not in the kernel of reduction has norm 1*--/
lemma norm_eq_one_of_toZMod_ne_zero {x : ℤ_[p]} (h : PadicInt.toZMod x ≠ 0) : ‖x‖ = 1 := by
  rcases (PadicInt.norm_le_one x).lt_or_eq with hlt | heq
  · grind only [toZMod_eq_zero_iff_dvd, PadicInt.norm_lt_one_iff_dvd]
  · grind

/--*Lemma 5.1.4 : Units of ℤ_p have nonzero residue mod p*--/
lemma toZMod_units_ne_zero (u : ℤ_[p]ˣ) : PadicInt.toZMod (u : ℤ_[p]) ≠ 0 := by
  intro h
  apply PadicInt.zmodRepr_units_ne_zero u
  grind only [PadicInt.zmodRepr_eq_zero_iff_dvd, toZMod_eq_zero_iff_dvd]

/--*Lemma 5.1.5 : The reduction map mod p is surjective*--/
lemma exists_toZMod_eq (a : ZMod p) : ∃ b : ℤ_[p], PadicInt.toZMod b = a := ⟨a.val, by simp⟩

/--*Lemma 5.1.6 : Two p-adic integers have the same residue mod pⁿ iff pⁿ divides their difference*--/
lemma toZModPow_eq_iff_dvd (n : ℕ) (x y : ℤ_[p]) :
    PadicInt.toZModPow n x = PadicInt.toZModPow n y ↔ (p : ℤ_[p]) ^ n ∣ x - y := by
  rw [← sub_eq_zero, ← map_sub, ← RingHom.mem_ker, PadicInt.ker_toZModPow,
    Ideal.mem_span_singleton]

/--*Lemma 5.1.7 : For odd p, the residue of 2 in ℤ/p is nonzero*--/
lemma two_ne_zero_zmod_of_odd (hp : Odd p) : (2 : ZMod p) ≠ 0 := by
  have h : p ≠ 2 := by
    grind
  apply Ring.two_ne_zero
  grind only [= Nat.odd_iff, ringChar.eq]

/--*Lemma 5.1.8 : The reduction map mod pⁿ is surjective*--/
lemma exists_toZModPow_eq (n : ℕ) (c : ZMod (p ^ n)) :
    ∃ a : ℤ_[p], PadicInt.toZModPow n a = c := ⟨c.val, by simp⟩

/- # 5.2 HENSEL'S LEMMA FOR X² − u (Serre II.2.2, Thm 1) -/

--*Lemma 5.2.1 : Hensel's lemma for square roots — an approximate root of X² − u lifts*
lemma exists_sq_eq_of_norm_lt (u a : ℤ_[p]) (h : ‖a ^ 2 - u‖ < ‖2 * a‖ ^ 2) :
    ∃ z : ℤ_[p], z ^ 2 = u := by
  set F : Polynomial ℤ_[p] := Polynomial.X ^ 2 - Polynomial.C u with hF
  have hFa : Polynomial.aeval a F = a ^ 2 - u := by
    simp only [Polynomial.aeval_sub, Polynomial.coe_aeval_eq_eval, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.aeval_C, Algebra.algebraMap_self, RingHom.id_apply, hF]
  have hF'a : Polynomial.aeval a (Polynomial.derivative F) = 2 * a := by
    rw [hF, Polynomial.derivative_sub, Polynomial.derivative_C, sub_zero,
      Polynomial.derivative_X_sq]
    simp only [Polynomial.coe_aeval_eq_eval, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X]
  have hnorm : ‖(Polynomial.aeval a) F‖ < ‖(Polynomial.aeval a) (Polynomial.derivative F)‖ ^ 2 := by
    rw [hFa, hF'a]
    exact h
  obtain ⟨z, hz, _, _, _⟩ := hensels_lemma hnorm
  have hFz : Polynomial.aeval z F = z ^ 2 - u := by
    simp [hF]
  rw [hFz, sub_eq_zero] at hz
  exact ⟨z, hz⟩


/- # 5.3 SQUARES IN ℤ_p VIA RESIDUES (Serre II.3.3, Thms 3–4) -/


--*Lemma 5.3.1 : For odd p, a unit of ℤ_p is a square iff its residue mod p is a square*
lemma isSquare_iff_isSquare_toZMod (hp : Odd p) (u : ℤ_[p]ˣ) :
    IsSquare (u : ℤ_[p]) ↔ IsSquare (PadicInt.toZMod (u : ℤ_[p])) := by
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨PadicInt.toZMod s, ?_⟩
    rw [hs, map_mul]
  · rintro ⟨c, hc⟩
    obtain ⟨a, ha⟩ := exists_toZMod_eq c
    have hc0 : c ≠ 0 := by
      grind only [toZMod_units_ne_zero]
    have h1 : ‖a ^ 2 - (u : ℤ_[p])‖ < 1 := by
      apply norm_lt_one_of_toZMod_eq_zero
      grind only [= map_sub, = map_pow]
    have h2 : ‖2 * a‖ = 1 := by
      apply norm_eq_one_of_toZMod_ne_zero
      rw [map_mul, ha, map_ofNat PadicInt.toZMod 2]
      exact mul_ne_zero (two_ne_zero_zmod_of_odd hp) hc0
    have hnorm : ‖a ^ 2 - (u : ℤ_[p])‖ < ‖2 * a‖ ^ 2 := by
      simp only [one_pow, h2, h1]
    obtain ⟨z, hz⟩ := exists_sq_eq_of_norm_lt (u : ℤ_[p]ˣ) a hnorm
    grind only [IsSquare.sq]

--*Lemma 5.3.2 : For p = 2, u ∈ ℤ_2 with u ≡ 1 (mod 8) is a square (Serre II.3.3, Thm 4)*
lemma isSquare_of_toZModPow_three_eq_one {u : ℤ_[2]} (h : PadicInt.toZModPow 3 u = 1) :
    IsSquare u := by
  have h8 : ((2 : ℕ) : ℤ_[2]) ^ 3 ∣ u - 1 := by
    rw [← toZModPow_eq_iff_dvd, h, map_one]
  have hnorm : ‖u - 1‖ ≤ ((2 : ℕ) : ℝ) ^ (-((3 : ℕ) : ℤ)) := by
    rw [PadicInt.norm_le_pow_iff_mem_span_pow, Ideal.mem_span_singleton]
    exact h8
  have h2 : ‖(2 : ℤ_[2])‖ = (2 : ℝ)⁻¹ := by
    simpa using PadicInt.norm_p (p := 2)
  have hlt : ((2 : ℕ) : ℝ) ^ (-((3 : ℕ) : ℤ)) < (2 : ℝ)⁻¹ ^ 2 := by
    norm_num
  have hH : ‖(1 : ℤ_[2]) ^ 2 - u‖ < ‖2 * (1 : ℤ_[2])‖ ^ 2 := by
    rw [one_pow, ← neg_sub, norm_neg, mul_one, h2]
    exact lt_of_le_of_lt hnorm hlt
  obtain ⟨z, hz⟩ := exists_sq_eq_of_norm_lt u 1 hH
  refine ⟨z, ?_⟩
  rw [← hz, sq]


/- # 5.4 THE UNITS CASE FOR p ≠ 2 -/


--*Lemma 5.4.1 : For units u, v ∈ ℤ_pˣ, z² = ux² + vy² has a solution with z ≠ 0*
--*(Serre III.1.2, case (i), via II.2.2 Cor. 2 to Thm 1 and Chevalley–Warning)*
lemma exists_sol_of_units (hp : Odd p) (u v : ℤ_[p]ˣ) :
    ∃ z x y : ℤ_[p], z ≠ 0 ∧ z ^ 2 = (u : ℤ_[p]) * x ^ 2 + (v : ℤ_[p]) * y ^ 2 := by
  sorry


/- # 5.5 ℚ_p-SOLUTIONS AND PRIMITIVE ℤ_p-SOLUTIONS -/


--*Lemma 5.5.1 : Dividing a ℚ_p-solution by a coordinate t of largest norm gives a ℤ_p-solution*
lemma exists_padicInt_sol_of_norm_le {a b : ℤ_[p]} {z x y t : ℚ_[p]} (ht : t ≠ 0)
    (hz : ‖z‖ ≤ ‖t‖) (hx : ‖x‖ ≤ ‖t‖) (hy : ‖y‖ ≤ ‖t‖) (heq : z ^ 2 = a * x ^ 2 + b * y ^ 2) :
    ∃ u v w : ℤ_[p], (u : ℚ_[p]) = z / t ∧ (v : ℚ_[p]) = x / t ∧ (w : ℚ_[p]) = y / t ∧
      u ^ 2 = a * v ^ 2 + b * w ^ 2 := by
  have hdiv : ∀ {s : ℚ_[p]}, ‖s‖ ≤ ‖t‖ → ‖s / t‖ ≤ 1 := fun hs => by
    rw[norm_div]
    apply div_le_one_of_le₀ hs
    exact norm_nonneg t
  refine ⟨⟨z / t, hdiv hz⟩, ⟨x / t, hdiv hx⟩, ⟨y / t, hdiv hy⟩, rfl, rfl, rfl, ?_⟩
  apply Subtype.ext
  push_cast
  rw[div_pow, heq]
  grind

/--*Lemma 5.5.2 : In a finite set of norms of p-adic numbers, there exists a maximum*--/
lemma exists_max_norm (z x y : ℚ_[p]) : ∃ t : ℚ_[p],
    (t = z ∨ t = x ∨ t = y) ∧ ‖z‖ ≤ ‖t‖ ∧ ‖x‖ ≤ ‖t‖ ∧ ‖y‖ ≤ ‖t‖ := by
  classical
  have hne : ({z, x, y} : Finset ℚ_[p]).Nonempty := by simp
  obtain ⟨ t, ht, hmax ⟩ := Finset.exists_max_image {z, x, y} (fun s => ‖s‖) hne
  grind

/--*Lemma 5.5.3 : Any ℚ_p-solution gives a ℤ_p-solution with some coordinate equal to 1*
*(Serre III.1.2, proof of Thm 1)*--/
lemma exists_primitive_sol {a b : ℤ_[p]} (h : HilbertSolvable ℚ_[p] a b) :
    ∃ z x y : ℤ_[p], (z = 1 ∨ x = 1 ∨ y = 1) ∧ z ^ 2 = a * x ^ 2 + b * y ^ 2 := by sorry

--*Lemma 5.5.4 : A ℤ_p-solution with z ≠ 0 is a ℚ_p-solution*
lemma hilbertSolvable_of_padicInt_sol {a b z x y : ℤ_[p]} (hz : z ≠ 0)
    (h : z ^ 2 = a * x ^ 2 + b * y ^ 2) : HilbertSolvable ℚ_[p] a b := by
  refine ⟨z, x, y, ?_, ?_⟩
  simp only [ne_eq, PadicInt.coe_eq_zero, not_false_eq_true, true_or, hz]
  have h1 := congrArg (fun t : ℤ_[p] => (t : ℚ_[p])) h
  push_cast at h1
  exact h1

--*Lemma 5.5.5 : A solution of z² = ax² + by² is preserved by any ring homomorphism out of ℤ_p*
lemma map_sol {R : Type*} [CommRing R] (f : ℤ_[p] →+* R) {z x y a b : ℤ_[p]}
    (h : z ^ 2 = a * x ^ 2 + b * y ^ 2) :
    f z ^ 2 = f a * f x ^ 2 + f b * f y ^ 2 := by
  have h := congrArg f h
  grind


/- # SECTION 6 : THE EXPLICIT FORMULA FOR ODD p (Serre III.1.2, Thm 1, p ≠ 2) -/
/-
**(1) What this section does :** By Lemma 3.5.2 (`hilbertSym_eq_of_valuationUnits_cases`) it
suffices to compare `hilbertSym` and `formulaOdd` on the three configurations
`(v a, v b) ∈ {(0,0),(1,0),(1,1)}`. We first collect the ingredients:
1) the value of `formulaOdd` on each configuration → 6.1
2) `quadraticCharUnits p (unitPartZMod b) = ±1` read as "the residue of the unit part of b is /
   is not a square" → 6.2
3) the two geometric facts Serre's proof rests on: two units always give a solution, and
   `(p, v)` has no solution when the residue of `v` is a non-square (Definitions 2.1.1–2.1.2,
   Lemmas 2.2.1–2.2.2) → 6.3
and then run Serre's cases:
4) case (i) two units, the key case `(p, v)`, case (ii) `(1,0)` and case (iii) `(1,1)` → 6.4
5) the theorem `hilbertSym ℚ_[p] = formulaOdd` → 6.5

**(2) Why we need it :** With the ingredients in hand each case is a short assembly:
case (i) is "both sides are 1"; the key case `(p,v)` is the dichotomy on whether the residue of
`v` is a square (Hensel for yes, primitivity for no); case (ii) strips the unit from `a` by
Prop 2 (iii) (Lemma 2.4.3) and lands in the key case; case (iii) reduces to (ii) by Prop 2 (iv)
(Lemma 2.4.4), whose formula-side analogue is `formulaOdd a (−a) = 1` for `v a = 1`
(Lemma 6.1.3).
-/

/- # 6.1 VALUES OF formulaOdd ON THE THREE CONFIGURATIONS -/

--*Lemma 6.1.1 : formulaOdd a b = 1 when v a = v b = 0*
lemma formulaOdd_eq_one_of_valuationUnits_zero_zero {a b : ℚ_[p]ˣ} (ha : valuationUnits a = 0)
    (hb : valuationUnits b = 0) : formulaOdd a b = 1 := by
  simp [formulaOdd, ha, hb]

--*Lemma 6.1.2 : formulaOdd (p, a) is the Legendre symbol of a when v a = 0 (Serre case (ii))*
lemma formulaOdd_uniformiser_of_valuationUnits_eq_zero {a : ℚ_[p]ˣ} (ha : valuationUnits a = 0) :
    formulaOdd (uniformiser p) a = quadraticCharUnits p (unitPartZMod a) := by
  simp [formulaOdd, valuationUnits_uniformiser, ha]

--*Lemma 6.1.3 : formulaOdd a (−a) = 1 when v a = 1 (formula-side Prop 2 (ii))*
lemma formulaOdd_neg_self_of_valuationUnits_eq_one {a : ℚ_[p]ˣ} (ha : valuationUnits a = 1) :
    formulaOdd a (-a) = 1 := by
  have hnega : valuationUnits (-a) = 1 := by
    rw [valuationUnits_neg, ha]
  unfold formulaOdd
  rw [ha, hnega, unitPartZMod_neg, map_mul, unitPartZMod_neg_one]
  simp only [mul_one, uzpow_one] -- simp?
  have hleg : quadraticCharUnits p (-1)
      * (quadraticCharUnits p (-1) * quadraticCharUnits p (unitPartZMod a))
      * quadraticCharUnits p (unitPartZMod a)
      = (quadraticCharUnits p (-1) * quadraticCharUnits p (-1))
        * (quadraticCharUnits p (unitPartZMod a) * quadraticCharUnits p (unitPartZMod a)) := by
    grind
  simp only [Int.units_mul_self, mul_one, hleg]

--*Lemma 6.1.4 : formulaOdd a (−a b) = formulaOdd a b when v a = 1 (formula-side Prop 2 (iv))*
lemma formulaOdd_neg_self_mul_of_valuationUnits_eq_one {a : ℚ_[p]ˣ} (ha : valuationUnits a = 1)
    (b : ℚ_[p]ˣ) : formulaOdd a (-a * b) = formulaOdd a b := by
  rw [formulaOdd_mul_right, formulaOdd_neg_self_of_valuationUnits_eq_one ha, one_mul]

/- # 6.2 THE LEGENDRE SYMBOL OF THE UNIT PART -/

--*Lemma 6.2.1 : Legendre symbol of the unit part is 1 iff its residue mod p is a square*
lemma quadraticCharUnits_unitPartZMod_eq_one_iff (a : ℚ_[p]ˣ) :
    quadraticCharUnits p (unitPartZMod a) = 1 ↔ IsSquare (PadicInt.toZMod (unitPart a : ℤ_[p])) := by
  rw [quadraticCharUnits_eq_one_iff, coe_unitPartZMod]

--*Lemma 6.2.2 : Legendre symbol of the unit part is -1 iff its residue mod p is not a square*
lemma quadraticCharUnits_unitPartZMod_eq_neg_one_iff (a : ℚ_[p]ˣ) :
    quadraticCharUnits p (unitPartZMod a) = -1
      ↔ ¬ IsSquare (PadicInt.toZMod (unitPart a : ℤ_[p])) := by
  rw [quadraticCharUnits_eq_neg_one_iff, coe_unitPartZMod]

/- # 6.3 THE GEOMETRIC SIDE : TWO UNITS, AND (p, v) FOR A NON-RESIDUE v -/

--*Lemma 6.3.1 : The Hilbert symbol of two units equals 1 (Serre III.1.2, case (i))*
lemma hilbertSym_eq_one_of_valuationUnits_zero_zero (hp : Odd p) {a b : ℚ_[p]ˣ}
    (ha : valuationUnits a = 0) (hb : valuationUnits b = 0) : hilbertSym ℚ_[p] a b = 1 := by
  rw [hilbertSym_eq_one_iff]
  obtain ⟨z, x, y, hz, heq⟩ := exists_sol_of_units hp (unitPart a) (unitPart b)
  have h := hilbertSolvable_of_padicInt_sol hz heq
  rwa [coe_unitPart_of_valuationUnits_eq_zero ha, coe_unitPart_of_valuationUnits_eq_zero hb] at h

--*Lemma 6.3.2 : z² = p x² + w y² is not solvable when the residue of w is a non-square*
--*(Serre III.1.2, case (ii), the primitivity argument)*
lemma not_hilbertSolvable_p_of_not_isSquare {w : ℤ_[p]} (h : ¬ IsSquare (PadicInt.toZMod w)) :
    ¬ HilbertSolvable ℚ_[p] ((p : ℤ_[p]) : ℚ_[p]) w := by
  sorry

/- # 6.4 SERRE'S CASES FOR ODD p -/

--*Lemma 6.4.1 : Case (i) — two units, (v a, v b) = (0,0)*
lemma hilbertSym_eq_formulaOdd_of_valuationUnits_zero_zero (hp : Odd p) {a b : ℚ_[p]ˣ}
    (ha : valuationUnits a = 0) (hb : valuationUnits b = 0) :
    hilbertSym ℚ_[p] a b = formulaOdd a b := by
  rw [hilbertSym_eq_one_of_valuationUnits_zero_zero hp ha hb,
    formulaOdd_eq_one_of_valuationUnits_zero_zero ha hb]

--*Lemma 6.4.2 : The key case (p, v) — split on whether the residue of v is a square*
lemma hilbertSym_uniformiser_eq_formulaOdd (hp : Odd p) {a : ℚ_[p]ˣ} (ha : valuationUnits a = 0) :
    hilbertSym ℚ_[p] (uniformiser p) a = formulaOdd (uniformiser p) a := by
  rw [formulaOdd_uniformiser_of_valuationUnits_eq_zero ha]
  by_cases hsq : IsSquare (PadicInt.toZMod (unitPart a : ℤ_[p]))
  · -- the residue of v is a square, so the symbol is 1
    rw [(quadraticCharUnits_unitPartZMod_eq_one_iff a).mpr hsq, hilbertSym_eq_one_iff]
    obtain ⟨s, hs⟩ := (isSquare_iff_isSquare_toZMod hp (unitPart a)).mpr hsq
    refine ⟨(s : ℚ_[p]), 0, 1, Or.inr (Or.inr one_ne_zero), ?_⟩
    rw [← coe_unitPart_of_valuationUnits_eq_zero ha, hs]
    push_cast
    ring
  · rw [(quadraticCharUnits_unitPartZMod_eq_neg_one_iff a).mpr hsq, hilbertSym_eq_neg_one_iff,
      val_uniformiser, ← PadicInt.coe_natCast, ← coe_unitPart_of_valuationUnits_eq_zero ha]
    exact not_hilbertSolvable_p_of_not_isSquare hsq

--*Lemma 6.4.3 : Case (ii) — (v a, v b) = (1,0); a = u·p with u a unit, stripped by Prop 2 (iii)*
lemma hilbertSym_eq_formulaOdd_of_valuationUnits_one_zero (hp : Odd p) {a b : ℚ_[p]ˣ}
    (ha : valuationUnits a = 1) (hb : valuationUnits b = 0) :
    hilbertSym ℚ_[p] a b = formulaOdd a b := by
  have h : valuationUnits ((uniformiser p)⁻¹ * a) = 0 := by
    rw [valuationUnits_mul, valuationUnits_inv, valuationUnits_uniformiser, ha]
    norm_num
  have hdecomp : (uniformiser p)⁻¹ * a * uniformiser p = a := by
    simp only [inv_mul_cancel_comm]
  rw [← hdecomp,
    hilbertSym_mul_left_of_eq_one (h := hilbertSym_eq_one_of_valuationUnits_zero_zero hp h hb),
    formulaOdd_mul_left, formulaOdd_eq_one_of_valuationUnits_zero_zero h hb, one_mul]
  exact hilbertSym_uniformiser_eq_formulaOdd hp hb

--*Lemma 6.4.4 : Case (iii) — (v a, v b) = (1,1); (a,b) = (a,−ab) by Prop 2 (iv), −ab = c·p²*
lemma hilbertSym_eq_formulaOdd_of_valuationUnits_one_one (hp : Odd p) {a b : ℚ_[p]ˣ}
    (ha : valuationUnits a = 1) (hb : valuationUnits b = 1) :
    hilbertSym ℚ_[p] a b = formulaOdd a b := by
  have h : -a * b = (-(a * b) * (uniformiser p ^ 2)⁻¹) * uniformiser p ^ 2 := by
    rw [neg_mul, inv_mul_cancel_right]
  have hval : valuationUnits (-(a * b) * (uniformiser p ^ 2)⁻¹) = 0 := by
    rw [valuationUnits_mul, valuationUnits_neg, valuationUnits_mul, valuationUnits_inv,
      valuationUnits_pow, valuationUnits_uniformiser, ha, hb]
    norm_num
  rw [← hilbertSym_neg_self_mul, ← formulaOdd_neg_self_mul_of_valuationUnits_eq_one ha b, h,
    hilbertSym_mul_sq_right, formulaOdd_mul_sq_right]
  exact hilbertSym_eq_formulaOdd_of_valuationUnits_one_zero hp ha hval


/- # 6.5 THE EXPLICIT FORMULA FOR ODD p -/


--*Theorem 6.5.1 : hilbertSym = formulaOdd for odd p (Serre III.1.2, Thm 1, p ≠ 2)*
theorem hilbertSym_eq_formulaOdd (hp : Odd p) : hilbertSym ℚ_[p] = formulaOdd := by
  refine hilbertSym_eq_of_valuationUnits_cases formulaOdd formulaOdd_comm formulaOdd_mul_sq_left
    ?_ ?_ ?_
  · intro a b ha hb
    exact hilbertSym_eq_formulaOdd_of_valuationUnits_zero_zero hp ha hb
  · intro a b ha hb
    exact hilbertSym_eq_formulaOdd_of_valuationUnits_one_zero hp ha hb
  · intro a b ha hb
    exact hilbertSym_eq_formulaOdd_of_valuationUnits_one_one hp ha hb


/- # SECTION 7 : THE EXPLICIT FORMULA FOR p = 2 (Serre III.1.2, Thm 1, p = 2) -/
/-
**(1) What this section does :** At `p = 2` a unit is determined up to squares by its residue
in `(ℤ/8)ˣ = {1,3,5,7}`, which `formulaTwo` reads through `ε` (mod 4) and `ω` (mod 8).
Ingredients:
1) express `epsilon2`/`omega2` as functions `epsilonMod8`/`omegaMod8` of the residue mod 8 → 7.1
2) compute the residues of `−1` and prove `formulaTwo a (−a) = 1` for `v a = 1` (formula-side
   Prop 2 (ii)) → 7.2
3) convert residue data mod 8 into solutions and non-solutions → 7.3
4) state Serre's case table over `(ℤ/8)ˣ × (ℤ/8)ˣ` and let `decide` verify it → 7.4
then Serre's cases:
5) the three configurations `(0,0)`, `(1,0)`, `(1,1)` → 7.5
6) the theorem `hilbertSym ℚ_[2] = formulaTwo` → 7.6

**(2) Why we need it :** Serre's proof at `p = 2` is a table: for each residue pattern either an
explicit witness `≡ 1 (mod 8)` (a square by Lemma 5.3.2) or a congruence obstruction mod 4 or
mod 8. `epsilonMod8`/`omegaMod8` exist because `decide` needs a statement over a finite type;
`epsilon2`/`omega2` take a 2-adic unit and cannot appear in it. Once the table is checked, cases
(0,0) and (1,0) are assembly (the table already contains Serre's combination of `(2,v)` and
`(u,v)`), and case (1,1) reduces to (1,0) exactly as for odd p.
-/


/- # 7.1 ε AND ω AS FUNCTIONS OF THE RESIDUE MOD 8 -/


--*Definition 7.1.1 : ε as a function on (ℤ/8)ˣ*
def epsilonMod8 (r : (ZMod 8)ˣ) : ZMod 2 := if ((r : ZMod 8).cast : ZMod 4) = 1 then 0 else 1

--*Definition 7.1.2 : ω as a function on (ℤ/8)ˣ*
def omegaMod8 (r : (ZMod 8)ˣ) : ZMod 2 := if r = 1 ∨ r = -1 then 0 else 1

--*Lemma 7.1.1 : The residue mod 4 is 1 iff the reduction mod 4 of the residue mod 8 is 1*
lemma unitPartZMod4_eq_one_iff (a : ℚ_[2]ˣ) :
    unitPartZMod4 a = 1 ↔ ((unitPartZMod8 a : ZMod 8).cast : ZMod 4) = 1 := by
  rw [← Units.val_eq_one, coe_unitPartZMod4, coe_unitPartZMod8,
    PadicInt.cast_toZModPow 2 3 (by norm_num)]

--*Lemma 7.1.2 : ε of a 2-adic unit is ε of its residue mod 8*
lemma epsilon2_eq_epsilonMod8 (a : ℚ_[2]ˣ) : epsilon2 a = epsilonMod8 (unitPartZMod8 a) := by
  grind only [epsilonMod8, epsilon2, unitPartZMod4_eq_one_iff]

--*Lemma 7.1.3 : ω of a 2-adic unit is ω of its residue mod 8*
lemma omega2_eq_omegaMod8 (a : ℚ_[2]ˣ) : omega2 a = omegaMod8 (unitPartZMod8 a) := by
  rfl


/- # 7.2 THE RESIDUES OF -1 -/


--*Lemma 7.2.1 : The residue mod 4 of -1 is -1*
lemma unitPartZMod4_neg_one : unitPartZMod4 (-1 : ℚ_[2]ˣ) = -1 := by
  apply Units.ext
  simp [unitPartZMod4, unitPart_neg_one]

--*Lemma 7.2.2 : The residue mod 8 of -1 is -1*
lemma unitPartZMod8_neg_one : unitPartZMod8 (-1 : ℚ_[2]ˣ) = -1 := by
  apply Units.ext
  simp [unitPartZMod8, unitPart_neg_one]

--*Lemma 7.2.3 : ε(-1) = 1*
lemma epsilon2_neg_one : epsilon2 (-1 : ℚ_[2]ˣ) = 1 := by
  rw [epsilon2, unitPartZMod4_neg_one]
  decide

--*Lemma 7.2.4 : ω(-1) = 0*
lemma omega2_neg_one : omega2 (-1 : ℚ_[2]ˣ) = 0 := by
  rw [omega2, unitPartZMod8_neg_one]
  decide

--*Lemma 7.2.5 : formulaTwo a (−a) = 1 when v a = 1 (formula-side Prop 2 (ii))*
lemma formulaTwo_neg_self_of_valuationUnits_eq_one {a : ℚ_[2]ˣ} (ha : valuationUnits a = 1) :
    formulaTwo a (-a) = 1 := by
  have hnega : valuationUnits (-a) = 1 := by
    rw [valuationUnits_neg, ha]
  have he : epsilon2 (-a) = 1 + epsilon2 a := by
    rw [← neg_one_mul, epsilon2_mul, epsilon2_neg_one]
  have hw : omega2 (-a) = omega2 a := by
    rw [← neg_one_mul, omega2_mul, omega2_neg_one, zero_add]
  unfold formulaTwo
  rw [ha, hnega, he, hw]
  simp only [Int.cast_one, one_mul]
  have key : ∀ x y : ZMod 2, sgn (x * (1 + x) + y + y) = 1 := by decide
  exact key _ _

--*Lemma 7.2.6 : formulaTwo a (−a b) = formulaTwo a b when v a = 1 (formula-side Prop 2 (iv))*
lemma formulaTwo_neg_self_mul_of_valuationUnits_eq_one {a : ℚ_[2]ˣ} (ha : valuationUnits a = 1)
    (b : ℚ_[2]ˣ) : formulaTwo a (-a * b) = formulaTwo a b := by
  rw [formulaTwo_mul_right, formulaTwo_neg_self_of_valuationUnits_eq_one ha, one_mul]


/- # 7.3 FROM RESIDUES MOD 8 TO SOLUTIONS, AND BACK -/


--*Lemma 7.3.1 : If a x² + b y² ≡ 1 (mod 8) for some x, y ∈ ℤ_2 then it is a square, hence a solution*
lemma hilbertSolvable_of_toZModPow_three_eq_one {a b x y : ℤ_[2]}
    (h : PadicInt.toZModPow 3 (a * x ^ 2 + b * y ^ 2) = 1) : HilbertSolvable ℚ_[2] a b := by
  obtain ⟨z, hz⟩ := isSquare_of_toZModPow_three_eq_one h
  have hz0 : z ≠ 0 := by
    intro hz0
    grind
  have heq : z ^ 2 = a * x ^ 2 + b * y ^ 2 := by
    rw [sq]
    exact hz.symm
  exact hilbertSolvable_of_padicInt_sol hz0 heq

--*Lemma 7.3.2 : No primitive solution mod 8 means not Hilbert solvable*
lemma not_hilbertSolvable_of_forall_zmod8_ne {a b : ℤ_[2]} (h : ∀ z x y : ZMod 8,
    (z = 1 ∨ x = 1 ∨ y = 1) →
      z ^ 2 ≠ PadicInt.toZModPow 3 a * x ^ 2 + PadicInt.toZModPow 3 b * y ^ 2) :
    ¬ HilbertSolvable ℚ_[2] a b := by
  intro hsol
  obtain ⟨z, x, y, hprim, heq⟩ := exists_primitive_sol hsol
  refine h _ _ _ ?_ (map_sol (PadicInt.toZModPow 3) heq)
  rcases hprim with h1 | h1 | h1
  · left; rw [h1, map_one]
  · right; left; rw [h1, map_one]
  · right; right; rw [h1, map_one]

--*Lemma 7.3.3 : An element of valuation 1 is 2 × (its unit part)*
lemma eq_two_mul_unitPart_of_valuationUnits_eq_one {a : ℚ_[2]ˣ} (ha : valuationUnits a = 1) :
    (a : ℚ_[2]) = ((2 * (unitPart a : ℤ_[2]) : ℤ_[2]) : ℚ_[2]) := by
  have h := coe_unitPart_of_valuationUnits_eq_one ha
  rw [eq_div_iff (by norm_num)] at h
  push_cast
  rw [← h]
  push_cast
  ring_nf
  rfl


/- # 7.4 SERRE'S CASE TABLE -/


--*Lemma 7.4.1 : Two units, (u,v) = (−1)^{ε(u)ε(v)} (Serre III.1.2, case (i) at p = 2)*
--*sgn = 1 gives a residue solution with z ≡ 1; sgn = −1 gives no primitive residue solution*
lemma hilbertSolvable_table_zmod8_units : ∀ r s : (ZMod 8)ˣ,
    (sgn (epsilonMod8 r * epsilonMod8 s) = 1 →
      ∃ x y : ZMod 8, (r : ZMod 8) * x ^ 2 + (s : ZMod 8) * y ^ 2 = 1) ∧
    (sgn (epsilonMod8 r * epsilonMod8 s) = -1 →
      ∀ z x y : ZMod 8, (z = 1 ∨ x = 1 ∨ y = 1) →
        z ^ 2 ≠ (r : ZMod 8) * x ^ 2 + (s : ZMod 8) * y ^ 2) := by
  decide

--*Lemma 7.4.2 : (2u, v) = (−1)^{ε(u)ε(v) + ω(v)} (Serre III.1.2, case (ii) at p = 2)*
lemma hilbertSolvable_table_zmod8_two_mul : ∀ r s : (ZMod 8)ˣ,
    (sgn (epsilonMod8 r * epsilonMod8 s + omegaMod8 s) = 1 →
      ∃ x y : ZMod 8, 2 * (r : ZMod 8) * x ^ 2 + (s : ZMod 8) * y ^ 2 = 1) ∧
    (sgn (epsilonMod8 r * epsilonMod8 s + omegaMod8 s) = -1 →
      ∀ z x y : ZMod 8, (z = 1 ∨ x = 1 ∨ y = 1) →
        z ^ 2 ≠ 2 * (r : ZMod 8) * x ^ 2 + (s : ZMod 8) * y ^ 2) := by
  decide


/- # 7.5 SERRE'S CASES FOR p = 2 -/


--*Lemma 7.5.1 : Two units, (v a, v b) = (0,0)*
lemma hilbertSym_eq_formulaTwo_of_valuationUnits_zero_zero {a b : ℚ_[2]ˣ}
    (ha : valuationUnits a = 0) (hb : valuationUnits b = 0) :
    hilbertSym ℚ_[2] a b = formulaTwo a b := by
  have h : formulaTwo a b = sgn (epsilonMod8 (unitPartZMod8 a) * epsilonMod8 (unitPartZMod8 b)) := by
    simp [formulaTwo, epsilon2_eq_epsilonMod8, omega2_eq_omegaMod8, ha, hb]
  have h' : HilbertSolvable ℚ_[2] a b ↔
      HilbertSolvable ℚ_[2] (unitPart a : ℤ_[2]) (unitPart b : ℤ_[2]) := by
    rw [coe_unitPart_of_valuationUnits_eq_zero ha, coe_unitPart_of_valuationUnits_eq_zero hb]
  obtain ⟨h1, h2⟩ := hilbertSolvable_table_zmod8_units (unitPartZMod8 a) (unitPartZMod8 b)
  rw [h]
  rcases Int.units_eq_one_or (sgn (epsilonMod8 (unitPartZMod8 a) * epsilonMod8 (unitPartZMod8 b)))
    with hx | hy
  · rw [hx, hilbertSym_eq_one_iff, h']
    obtain ⟨x, y, hxy⟩ := h1 hx
    obtain ⟨u, hu⟩ := exists_toZModPow_eq (p := 2) 3 x
    obtain ⟨v, hv⟩ := exists_toZModPow_eq (p := 2) 3 y
    apply hilbertSolvable_of_toZModPow_three_eq_one (x := u) (y := v)
    simp only [map_add, map_mul, map_pow, hu, hv, ← coe_unitPartZMod8]
    exact hxy
  · rw [hy, hilbertSym_eq_neg_one_iff, h']
    apply not_hilbertSolvable_of_forall_zmod8_ne
    simp only [← coe_unitPartZMod8]
    exact h2 hy

--*Lemma 7.5.2 : (v a, v b) = (1,0); a = 2·(unit part), handled by table 7.4.2*
lemma hilbertSym_eq_formulaTwo_of_valuationUnits_one_zero {a b : ℚ_[2]ˣ}
    (ha : valuationUnits a = 1) (hb : valuationUnits b = 0) :
    hilbertSym ℚ_[2] a b = formulaTwo a b := by
  have h : formulaTwo a b = sgn (epsilonMod8 (unitPartZMod8 a) * epsilonMod8 (unitPartZMod8 b)
      + omegaMod8 (unitPartZMod8 b)) := by
    simp [formulaTwo, epsilon2_eq_epsilonMod8, omega2_eq_omegaMod8, ha, hb]
  have h' : HilbertSolvable ℚ_[2] a b ↔
      HilbertSolvable ℚ_[2] (2 * (unitPart a : ℤ_[2]) : ℤ_[2]) (unitPart b : ℤ_[2]) := by
    rw [← eq_two_mul_unitPart_of_valuationUnits_eq_one ha,
      coe_unitPart_of_valuationUnits_eq_zero hb]
  obtain ⟨h1, h2⟩ := hilbertSolvable_table_zmod8_two_mul (unitPartZMod8 a) (unitPartZMod8 b)
  rw [h]
  rcases Int.units_eq_one_or (sgn (epsilonMod8 (unitPartZMod8 a) * epsilonMod8 (unitPartZMod8 b)
      + omegaMod8 (unitPartZMod8 b))) with hx | hy
  · rw [hx, hilbertSym_eq_one_iff, h']
    obtain ⟨x, y, hxy⟩ := h1 hx
    obtain ⟨u, hu⟩ := exists_toZModPow_eq (p := 2) 3 x
    obtain ⟨v, hv⟩ := exists_toZModPow_eq (p := 2) 3 y
    apply hilbertSolvable_of_toZModPow_three_eq_one (x := u) (y := v)
    simp only [map_add, map_mul, map_pow, map_ofNat, hu, hv, ← coe_unitPartZMod8]
    exact hxy
  · rw [hy, hilbertSym_eq_neg_one_iff, h']
    apply not_hilbertSolvable_of_forall_zmod8_ne
    simp only [map_mul, map_ofNat, ← coe_unitPartZMod8]
    exact h2 hy

--*Lemma 7.5.3 : (v a, v b) = (1,1); (a,b) = (a,−ab) by Prop 2 (iv), −ab = c·2² with c a unit*
lemma hilbertSym_eq_formulaTwo_of_valuationUnits_one_one {a b : ℚ_[2]ˣ}
    (ha : valuationUnits a = 1) (hb : valuationUnits b = 1) :
    hilbertSym ℚ_[2] a b = formulaTwo a b := by
  have h : -a * b = (-(a * b) * (uniformiser 2 ^ 2)⁻¹) * uniformiser 2 ^ 2 := by
    simp only [neg_mul, inv_mul_cancel_right]
  have hval : valuationUnits (-(a * b) * (uniformiser 2 ^ 2)⁻¹) = 0 := by
    rw [valuationUnits_mul, valuationUnits_neg, valuationUnits_mul, valuationUnits_inv,
      valuationUnits_pow, valuationUnits_uniformiser, ha, hb]
    norm_num
  rw [← hilbertSym_neg_self_mul (a := a) (b := b),
    ← formulaTwo_neg_self_mul_of_valuationUnits_eq_one ha b, h,
    hilbertSym_mul_sq_right, formulaTwo_mul_sq_right]
  exact hilbertSym_eq_formulaTwo_of_valuationUnits_one_zero ha hval


/- # 7.6 THE EXPLICIT FORMULA FOR p = 2 -/


--*Theorem 7.6.1 : hilbertSym = formulaTwo (Serre III.1.2, Thm 1, p = 2)*
theorem hilbertSym_eq_formulaTwo : hilbertSym ℚ_[2] = formulaTwo := by
  refine hilbertSym_eq_of_valuationUnits_cases formulaTwo formulaTwo_comm formulaTwo_mul_sq_left
    ?_ ?_ ?_
  · intro a b ha hb
    exact hilbertSym_eq_formulaTwo_of_valuationUnits_zero_zero ha hb
  · intro a b ha hb
    exact hilbertSym_eq_formulaTwo_of_valuationUnits_one_zero ha hb
  · intro a b ha hb
    exact hilbertSym_eq_formulaTwo_of_valuationUnits_one_one ha hb


/- # SECTION 8 : BILINEARITY OF THE HILBERT SYMBOL (Serre III.1.2, Thm 2) -/
/-
**(1) What this section does :** It combines Theorems 6.5.1 and 7.6.1: for every prime `p`
the Hilbert symbol agrees with its explicit formula, and the formulas are bimultiplicative
(Lemmas 4.2.4, 4.4.4).
1) `hilbertSym ℚ_[p]` is bimultiplicative → Section 8.1
2) The bilinear pairing `ℚ_pˣ/(ℚ_pˣ)² × ℚ_pˣ/(ℚ_pˣ)² → {±1}` → Section 8.2

**(2) Why we need it :** This is the goal of the file. Serre states Thm 2 as "the Hilbert symbol
is a nondegenerate bilinear form on the 𝔽₂-vector space `kˣ/kˣ²`"; bilinearity is exactly
`hilbertSym_isSqBimult`, while `hilbertPairing` is the bilinear form itself (see Section 1 for
why this monoid homomorphism is the right formalisation of an 𝔽₂-bilinear form). Bilinearity
cannot be proved at the level of a general field (it fails over `ℚ`), which is why it is deduced
from the local formulas rather than from the definition.
-/


/- # 8.1 BIMULTIPLICATIVITY OF THE HILBERT SYMBOL AT THE p-ADIC PLACE -/
/-
We combine Lemmas 4.2.4 and 4.4.4 (bimultiplicativity of the explicit formulas for odd p and
p = 2) with Theorems 6.5.1 and 7.6.1 (equality of the Hilbert symbol with its explicit formula
for odd p and p = 2).
-/


--*Theorem 8.1.1 : The Hilbert symbol on ℚ_p is bimultiplicative (Serre III.1.2, Thm 2)*
theorem hilbertSym_isSqBimult : IsSqBimult (hilbertSym ℚ_[p]) := by
  rcases Nat.even_or_odd p with hp | hp
  · have hprime : Nat.Prime p := Fact.out
    rw [Nat.Prime.even_iff hprime] at hp
    subst hp
    rw [hilbertSym_eq_formulaTwo]
    exact formulaTwo_isSqBimult
  · rw [hilbertSym_eq_formulaOdd hp]
    exact formulaOdd_isSqBimult


/- # 8.2 THE HILBERT PAIRING ON THE SQUARE CLASS GROUP -/


--*Definition 8.2.1 : The Hilbert symbol as a bilinear pairing SqCl ℚ_p →* (SqCl ℚ_p →* ℤˣ)*
noncomputable def hilbertPairing : SqCl ℚ_[p] →* (SqCl ℚ_[p] →* ℤˣ) :=
  (hilbertSym_isSqBimult (p := p)).sqClHom

end Padic
