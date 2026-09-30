import MscDiss.HilbertSymbolandSquareClasses
import Mathlib.Tactic
import Mathlib.NumberTheory.Padics.RingHoms

/- # SECTION 3 : SOME p-ADIC MACHINERY -/
/-
**(1) What this section does and design discussion :** Every `a ∈ ℚ_pˣ` is uniquely expressed as
`a = p^{v(a)} · u` with `u ∈ ℤ_pˣ` (Serre II.1.2). This section packages that decomposition for the
explicit formula of Section 4, since most of these lemmas do not exist in Mathlib in this form.
We read off `a ∈ ℚ_pˣ` as :
1) The valuation `valuationUnits a : ℤ` → Section 3.1
2) The uniformiser `uniformiser p : ℚ_pˣ` → Section 3.2
3) The unit part `unitPart a : ℤ_pˣ` → Section 3.3
and finally its residue class mod `p`,
4) `unitPartZMod a : (ℤ/p)ˣ` → Section 3.4
Each subsection records multiplicativity and the values at `1` and `−1`.

**(2) Why we need it :** In Section 4 the explicit formulas `formulaOdd` and `formulaTwo` are
functions of `(valuationUnits a, unitPartZMod a)`. Defining these pieces individually gives a
cleaner way of computing the formula than working directly with Mathlib's `Padic.valuation` and
`PadicInt.toZMod`, which was messy and hard to track in the InfoView. The last subsection
formalises the first step of Serre's proof of Thm 1 (III.1.2): since the symbol depends only on
classes mod squares, it suffices to compare `hilbertSym` and a formula `F` on pairs with
valuations in `{0,1}`.
-/

namespace Padic

variable {p : ℕ} [Fact p.Prime]

/- # 3.1 THE p-ADIC VALUATION vₚ ON ℚ_pˣ -/

/--*Definition 3.1.1 : The p-adic valuation of a unit of ℚ_p, as an integer*--/
noncomputable def valuationUnits (a : ℚ_[p]ˣ) : ℤ := Padic.valuation (a : ℚ_[p])

/--*Lemma 3.1.1 : The valuation is a homomorphism ℚ_pˣ → ℤ*--/
lemma valuationUnits_mul (a b : ℚ_[p]ˣ) :
    valuationUnits (a * b) = valuationUnits a + valuationUnits b := by
  unfold valuationUnits
  simp only [Units.val_mul, ne_eq, Units.ne_zero, not_false_eq_true, Padic.valuation_mul]

/--*Lemma 3.1.2 : The valuation of 1 is 0*--/
lemma valuationUnits_one : valuationUnits (1 : ℚ_[p]ˣ) = 0 := Padic.valuation_one

/--*Lemma 3.1.3 : The valuation of an inverse*--/
lemma valuationUnits_inv (a : ℚ_[p]ˣ) : valuationUnits a⁻¹ = -valuationUnits a := by
  unfold valuationUnits
  simp only [Units.val_inv_eq_inv_val, Padic.valuation_inv]

/--*Lemma 3.1.4 : The valuation of a natural power*--/
lemma valuationUnits_pow (a : ℚ_[p]ˣ) (n : ℕ) : valuationUnits (a ^ n) = n * valuationUnits a := by
  unfold valuationUnits
  simp only [Units.val_pow_eq_pow_val, Padic.valuation_pow]

/--*Lemma 3.1.5 : The valuation of an integer power*--/
lemma valuationUnits_zpow (a : ℚ_[p]ˣ) (n : ℤ) :
    valuationUnits (a ^ n) = n * valuationUnits a := by
  unfold valuationUnits
  simp only [Units.val_zpow_eq_zpow_val, Padic.valuation_zpow]

/--*Lemma 3.1.6 : The valuation of -1 is 0*--/
lemma valuationUnits_neg_one : valuationUnits (-1 : ℚ_[p]ˣ) = 0 := by
  have h := valuationUnits_pow (-1 : ℚ_[p]ˣ) 2
  rw [neg_one_sq, valuationUnits_one] at h
  push_cast at h
  grind

/--*Lemma 3.1.7 : The valuation of an additive inverse*--/
lemma valuationUnits_neg (a : ℚ_[p]ˣ) : valuationUnits (-a) = valuationUnits a := by
  rw [← neg_one_mul, valuationUnits_mul, valuationUnits_neg_one, zero_add]

/- # 3.2 THE UNIFORMISER p IN ℚ_pˣ -/

/--*Definition 3.2.1 : The uniformiser p ∈ ℚ_pˣ*--/
noncomputable def uniformiser (p : ℕ) [Fact p.Prime] : ℚ_[p]ˣ :=
  Units.mk0 (p : ℚ_[p]) (Nat.cast_ne_zero.mpr (Fact.out (p := p.Prime)).ne_zero)

/--*Lemma 3.2.1 : The uniformiser viewed in ℚ_p is p (sanity check)*--/
lemma val_uniformiser : ((uniformiser p : ℚ_[p]ˣ) : ℚ_[p]) = p := by rfl

/--*Lemma 3.2.2 : The valuation of the uniformiser is 1*--/
lemma valuationUnits_uniformiser : valuationUnits (uniformiser p) = 1 := Padic.valuation_p


/- # 3.3 THE UNIT PART OF a = p^{v(a)} · u IN ℚ_pˣ -/

/--*Lemma 3.3.1 : x / p^{v(x)} has norm 1, hence is a unit of ℤ_p*--/
lemma norm_div_p_zpow_valuation (x : ℚ_[p]) (hx : x ≠ 0) :
    ‖x / (p : ℚ_[p]) ^ (Padic.valuation x)‖ = 1 := by
  simp only [norm_div, Padic.norm_p_zpow, zpow_neg, div_inv_eq_mul]
  simp [hx, Padic.norm_eq_zpow_neg_valuation, zpow_ne_zero, NeZero.ne]

/--*Definition 3.3.1 : The unit part u ∈ ℤ_pˣ of a ∈ ℚ_pˣ*--/
noncomputable def unitPart (a : ℚ_[p]ˣ) : ℤ_[p]ˣ :=
  PadicInt.mkUnits (norm_div_p_zpow_valuation (a : ℚ_[p]) a.ne_zero)

/--*Lemma 3.3.2 : The unit part viewed in ℚ_p is a / p^{v(a)} (sanity check)*--/
lemma coe_unitPart (a : ℚ_[p]ˣ) :
    ((unitPart a : ℤ_[p]) : ℚ_[p]) = (a : ℚ_[p]) / (p : ℚ_[p]) ^ valuationUnits a := rfl

/--*Lemma 3.3.3 : The unit part is multiplicative*--/
lemma unitPart_mul (a b : ℚ_[p]ˣ) : unitPart (a * b) = unitPart a * unitPart b := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out (p := p.Prime)).ne_zero
  apply Units.ext
  apply Subtype.ext
  push_cast
  rw [coe_unitPart (a * b), coe_unitPart a, coe_unitPart b, valuationUnits_mul, zpow_add₀ hp0,
    Units.val_mul, div_mul_div_comm]

/--*Lemma 3.3.4 : The unit part of 1 is 1*--/
lemma unitPart_one : unitPart (1 : ℚ_[p]ˣ) = 1 := by
  have h := unitPart_mul (1 : ℚ_[p]ˣ) 1
  rw [mul_one] at h
  exact right_eq_mul.mp h

/--*Lemma 3.3.5 : The unit part of -1 is -1*--/
lemma unitPart_neg_one : unitPart (-1 : ℚ_[p]ˣ) = -1 := by
  apply Units.ext
  apply Subtype.ext
  rw [coe_unitPart, valuationUnits_neg_one, zpow_zero, div_one]
  simp only [Units.val_neg, Units.val_one, PadicInt.coe_neg, PadicInt.coe_one]

/--*Lemma 3.3.6 : If v(a) = 0 then the unit part of a is a itself*--/
lemma coe_unitPart_of_valuationUnits_eq_zero {a : ℚ_[p]ˣ} (ha : valuationUnits a = 0) :
    ((unitPart a : ℤ_[p]) : ℚ_[p]) = (a : ℚ_[p]) := by
  rw [coe_unitPart, ha, zpow_zero, div_one]

/--*Lemma 3.3.7 : If v(a) = 1 then the unit part of a is a / p, i.e. a = p · unitPart a*--/
lemma coe_unitPart_of_valuationUnits_eq_one {a : ℚ_[p]ˣ} (ha : valuationUnits a = 1) :
    ((unitPart a : ℤ_[p]) : ℚ_[p]) = (a : ℚ_[p]) / p := by
  rw [coe_unitPart, ha, zpow_one]

/- # 3.4 THE RESIDUE MOD p OF THE UNIT PART IN (ℤ/p)ˣ -/

/--*Definition 3.4.1 : The residue mod p of the unit part of a ∈ ℚ_pˣ*--/
noncomputable def unitPartZMod (a : ℚ_[p]ˣ) : (ZMod p)ˣ :=
  Units.map (PadicInt.toZMod (p := p)).toMonoidHom (unitPart a)

/--*Lemma 3.4.1 : The residue viewed in ℤ/p is the reduction of the unit part (sanity check)*--/
lemma coe_unitPartZMod (a : ℚ_[p]ˣ) :
    ((unitPartZMod a : (ZMod p)ˣ) : ZMod p) = PadicInt.toZMod (unitPart a : ℤ_[p]) := rfl

/--*Lemma 3.4.2 : The residue of the unit part is multiplicative*--/
lemma unitPartZMod_mul (a b : ℚ_[p]ˣ) : unitPartZMod (a * b) = unitPartZMod a * unitPartZMod b := by
  unfold unitPartZMod
  rw [unitPart_mul, map_mul]

/--*Lemma 3.4.3 : The residue of the unit part of 1 is 1*--/
lemma unitPartZMod_one : unitPartZMod (1 : ℚ_[p]ˣ) = 1 := by
  unfold unitPartZMod
  rw [unitPart_one, map_one]

/--*Lemma 3.4.4 : The residue of the unit part of -1 is -1*--/
lemma unitPartZMod_neg_one : unitPartZMod (-1 : ℚ_[p]ˣ) = -1 := by
  apply Units.ext
  simp [unitPartZMod, unitPart_neg_one]

/--*Lemma 3.4.5 : The residue of the unit part of -a is unitPartZMod (-1) · unitPartZMod a*--/
lemma unitPartZMod_neg (a : ℚ_[p]ˣ) : unitPartZMod (-a) = unitPartZMod (-1) * unitPartZMod a := by
  rw [← unitPartZMod_mul, neg_one_mul]


/- # 3.5 REDUCTION TO VALUATIONS IN {0, 1} (Serre III.1.2) -/

/--*Lemma 3.5.1 : Every a ∈ ℚ_pˣ is (an element of valuation 0 or 1) × (a square)*--/
lemma exists_eq_mul_sq (a : ℚ_[p]ˣ) :
    ∃ b c : ℚ_[p]ˣ, a = b * c ^ 2 ∧ (valuationUnits b = 1 ∨ valuationUnits b = 0) := by
  obtain ⟨k, hk⟩ := Int.even_or_odd' (valuationUnits a)
  refine ⟨a * ((uniformiser p ^ k)⁻¹) ^ 2, uniformiser p ^ k, ?_, ?_⟩
  · rw [mul_assoc, ← mul_pow, inv_mul_cancel, one_pow, mul_one]
  · rw [valuationUnits_mul, sq, valuationUnits_mul, valuationUnits_inv, valuationUnits_zpow,
      valuationUnits_uniformiser]
    grind

/--*Lemma 3.5.2 : Reduction principle — a symmetric, square-invariant F that agrees with the*
*Hilbert symbol whenever (v a, v b) ∈ {(0,0), (1,0), (1,1)} agrees with it everywhere*--/
lemma hilbertSym_eq_of_valuationUnits_cases (F : ℚ_[p]ˣ → ℚ_[p]ˣ → ℤˣ)
    (hsymm : ∀ a b, F a b = F b a)
    (hsq : ∀ a c b, F (a * c ^ 2) b = F a b)
    (h00 : ∀ a b, valuationUnits a = 0 → valuationUnits b = 0 → hilbertSym ℚ_[p] a b = F a b)
    (h10 : ∀ a b, valuationUnits a = 1 → valuationUnits b = 0 → hilbertSym ℚ_[p] a b = F a b)
    (h11 : ∀ a b, valuationUnits a = 1 → valuationUnits b = 1 → hilbertSym ℚ_[p] a b = F a b) :
    hilbertSym ℚ_[p] = F := by
  have hsq' : ∀ a b c, F a (b * c ^ 2) = F a b :=
    fun a b c => (hsymm _ _).trans ((hsq _ _ _).trans (hsymm _ _))
  funext a b
  obtain ⟨a', c, rfl, ha⟩ := exists_eq_mul_sq a
  obtain ⟨b', d, rfl, hb⟩ := exists_eq_mul_sq b
  rw [hilbertSym_mul_sq_left, hilbertSym_mul_sq_right, hsq, hsq']
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · exact h11 a' b' ha hb
  · exact h10 a' b' ha hb
  · rw [hilbertSym_comm, hsymm]
    exact h10 b' a' hb ha
  · exact h00 a' b' ha hb
end Padic
