import Mathlib.Tactic
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib

namespace HilbertSymbol

/- DEFINING THE HILBERT SYMBOL-/
def HilbertSolvable (K : Type*) [Field K] (a b : K) : Prop :=
  ∃ z x y : K, (z ≠ 0 ∨ x ≠ 0 ∨ y ≠ 0) ∧ z ^ 2 = a * x ^ 2 + b * y ^ 2

noncomputable def hilbertSym
    (K : Type*) [Field K] (a b : Kˣ) : ℤˣ  := by
  classical
  exact if HilbertSolvable K a b then 1 else -1

lemma hilbertSym_solvable {K : Type*} [Field K] {a b : Kˣ}
(h : HilbertSolvable K a b) : hilbertSym K a b = 1 :=
  if_pos h

lemma hilbertSym_not_solvable {K : Type*} [Field K] {a b : Kˣ}
(h : ¬ HilbertSolvable K a b) : hilbertSym K a b = -1 :=
  if_neg h


/- PROPERTIES OF THE HILBERT SYMBOL -/
variable (K : Type*) [Field K] (a b : Kˣ)

-- Symmetry : (a,b)_p = (b,a)_p
lemma HilbertSym.symmetric: hilbertSym K a b = hilbertSym K b a := by
  have h : ∀ c d : K, HilbertSolvable K c d → HilbertSolvable K d c := by
    intro c d  ⟨z, x, y, hnt, heq⟩
    exact ⟨z, y, x, by grind, by grind⟩
  unfold hilbertSym
  by_cases hab : HilbertSolvable K a b
  · rw [if_pos hab, if_pos (h a b hab)]
  · rw [if_neg hab, if_neg (fun hba => hab (h b a hba))] --add the function to show that
    --proof by contra. we apply the lemma in reverse order since hab : HilbertSolvable K b a

-- (1, b)_p = 1 and (b, 1)_p = 1
lemma HilbertSym.one_left: hilbertSym K 1 b = 1 := by
  have h : HilbertSolvable K 1 b := by
    refine ⟨1, 1, 0, ?_, ?_⟩
    simp
    ring
  exact if_pos h

lemma hilbertSym.one_right: hilbertSym K b 1 = 1 := by
  have h : HilbertSolvable K b 1 := by
    refine ⟨1, 0, 1, ?_, ?_⟩
    simp
    ring
  exact if_pos h


-- (a,-a)_p = 1
lemma HilbertSym.neg : hilbertSym K a (-a) = 1 := by
  have h : HilbertSolvable K a (-a) := by
    refine ⟨0, 1, 1, ?_, ?_⟩
    simp
    ring
  exact if_pos h


-- (a, 1-a)_p = 1 for a ≠ 1
lemma HilbertSym.one_sub  (ha: a.val ≠ 1)  : hilbertSym K a ( Units.mk0 (1-a) (by grind))  = 1 := by
  have h : HilbertSolvable K a (1 - a) := by
    refine ⟨1, 1, 1, ?_, ?_⟩
    simp
    ring
  exact if_pos h


-- If a is a square in K then (a,b)_p = 1 for every b
lemma HilbertSym.isSquare (ha : IsSquare a) (b : Kˣ) :
hilbertSym K a b = 1 := by
  obtain ⟨c, rfl⟩ := ha
  have h : HilbertSolvable K (c * c) b := by
    refine ⟨c, 1, 0, ?_, ?_⟩
    simp
    ring
  exact if_pos h


-- (a, a)_p = (a, -1)_p
lemma HilbertSym.self [CharZero K]: hilbertSym K a a = hilbertSym K a (-1) := by
  have h : HilbertSolvable K a a ↔ HilbertSolvable K a (-1) := by
    constructor
    · rintro ⟨z, x, y, hnt, heq⟩
      refine ⟨a * x, z, a * y, by aesop, by grind⟩
    · rintro ⟨z, x, y, hnt, heq⟩
      refine ⟨a * x, z, y, by aesop, by grind⟩
  unfold hilbertSym
  by_cases hsolv : HilbertSolvable K a a
  · simp_all
  · simp_all

-- Square invariances
lemma hilbertSym.sq_left [CharZero K ] : hilbertSym K (a * c ^ 2) b = hilbertSym K a b := by sorry
  have hcom : ∀ u w d : K, d ≠ 0 → HilbertSolvable K u w → HilbertSolvable K (u * d ^ 2) w := by
    rintro u w d hd ⟨z, x, y, hnt, heq⟩
    refine ⟨z, d⁻¹ * x, y, by grind, by grind⟩
  have hsol : HilbertSolvable K (a * c ^ 2) b ↔ HilbertSolvable K a b := by
    refine ⟨fun h => ?_, hcom a b (c : K) c.ne_zero⟩
    have h2 := hcom (a * c ^ 2) b c⁻¹ (inv_ne_zero c.ne_zero) h
    have hcancel : a * c ^ 2 * (c⁻¹) ^ 2 = a := by
      simp only [inv_pow, mul_inv_cancel_right]
      rwa [hcancel] at h2
  grind only [hilbertSym2, hilbertSym]


lemma hilbertSym2.sq_right (v : Place) (a b : Completion v)
    {c : Completion v} (hc : c ≠ 0) :
    hilbertSym2 v a (b * c ^ 2) = hilbertSym2 v a b := by sorry
  rw [hilbertSym2.symmetric v a (b * c ^ 2), hilbertSym2.symmetric v a b]
  exact hilbertSym2.sq_left v b a hc
lemma hilbertSym2.sq_right (v : Place) (a b : Completion v)
    {c : Completion v} (hc : c ≠ 0) : hilbertSym2 v a (b * c ^ 2) = hilbertSym2 v a b := by
  rw [hilbertSym2.symmetric v a (b * c ^ 2), hilbertSym2.symmetric v a b]
  exact hilbertSym2.sq_left v b a hc
  sorry

/- Defining p-adic numbers from scratch -/
variable {p : ℕ} [Fact p.Prime ]

lemma Padic.norm (x : ℚ_[p]) (hx : x ≠ 0) : ‖x / (p : ℚ_[p]) ^ (Padic.valuation x)‖ = 1 := by
  have hpR : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  rw [norm_div, Padic.norm_eq_zpow_neg_valuation hx, norm_zpow, Padic.norm_p]
  rw [inv_zpow, ← zpow_neg]
  exact div_self (zpow_ne_zero _ hpR)

noncomputable def Padic.unit_coeff (x : ℚ_[p]) (hx : x ≠ 0) : (ℤ_[p])ˣ :=
  PadicInt.mkUnits (Padic.norm x hx)

/- x = u x p^(v_p(x)) -/
lemma Padic.unit_coeff_spec (x : ℚ_[p]) (hx : x ≠ 0) :
x = ((Padic.unit_coeff x hx : ℤ_[p]) : ℚ_[p]) * (p : ℚ_[p]) ^ (Padic.valuation x) := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have h1 : ((Padic.unit_coeff x hx : ℤ_[p]) : ℚ_[p]) = x / (p : ℚ_[p]) ^ (Padic.valuation x) := rfl
  rw [h1]
  field_simp

/- EXPLICIT FORMULAE FOR HILBERT SYMBOLS-/

-- CASE 1 : p odd
lemma hilbertSym_Padic_odd (a b : (ℚ_[p])ˣ) (hp : p ≠ 2) :
  hilbertSym ℚ_[p] a b = (-1) ^ ((Padic.valuation a.val * Padic.valuation b.val *  ((p-1) / 2)) % 2 ).toNat
   * (legendreSym p ( PadicInt.toZMod (Padic.unit_coeff (a.val) (by simp)).val ).val)^((Padic.valuation a.val) % 2).toNat *
     (legendreSym p ( PadicInt.toZMod (Padic.unit_coeff (b.val) (by simp)).val ).val)^(Padic.valuation b.val % 2).toNat := sorry
--Explain how you arrived at this, reasons for taking mod2, .toNat, .val etc etc.....

--CASE 2 : p = 2
lemma Padic.unit_coeff_2 (x : ℚ_[2]) (hx : x≠ 0) :
   Padic.valuation (((Padic.unit_coeff x hx) - 1 : ℚ_[2])/ 2 ) = 0  := by sorry

noncomputable def Padic.unitRes8 (a : ℚ_[2]) (ha : a ≠ 0) : ℤ :=
  ((PadicInt.toZModPow 3 ((Padic.unit_coeff a ha : ℤ_[2]))).val : ℤ)

lemma hilbertSym_Padic_two (a b : (ℚ_[2])ˣ) :
  hilbertSym ℚ_[2] a b = (-1) ^ ((((Padic.unitRes8 a.val a.ne_zero - 1) / 2) * ((Padic.unitRes8 b.val b.ne_zero - 1) / 2)
          + Padic.valuation a.val * ((Padic.unitRes8 b.val b.ne_zero ^ 2 - 1) / 8)
          + Padic.valuation b.val * ((Padic.unitRes8 a.val a.ne_zero ^ 2 - 1) / 8)) % 2).toNat := by sorry

-- CASE 3 : ℝ
lemma hilbertSym_real (a b : ℝˣ) :
    hilbertSym ℝ a b = if a.val < 0 ∧ b.val < 0 then -1 else 1 := by sorry

--Show that every rational modulo square classes can be written as a product of -1 or some prime p

--Define the explicit formula for hilbert symbol for v = p (odd/even) and v = ∞
-- Then show the special values used in the proof

/-
/- Square class groups -/
#synth Field (ZMod 2)
--MENTION U TAKE CHAR ZERO SINCE P-ADIC NUMBERS AND R BOTH HAVE CHAR 0
/- Bilinearity -/
def HilberSym2 [CharZero K] : Kˣ →* Kˣ →* ℤˣ where
  toFun := hilbertSym K

lemma HilbertSym.mul_left [CharZero K] (a b c : Kˣ) :
  hilbertSym K (a * b) c = hilbertSym K a c * hilbertSym K b c := by




lemma bilinearAt_right
(v : Place) (hbi : BilinearQ v) (a b b' : Completion v)
    (ha : a ≠ 0) (hb : b ≠ 0) (hb' : b' ≠ 0) :
    hilbertSym2 v a (b * b') = hilbertSym2 v a b * hilbertSym2 v a b' := by
  grind only [hilbertSym2.symmetric, BilinearQ.eq_def]



-/


/- SERRE HILBERT RECIPROCITY-/

/- Multiplicativity : Cleaning up the modulo parts-/

noncomputable def v (a : ℚ_[p]ˣ) : ℤ := Padic.valuation (a : ℚ_[p])

lemma v_mul (a b : ℚ_[p]ˣ) : v (a * b) = v a + v b := by
  unfold v
  simp only [Units.val_mul, ne_eq, Units.ne_zero, not_false_eq_true, Padic.valuation_mul]

noncomputable def unitPart (a : ℚ_[p]ˣ) : ℤ_[p]ˣ :=
  Padic.unit_coeff (a : ℚ_[p]) a.ne_zero

lemma unitPart_coeff (a : ℚ_[p]ˣ) :
    ((unitPart a : ℤ_[p]) : ℚ_[p]) = (a : ℚ_[p]) / (p : ℚ_[p]) ^ v a := by rfl

lemma unitPart_mul (a b : ℚ_[p]ˣ) : unitPart (a * b) = unitPart a * unitPart b := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out (p := p.Prime)).ne_zero
  apply Units.ext
  apply Subtype.ext
  push_cast
  rw [unitPart_coeff (a * b), unitPart_coeff a, unitPart_coeff b, v_mul,
      zpow_add₀ hp0, Units.val_mul, div_mul_div_comm]

lemma unitPart_one : unitPart (1 : ℚ_[p]ˣ) = 1 := by
  have h := unitPart_mul (1 : ℚ_[p]ˣ) 1
  rw [mul_one] at h
  exact right_eq_mul.mp h

noncomputable def resU (a : ℚ_[p]ˣ) : (ZMod p)ˣ :=
  Units.map (PadicInt.toZMod (p := p)).toMonoidHom (unitPart a)

lemma resU_mul (a b : ℚ_[p]ˣ) : resU (a * b) = resU a * resU b := by
  unfold resU
  rw [unitPart_mul, map_mul]

lemma resU_one : resU (1 : ℚ_[p]ˣ) = 1 := by
  unfold resU
  rw [unitPart_one, map_one]

lemma v_one : v (1 : ℚ_[p]ˣ) = 0 := Padic.valuation_one


/- ODD PRIME CASE -/

noncomputable def legU (p : ℕ) [Fact p.Prime] : (ZMod p)ˣ →* ℤˣ :=
  (quadraticChar (ZMod p)).toUnitHom

noncomputable def H_odd (a b : ℚ_[p]ˣ) : ℤˣ := legU p (-1) ^ (v a * v b) * legU p (resU b) ^ v a * legU p (resU a) ^ v b

lemma H_odd_mul_left (a a' b : ℚ_[p]ˣ) : H_odd (a * a') b = H_odd a b * H_odd a' b := by sorry

lemma H_odd_comm (a b : ℚ_[p]ˣ) : H_odd a b = H_odd b a := by
  unfold H_odd
  rw [mul_comm (v a) (v b)]
  ac_rfl

lemma H_odd_mul_right (a b b' : ℚ_[p]ˣ) :
    H_odd a (b * b') = H_odd a b * H_odd a b' := by
  rw [H_odd_comm, H_odd_mul_left, H_odd_comm b a, H_odd_comm b' a]

lemma H_odd_one_left (b : ℚ_[p]ˣ) : H_odd 1 b = 1 := by
  simp [H_odd, v_one, resU_one, map_one]

lemma H_odd_sq_left (a c b : ℚ_[p]ˣ) : H_odd (a * c ^ 2) b = H_odd a b := by
  rw [sq, ← mul_assoc, H_odd_mul_left, H_odd_mul_left]
  rw [mul_assoc, ← sq, Int.units_sq, mul_one]

lemma H_odd_sq_right (a b c : ℚ_[p]ˣ) : H_odd a (b * c ^ 2) = H_odd a b := by
  rw [H_odd_comm, H_odd_sq_left, H_odd_comm]

noncomputable def H_oddHom (b : ℚ_[p]ˣ) : ℚ_[p]ˣ →* ℤˣ where
  toFun a := H_odd a b
  map_one' := H_odd_one_left b
  map_mul' a a' := H_odd_mul_left a a' b

/- p = 2 CASE-/

noncomputable def res4 (a : ℚ_[2]ˣ) : (ZMod 4)ˣ :=
  Units.map (PadicInt.toZModPow 2).toMonoidHom (unitPart a)

noncomputable def res8 (a : ℚ_[2]ˣ) : (ZMod 8)ˣ :=
  Units.map (PadicInt.toZModPow 3).toMonoidHom (unitPart a)

lemma res4_mul (a b : ℚ_[2]ˣ) : res4 (a * b) = res4 a * res4 b := by
  unfold res4
  rw [unitPart_mul, map_mul]

lemma res8_mul (a b : ℚ_[2]ˣ) : res8 (a * b) = res8 a * res8 b := by
  unfold res8
  rw [unitPart_mul, map_mul]

/-- `ε(a) = 0 ↔ u_a ≡ 1 (mod 4)`. -/
noncomputable def eps2 (a : ℚ_[2]ˣ) : ZMod 2 := if res4 a = 1 then 0 else 1

/-- `ω(a) = 0 ↔ u_a ≡ ±1 (mod 8)`. -/
noncomputable def omg2 (a : ℚ_[2]ˣ) : ZMod 2 :=
  if res8 a = 1 ∨ res8 a = -1 then 0 else 1

/-- Serre III.1.2, Lemma (`ε` is a homomorphism) — as a finite check. -/
lemma eps2_aux : ∀ u v : (ZMod 4)ˣ,
    (if u * v = 1 then (0 : ZMod 2) else 1)
      = (if u = 1 then (0 : ZMod 2) else 1) + (if v = 1 then 0 else 1) := by
  decide

lemma eps2_mul (a b : ℚ_[2]ˣ) : eps2 (a * b) = eps2 a + eps2 b := by
  unfold eps2
  rw [res4_mul]
  exact eps2_aux (res4 a) (res4 b)

/-- Serre III.1.2, Lemma (`ω` is a homomorphism) — 16 cases, one `decide`. -/
lemma omg2_aux : ∀ u v : (ZMod 8)ˣ ,
  (if u * v = 1 ∨ u * v = -1 then (0 : ZMod 2) else 1)
  = (if u = 1 ∨ u = -1 then (0 : ZMod 2) else 1)
  + (if v = 1 ∨ v = -1 then (0 : ZMod 2) else 1) := by decide

lemma omg2_mul (a b : ℚ_[2]ˣ) : omg2 (a * b) = omg2 a + omg2 b := by
  unfold omg2
  rw [res8_mul]
  exact omg2_aux (res8 a) (res8 b)

/-- The isomorphism `ZMod 2 ≃ {±1}`, converting `+` to `*`. -/
def sgn : ZMod 2 → ℤˣ := fun t => if t = 0 then 1 else -1

lemma sgn_add : ∀ s t : ZMod 2, sgn (s + t) = sgn s * sgn t := by decide

noncomputable def H2 (a b : ℚ_[2]ˣ) : ℤˣ :=
  sgn (eps2 a * eps2 b + (v a : ZMod 2) * omg2 b + (v b : ZMod 2) * omg2 a)

lemma H2_comm (a b : ℚ_[2]ˣ) : H2 a b = H2 b a := by
  unfold H2
  congr 1
  ring

lemma H2_mul_left (a a' b : ℚ_[2]ˣ) : H2 (a * a') b = H2 a b * H2 a' b := by
  unfold H2
  rw [← sgn_add]
  congr 1
  rw [eps2_mul, omg2_mul, v_mul]
  grind

lemma H2_mul_right (a b b' : ℚ_[2]ˣ) : H2 a (b * b') = H2 a b * H2 a b' := by
  grind only [H2_comm, H2_mul_left]


lemma H2_one_left (b : ℚ_[2]ˣ) : H2 1 b = 1 := by
  have he : eps2 (1 : ℚ_[2]ˣ) = 0 := by simp [eps2, res4, unitPart_one]
  have ho : omg2 (1 : ℚ_[2]ˣ) = 0 := by simp [omg2, res8, unitPart_one]
  simp [H2, he, ho, v_one, sgn]

lemma H2_sq_left (a c b : ℚ_[2]ˣ) : H2 (a * c ^ 2) b = H2 a b := by
  rw [sq, ← mul_assoc, H2_mul_left, H2_mul_left, mul_assoc,
      Int.units_mul_self, mul_one]

lemma H2_sq_right (a b c : ℚ_[2]ˣ) : H2 a (b * c ^ 2) = H2 a b := by
  rw [H2_comm, H2_sq_left, H2_comm]

noncomputable def H2Hom (b : ℚ_[2]ˣ) : ℚ_[2]ˣ →* ℤˣ where
  toFun a := H2 a b
  map_one' := H2_one_left b
  map_mul' a a' := H2_mul_left a a' b










































end HilbertSymbol

 -- TALK ABUT HOW THE HILBERT SYMBOL WAS DEFINED
 -- HOW I went about the proof
 --talk about how I defined wrt to K, not a specific completion of Q, why it worked for a
 --general field and not specificslly Qp or R
