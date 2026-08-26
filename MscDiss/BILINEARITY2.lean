import Mathlib.Tactic
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib

/-
SECTION 1 : THE SQUARE CLASS GROUP
Construct k^×/(k^×)², show it is an 𝔽₂ vector space, and  show bimultiplicativity
-/

variable {K : Type*} [Field K]

/- # (1) the subgroup of squares and the quotient -/

/-SUBRGOUP OF SQUARES
powMonoidHom is a map sending c ↦ c^2 on Kˣ whose image we take as the group elements, from
prev costructions design choice is as follows : lean knows image of a monoid hom is a subgroup so
easier to construct the quotient-/
abbrev SqSubgroup (K : Type*) [Field K] : Subgroup Kˣ := (powMonoidHom 2 : Kˣ →* Kˣ).range

/- SQUARE CLASS GROUP
Taking the quotient, since Kˣ commutative no need to proven normality. def was used but lean insited
used abbrev (maybe add to the comments for design choice but not sure if relevent) -/
abbrev SqCl (K : Type*) [Field K] := Kˣ ⧸ SqSubgroup K

/- QUOTIENT RING HOMOM-/
def SqCl.mk : Kˣ →* SqCl K := QuotientGroup.mk' (SqSubgroup K)

--membership lemma
lemma sq_mem_SqSubgroup (c : Kˣ) : c ^ 2 ∈ SqSubgroup K := ⟨c, rfl⟩

/- # (2) the 𝔽₂ structure
Every element squares to 1 is an 𝔽₂-vector space since an abelian group of exponent 2
carries a ZMod 2-module structure -/

lemma SqCl.elem_squared_eq_one (x : SqCl K) : x ^ 2 = 1 := by
  induction x using QuotientGroup.induction_on with
  | H a =>
    have h : ((a : SqCl K)) ^ 2 = ((a ^ 2 : Kˣ) : SqCl K) := by simp
    rw [h]
    refine (QuotientGroup.eq_one_iff (a ^ 2)).mpr ?_ -- found using apply? followd by try?
    simp


def descendTo {M : Type*} [CommMonoid M] (f : Kˣ →* M) (hf : ∀ c : Kˣ, f (c ^ 2) = 1) :
    SqCl K →* M := by
  have h : ∀ x ∈ SqSubgroup K, f x = 1 := by
    rintro x ⟨c, rfl⟩
    simp_all
  exact QuotientGroup.lift (SqSubgroup K) f h

/- # (4) bimultiplicativity
Bimultiplicative on the square class group (i think would be enough to imply) 𝔽₂ bilinear -/

structure IsSqBimult (F : Kˣ → Kˣ → ℤˣ) : Prop where
  one_left   : ∀ b, F 1 b = 1
  one_right  : ∀ a, F a 1 = 1
  mul_left   : ∀ a a' b, F (a * a') b = F a b * F a' b
  mul_right  : ∀ a b b', F a (b * b') = F a b * F a b'
  sq_left    : ∀ a c b, F (a * c ^ 2) b = F a b
  sq_right   : ∀ a b c, F a (b * c ^ 2) = F a b


lemma IsSqBimult.sq_arg_left {F : Kˣ → Kˣ → ℤˣ} (h : IsSqBimult F) (c b : Kˣ) :
    F (c ^ 2) b = 1 := by
  (induction h ; simp_all)
lemma IsSqBimult.sq_arg_right {F : Kˣ → Kˣ → ℤˣ} (h : IsSqBimult F) (a c : Kˣ) :
    F a (c ^ 2) = 1 := by
  (induction h ; simp_all)


-- GOING OFF SERRE'S CONSTRUCTION
-- φ_a : Kˣ/(Kˣ)² → {±1}, φ_a(b) = (a,b)
def IsSqBimult.rightHom {F : Kˣ → Kˣ → ℤˣ} (h : IsSqBimult F) (a : Kˣ) : SqCl K →* ℤˣ :=
  descendTo
    { toFun := F a
      map_one' := h.one_right a
      map_mul' := h.mul_right a }
    (fun c => h.sq_arg_right a c)

-- the map a ↦ φ_a
def IsSqBimult.leftHom {F : Kˣ → Kˣ → ℤˣ} (h : IsSqBimult F) :
    Kˣ →* (SqCl K →* ℤˣ) where
  toFun a := h.rightHom a
  map_one' := by
    ext x
    (induction h ; solve_by_elim)
  map_mul' a a' := by
    ext x
    (induction h ; solve_by_elim)

/- # (5) combining all to get Kˣ × Kˣ → Kˣ × SqCl → SqCl × SqCl → {±1} -/

def IsSqBimult.combined {F : Kˣ → Kˣ → ℤˣ} (h : IsSqBimult F) : SqCl K →* (SqCl K →* ℤˣ) := by
  have h' : ∀ c : Kˣ, h.leftHom (c ^ 2) = 1 := by
    intro c
    ext x
    simp
  exact descendTo h.leftHom h'
 --- explain why sqCla Kx x sqCl Kx → [ZMOD2] sqCl Kx → [Zmod2] Zx wont work bc of additivity
 -- TRY DEFINING AS ONE MAP INSETAD OF FIXING ONE ENTRY LIKE SERRE'S
-- verifcation
lemma IsSqBimult.pairing_mk_mk {F : Kˣ → Kˣ → ℤˣ} (h : IsSqBimult F) (a b : Kˣ) :
h.combined (SqCl.mk a) (SqCl.mk b) = F a b := rfl


/- SECTION 2 : THE GEOMETRIC HILBERT SYMBOL AND ITS PROPERTIES
COPY PASTED -/

/- # (1) definition of geometric hilbert symbol-/

def HilbertSolvable (K : Type*) [Field K] (a b : K) : Prop :=
  ∃ z x y : K, (z ≠ 0 ∨ x ≠ 0 ∨ y ≠ 0) ∧ z ^ 2 = a * x ^ 2 + b * y ^ 2

noncomputable def hilbertSym (K : Type*) [Field K] (a b : Kˣ) : ℤˣ := by
  classical
  exact if HilbertSolvable K a b then 1 else -1

/- # (2) properties of the hilbert symbol -/

variable (K : Type*) [Field K] (a b : Kˣ)

-- (a,b) = (b,a)
lemma HilbertSym.symmetric : hilbertSym K a b = hilbertSym K b a := by
  have h : ∀ c d : K, HilbertSolvable K c d → HilbertSolvable K d c := by
    intro c d ⟨z, x, y, hnt, heq⟩
    exact ⟨z, y, x, by grind, by grind⟩
  unfold hilbertSym
  by_cases hab : HilbertSolvable K a b
  · rw [if_pos hab, if_pos (h a b hab)]
  · rw [if_neg hab, if_neg (fun hba => hab (h b a hba))]

-- (1,b) = 1 and (b,1) = 1
lemma HilbertSym.one_left : hilbertSym K 1 b = 1 := by
  have h : HilbertSolvable K 1 b := by
    refine ⟨1, 1, 0, ?_, ?_⟩
    simp
    ring
  exact if_pos h

lemma hilbertSym.one_right : hilbertSym K b 1 = 1 := by
  have h : HilbertSolvable K b 1 := by
    refine ⟨1, 0, 1, ?_, ?_⟩
    simp
    ring
  exact if_pos h

-- (a,-a) = 1
lemma HilbertSym.neg : hilbertSym K a (-a) = 1 := by
  have h : HilbertSolvable K a (-a) := by
    refine ⟨0, 1, 1, ?_, ?_⟩
    simp
    ring
  exact if_pos h

-- (a,1-a) = 1 for a ≠ 1
lemma HilbertSym.one_sub (ha : a.val ≠ 1) : hilbertSym K a (Units.mk0 (1 - a) (by grind)) = 1 := by
  have h : HilbertSolvable K a (1 - a) := by
    refine ⟨1, 1, 1, ?_, ?_⟩
    simp
    ring
  exact if_pos h

-- a a square ⇒ (a,b) = 1
lemma HilbertSym.isSquare (ha : IsSquare a) (b : Kˣ) : hilbertSym K a b = 1 := by
  obtain ⟨c, rfl⟩ := ha
  have h : HilbertSolvable K (c * c) b := by
    refine ⟨c, 1, 0, ?_, ?_⟩
    simp
    ring
  exact if_pos h

-- (a,a) = (a,-1)
lemma HilbertSym.self : hilbertSym K a a = hilbertSym K a (-1) := by
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

/- # (3) square invariance -/

lemma hilbertSolvable_mul_sq_left {K : Type*} [Field K] (a c b : Kˣ) :
    HilbertSolvable K ((a * c ^ 2 : Kˣ) : K) (b : K)
      ↔ HilbertSolvable K (a : K) (b : K) := by sorry

lemma hilbertSym_sq_left {K : Type*} [Field K] (a c b : Kˣ) : hilbertSym K (a * c ^ 2) b = hilbertSym K a b := by
  unfold hilbertSym
  by_cases hs : HilbertSolvable K ((a * c ^ 2 : Kˣ) : K) (b : K)
  · rw [if_pos hs, if_pos ((hilbertSolvable_mul_sq_left a c b).mp hs)]
  · rw [if_neg hs, if_neg (fun hc => hs ((hilbertSolvable_mul_sq_left a c b).mpr hc))]

lemma hilbertSym_sq_right {K : Type*} [Field K] (a b c : Kˣ) : hilbertSym K a (b * c ^ 2) = hilbertSym K a b := by
  rw [HilbertSym.symmetric, hilbertSym_sq_left, HilbertSym.symmetric]


/- SECTION 3 : units and padic machinery needed in the explicit formula for hilbert symbol -/

variable {p : ℕ} [Fact p.Prime]

lemma Padic.norm (x : ℚ_[p]) (hx : x ≠ 0) : ‖x / (p : ℚ_[p]) ^ (Padic.valuation x)‖ = 1 := by
  simp only [norm_div, norm_p_zpow, zpow_neg, div_inv_eq_mul]
  simp [hx, Padic.norm_eq_zpow_neg_valuation, zpow_ne_zero, NeZero.ne]

noncomputable def Padic.unit_coeff (x : ℚ_[p]) (hx : x ≠ 0) : (ℤ_[p])ˣ :=
  PadicInt.mkUnits (Padic.norm x hx)

noncomputable def v (a : ℚ_[p]ˣ) : ℤ := Padic.valuation (a : ℚ_[p])

lemma v_mul (a b : ℚ_[p]ˣ) : v (a * b) = v a + v b := by
  unfold v
  simp only [Units.val_mul, ne_eq, Units.ne_zero, not_false_eq_true, Padic.valuation_mul]

lemma v_one : v (1 : ℚ_[p]ˣ) = 0 := Padic.valuation_one

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


/- SECTION 4 : THE HILBERT SYMBOL AS QUADRATIC CHARACTERS -/

lemma sq_left_of_mul_left {K : Type*} [Field K] {F : Kˣ → Kˣ → ℤˣ}
    (hml : ∀ a a' b, F (a * a') b = F a b * F a' b) (a c b : Kˣ) :
    F (a * c ^ 2) b = F a b := by
  rw [sq, ← mul_assoc, hml, hml, mul_assoc, ← sq, Int.units_sq, mul_one]

/- # (1) the quadratic character -/

noncomputable def legU (p : ℕ) [Fact p.Prime] : (ZMod p)ˣ →* ℤˣ :=
  (quadraticChar (ZMod p)).toUnitHom

/- # (2) odd p -/

noncomputable def H_odd (a b : ℚ_[p]ˣ) : ℤˣ :=
  legU p (-1) ^ (v a * v b) * legU p (resU b) ^ v a * legU p (resU a) ^ v b

/- # (3) p = 2 -/

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

-- ε(a) = 0 ↔ u_a ≡ 1 (mod 4)
noncomputable def eps2 (a : ℚ_[2]ˣ) : ZMod 2 := if res4 a = 1 then 0 else 1

-- ω(a) = 0 ↔ u_a ≡ ±1 (mod 8)
noncomputable def omg2 (a : ℚ_[2]ˣ) : ZMod 2 :=
  if res8 a = 1 ∨ res8 a = -1 then 0 else 1

-- Serre III.1.2, Lemma: ε and ω are homomorphisms — finite checks
lemma eps2_hom : ∀ u v : (ZMod 4)ˣ,
    (if u * v = 1 then (0 : ZMod 2) else 1)
      = (if u = 1 then (0 : ZMod 2) else 1) + (if v = 1 then 0 else 1) := by decide

lemma eps2_mul (a b : ℚ_[2]ˣ) : eps2 (a * b) = eps2 a + eps2 b := by
  unfold eps2
  rw [res4_mul]
  exact eps2_hom (res4 a) (res4 b)

lemma omg2_hom : ∀ u v : (ZMod 8)ˣ,
    (if u * v = 1 ∨ u * v = -1 then (0 : ZMod 2) else 1)
      = (if u = 1 ∨ u = -1 then (0 : ZMod 2) else 1)
      + (if v = 1 ∨ v = -1 then (0 : ZMod 2) else 1) := by decide

lemma omg2_mul (a b : ℚ_[2]ˣ) : omg2 (a * b) = omg2 a + omg2 b := by
  unfold omg2
  rw [res8_mul]
  exact omg2_hom (res8 a) (res8 b)

-- ZMod 2 ≃ {±1}, converting + to ×
def sgn : ZMod 2 → ℤˣ := fun t => if t = 0 then 1 else -1
lemma sgn_add_to_mul : ∀ s t : ZMod 2, sgn (s + t) = sgn s * sgn t := by decide

noncomputable def H2 (a b : ℚ_[2]ˣ) : ℤˣ :=
  sgn (eps2 a * eps2 b + (v a : ZMod 2) * omg2 b + (v b : ZMod 2) * omg2 a)

/- # (4) properties, odd p -/

lemma H_odd_comm (a b : ℚ_[p]ˣ) : H_odd a b = H_odd b a := by
  unfold H_odd
  rw [mul_comm (v a) (v b)]
  ac_rfl

lemma H_odd_mul_left (a a' b : ℚ_[p]ˣ) :
    H_odd (a * a') b = H_odd a b * H_odd a' b := by sorry

lemma H_odd_mul_right (a b b' : ℚ_[p]ˣ) :
    H_odd a (b * b') = H_odd a b * H_odd a b' := by
  rw [H_odd_comm, H_odd_mul_left, H_odd_comm b a, H_odd_comm b' a]

lemma H_odd_one_left (b : ℚ_[p]ˣ) : H_odd 1 b = 1 := by
  simp [H_odd, v_one, resU_one, map_one]
lemma H_odd_one_right (a : ℚ_[p]ˣ) : H_odd a 1 = 1 := by
  rw [H_odd_comm]; exact H_odd_one_left a

lemma H_odd_sq_left (a c b : ℚ_[p]ˣ) : H_odd (a * c ^ 2) b = H_odd a b :=
  sq_left_of_mul_left H_odd_mul_left a c b
lemma H_odd_sq_right (a b c : ℚ_[p]ˣ) : H_odd a (b * c ^ 2) = H_odd a b := by
  rw [H_odd_comm, H_odd_sq_left, H_odd_comm]

/- # (5) properties, p = 2 -/

lemma H2_comm (a b : ℚ_[2]ˣ) : H2 a b = H2 b a := by
  unfold H2
  congr 1
  ring

lemma H2_mul_left (a a' b : ℚ_[2]ˣ) : H2 (a * a') b = H2 a b * H2 a' b := by
  unfold H2
  rw [← sgn_add_to_mul]
  congr 1
  rw [eps2_mul, omg2_mul, v_mul]
  grind

lemma H2_mul_right (a b b' : ℚ_[2]ˣ) : H2 a (b * b') = H2 a b * H2 a b' := by
  grind only [H2_comm, H2_mul_left]

lemma H2_one_left (b : ℚ_[2]ˣ) : H2 1 b = 1 := by
  have he : eps2 (1 : ℚ_[2]ˣ) = 0 := by simp [eps2, res4, unitPart_one]
  have ho : omg2 (1 : ℚ_[2]ˣ) = 0 := by simp [omg2, res8, unitPart_one]
  simp [H2, he, ho, v_one, sgn]
lemma H2_one_right (a : ℚ_[2]ˣ) : H2 a 1 = 1 := by
  rw [H2_comm]; exact H2_one_left a

lemma H2_sq_left (a c b : ℚ_[2]ˣ) : H2 (a * c ^ 2) b = H2 a b :=
  sq_left_of_mul_left H2_mul_left a c b
lemma H2_sq_right (a b c : ℚ_[2]ˣ) : H2 a (b * c ^ 2) = H2 a b := by
  rw [H2_comm, H2_sq_left, H2_comm]

/- # (6) bimultiplicativity, and the pairing on square classes -/

lemma H_odd_isSqBimult : IsSqBimult (H_odd (p := p)) where
  one_left  := H_odd_one_left
  one_right := H_odd_one_right
  mul_left  := H_odd_mul_left
  mul_right := H_odd_mul_right
  sq_left   := H_odd_sq_left
  sq_right  := H_odd_sq_right

lemma H2_isSqBimult : IsSqBimult H2 where
  one_left  := H2_one_left
  one_right := H2_one_right
  mul_left  := H2_mul_left
  mul_right := H2_mul_right
  sq_left   := H2_sq_left
  sq_right  := H2_sq_right

-- as maps ℚ_p^×/(ℚ_p^×)² →* ℚ_p^×/(ℚ_p^×)² →* ℤˣ
noncomputable def H_oddCombined (p : ℕ) [Fact p.Prime] :
    SqCl ℚ_[p] →* (SqCl ℚ_[p] →* ℤˣ) := (H_odd_isSqBimult (p := p)).combined

noncomputable def H2Combined :
    SqCl ℚ_[2] →* (SqCl ℚ_[2] →* ℤˣ) := H2_isSqBimult.combined

-- on representatives they are the original symbols
lemma H_oddcombined_mk_mk (a b : ℚ_[p]ˣ) :
    H_oddCombined p (SqCl.mk a) (SqCl.mk b) = H_odd a b := rfl

lemma H2combined_mk_mk (a b : ℚ_[2]ˣ) :
    H2Combined (SqCl.mk a) (SqCl.mk b) = H2 a b := rfl

/- EQUATING THE TWO -/
theorem hilbertSym_eq_odd (hp : Odd p ) : hilbertSym ℚ_[p] = H_odd :=  by sorry
theorem hilbertSym_eq_2 : hilbertSym ℚ_[2] = H2 := by sorry

theorem hilbertSym_bimult : IsSqBimult (hilbertSym ℚ_[p]) := by
  rcases Nat.even_or_odd p with ( hp | hp' )
  · have hev : Nat.Prime p := by exact Fact.out
    rw[Nat.Prime.even_iff hev ] at hp
    subst hp
    rw[hilbertSym_eq_2]
    exact H2_isSqBimult
  · rw [hilbertSym_eq_odd hp']
    exact H_odd_isSqBimult
