import Mathlib.Tactic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

/- # SECTION 1 : THE SQUARE CLASS GROUP -/
/-
**(1) What this section does :** For a field `K` we build the square class group
`SqCl K = Kˣ/(Kˣ)²`, show it has exponent 2 (so it is an 𝔽₂-vector space), and prove the
descent principle: a function `F : Kˣ → Kˣ → ℤˣ = {±1}` that is multiplicative in each
variable factors uniquely through a bilinear pairing `SqCl K →* (SqCl K →* ℤˣ)`.

**(2) Why we need it :** Serre states bilinearity of the Hilbert symbol as "`(a,b)` is a
nondegenerate bilinear form on the 𝔽₂-vector space `kˣ/kˣ²`" (III.1.1, remark after Prop. 2;
III.1.2, Thm 2). Sections 2–7 show the Hilbert symbol on `ℚ_p` is such a function `F`. This
section turns any such `F` into the bundled pairing over any field.

**(3) Design choice :** As discussed in prior meetings, we do not take
`SqCl K →ₗ[ZMod 2] SqCl K →ₗ[ZMod 2] ℤˣ`. Mathlib's linear maps are defined on additive modules
whereas `SqCl K` and `ℤˣ` are multiplicative groups. To use `Module (ZMod 2)` one would have to
pass to `Additive (SqCl K)` and `Additive ℤˣ`, and every Hilbert symbol value `(a,b)` would appear
as `Additive.ofMul (a,b)` with `ofMul`/`toMul` conversions in every statement. This felt messy;
moreover, on a group of exponent 2 the only scalars are 0 and 1, so 𝔽₂-linearity is additivity,
i.e. being a group homomorphism.
-/

variable {K : Type*} [Field K]


/- # 1.1 THE SUBGROUP OF SQUARES AND THE SQUARE CLASS GROUP -/


--*Definition 1.1.1 : The subgroup of squares (Kˣ)² ≤ Kˣ*
abbrev sqSubgroup (K : Type*) [Field K] : Subgroup Kˣ := (powMonoidHom 2 : Kˣ →* Kˣ).range

--*Definition 1.1.2 : The square class group SqCl K = Kˣ/(Kˣ)²*
abbrev SqCl (K : Type*) [Field K] := Kˣ ⧸ sqSubgroup K

--*Definition 1.1.3 : The quotient homomorphism Kˣ →* SqCl K*
def SqCl.mk : Kˣ →* SqCl K := QuotientGroup.mk' (sqSubgroup K)


/- # 1.2 THE 𝔽₂ STRUCTURE -/


--*Lemma 1.2.1 : Every square class squares to 1, i.e. SqCl K has exponent 2*
lemma SqCl.sq_eq_one (x : SqCl K) : x ^ 2 = 1 := by
  induction x using QuotientGroup.induction_on with
  | H a =>
    rw [← QuotientGroup.mk_pow]
    refine (QuotientGroup.eq_one_iff (a ^ 2)).mpr ?_
    simp


/- # 1.3 HOMOMORPHISMS KILLING SQUARES FACTOR THROUGH THE SQUARE CLASS GROUP -/


--*Definition 1.3.1 : Universal property — a homomorphism killing squares descends to SqCl K*
def SqCl.lift {M : Type*} [CommMonoid M] (f : Kˣ →* M) (hf : ∀ c : Kˣ, f (c ^ 2) = 1) :
    SqCl K →* M := by
  have h : ∀ x ∈ sqSubgroup K, f x = 1 := by
    rintro x ⟨c, rfl⟩
    exact hf c
  exact QuotientGroup.lift (sqSubgroup K) f h


/- # 1.4 BIMULTIPLICATIVE FUNCTIONS -/


--*Definition 1.4.1 : F : Kˣ → Kˣ → ℤˣ is bimultiplicative*
structure IsSqBimult (F : Kˣ → Kˣ → ℤˣ) : Prop where
  mul_left : ∀ a a' b, F (a * a') b = F a b * F a' b
  mul_right : ∀ a b b', F a (b * b') = F a b * F a b'

namespace IsSqBimult

variable {F : Kˣ → Kˣ → ℤˣ}

--*Lemma 1.4.1 : For a bimultiplicative F, F 1 a = 1*
lemma one_left (h : IsSqBimult F) (a : Kˣ) : F 1 a = 1 := by
  have h1 := h.mul_left 1 1 a
  rw [one_mul] at h1
  exact left_eq_mul.mp h1

--*Lemma 1.4.2 : For a bimultiplicative F, F a 1 = 1*
lemma one_right (h : IsSqBimult F) (a : Kˣ) : F a 1 = 1 := by
  have h1 := h.mul_right a 1 1
  rw [one_mul] at h1
  exact left_eq_mul.mp h1

--*Lemma 1.4.3 : For a bimultiplicative F, F (a²) b = 1*
lemma sq_left (h : IsSqBimult F) (a b : Kˣ) : F (a ^ 2) b = 1 := by
  rw [sq, h.mul_left, Int.units_mul_self]

--*Lemma 1.4.4 : For a bimultiplicative F, F a (b²) = 1*
lemma sq_right (h : IsSqBimult F) (a b : Kˣ) : F a (b ^ 2) = 1 := by
  rw [sq, h.mul_right, Int.units_mul_self]

--*Lemma 1.4.5 : Square invariance in the first variable, F (a c²) b = F a b*
lemma mul_sq_left (h : IsSqBimult F) (a b c : Kˣ) : F (a * c ^ 2) b = F a b := by
  rw [h.mul_left, h.sq_left, mul_one]

--*Lemma 1.4.6 : Square invariance in the second variable, F a (b c²) = F a b*
lemma mul_sq_right (h : IsSqBimult F) (a b c : Kˣ) : F a (b * c ^ 2) = F a b := by
  rw [h.mul_right, h.sq_right, mul_one]


/- # 1.5 BUNDLING THE PAIRING -/


--*Definition 1.5.1 : The curried homomorphism Kˣ →* (Kˣ →* ℤˣ) attached to F*
def hom (h : IsSqBimult F) : Kˣ →* (Kˣ →* ℤˣ) where
  toFun a :=
    { toFun := F a
      map_one' := h.one_right a
      map_mul' := h.mul_right a }
  map_one' := by
    apply MonoidHom.ext
    intro b
    exact h.one_left b
  map_mul' a a' := by
    apply MonoidHom.ext
    intro b
    exact h.mul_left a a' b

--*Definition 1.5.2 : The descended pairing SqCl K →* (SqCl K →* ℤˣ)*
def sqClHom (h : IsSqBimult F) : SqCl K →* (SqCl K →* ℤˣ) := by
  refine SqCl.lift
    { toFun := fun a => SqCl.lift (h.hom a) (h.sq_right a)
      map_one' := ?_
      map_mul' := ?_ } ?_
  · apply MonoidHom.ext
    intro x
    induction x using QuotientGroup.induction_on with
    | H b => exact h.one_left b
  · intro a a'
    apply MonoidHom.ext
    intro x
    induction x using QuotientGroup.induction_on with
    | H b => exact h.mul_left a a' b
  · intro c
    apply MonoidHom.ext
    intro x
    induction x using QuotientGroup.induction_on with
    | H b => exact h.sq_left c b

end IsSqBimult


/- # SECTION 2 : THE HILBERT SYMBOL AND SERRE'S PROPOSITION 2 -/
/-
**(1) What this section does :** Over an arbitrary field `K` we define the Hilbert symbol
`(a,b) ∈ {±1}` by solvability of the conic equation `z² = ax² + by²` (Serre III.1.1) and prove
its elementary properties, listed in Serre as Proposition 2 — specifically those used in later
sections, namely symmetry, invariance under squares, and the two cancellation rules. Some further
properties are included; the ones used later are flagged (†).

**(2) Why we need it :** Serre proves the explicit formula for `(a,b)_p` (Thm 1) using these
properties, and bilinearity (Thm 2) as a corollary of the formula. So this section must be
proved without bilinearity, and Sections 6–7 follow from what is here.

**(3) Two design decisions :**
1) Transfer lemmas (2.2) — `hilbertSym` is a classical `if`, so nothing about it computes.
   Since `ℤˣ = {±1}` the symbol is determined by whether it equals `1`. The lemmas
   `hilbertSym_eq_one_iff`, `hilbertSym_eq_neg_one_iff`, `hilbertSym_congr` do the `if`
   elimination, after which every argument is about solutions of `z² = ax² + by²`.
2) Norm form instead of Serre's Prop. 1 (2.4) — Serre derives (iii) from
   `(a,b) = 1 ⟺ a ∈ N(K(√b)ˣ)`. We avoid constructing `K(√b)`: a nontrivial solution of
   `z² = ax² + by²` is the same as an expression `a = z² − b y²` (unless `b` is a square),
   and closure of such `a` under multiplication is the identity
   `(z₁² − by₁²)(z₂² − by₂²) = (z₁z₂ + by₁y₂)² − b(z₁y₂ + z₂y₁)²`, i.e. multiplicativity of
   the norm.
-/


/- # 2.1 DEFINITION OF THE HILBERT SYMBOL -/


--*Definition 2.1.1 : The Hilbert solvability condition — z² = ax² + by² has a nontrivial solution*
def HilbertSolvable (K : Type*) [Field K] (a b : K) : Prop :=
  ∃ z x y : K, (z ≠ 0 ∨ x ≠ 0 ∨ y ≠ 0) ∧ z ^ 2 = a * x ^ 2 + b * y ^ 2

--*Definition 2.1.2 : The Hilbert symbol (a,b) ∈ ℤˣ of two units of a field*
noncomputable def hilbertSym (K : Type*) [Field K] (a b : Kˣ) : ℤˣ := by
  classical
  exact if HilbertSolvable K a b then 1 else -1


/- # 2.2 TRANSFER LEMMAS -/


--*Lemma 2.2.1 : The Hilbert symbol equals 1 iff the conic equation has a nontrivial solution*
lemma hilbertSym_eq_one_iff (a b : Kˣ) : hilbertSym K a b = 1 ↔ HilbertSolvable K a b := by
  unfold hilbertSym
  by_cases hs : HilbertSolvable K a b
  · rw [if_pos hs]
    grind
  · rw [if_neg hs]
    simp_all

--*Lemma 2.2.2 : The Hilbert symbol equals -1 iff the conic equation has no nontrivial solution*
lemma hilbertSym_eq_neg_one_iff (a b : Kˣ) :
    hilbertSym K a b = -1 ↔ ¬ HilbertSolvable K a b := by
  unfold hilbertSym
  by_cases hs : HilbertSolvable K a b
  · rw [if_pos hs]
    simp_all
  · rw [if_neg hs]
    simp_all

--*Lemma 2.2.3 : Solvability is invariant under multiplying the first entry by a square*
lemma hilbertSolvable_mul_sq (a b c : Kˣ) :
    HilbertSolvable K ((a * c ^ 2 : Kˣ) : K) (b : K) ↔ HilbertSolvable K (a : K) (b : K) := by
  constructor
  · rintro ⟨z, x, y, hnt, heq⟩
    refine ⟨z, (c : K) * x, y, ?_, ?_⟩
    simp_all
    rw [heq]
    push_cast
    ring
  · rintro ⟨z, x, y, hnt, heq⟩
    refine ⟨(c : K) * z, x, (c : K) * y, ?_, ?_⟩
    simp_all
    push_cast
    grind


/- # 2.3 PROPERTIES OF THE HILBERT SYMBOL -/

variable (K) (a b : Kˣ)


--*(†) Lemma 2.3.1 : The Hilbert symbol is symmetric*
lemma hilbertSym_comm : hilbertSym K a b = hilbertSym K b a := by
  have h : ∀ c d : K, HilbertSolvable K c d → HilbertSolvable K d c := by
    intro c d ⟨z, x, y, hnt, heq⟩
    exact ⟨z, y, x, by grind, by grind⟩
  unfold hilbertSym
  by_cases hab : HilbertSolvable K a b
  · rw [if_pos hab, if_pos (h a b hab)]
  · rw [if_neg hab, if_neg (fun hba => hab (h b a hba))]

--*Lemma 2.3.2 : The Hilbert symbol with 1 in the first entry equals 1*
lemma hilbertSym_one_left : hilbertSym K 1 a = 1 := by
  have h : HilbertSolvable K 1 a := by
    refine ⟨1, 1, 0, ?_, ?_⟩
    simp
    ring
  exact if_pos h

--*Lemma 2.3.3 : The Hilbert symbol with 1 in the second entry equals 1*
lemma hilbertSym_one_right : hilbertSym K b 1 = 1 := by
  have h : HilbertSolvable K b 1 := by
    refine ⟨1, 0, 1, ?_, ?_⟩
    simp
    ring
  exact if_pos h

--*(†) Lemma 2.3.4 : (a, −a) = 1*
lemma hilbertSym_neg_self : hilbertSym K a (-a) = 1 := by
  have h : HilbertSolvable K a (-a) := by
    refine ⟨0, 1, 1, ?_, ?_⟩
    simp
    ring
  exact if_pos h

--*Lemma 2.3.5 : (a, 1 − a) = 1 for a ≠ 1*
lemma hilbertSym_one_sub (ha : a.val ≠ 1) :
    hilbertSym K a (Units.mk0 (1 - a) (by grind)) = 1 := by
  have h : HilbertSolvable K a (1 - a) := by
    refine ⟨1, 1, 1, ?_, ?_⟩
    simp
    ring
  exact if_pos h

--*Lemma 2.3.6 : (a, b) = 1 whenever a is a square*
lemma hilbertSym_of_isSquare (ha : IsSquare a) (b : Kˣ) : hilbertSym K a b = 1 := by
  obtain ⟨c, rfl⟩ := ha
  have h : HilbertSolvable K (c * c) b := by
    refine ⟨c, 1, 0, ?_, ?_⟩
    simp
    ring
  exact if_pos h

--*Lemma 2.3.7 : (a, a) = (a, −1)*
lemma hilbertSym_self : hilbertSym K a a = hilbertSym K a (-1) := by
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

--*Lemma 2.3.8 : Hilbert symbols agree when the two solvability conditions are equivalent*
lemma hilbertSym_congr (a b a' b' : Kˣ)
    (h : HilbertSolvable K a b ↔ HilbertSolvable K a' b') :
    hilbertSym K a b = hilbertSym K a' b' := by
  unfold hilbertSym
  grind

--*(†) Lemma 2.3.9 : Square invariance in the first entry, (a c², b) = (a, b)*
lemma hilbertSym_mul_sq_left (a b c : Kˣ) : hilbertSym K (a * c ^ 2) b = hilbertSym K a b := by
  grind only [hilbertSym_congr, hilbertSolvable_mul_sq]

--*(†) Lemma 2.3.10 : Square invariance in the second entry, (a, b c²) = (a, b)*
lemma hilbertSym_mul_sq_right (a b c : Kˣ) :
    hilbertSym K a (b * c ^ 2) = hilbertSym K a b := by
  grind only [hilbertSym_comm, hilbertSym_mul_sq_left]


/- # 2.4 THE NORM FORM AND ITS CANCELLATION PROPERTIES -/


--*Lemma 2.4.1 : Norm form of Definition 2.1.1 — solvable iff b is a square or a = z² − b y²*
lemma hilbertSolvable_iff_sq_or_norm :
    HilbertSolvable K a b ↔ (∃ c : K, (b : K) = c ^ 2) ∨ ∃ z y : K, (a : K) = z ^ 2 - b * y ^ 2 := by
  constructor
  · rintro ⟨z, x, y, hnt, heq⟩
    by_cases hx : x = 0
    · subst hx
      have hy : y ≠ 0 := by
        rintro rfl
        have hz : z = 0 := by
          have h0 : z ^ 2 = 0 := by
            rw [heq]
            ring
          exact eq_zero_of_pow_eq_zero h0
        simp [hz] at hnt
      left
      refine ⟨z / y, ?_⟩
      rw [div_pow, eq_div_iff (pow_ne_zero 2 hy), heq]
      ring
    · right
      refine ⟨z / x, y / x, ?_⟩
      rw [div_pow, div_pow, ← mul_div_assoc, ← sub_div, eq_div_iff (pow_ne_zero 2 hx), heq]
      ring
  · rintro (⟨c, hc⟩ | ⟨z, y, hzy⟩)
    · exact ⟨c, 0, 1, Or.inr (Or.inr one_ne_zero), by rw [hc]; ring⟩
    · exact ⟨z, 1, y, Or.inr (Or.inl one_ne_zero), by rw [hzy]; ring⟩

--*Lemma 2.4.2 : Solvability is closed under multiplication in the first entry (norms form a subgroup)*
variable {K} in
lemma hilbertSolvable_mul_left {a a' b : Kˣ} (h : HilbertSolvable K a b)
    (h' : HilbertSolvable K a' b) : HilbertSolvable K ((a * a' : Kˣ) : K) b := by
  rw [hilbertSolvable_iff_sq_or_norm] at h h' ⊢
  rcases h with hb | ⟨z, y, hzy⟩
  · exact Or.symm (Or.inr hb)
  rcases h' with hb | ⟨z', y', hz'y'⟩
  · exact Or.symm (Or.inr hb)
  refine Or.inr ⟨z * z' + (b : K) * y * y', z * y' + z' * y, ?_⟩
  push_cast
  rw [hzy, hz'y']
  ring

--*Lemma 2.4.3 : Cancellation 1 — (a,b) = 1 ⟹ (a c, b) = (c, b) (Serre Prop 2 (iii))*
lemma hilbertSym_mul_left_of_eq_one {a b : Kˣ} (h : hilbertSym K a b = 1) (c : Kˣ) :
    hilbertSym K (a * c) b = hilbertSym K c b := by
  rw [hilbertSym_eq_one_iff] at h
  apply hilbertSym_congr
  constructor
  · intro hac
    have h2 := hilbertSolvable_mul_left hac h
    have h3 : a * c * a = c * a ^ 2 := by
      rw [sq, mul_comm a c, mul_assoc]
    rw [h3] at h2
    grind only [hilbertSolvable_mul_sq]
  · intro ha
    grind only [hilbertSolvable_mul_left]

--*Lemma 2.4.4 : Cancellation 2 — (a, −a b) = (a, b) (Serre Prop 2 (iv))*
lemma hilbertSym_neg_self_mul {a b : Kˣ} : hilbertSym K a (-a * b) = hilbertSym K a b := by
  have h : hilbertSym K (-a) a = 1 := by
    grind only [hilbertSym_comm, hilbertSym_neg_self]
  grind only [hilbertSym_comm, hilbertSym_mul_left_of_eq_one]


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


--*Definition 3.1.1 : The p-adic valuation of a unit of ℚ_p, as an integer*
noncomputable def valuationUnits (a : ℚ_[p]ˣ) : ℤ := Padic.valuation (a : ℚ_[p])

--*Lemma 3.1.1 : The valuation is a homomorphism ℚ_pˣ → ℤ*
lemma valuationUnits_mul (a b : ℚ_[p]ˣ) :
    valuationUnits (a * b) = valuationUnits a + valuationUnits b := by
  unfold valuationUnits
  simp only [Units.val_mul, ne_eq, Units.ne_zero, not_false_eq_true, Padic.valuation_mul]

--*Lemma 3.1.2 : The valuation of 1 is 0*
lemma valuationUnits_one : valuationUnits (1 : ℚ_[p]ˣ) = 0 := Padic.valuation_one

--*Lemma 3.1.3 : The valuation of an inverse*
lemma valuationUnits_inv (a : ℚ_[p]ˣ) : valuationUnits a⁻¹ = -valuationUnits a := by
  unfold valuationUnits
  simp only [Units.val_inv_eq_inv_val, Padic.valuation_inv]

--*Lemma 3.1.4 : The valuation of a natural power*
lemma valuationUnits_pow (a : ℚ_[p]ˣ) (n : ℕ) : valuationUnits (a ^ n) = n * valuationUnits a := by
  unfold valuationUnits
  simp only [Units.val_pow_eq_pow_val, Padic.valuation_pow]

--*Lemma 3.1.5 : The valuation of an integer power*
lemma valuationUnits_zpow (a : ℚ_[p]ˣ) (n : ℤ) :
    valuationUnits (a ^ n) = n * valuationUnits a := by
  unfold valuationUnits
  simp only [Units.val_zpow_eq_zpow_val, Padic.valuation_zpow]

--*Lemma 3.1.6 : The valuation of -1 is 0*
lemma valuationUnits_neg_one : valuationUnits (-1 : ℚ_[p]ˣ) = 0 := by
  have h := valuationUnits_pow (-1 : ℚ_[p]ˣ) 2
  rw [neg_one_sq, valuationUnits_one] at h
  push_cast at h
  grind

--*Lemma 3.1.7 : The valuation of an additive inverse*
lemma valuationUnits_neg (a : ℚ_[p]ˣ) : valuationUnits (-a) = valuationUnits a := by
  rw [← neg_one_mul, valuationUnits_mul, valuationUnits_neg_one, zero_add]


/- # 3.2 THE UNIFORMISER p IN ℚ_pˣ -/


--*Definition 3.2.1 : The uniformiser p ∈ ℚ_pˣ*
noncomputable def uniformiser (p : ℕ) [Fact p.Prime] : ℚ_[p]ˣ :=
  Units.mk0 (p : ℚ_[p]) (Nat.cast_ne_zero.mpr (Fact.out (p := p.Prime)).ne_zero)

--*Lemma 3.2.1 : The uniformiser viewed in ℚ_p is p (sanity check)*
lemma val_uniformiser : ((uniformiser p : ℚ_[p]ˣ) : ℚ_[p]) = p := by rfl

--*Lemma 3.2.2 : The valuation of the uniformiser is 1*
lemma valuationUnits_uniformiser : valuationUnits (uniformiser p) = 1 := Padic.valuation_p


/- # 3.3 THE UNIT PART OF a = p^{v(a)} · u IN ℚ_pˣ -/


--*Lemma 3.3.1 : x / p^{v(x)} has norm 1, hence is a unit of ℤ_p*
lemma norm_div_p_zpow_valuation (x : ℚ_[p]) (hx : x ≠ 0) :
    ‖x / (p : ℚ_[p]) ^ (Padic.valuation x)‖ = 1 := by
  simp only [norm_div, Padic.norm_p_zpow, zpow_neg, div_inv_eq_mul]
  simp [hx, Padic.norm_eq_zpow_neg_valuation, zpow_ne_zero, NeZero.ne]

--*Definition 3.3.1 : The unit part u ∈ ℤ_pˣ of a ∈ ℚ_pˣ*
noncomputable def unitPart (a : ℚ_[p]ˣ) : ℤ_[p]ˣ :=
  PadicInt.mkUnits (norm_div_p_zpow_valuation (a : ℚ_[p]) a.ne_zero)

--*Lemma 3.3.2 : The unit part viewed in ℚ_p is a / p^{v(a)} (sanity check)*
lemma coe_unitPart (a : ℚ_[p]ˣ) :
    ((unitPart a : ℤ_[p]) : ℚ_[p]) = (a : ℚ_[p]) / (p : ℚ_[p]) ^ valuationUnits a := rfl

--*Lemma 3.3.3 : The unit part is multiplicative*
lemma unitPart_mul (a b : ℚ_[p]ˣ) : unitPart (a * b) = unitPart a * unitPart b := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out (p := p.Prime)).ne_zero
  apply Units.ext
  apply Subtype.ext
  push_cast
  rw [coe_unitPart (a * b), coe_unitPart a, coe_unitPart b, valuationUnits_mul, zpow_add₀ hp0,
    Units.val_mul, div_mul_div_comm]

--*Lemma 3.3.4 : The unit part of 1 is 1*
lemma unitPart_one : unitPart (1 : ℚ_[p]ˣ) = 1 := by
  have h := unitPart_mul (1 : ℚ_[p]ˣ) 1
  rw [mul_one] at h
  exact right_eq_mul.mp h

--*Lemma 3.3.5 : The unit part of -1 is -1*
lemma unitPart_neg_one : unitPart (-1 : ℚ_[p]ˣ) = -1 := by
  apply Units.ext
  apply Subtype.ext
  rw [coe_unitPart, valuationUnits_neg_one, zpow_zero, div_one]
  simp only [Units.val_neg, Units.val_one, PadicInt.coe_neg, PadicInt.coe_one]

--*Lemma 3.3.6 : If v(a) = 0 then the unit part of a is a itself*
lemma coe_unitPart_of_valuationUnits_eq_zero {a : ℚ_[p]ˣ} (ha : valuationUnits a = 0) :
    ((unitPart a : ℤ_[p]) : ℚ_[p]) = (a : ℚ_[p]) := by
  rw [coe_unitPart, ha, zpow_zero, div_one]

--*Lemma 3.3.7 : If v(a) = 1 then the unit part of a is a / p, i.e. a = p · unitPart a*
lemma coe_unitPart_of_valuationUnits_eq_one {a : ℚ_[p]ˣ} (ha : valuationUnits a = 1) :
    ((unitPart a : ℤ_[p]) : ℚ_[p]) = (a : ℚ_[p]) / p := by
  rw [coe_unitPart, ha, zpow_one]


/- # 3.4 THE RESIDUE MOD p OF THE UNIT PART IN (ℤ/p)ˣ -/


--*Definition 3.4.1 : The residue mod p of the unit part of a ∈ ℚ_pˣ*
noncomputable def unitPartZMod (a : ℚ_[p]ˣ) : (ZMod p)ˣ :=
  Units.map (PadicInt.toZMod (p := p)).toMonoidHom (unitPart a)

--*Lemma 3.4.1 : The residue viewed in ℤ/p is the reduction of the unit part (sanity check)*
lemma coe_unitPartZMod (a : ℚ_[p]ˣ) :
    ((unitPartZMod a : (ZMod p)ˣ) : ZMod p) = PadicInt.toZMod (unitPart a : ℤ_[p]) := rfl

--*Lemma 3.4.2 : The residue of the unit part is multiplicative*
lemma unitPartZMod_mul (a b : ℚ_[p]ˣ) : unitPartZMod (a * b) = unitPartZMod a * unitPartZMod b := by
  unfold unitPartZMod
  rw [unitPart_mul, map_mul]

--*Lemma 3.4.3 : The residue of the unit part of 1 is 1*
lemma unitPartZMod_one : unitPartZMod (1 : ℚ_[p]ˣ) = 1 := by
  unfold unitPartZMod
  rw [unitPart_one, map_one]

--*Lemma 3.4.4 : The residue of the unit part of -1 is -1*
lemma unitPartZMod_neg_one : unitPartZMod (-1 : ℚ_[p]ˣ) = -1 := by
  apply Units.ext
  simp [unitPartZMod, unitPart_neg_one]

--*Lemma 3.4.5 : The residue of the unit part of -a is unitPartZMod (-1) · unitPartZMod a*
lemma unitPartZMod_neg (a : ℚ_[p]ˣ) : unitPartZMod (-a) = unitPartZMod (-1) * unitPartZMod a := by
  rw [← unitPartZMod_mul, neg_one_mul]


/- # 3.5 REDUCTION TO VALUATIONS IN {0, 1} (Serre III.1.2) -/


--*Lemma 3.5.1 : Every a ∈ ℚ_pˣ is (an element of valuation 0 or 1) × (a square)*
lemma exists_eq_mul_sq (a : ℚ_[p]ˣ) :
    ∃ b c : ℚ_[p]ˣ, a = b * c ^ 2 ∧ (valuationUnits b = 1 ∨ valuationUnits b = 0) := by
  obtain ⟨k, hk⟩ := Int.even_or_odd' (valuationUnits a)
  refine ⟨a * ((uniformiser p ^ k)⁻¹) ^ 2, uniformiser p ^ k, ?_, ?_⟩
  · rw [mul_assoc, ← mul_pow, inv_mul_cancel, one_pow, mul_one]
  · rw [valuationUnits_mul, sq, valuationUnits_mul, valuationUnits_inv, valuationUnits_zpow,
      valuationUnits_uniformiser]
    grind

--*Lemma 3.5.2 : Reduction principle — a symmetric, square-invariant F that agrees with the*
--*Hilbert symbol whenever (v a, v b) ∈ {(0,0), (1,0), (1,1)} agrees with it everywhere*
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


--*Definition 4.1.1 : The Legendre symbol as the unit-valued quadratic character (ℤ/p)ˣ →* ℤˣ*
noncomputable def quadraticCharUnits (p : ℕ) [Fact p.Prime] : (ZMod p)ˣ →* ℤˣ :=
  (quadraticChar (ZMod p)).toUnitHom

--*Lemma 4.1.1 : The Legendre symbol of a unit equals 1 iff it is a square in ℤ/p*
lemma quadraticCharUnits_eq_one_iff (w : (ZMod p)ˣ) :
    quadraticCharUnits p w = 1 ↔ IsSquare (w : ZMod p) := by
  rw [← quadraticChar_one_iff_isSquare w.ne_zero, ← Units.val_eq_one]
  unfold quadraticCharUnits
  simp

--*Lemma 4.1.2 : The Legendre symbol of a unit equals -1 iff it is not a square in ℤ/p*
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


--*Definition 4.2.1 : Explicit formula for the Hilbert symbol at odd p (Serre III.1.2, Thm 1)*
private noncomputable def formulaOdd (a b : ℚ_[p]ˣ) : ℤˣ :=
  quadraticCharUnits p (-1) ^ (valuationUnits a * valuationUnits b)
    * quadraticCharUnits p (unitPartZMod b) ^ valuationUnits a
    * quadraticCharUnits p (unitPartZMod a) ^ valuationUnits b

--*Lemma 4.2.1 : formulaOdd is symmetric*
lemma formulaOdd_comm (a b : ℚ_[p]ˣ) : formulaOdd a b = formulaOdd b a := by
  unfold formulaOdd
  rw [mul_comm (valuationUnits a) (valuationUnits b)]
  ac_rfl

--*Lemma 4.2.2 : formulaOdd is multiplicative in the first entry*
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

--*Lemma 4.2.3 : formulaOdd is multiplicative in the second entry*
lemma formulaOdd_mul_right (a b b' : ℚ_[p]ˣ) :
    formulaOdd a (b * b') = formulaOdd a b * formulaOdd a b' := by
  rw [formulaOdd_comm, formulaOdd_mul_left, formulaOdd_comm b a, formulaOdd_comm b' a]

--*Lemma 4.2.4 : formulaOdd is bimultiplicative*
lemma formulaOdd_isSqBimult : IsSqBimult (formulaOdd (p := p)) :=
  ⟨formulaOdd_mul_left, formulaOdd_mul_right⟩

--*Lemma 4.2.5 : Square invariance of formulaOdd in the first entry*
lemma formulaOdd_mul_sq_left (a c b : ℚ_[p]ˣ) : formulaOdd (a * c ^ 2) b = formulaOdd a b :=
  formulaOdd_isSqBimult.mul_sq_left a b c

--*Lemma 4.2.6 : Square invariance of formulaOdd in the second entry*
lemma formulaOdd_mul_sq_right (a b c : ℚ_[p]ˣ) : formulaOdd a (b * c ^ 2) = formulaOdd a b :=
  formulaOdd_isSqBimult.mul_sq_right a b c


/- # 4.3 RESIDUES MOD 4 AND 8, AND ε, ω, sgn FOR THE p = 2 CASE -/


--*Definition 4.3.1 : The residue mod 4 of the unit part of a 2-adic number*
private noncomputable def unitPartZMod4 (a : ℚ_[2]ˣ) : (ZMod 4)ˣ :=
  Units.map (PadicInt.toZModPow 2).toMonoidHom (unitPart a)

--*Lemma 4.3.1 : The residue mod 4 viewed in ℤ/4 is the reduction mod 4 of the unit part*
lemma coe_unitPartZMod4 (a : ℚ_[2]ˣ) :
    ((unitPartZMod4 a : (ZMod 4)ˣ) : ZMod 4) = PadicInt.toZModPow 2 (unitPart a : ℤ_[2]) := rfl

--*Lemma 4.3.2 : The residue mod 4 is multiplicative*
lemma unitPartZMod4_mul (a b : ℚ_[2]ˣ) :
    unitPartZMod4 (a * b) = unitPartZMod4 a * unitPartZMod4 b := by
  unfold unitPartZMod4
  rw [unitPart_mul, map_mul]

--*Definition 4.3.2 : The residue mod 8 of the unit part of a 2-adic number*
private noncomputable def unitPartZMod8 (a : ℚ_[2]ˣ) : (ZMod 8)ˣ :=
  Units.map (PadicInt.toZModPow 3).toMonoidHom (unitPart a)

--*Lemma 4.3.3 : The residue mod 8 viewed in ℤ/8 is the reduction mod 8 of the unit part*
lemma coe_unitPartZMod8 (a : ℚ_[2]ˣ) :
    ((unitPartZMod8 a : (ZMod 8)ˣ) : ZMod 8) = PadicInt.toZModPow 3 (unitPart a : ℤ_[2]) := rfl

--*Lemma 4.3.4 : The residue mod 8 is multiplicative*
lemma unitPartZMod8_mul (a b : ℚ_[2]ˣ) :
    unitPartZMod8 (a * b) = unitPartZMod8 a * unitPartZMod8 b := by
  unfold unitPartZMod8
  rw [unitPart_mul, map_mul]

--*Definition 4.3.3 : ε(a) ∈ ℤ/2, with ε(a) = 0 ↔ unit part of a ≡ 1 (mod 4)*
noncomputable def epsilon2 (a : ℚ_[2]ˣ) : ZMod 2 := if unitPartZMod4 a = 1 then 0 else 1

--*Lemma 4.3.5 : Finite check on (ℤ/4)ˣ that ε is additive (Serre III.1.2)*
private lemma epsilon2_aux : ∀ u v : (ZMod 4)ˣ,
    (if u * v = 1 then (0 : ZMod 2) else 1)
      = (if u = 1 then (0 : ZMod 2) else 1) + (if v = 1 then 0 else 1) := by
  decide

--*Lemma 4.3.6 : ε is a homomorphism (ℚ_2ˣ, ·) → (ℤ/2, +)*
lemma epsilon2_mul (a b : ℚ_[2]ˣ) : epsilon2 (a * b) = epsilon2 a + epsilon2 b := by
  unfold epsilon2
  rw [unitPartZMod4_mul]
  exact epsilon2_aux (unitPartZMod4 a) (unitPartZMod4 b)

--*Definition 4.3.4 : ω(a) ∈ ℤ/2, with ω(a) = 0 ↔ unit part of a ≡ ±1 (mod 8)*
noncomputable def omega2 (a : ℚ_[2]ˣ) : ZMod 2 :=
  if unitPartZMod8 a = 1 ∨ unitPartZMod8 a = -1 then 0 else 1

--*Lemma 4.3.7 : Finite check on (ℤ/8)ˣ that ω is additive (Serre III.1.2)*
private lemma omega2_aux : ∀ u v : (ZMod 8)ˣ,
    (if u * v = 1 ∨ u * v = -1 then (0 : ZMod 2) else 1)
      = (if u = 1 ∨ u = -1 then (0 : ZMod 2) else 1)
        + (if v = 1 ∨ v = -1 then (0 : ZMod 2) else 1) := by
  decide

--*Lemma 4.3.8 : ω is a homomorphism (ℚ_2ˣ, ·) → (ℤ/2, +)*
lemma omega2_mul (a b : ℚ_[2]ˣ) : omega2 (a * b) = omega2 a + omega2 b := by
  unfold omega2
  rw [unitPartZMod8_mul]
  exact omega2_aux (unitPartZMod8 a) (unitPartZMod8 b)

--*Definition 4.3.5 : The sign map (ℤ/2, +) → ({±1}, ·), t ↦ (−1)^t*
def sgn : ZMod 2 → ℤˣ := fun t => if t = 0 then 1 else -1

--*Lemma 4.3.9 : sgn is a homomorphism, sgn (s + t) = sgn s · sgn t (sanity check)*
lemma sgn_add : ∀ s t : ZMod 2, sgn (s + t) = sgn s * sgn t := by decide


/- # 4.4 THE EXPLICIT FORMULA FOR p = 2 AND ITS PROPERTIES -/


--*Definition 4.4.1 : Explicit formula for the Hilbert symbol at p = 2 (Serre III.1.2, Thm 1)*
private noncomputable def formulaTwo (a b : ℚ_[2]ˣ) : ℤˣ :=
  sgn (epsilon2 a * epsilon2 b + (valuationUnits a : ZMod 2) * omega2 b
    + (valuationUnits b : ZMod 2) * omega2 a)

--*Lemma 4.4.1 : formulaTwo is symmetric*
lemma formulaTwo_comm (a b : ℚ_[2]ˣ) : formulaTwo a b = formulaTwo b a := by
  unfold formulaTwo
  congr 1
  ring

--*Lemma 4.4.2 : formulaTwo is multiplicative in the first entry*
lemma formulaTwo_mul_left (a a' b : ℚ_[2]ˣ) :
    formulaTwo (a * a') b = formulaTwo a b * formulaTwo a' b := by
  unfold formulaTwo
  rw [← sgn_add]
  congr 1
  rw [epsilon2_mul, omega2_mul, valuationUnits_mul]
  grind

--*Lemma 4.4.3 : formulaTwo is multiplicative in the second entry*
lemma formulaTwo_mul_right (a b b' : ℚ_[2]ˣ) :
    formulaTwo a (b * b') = formulaTwo a b * formulaTwo a b' := by
  grind only [formulaTwo_comm, formulaTwo_mul_left]

--*Lemma 4.4.4 : formulaTwo is bimultiplicative*
lemma formulaTwo_isSqBimult : IsSqBimult formulaTwo := ⟨formulaTwo_mul_left, formulaTwo_mul_right⟩

--*Lemma 4.4.5 : Square invariance of formulaTwo in the first entry*
lemma formulaTwo_mul_sq_left (a c b : ℚ_[2]ˣ) : formulaTwo (a * c ^ 2) b = formulaTwo a b :=
  formulaTwo_isSqBimult.mul_sq_left a b c

--*Lemma 4.4.6 : Square invariance of formulaTwo in the second entry*
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


--*Lemma 5.1.1 : The kernel of the reduction map ℤ_p → ℤ/p is the ideal generated by p*
lemma toZMod_eq_zero_iff_dvd (x : ℤ_[p]) : PadicInt.toZMod x = 0 ↔ (p : ℤ_[p]) ∣ x := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p,
    Ideal.mem_span_singleton]

--*Lemma 5.1.2 : A p-adic integer in the kernel of reduction has norm < 1*
lemma norm_lt_one_of_toZMod_eq_zero {x : ℤ_[p]} (h : PadicInt.toZMod x = 0) : ‖x‖ < 1 := by
  grind only [toZMod_eq_zero_iff_dvd, PadicInt.norm_lt_one_iff_dvd]

--*Lemma 5.1.3 : A p-adic integer not in the kernel of reduction has norm 1*
lemma norm_eq_one_of_toZMod_ne_zero {x : ℤ_[p]} (h : PadicInt.toZMod x ≠ 0) : ‖x‖ = 1 := by
  rcases (PadicInt.norm_le_one x).lt_or_eq with hlt | heq
  · grind only [toZMod_eq_zero_iff_dvd, PadicInt.norm_lt_one_iff_dvd]
  · grind

--*Lemma 5.1.4 : Units of ℤ_p have nonzero residue mod p*
lemma toZMod_units_ne_zero (u : ℤ_[p]ˣ) : PadicInt.toZMod (u : ℤ_[p]) ≠ 0 := by
  intro h
  apply PadicInt.zmodRepr_units_ne_zero u
  grind only [PadicInt.zmodRepr_eq_zero_iff_dvd, toZMod_eq_zero_iff_dvd]

--*Lemma 5.1.5 : The reduction map mod p is surjective*
lemma exists_toZMod_eq (a : ZMod p) : ∃ b : ℤ_[p], PadicInt.toZMod b = a := ⟨a.val, by simp⟩

--*Lemma 5.1.6 : Two p-adic integers have the same residue mod pⁿ iff pⁿ divides their difference*
lemma toZModPow_eq_iff_dvd (n : ℕ) (x y : ℤ_[p]) :
    PadicInt.toZModPow n x = PadicInt.toZModPow n y ↔ (p : ℤ_[p]) ^ n ∣ x - y := by
  rw [← sub_eq_zero, ← map_sub, ← RingHom.mem_ker, PadicInt.ker_toZModPow,
    Ideal.mem_span_singleton]

--*Lemma 5.1.7 : For odd p, the residue of 2 in ℤ/p is nonzero*
lemma two_ne_zero_zmod_of_odd (hp : Odd p) : (2 : ZMod p) ≠ 0 := by
  have h : p ≠ 2 := by
    grind
  apply Ring.two_ne_zero
  grind only [= Nat.odd_iff, ringChar.eq]

--*Lemma 5.1.8 : The reduction map mod pⁿ is surjective*
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
  sorry

--*Lemma 5.5.2 : Any ℚ_p-solution gives a ℤ_p-solution with some coordinate equal to 1*
--*(Serre III.1.2, proof of Thm 1)*
lemma exists_primitive_sol {a b : ℤ_[p]} (h : HilbertSolvable ℚ_[p] a b) :
    ∃ z x y : ℤ_[p], (z = 1 ∨ x = 1 ∨ y = 1) ∧ z ^ 2 = a * x ^ 2 + b * y ^ 2 := by
  sorry

--*Lemma 5.5.3 : A ℤ_p-solution with z ≠ 0 is a ℚ_p-solution*
lemma hilbertSolvable_of_padicInt_sol {a b z x y : ℤ_[p]} (hz : z ≠ 0)
    (h : z ^ 2 = a * x ^ 2 + b * y ^ 2) : HilbertSolvable ℚ_[p] a b := by
  refine ⟨z, x, y, ?_, ?_⟩
  simp only [ne_eq, PadicInt.coe_eq_zero, not_false_eq_true, true_or, hz]
  have h1 := congrArg (fun t : ℤ_[p] => (t : ℚ_[p])) h
  push_cast at h1
  exact h1

--*Lemma 5.5.4 : A solution of z² = ax² + by² is preserved by any ring homomorphism out of ℤ_p*
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
