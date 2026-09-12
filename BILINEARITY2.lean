import Mathlib.Tactic
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib

/-# SECTION 1 : THE SQUARE CLASS GROUP -/
/-
**(1) What this section does :** For a field `K` we build the square class group `SqCl K = Kˣ/(Kˣ)²`
show it has exponent 2 (so it is an 𝔽₂-vector space), and prove the
descent principle: a function `F : Kˣ → Kˣ → ℤˣ = {±1}` that is multiplicative in each
variable factors uniquely through a bilinear pairing `SqCl K →* (SqCl K →* ℤˣ)`.

**(2) Why we need it :** Serre states bilinearity of the Hilbert symbol as `(a,b)` is a
nondegenerate bilinear form on the 𝔽₂-vector space `kˣ/kˣ²` (III.1.1, remark after Prop. 2 III.1.2, Thm 2).
Sections 2–7 show the Hilbert symbol on `ℚ_p` is such a function `F`. This section turns any such `F` into
the bundled pairing over any field.

**(3) Design choice :** As disscussed in prior meetings, why we do not take `SqCl K →ₗ[ZMod 2] SqCl K →ₗ[ZMod 2] ℤˣ`
Mathlib's linear maps are defined on additive modules whereas `SqCl K` and `ℤˣ` are
multiplicative groups. To use `Module (ZMod 2)` one would have to pass to `Additive (SqCl K)`
and `Additive ℤˣ` and every Hilbert symbol value `(a,b)` would appear as `Additive.ofMul (a,b)` with `ofMul`/`toMul`
conversions in every statement. This felt a boit messy, moreover, on a group of exponent 2 the only
scalars are 0 and 1, so 𝔽₂-linearity is additivity, being a group homomorphism.
-/

variable {K : Type*} [Field K]

/- # 1.1 THE SUBGROUP OF SQUARES AND THE SQUARE CLASS GROUP -/


--*Definition 1.1.1 : Subgroup of Squares*
abbrev SqSubgroup (K : Type*) [Field K] : Subgroup Kˣ := (powMonoidHom 2 : Kˣ →* Kˣ).range
--*Definition 1.1.2 : Square Class Group*
abbrev SqCl (K : Type*) [Field K] := Kˣ ⧸ SqSubgroup K
--*Definition 1.1.3 : Quotient Group Homomorphism*
def SqCl.mk : Kˣ →* SqCl K := QuotientGroup.mk' (SqSubgroup K)


/- # 1.2 THE 𝔽₂ STRUCTURE -/


--*Lemma 1.2.1 : Every square class squares to 1*
lemma SqCl.squares_eq_one (x : SqCl K) : x ^ 2 = 1 := by
  induction x using QuotientGroup.induction_on with
  | H a =>
    rw [← QuotientGroup.mk_pow]
    refine (QuotientGroup.eq_one_iff (a ^ 2)).mpr ?_
    simp


/- # 1.3 HOMORPHISMS KILLING SQUARES FACTORS THROUGH THE SQUARE CLASS GROUP-/


--*Definition 1.3.1 : The Universal Property of the Square Class Group*
def SqCl.lift {M : Type*} [CommMonoid M] (f : Kˣ →* M) (hf : ∀ c : Kˣ, f (c ^ 2) = 1) :
    SqCl K →* M := by
  have h : ∀ x ∈ SqSubgroup K, f x = 1 := by
    rintro x ⟨c, rfl⟩
    exact hf c
  exact QuotientGroup.lift (SqSubgroup K) f h


/- # 1.4  BIMULTIPLICATIVE FUCNTIONS -/


--*Definition 1.4.1 : Bimultiplicativity*
structure IsSqBimult (F : Kˣ → Kˣ → ℤˣ) : Prop where
  mul_left   : ∀ a a' b, F (a * a') b = F a b * F a' b
  mul_right  : ∀ a b b', F a (b * b') = F a b * F a b'

namespace IsSqBimult
variable {F : Kˣ → Kˣ → ℤˣ}

--*Lemma 1.4.1 : For a bimutiplicative map F, F 1 a = 1*
lemma one_left (h : IsSqBimult F) (a : Kˣ) : F 1 a = 1 := by
  have h1 := h.mul_left 1 1 a
  rw[one_mul] at h1
  exact left_eq_mul.mp h1
--*Lemma 1.4.2 : For a bimutiplicative map F, F a 1 = 1*
lemma one_right (h : IsSqBimult F) (a : Kˣ) : F a 1 = 1 := by
  have h1 := h.mul_right a 1 1
  rw[one_mul] at h1
  exact left_eq_mul.mp h1
--*Lemma 1.4.3 : For a bimutiplicative map F, F (a²) b = 1*
lemma sq_left (h : IsSqBimult F) (a b : Kˣ) : F (a ^ 2) b = 1 := by
  rw[sq, h.mul_left, Int.units_mul_self]
--*Lemma 1.4.4 : For a bimutiplicative map F, F b (a²) = 1*
lemma sq_right (h : IsSqBimult F) (a b : Kˣ) : F a (b ^ 2) = 1 := by
  rw[sq, h.mul_right, Int.units_mul_self]
--*Lemma 1.4.4 : Square Invariance in the first variable, F (a c²) b = F a b*
lemma sq_invariance_left (h : IsSqBimult F) (a b c : Kˣ) : F (a * c ^ 2) b  = F a b := by
  rw[h.mul_left, h.sq_left, mul_one]
--*Lemma 1.4.5 : Square invariance in the second variable, F a (b c²) = F a b*
lemma sq_invariance_right (h : IsSqBimult F) (a b c : Kˣ) : F a (b * c ^ 2)  = F a b := by
  rw[h.mul_right, h.sq_right, mul_one]


/- # 1.5 BUNDLING THE DEFINITION-/


--*Definition 1.5.1 : The homomorphism Kˣ → (Kˣ → ℤˣ)*
def HomK(h : IsSqBimult F) : Kˣ →* (Kˣ →* ℤˣ) where
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
--*Definition 1.5.2 : The homomorphism SqCl K → (SqCl K → ℤˣ)*
def HomSqCl (h : IsSqBimult F) : SqCl K →* (SqCl K →* ℤˣ) := by
  refine SqCl.lift
    { toFun := fun a => SqCl.lift (h.HomK a) (h.sq_right a)
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
**(1) What this section does :** Over an arbitrary field `K` we define the Hilbert symbol `(a,b) ∈ {±1}`
by solvability of the conic equation `z² = ax² + by²` (Serre III.1.1) and prove its elementary
properties as listed in Serre as Proposition 2 specifically those useful to us in later formalisations
namely symmetry, invariance under squares, and the two cancellation rules. This formalisation does
include some additional properties of the Hilbert symbol, however the ones used in later formalisations will
be flagged as (†)

**(2) Why we need it :** Serre proves the explicit formula for `(a,b)_p` (Thm 1) using these
properties, and bilinearity (Thm 2) as a corollary of the formula. So this section must be
proved without bilinearity, and Sections 6–7 follows from what is here.

**(3) Two design decisions :**
1) Transfer lemmas (2.2) -  `hilbertSym` is a classical `if`, so nothing about it computes.
   Since `ℤˣ = {±1}` the symbol is determined by whether it equals `1`. The lemmas
   `hilbertSym_eq_one_iff`, `hilbertSym_eq_neg_one_iff`, `hilbertSym_congr` do the
   `if` elimination after which, every argument is about solutions of
   `z² = ax² + by²`, removing the if dependency
2) Norm form instead of Serre's Prop. 1 (2.5) - Serre derives (iii) from
   `(a,b) = 1 ⟺ a ∈ N(K(√b)ˣ)`. We avoid constructing `K(√b)` as a nontrivial solution of
   `z² = ax² + by²` is the same as an expression `a = z² − b y²` (unless `b` is a square),
   and closure of such `a` under multiplication is the identity
   `(z₁² − by₁²)(z₂² − by₂²) = (z₁z₂ + by₁y₂)² − b(z₁y₂ + z₂y₁)²` i.e. multiplicativity of the norm.
-/


/- # 2.1 DEFINITION OF THE HILBERT SYMBOL -/


--*Definition 2.1.1 : The Hilbert Solvability condiition*
def HilbertSolvable (K : Type*) [Field K] (a b : K) : Prop :=
  ∃ z x y : K, (z ≠ 0 ∨ x ≠ 0 ∨ y ≠ 0) ∧ z ^ 2 = a * x ^ 2 + b * y ^ 2
--*Definition 2.1.2 : The Hilbert Symbol of two nonzero units in a field*
noncomputable def HilbertSym (K : Type*) [Field K] (a b : Kˣ) : ℤˣ := by
  classical
  exact if HilbertSolvable K a b then 1 else -1


/- # 2.2 TRANSFER LEMMAS -/


--*Lemma 2.2.1 : The Hilbert Symbol equals 1 iff the conic equation has a nontrivial solution*
lemma hilbertSym_eq_one_iff {K : Type*} [Field K] (a b : Kˣ) :
HilbertSym K a b = 1 ↔ HilbertSolvable K a b := by
  unfold HilbertSym
  by_cases hs : HilbertSolvable K a b
  · rw [if_pos hs]
    grind
  · rw [if_neg hs]
    simp_all
--*Lemma 2.2.2 : The Hilbert Symbol equals -1 iff the conic equation does not have a nontrivial solution*
lemma hilbertSym_eq_neg_one_iff {K : Type*} [Field K] (a b : Kˣ) :
HilbertSym K a b = -1 ↔ ¬ HilbertSolvable K a b := by
  unfold HilbertSym
  by_cases hs : HilbertSolvable K a b
  · rw [if_pos hs]
    simp_all
  · rw [if_neg hs]
    simp_all
--*Lemma 2.2.3 : The Solvability of the conic equation is invariant under multiplication by a square*
lemma hilberSol_mul_sq (a b c : Kˣ) :
HilbertSolvable K ((a * c ^ 2 : Kˣ) : K) (b : K) ↔ HilbertSolvable K (a : K) (b : K) := by
  constructor
  · rintro ⟨ z, x, y, hnt, heq ⟩
    refine ⟨ z, (c : K) * x, y, ?_, ?_ ⟩
    simp_all
    rw[heq]
    push_cast
    ring
  · rintro ⟨ z, x, y, hnt, heq ⟩
    refine ⟨ (c : K) * z, x, (c : K) * y, ?_, ?_ ⟩
    simp_all
    push_cast
    grind


/-# 2.3 PROPERTIES OF THE HILBERT SYMBOL-/
variable (K : Type*) [Field K] (a b : Kˣ)


--*(†) Lemma 2.3.1 : The Hilbert Symbol is Symmetric*
lemma hilbertSym_symmetric : HilbertSym  K a b = HilbertSym  K b a := by
  have h : ∀ c d : K, HilbertSolvable K c d → HilbertSolvable K d c := by
    intro c d ⟨z, x, y, hnt, heq⟩
    exact ⟨z, y, x, by grind, by grind⟩
  unfold HilbertSym
  by_cases hab : HilbertSolvable K a b
  · rw [if_pos hab, if_pos (h a b hab)]
  · rw [if_neg hab, if_neg (fun hba => hab (h b a hba))]
--*Lemma 2.3.2 : The Hilbert symbol of any nonzero a ∈ K with 1 in the first entry equals 1*
lemma hilbertSym_one_left : HilbertSym  K 1 a = 1 := by
  have h : HilbertSolvable K 1 a := by
    refine ⟨1, 1, 0, ?_, ?_⟩
    simp
    ring
  exact if_pos h
--*Lemma 2.3.3 : The Hilbert symbol of any nonzero a ∈ K with 1 in the second entry equals 1*
lemma hilbertSym_one_right : HilbertSym K b 1 = 1 := by
  have h : HilbertSolvable K b 1 := by
    refine ⟨1, 0, 1, ?_, ?_⟩
    simp
    ring
  exact if_pos h
--*(†) Lemma 2.3.4 : The Hilbert Symbol of a nonzero a ∈ K with its additive inverse -a equals 1*
lemma hilbertSym_neg : HilbertSym K a (-a) = 1 := by
  have h : HilbertSolvable K a (-a) := by
    refine ⟨0, 1, 1, ?_, ?_⟩
    simp
    ring
  exact if_pos h
--*Lemma 2.3.5 : The Hilbert Symbol of some nonzero a ∈ K with 1-a equals 1*
lemma hilbertSym_one_sub (ha : a.val ≠ 1) : HilbertSym K a (Units.mk0 (1 - a) (by grind)) = 1 := by
  have h : HilbertSolvable K a (1 - a) := by
    refine ⟨1, 1, 1, ?_, ?_⟩
    simp
    ring
  exact if_pos h
--*Lemma 2.3.6 : The Hilbert Symbol of some nonzero b ∈ K and a nonzero square a ∈ K² is 1*
lemma hilbertSym_of_square (ha : IsSquare a) (b : Kˣ) : HilbertSym K a b = 1 := by
  obtain ⟨c, rfl⟩ := ha
  have h : HilbertSolvable K (c * c) b := by
    refine ⟨c, 1, 0, ?_, ?_⟩
    simp
    ring
  exact if_pos h
--*Lemma 2.3.7 : The Hilbert Symbol of a nonzero a ∈ K with itself equals the Hilbert Symbol of a and -1*
lemma hilbertSym_of_self : HilbertSym K a a = HilbertSym K a (-1) := by
  have h : HilbertSolvable K a a ↔ HilbertSolvable K a (-1) := by
    constructor
    · rintro ⟨z, x, y, hnt, heq⟩
      refine ⟨a * x, z, a * y, by aesop, by grind⟩
    · rintro ⟨z, x, y, hnt, heq⟩
      refine ⟨a * x, z, y, by aesop, by grind⟩
  unfold HilbertSym
  by_cases hsolv : HilbertSolvable K a a
  · simp_all
  · simp_all
--*Lemma 2.3.8 : Congruence of the Hilbert Symbol*
lemma hilbertSym_congr (a b a' b' : Kˣ) (h : HilbertSolvable K a b ↔ HilbertSolvable K a' b') :
HilbertSym K a b = HilbertSym K a' b' := by
  unfold HilbertSym
  grind
--*(†) Lemma 2.3.9 : Square Invariance on the left*
lemma hilbertSym_sq_inv_left (a b c : Kˣ) : HilbertSym K (a * c ^ 2) b = HilbertSym K a b := by
  grind only [hilbertSym_congr, hilberSol_mul_sq]
--*(†) Lemma 2.3.10 : Square Invariance on the right*
lemma hilbertSym_sq_inv_right (a b c : Kˣ) : HilbertSym K a (b * c ^ 2) = HilbertSym K a b := by
  grind only [hilbertSym_symmetric, hilbertSym_sq_inv_left]


/- # 2.4 THE NORM FORM AND ITS CANCELLATION PROPERTIES -/


--*Lemma 2.4.1 : Norm form of the Hilbert Solvability condition stated in Definition 2.2.1*
lemma hilbertSol_norm :
HilbertSolvable K a b ↔ (∃ c : K, (b : K) = c^2) ∨ ∃ z y : K, (a : K) = z ^2 - b * y ^ 2 := by
  constructor
  · rintro ⟨ z, x, y, hnt, heq⟩
    by_cases hx : x = 0
    · subst hx
      have hy : y ≠ 0 := by
        rintro rfl
        have hz : z = 0 := by
          have h0 : z ^ 2 = 0 := by
            rw[heq]
            ring
          exact eq_zero_of_pow_eq_zero h0
        simp [hz] at hnt
      left
      refine ⟨ z / y , ?_⟩
      rw [div_pow, eq_div_iff (pow_ne_zero 2 hy), heq]
      ring
    · right
      refine ⟨z / x, y / x, ?_⟩
      rw [div_pow, div_pow, ← mul_div_assoc, ← sub_div, eq_div_iff (pow_ne_zero 2 hx), heq]
      ring
  · rintro (⟨c, hc⟩ | ⟨z, y, hzy⟩)
    · exact ⟨c, 0, 1, Or.inr (Or.inr one_ne_zero), by rw [hc]; ring⟩
    · exact ⟨z, 1, y, Or.inr (Or.inl one_ne_zero), by rw [hzy]; ring⟩
--*Lemma 2.4.2 : Norms are closed under multiplication- Serre's retsatement of norms are closed subgroups*
lemma hilbertSol_norm_mul {K : Type*} [Field K] { a a' b : Kˣ} (h : HilbertSolvable K a b ) ( h' : HilbertSolvable K a' b) :
HilbertSolvable K ((a * a' : Kˣ) : K) b := by
  rw [hilbertSol_norm] at h h' ⊢
  rcases h with hb | ⟨z, y, hzy⟩
  · exact Or.symm (Or.inr hb)
  rcases h' with hb | ⟨z', y', hz'y'⟩
  · exact Or.symm (Or.inr hb)
  refine Or.inr ⟨z * (z') + (b : K) * y * (y'), z * (y') + (z') * y, ?_⟩
  push_cast
  rw [hzy, hz'y']
  ring
--*Lemma 2.4.3 : Cancellation Property 1 - (a,b) = 1 ⟹ (aa′,b) = (a′,b)*
lemma hilbertSym_eq_one_cancel {a b : Kˣ} (h : HilbertSym K a b = 1) (c : Kˣ) :
HilbertSym K (a * c) b = HilbertSym K c b := by
  rw [hilbertSym_eq_one_iff] at h
  apply hilbertSym_congr
  constructor
  · intro hac
    have h2 := hilbertSol_norm_mul hac h
    have h3 : a * c * a = c * a ^ 2 := by
      rw [sq, mul_comm a c, mul_assoc]
    rw [h3] at h2
    grind only [hilberSol_mul_sq]
  · intro ha
    grind only [hilbertSol_norm_mul]
--*Lemma 2.4.4 : Cancellation property 2 - (a,b) = (a,−ab)*
lemma hilbertSym_eq_neg_one_cancel {a b : Kˣ } : HilbertSym K a (-a * b) = HilbertSym K a b := by
  have h : HilbertSym K (-a) a = 1 := by
    grind only [hilbertSym_symmetric, hilbertSym_neg]
  grind only [hilbertSym_symmetric, hilbertSym_eq_one_cancel]


/-# SECTION 3 : SOME P-ADIC MACHINERY -/
/-
**(1) What this section does and design disscussion :** Every `a ∈ ℚ_pˣ` is uniquely expressed as
`a = p^{v(a)} · u` with `u ∈ ℤ_pˣ` (Serre II.1.2). This Sections aims at packaging them for the
explicit formula we will see in Section 4, since most of these lemmas / properties do not exists in
Mathlib. Subsequently, we read off `a ∈ ℚ_p` as a decomposition of
1) The valuation `v a : ℤ` → Section 3.1
2) The uniformiser `p : ℚ_pˣ` → Section 3.2
3) The unit part `unitPart a : ℤ_pˣ` → Section 3.3
Finally taking its residue class `mod p` to get
4) The residue mod p of the unit part `resU a : (ℤ/p)ˣ` → Section 3.4
Each subsection explores these decompositions explicitly looking into its defining properties such as
multiplicativity and record their values individually at `1`, `−1`.

**(2) Why we need it :** We will see later in Section 4 when defining the explicit formula for
the Hilbert symbol as defined in Serre, the formulas `H_odd` and `H2` (the explicit formula for
the hilbert symbol for p odd and p = 2), are functions of `(v a, resU a)`. As a result, to define a
cleaner, more organised way of computing this formula, we have individually defined then in the
aforementioned subsections, later combining them into one master formula to show equivalence of the
Hilbert Symbol as defined in Section 2 and the Explicit formula in Section 4. Directly using the Mathlib
documentation came out to be quite messy and hard to track in the InfoView. The last subsection
formalises the first step of Serre's proof of Thm 1 (III.1.2), since the symbol depends only on
classes mod squares, it suffices to compare `hilbertSym` and a formula `F` on pairs with
 `v a, v b ∈ {0,1}`.
-/


/- # 3.1 THE P-ADIC VALUATION vₚ -/
variable {p : ℕ} [Fact p.Prime]


--*Definition 3.1.1 : The p-adic valuation of a unit of ℚ_p as an integer*
noncomputable def v (a : ℚ_[p]ˣ) : ℤ := Padic.valuation (a : ℚ_[p])
--*Lemma 3.1.1 : The p-adic valuation is a homomorphism*
lemma v_mul (a b : ℚ_[p]ˣ) : v (a * b) = v a + v b := by
  unfold v
  simp only [Units.val_mul, ne_eq, Units.ne_zero, not_false_eq_true, Padic.valuation_mul]
--*Lemma 3.1.2 : The p-adic valuation of 1*
lemma v_one : v (1 : ℚ_[p]ˣ) = 0 := Padic.valuation_one
--*Lemma 3.1.3 : The p-adic valuation of the multiplicative inverse of some nonzero a ∈ ℚ_p*
lemma v_inv (a : ℚ_[p]ˣ) : v a⁻¹ = -v a := by
  unfold v
  simp only [Units.val_inv_eq_inv_val, Padic.valuation_inv]
--*Lemma 3.1.4 : The p-adic valuation of a positive power of some nonzero a ∈ ℚ_p*
lemma v_pow (a : ℚ_[p]ˣ) (n : ℕ) : v (a ^ n) = n * v a := by
  unfold v
  simp only [Units.val_pow_eq_pow_val, Padic.valuation_pow]
--*Lemma 3.1.5 : The p-adic valuation of an integer power of some nonzero a ∈ ℚ_p*
lemma v_zpow (a : ℚ_[p]ˣ) (n : ℤ) : v (a ^ n) = n * v a := by
  unfold v
  simp only [Units.val_zpow_eq_zpow_val, Padic.valuation_zpow]
--*Lemma 3.1.6 : The p-adic valuation of -1*
lemma v_neg_one : v (-1 : ℚ_[p]ˣ) = 0 := by
  have h := v_pow (-1 : ℚ_[p]ˣ) 2
  rw[neg_one_sq, v_one] at h
  push_cast at h
  grind
--*Lemma 3.1.7 : The p-adic valuation of the additive inverse of some nonzero a ∈ ℚ_p*
lemma v_neg (a : ℚ_[p]ˣ) : v (-a) = v a := by
  rw[← neg_one_mul, v_mul, v_neg_one, zero_add]


/- # 3.2 THE UNIFORMISER p IN ℚ_pˣ -/


--*Definition 3.2.1 : The uniformiser p ∈ ℚ_pˣ*
noncomputable def pU (p : ℕ) [Fact p.Prime] : ℚ_[p]ˣ :=
 Units.mk0 (p : ℚ_[p]) (Nat.cast_ne_zero.mpr (Fact.out (p := p.Prime)).ne_zero)
--*Lemma 3.2.1 : The uniformiser p ∈ ℚ_pˣ when viewed as an element of ℚ_p is p itself (sanity check)*
lemma coe_pU : ((pU p : ℚ_[p]ˣ) : ℚ_[p]) = p := by rfl
--*Lemma 3.2.2 : The p-adic valuation of the uniformiser p is 1*
lemma v_pU : v (pU p) = 1 := Padic.valuation_p


/- # 3.3 THE UNIT PART a = p^{v(a)} IN ℚ_p-/


--*Lemma 3.3.1 : The unit part of a p-adic number x ∈ ℚ_p has norm 1 hence a unit of ℤ_p*
lemma norm_div_pow_valuation (x : ℚ_[p]) (hx : x ≠ 0) : ‖x / (p : ℚ_[p]) ^ (Padic.valuation x)‖ = 1 := by
  simp only [norm_div, Padic.norm_p_zpow, zpow_neg, div_inv_eq_mul]
  simp [hx, Padic.norm_eq_zpow_neg_valuation, zpow_ne_zero, NeZero.ne]
--*Definition 3.3.1 : The unit part u ∈ ℤ_pˣ of a p-adic number a ∈ ℚ_p*
noncomputable def unitPart (a : ℚ_[p]ˣ) : ℤ_[p]ˣ :=
  PadicInt.mkUnits (norm_div_pow_valuation (a : ℚ_[p]) a.ne_zero)
--*Lemma 3.3.2 : The unit part u ∈ ℤ_p of a p-adic number a ∈ ℚ_pˣ is a p-adic unit (sanity check)*
lemma coe_unitPart (a : ℚ_[p]ˣ) : ((unitPart a : ℤ_[p]) : ℚ_[p]) = (a : ℚ_[p]) / (p : ℚ_[p]) ^ v a := rfl
--*Lemma 3.3.3 : The unit part of a p-adic number is multiplicative*
lemma unitPart_mul (a b : ℚ_[p]ˣ) : unitPart (a * b) = unitPart a * unitPart b := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out (p := p.Prime)).ne_zero
  apply Units.ext
  apply Subtype.ext
  push_cast
  rw [coe_unitPart (a * b), coe_unitPart a, coe_unitPart b, v_mul, zpow_add₀ hp0, Units.val_mul, div_mul_div_comm]
--*Lemma 3.3.4 : The unit part of 1 is 1*
lemma unitPart_one : unitPart (1 : ℚ_[p]ˣ) = 1 := by
  have h := unitPart_mul (1 : ℚ_[p]ˣ) 1
  rw [mul_one] at h
  exact right_eq_mul.mp h
--*Lemma 3.3.5 : The unit part of -1 is -1*
lemma unitPart_neg_one : unitPart (-1 : ℚ_[p]ˣ) = -1 := by
  apply Units.ext
  apply Subtype.ext
  rw[coe_unitPart, v_neg_one, zpow_zero, div_one]
  simp only [Units.val_neg, Units.val_one, PadicInt.coe_neg, PadicInt.coe_one]
--*Lemma 3.3.6 : The unit part of a p-adic number with valuation 0 is itself*
lemma unitPart_of_v_eq_zero {a : ℚ_[p]ˣ} (ha : v a = 0) :
((unitPart a : ℤ_[p]) : ℚ_[p]) = (a : ℚ_[p]) := by
  rw[coe_unitPart, ha, zpow_zero, div_one]
--*Lemma 3.3.7 : The unit part of a p-adic number with valuation 1 is p times its unit part*
lemma unitPart_of_v_eq_one {a : ℚ_[p]ˣ} (ha : v a = 1) :
((unitPart a : ℤ_[p]) : ℚ_[p]) = (a : ℚ_[p]) / p := by
  rw[coe_unitPart, ha, zpow_one]


/- # 3.4 THE RESIDUE MOD p IN (ℤ/p)ˣ -/


--*Definition 3.4.1 : The residue mod p of the unit part of a p-adic number*
noncomputable def resU (a : ℚ_[p]ˣ) : (ZMod p)ˣ :=
  Units.map (PadicInt.toZMod (p := p)).toMonoidHom (unitPart a)
--*Lemma 3.4.1 : The residue mod p as an element of ℤ/p is the reduction of the unit part (sanity check)*
lemma coe_resU (a : ℚ_[p]ˣ) : ((resU a : (ZMod p)ˣ) : ZMod p) = PadicInt.toZMod (unitPart a : ℤ_[p]) := rfl
--*Lemma 3.4.2 : The residue mod p is multiplicative*
lemma resU_mul (a b : ℚ_[p]ˣ) : resU (a * b) = resU a * resU b := by
  unfold resU
  rw [unitPart_mul, map_mul]
--*Lemma 3.4.3 : The residue mod p of 1 is 1*
lemma resU_one : resU (1 : ℚ_[p]ˣ) = 1 := by
  unfold resU
  rw [unitPart_one, map_one]
--*Lemma 3.4.4 : The residue mod p of -1 is -1*
lemma resU_neg_one : resU (-1 : ℚ_[p]ˣ) = -1 := by
  apply Units.ext
  simp [resU, unitPart_neg_one]
--*Lemma 3.4.5 : The residue mod p of the additive inverse of a p-adic number*
lemma resU_neg (a : ℚ_[p]ˣ) : resU (-a) = resU (-1) * resU a := by
  rw [← resU_mul, neg_one_mul]


/- # 3.5 REDUCTION TO VALUATIONS IN {0, 1} (Serre III.1.2) -/


--*Lemma 3.5.1 : Every p-adic number is a product of a number with valuation 0 or 1 and a square*
lemma decomp_a (a : ℚ_[p]ˣ) : ∃ b c : ℚ_[p]ˣ, a = b * c^2 ∧ (v b = 1 ∨ v b = 0) := by
  obtain ⟨k, hk⟩ := Int.even_or_odd' (v a)
  refine ⟨ a * ((pU p^k)⁻¹)^2, pU p^k, ?_, ?_ ⟩
  rw [mul_assoc, ← mul_pow, inv_mul_cancel, one_pow, mul_one]
  rw [v_mul, sq, v_mul, v_inv, v_zpow, v_pU]
  grind
--*Lemma 3.5.2 : Reduction principle, for any a,b ∈ ℚ_pˣ we have (v a, v b) ∈ {(0,0), (1,0), (1,1)}*
 lemma hilbertSym_v_cases (F : ℚ_[p]ˣ → ℚ_[p]ˣ → ℤˣ)
(hsymm : ∀ a b, F a b = F b a)
(hsq : ∀ a c b, F (a * c ^ 2) b = F a b)
(h00 : ∀ a b, v a = 0 → v b = 0 → HilbertSym ℚ_[p] a b = F a b)
(h10 : ∀ a b, v a = 1 → v b = 0 → HilbertSym ℚ_[p] a b = F a b)
(h11 : ∀ a b, v a = 1 → v b = 1 → HilbertSym ℚ_[p] a b = F a b) :
HilbertSym ℚ_[p] = F := by
  funext a b
  obtain ⟨ a', c, rfl, ha ⟩ := decomp_a a
  obtain ⟨ b', d, rfl, hb ⟩ := decomp_a b
  grind only [hilbertSym_symmetric, hilbertSym_sq_inv_right, hilbertSym_sq_inv_left, #d3b4, #d40b,
    #57af, #ee66, #66f4, #d9713768f6b7c904]


/-# SECTION 4 : THE EXPLICIT FORMULA FOR THE HILBERT SYMBOL AT p = 2 OR p ODD-/
/-
**(1) What this section does :** For `a = p^α u`, `b = p^β v` in `ℚ_pˣ` Serre's Theorem 1
gives the explicit formulae for the Hilbert symbol at p where :
→ for `p ≠ 2` :  `(a,b) = (−1)^{αβ ε(p)} · (u/p)^β · (v/p)^α`
→ for `p = 2` :  `(a,b) = (−1)^{ε(u)ε(v) + α ω(v) + β ω(u)}`
where,
`(·/p)` denotes the Legendre symbol and `ε(u) = (u−1)/2`, `ω(u) = (u²−1)/8` mod 2 from (Serre I.3.2).
We define these right-hand sides as functions `H_odd` and `H2 : ℚ_pˣ → ℚ_pˣ → ℤˣ` and prove they
are bimultiplicative and symmetric. Finally equating the two formulae in Sections 2 and 4.

**(2) Why we need it :** Serre proves bilinearity of the Hilbert symbol (Thm 2) as a corollary of
Thm 1 where, the right-hand sides are bimultiplicative because they are built from
characters. That is exactly what happens here — `H_odd` inherits multiplicativity from the
Legendre character `legU` and from `v`, `resU`, while `H2` from `ε`, `ω` being homomorphisms.
Sections 6–7 then prove `hilbertSym = H_odd` and `hilbertSym = H2`, and bimultiplicativity of
the geometric symbol is naturally seen across those equalities.

**(3) Design disscussion :** Serre's `(−1)^{ε(p)}` is `(−1/p)` (Euler's criterion, Serre I.3.2 Thm 4),
so the odd formula is written with `legU p (−1)` in place of `(−1)^{ε(p)}`. For `p = 2` the
exponent lives in `ZMod 2` and `sgn : ZMod 2 → ℤˣ` converts it to a sign. I chose to define them using the
quadratic characters and sgn homomorphism since most of their properties are contained in Mathlib. This
removes the need for a long and messy formulae (from previous experience) and too many fucntions crowiding
the leancode and tactic state.
-/


/-# 4.1 THE LEGENDRE SYMBOL AS A QUADRATIC CHARACTER -/


--*Definition 4.1.1 : The legendre symbol as a quadratic character*
noncomputable def legU (p : ℕ) [Fact p.Prime] : (ZMod p)ˣ →* ℤˣ :=
  (quadraticChar (ZMod p)).toUnitHom
--*Lemma 4.1.1 : Legendre symbol of a unit equals 1 iff its a square in ℤ/p*
lemma legU_eq_one_iff (w : (ZMod p)ˣ) : legU p w = 1 ↔ IsSquare (w : ZMod p) := by
  rw [← quadraticChar_one_iff_isSquare w.ne_zero, ← Units.val_eq_one]
  unfold legU
  simp
--*Lemma 4.1.2 : Legndre symbol of a unit equals -1 iff its not a square in ℤ/p*
lemma legU_eq_neg_one_iff (w : (ZMod p)ˣ) : legU p w = -1 ↔ ¬ IsSquare (w : ZMod p) := by
  rw [← legU_eq_one_iff]
  constructor
  · intro h h1
    simp_all
  · intro h
    rcases Int.units_eq_one_or (legU p w) with h1 | h1
    solve_by_elim
    grind


/-# 4.2 EXPLICIT FORMULA OF THE HILBERT SYMBOL FOR ODD p AND ITS PROPERTIES-/


--*Definition 4.2.1 : Explicit formula of the Hilbert symbol for odd p, Serre (III.1.2, Thm 1)*
noncomputable def H_odd (a b : ℚ_[p]ˣ) : ℤˣ :=
  legU p (-1) ^ (v a * v b) * legU p (resU b) ^ v a * legU p (resU a) ^ v b
--*Lemma 4.2.1 : H_odd is symmetric*
lemma H_odd_symm (a b : ℚ_[p]ˣ) : H_odd a b = H_odd b a := by
  unfold H_odd
  rw [mul_comm (v a) (v b)]
  ac_rfl
--*Lemma 4.2.2 : Multiplicativity in the first entry*
lemma H_odd_mul_left (a a' b : ℚ_[p]ˣ) : H_odd (a * a') b = H_odd a b * H_odd a' b := by
  unfold H_odd
  simp only [v_mul, resU_mul, map_mul, add_mul]
  have h1 : legU p (-1) ^ (v a * v b + v a' * v b)
  = legU p (-1) ^ (v a * v b) * legU p (-1) ^ (v a' * v b) := zpow_add _ _ _
  have h2 : legU p (resU b) ^ (v a + v a')
  = legU p (resU b) ^ v a * legU p (resU b) ^ v a' := zpow_add _ _ _
  have h3 : (legU p (resU a) * legU p (resU a')) ^ v b
  = legU p (resU a) ^ v b * legU p (resU a') ^ v b := mul_zpow _ _ _
  rw [h1, h2, h3]
  ac_rfl
--*Lemma 4.2.3 : Multiplicativity in the second entry*
lemma H_odd_mul_right (a b b' : ℚ_[p]ˣ) : H_odd a (b * b') = H_odd a b * H_odd a b' := by
  rw [H_odd_symm, H_odd_mul_left, H_odd_symm b a, H_odd_symm b' a]
--*Lemma 4.2.4 : H_odd is bimultiplicative*
lemma H_odd_isSqBimult : IsSqBimult (H_odd (p := p)) := ⟨H_odd_mul_left, H_odd_mul_right⟩
--*Lemma 4.2.5 : Square invariance on the left*
lemma H_odd_sq_left (a c b : ℚ_[p]ˣ) : H_odd (a * c ^ 2) b = H_odd a b :=
H_odd_isSqBimult.sq_invariance_left a b c
--*Lemma 4.2.6 : Square invariance on the right*
lemma H_odd_sq_right (a b c : ℚ_[p]ˣ) : H_odd a (b * c ^ 2) = H_odd a b :=
H_odd_isSqBimult.sq_invariance_right a b c


/-# 4.3 RESIDUES MOD 4 AND 8 AND SOME MACHINERY FOR THE p = 2 CASE  -/


--*Definition 4.3.1 : Residue mod 4 of the unit part of a 2-adic number*
noncomputable def res4 (a : ℚ_[2]ˣ) : (ZMod 4)ˣ :=
  Units.map (PadicInt.toZModPow 2).toMonoidHom (unitPart a)
--*Lemma 4.3.1 : Residue mod 4 of a 2-adic number in ℤ/4 equals the residue mod 4 of its unit part*
lemma coe_res4 (a : ℚ_[2]ˣ) :
((res4 a : (ZMod 4)ˣ) : ZMod 4) = PadicInt.toZModPow 2 (unitPart a : ℤ_[2]) := rfl
--*Lemma 4.3.2 : Residue mod 4 multiplicaivity*
lemma res4_mul (a b : ℚ_[2]ˣ) : res4 (a * b) = res4 a * res4 b := by
  unfold res4
  rw [unitPart_mul, map_mul]
--*Definition 4.3.2 : Residue mod 8 of the unit part of a 2-adic number*
noncomputable def res8 (a : ℚ_[2]ˣ) : (ZMod 8)ˣ :=
  Units.map (PadicInt.toZModPow 3).toMonoidHom (unitPart a)
--*Lemma 4.3.3 : Residue mod 8 of a 2-adic number in ℤ/4 equals the residue mod 8 of its unit part*
lemma coe_res8 (a : ℚ_[2]ˣ) :
((res8 a : (ZMod 8)ˣ) : ZMod 8) = PadicInt.toZModPow 3 (unitPart a : ℤ_[2]) := rfl
--*Lemma 4.3.4 : Residue mod 8 multiplicaivity*
lemma res8_mul (a b : ℚ_[2]ˣ) : res8 (a * b) = res8 a * res8 b := by
  unfold res8
  rw [unitPart_mul, map_mul]

--*Definition 4.3.3 :  ε(a) = 0 ↔ u_a ≡ 1 (mod 4)*
noncomputable def eps2 (a : ℚ_[2]ˣ) : ZMod 2 := if res4 a = 1 then 0 else 1
--*Lemma 4.3.5 : ε is a homomorphism (Serre III.1.2)*
lemma eps2_hom : ∀ u v : (ZMod 4)ˣ,
(if u * v = 1 then (0 : ZMod 2) else 1)
= (if u = 1 then (0 : ZMod 2) else 1)
+ (if v = 1 then 0 else 1) := by decide
--*Lemma 4.3.6 : ε is multiplicative*
lemma eps2_mul (a b : ℚ_[2]ˣ) : eps2 (a * b) = eps2 a + eps2 b := by
  unfold eps2
  rw [res4_mul]
  exact eps2_hom (res4 a) (res4 b)
--*Definition 4.3.4 : ω(a) = 0 ↔ u_a ≡ ±1 (mod 8)*
noncomputable def omg2 (a : ℚ_[2]ˣ) : ZMod 2 :=
  if res8 a = 1 ∨ res8 a = -1 then 0 else 1
--*Lemma 4.3.6 : ω is a homomorphism (Serre III.1.2)*
lemma omg2_hom : ∀ u v : (ZMod 8)ˣ,
(if u * v = 1 ∨ u * v = -1 then (0 : ZMod 2) else 1)
= (if u = 1 ∨ u = -1 then (0 : ZMod 2) else 1)
+ (if v = 1 ∨ v = -1 then (0 : ZMod 2) else 1) := by decide
--*Lemma 4.3.7 : ω is multiplicative*
lemma omg2_mul (a b : ℚ_[2]ˣ) : omg2 (a * b) = omg2 a + omg2 b := by
  unfold omg2
  rw [res8_mul]
  exact omg2_hom (res8 a) (res8 b)

--*Definition 4.3.5 : The sgn homomorphism*
def sgn : ZMod 2 → ℤˣ := fun t => if t = 0 then 1 else -1
--*Lemma 4.3.8 : Change of operation (sanity check)*
lemma sgn_add_to_mul : ∀ s t : ZMod 2, sgn (s + t) = sgn s * sgn t := by decide


/-# 4.4 EXPLICIT FORMULA OF THE HILBERT SYMBOL FOR p = 2 AND ITS PROPERTIES-/


--*Definition 4.4.1 : Explicit formula of the Hilbert symbol for p = 2, Serre (III.1.2, Thm 1)*
noncomputable def H2 (a b : ℚ_[2]ˣ) : ℤˣ :=
sgn (eps2 a * eps2 b + (v a : ZMod 2) * omg2 b + (v b : ZMod 2) * omg2 a)
--*Lemma 4.4.1 : H2 is symmetric*
lemma H2_symm (a b : ℚ_[2]ˣ) : H2 a b = H2 b a := by
  unfold H2
  congr 1
  ring
--*Lemma 4.4.2 : Multiplicativity in the first entry*
lemma H2_mul_left (a a' b : ℚ_[2]ˣ) : H2 (a * a') b = H2 a b * H2 a' b := by
  unfold H2
  rw [← sgn_add_to_mul]
  congr 1
  rw [eps2_mul, omg2_mul, v_mul]
  grind
--*Lemma 4.4.3 : Multiplicativity in the second entry*
lemma H2_mul_right (a b b' : ℚ_[2]ˣ) : H2 a (b * b') = H2 a b * H2 a b' := by
  grind only [H2_symm, H2_mul_left]
--*Lemma 4.4.4 : H2 is bimultiplicative*
lemma H2_isSqBimult : IsSqBimult H2 := ⟨H2_mul_left, H2_mul_right⟩
--*Lemma 4.4.5 : Square invariance on the left*
lemma H2_sq_left (a c b : ℚ_[2]ˣ) : H2 (a * c ^ 2) b = H2 a b :=
H2_isSqBimult.sq_invariance_left a b c
--*Lemma 4.4.6 : Square invariance on the right*
lemma H2_sq_right (a b c : ℚ_[2]ˣ) : H2 a (b * c ^ 2) = H2 a b :=
H2_isSqBimult.sq_invariance_right a b c


/-# SECTION 5 : FINAL MACHINERY FOR THE PROOF — RESIDUES, HENSEL'S LEMMA, PRIMITIVE SOLUTIONS -/
/-
**(1) What this section does :** This section aims to bridge any gaps when proving the equivalence
of the Hilbert Symbol with respect to solvability of `z² = ax² + by²` and the explicit formulae with
respect to finite residues. We achieve this in sections :
1) The reduction map `ℤ_p → ℤ/p` (and `ℤ/pⁿ`) against divisibility and the norm → Section 5.1
2) Hensel's lemma for `X² − u` (Serre II.2.2, Thm 1) → Scetion 5.2
3) Its consequences - a unit is a square iff its residue is (`p ≠ 2`, Serre II.3.3 Thm 3) and
   `u ≡ 1 (mod 8)` implies `u` is a square (`p = 2`, Serre II.3.3 Thm 4) → Section 5.3
4) The units case `z² = ux² + vy²` for `p ≠ 2` (Serre III.1.2, case (i)) → Section 5.4
5) From a `ℚ_p`-solution to a primitive `ℤ_p` solution and back → Section 5.5

**(2) Why we need it :** The formulas of Section 4 are residue computations while the actual symbol
is a statement about `ℚ_p`. Every `⟸` direction in Sections 6–7 builds a `ℚ_p`solution from the
explicit formula and which can only be done using Hensel's lemma. Every `⟹` direction reduces a
supposed solution mod `p` or mod `8`, which needs the primitive solution lemma in Section 5.5 and the
reduction map in Section 5.1.

**(3) Design disscussion :** Serre takes a primitive solution in `ℤ_p` (not all
divisible by `p`). We instead divide a solution by its coordinate of largest norm which becomes `1`.
-/


/- # 5.1 THE REDUCTION MAP AND THE NORM -/


--*Lemma 5.1.1 : The kernel of the reduction map from ℤ_p is the ideal generated by p*
lemma to_ZMod_eq_zero (x : ℤ_[p]) : PadicInt.toZMod x = 0 ↔ (p : ℤ_[p]) ∣ x := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton]
--*Lemma 5.1.2 : The norm of a p-adic integer is strictly less than 1 if it lies in the kernel*
lemma norm_of_int_to_ZMod_eq_zero {x : ℤ_[p]} (h : PadicInt.toZMod x = 0) : ‖x‖ < 1 := by
  grind only [to_ZMod_eq_zero, PadicInt.norm_lt_one_iff_dvd]
--*Lemma 5.1.3 : The norm of a p-adic integer is equal to 1 if it does not lie in the kenerl*
lemma norm_of_int_to_ZMod_neq_zero {x : ℤ_[p]} (h : PadicInt.toZMod x ≠ 0) : ‖x‖ = 1 := by
  rcases (PadicInt.norm_le_one x).lt_or_eq with hlt | heq
  grind only [to_ZMod_eq_zero, PadicInt.norm_lt_one_iff_dvd]
  grind
--*Lemma 5.1.4 : P-adic integer units have nonzero residues*
lemma to_ZMod_units (u : ℤ_[p]ˣ) : PadicInt.toZMod (u : ℤ_[p]) ≠ 0 := by
  intro h
  apply PadicInt.zmodRepr_units_ne_zero u
  grind only [PadicInt.zmodRepr_eq_zero_iff_dvd, to_ZMod_eq_zero]
--*Lemma 5.1.5 : The reduction map mod p is surjective*
lemma to_ZMod_surj (a : ZMod p) : ∃ b : ℤ_[p], PadicInt.toZMod b = a := ⟨a.val, by simp⟩
--*Lemma 5.1.6 : Equivalence of residues of p-adic integers mod pⁿ*
lemma toZModPow_eq (n : ℕ) (x y : ℤ_[p]) :
PadicInt.toZModPow n x = PadicInt.toZModPow n y ↔ (p : ℤ_[p]) ^ n ∣ x - y := by
  rw[← sub_eq_zero, ← map_sub, ← RingHom.mem_ker, PadicInt.ker_toZModPow, Ideal.mem_span_singleton]
--*Lemma 5.1.7: The residue of 2 is nonzero*
lemma two_neq_zero_ZMod (hp : Odd p) : (2 : ZMod p) ≠ 0 := by
  have h : p ≠ 2 := by
    grind
  apply Ring.two_ne_zero
  grind only [= Nat.odd_iff, ringChar.eq]
--*Lemma 5.1.6 : The reduction map mod pⁿ is surjective*
lemma to_ZModPow_surj (n : ℕ) (c : ZMod (p ^ n)) : ∃ a : ℤ_[p], PadicInt.toZModPow n a = c := ⟨c.val, by simp⟩

/-# 5.2 HENSEL'S LEMMA X² - u (Serre II.2.2, Thm 1)-/


--*Lemma 5.2.1 : Hensel's lemma for square roots*
lemma exists_sq_eq_of_norm_lt (u a : ℤ_[p]) (h : ‖a ^ 2 - u‖ < ‖2 * a‖ ^ 2) :
∃ z : ℤ_[p], z ^ 2 = u := by
  set F : Polynomial ℤ_[p] := Polynomial.X ^ 2 - Polynomial.C u with hF
  have hFa : Polynomial.aeval a F = a^2 - u := by
    simp only [Polynomial.aeval_sub, Polynomial.coe_aeval_eq_eval, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.aeval_C, Algebra.algebraMap_self, RingHom.id_apply, hF]
  have hF'a : Polynomial.aeval a (Polynomial.derivative F) = 2 * a := by
    rw[hF, Polynomial.derivative_sub, Polynomial.derivative_C, sub_zero, Polynomial.derivative_X_sq ]
    simp only [Polynomial.coe_aeval_eq_eval, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X]
  have hnorm : ‖(Polynomial.aeval a) F‖ < ‖(Polynomial.aeval a) (Polynomial.derivative F)‖ ^ 2 := by
    rw[hFa, hF'a]
    exact h
  obtain ⟨ z, hz, _, _, _ ⟩ := hensels_lemma hnorm
  have hFz : Polynomial.aeval z F = z^2 - u := by
    simp[hF]
  rw[hFz, sub_eq_zero] at hz
  exact ⟨ z, hz ⟩


/-# 5.3 SQUARES IN ℤ_p WITH RESPECT TO RESIDUES (Serre II.3.3, Thms 3–4)-/


--*Lemma 5.3.1 : For an odd prime p, a unit in ℤ_pˣ is a square iff its residue mod p is a square*
lemma isSquare_iff_isSquare_toZMod (hp : Odd p) (u : ℤ_[p]ˣ) :
IsSquare (u : ℤ_[p]) ↔ IsSquare (PadicInt.toZMod (u : ℤ_[p])) := by
  constructor
  · rintro ⟨ s , hs ⟩
    refine ⟨ PadicInt.toZMod s , ?_ ⟩
    rw[hs, map_mul]
  · rintro ⟨ c , hc ⟩
    obtain ⟨ a , ha ⟩ := to_ZMod_surj c
    have hc0 : c ≠ 0 := by
      grind only [to_ZMod_units]
    have h1 : ‖a ^ 2 - (u : ℤ_[p])‖ < 1 := by
      apply norm_of_int_to_ZMod_eq_zero
      grind only [= map_sub, = map_pow]
    have h2 : ‖2 * a‖ = 1 := by
      apply norm_of_int_to_ZMod_neq_zero
      rw[map_mul, ha, map_ofNat PadicInt.toZMod 2]
      exact mul_ne_zero (two_neq_zero_ZMod hp) hc0
    have hnorm : ‖a ^ 2 - (u : ℤ_[p])‖ < ‖2 * a‖ ^ 2 := by
      simp only [one_pow, h2, h1]
    obtain ⟨ z, hz ⟩ := exists_sq_eq_of_norm_lt (u :  ℤ_[p]ˣ) a hnorm
    grind only [IsSquare.sq]
--*Lemma 5.3.2 : For p = 2, a unit in ℤ_pˣ is a square if its residue mod 8 equals 1 (Serre II.3.3, Thm 4)*
lemma isSquare_of_toZModPow_three_eq_one {u : ℤ_[2]} (h : PadicInt.toZModPow 3 u = 1) : IsSquare u := by
  have h8 : ((2 : ℕ) : ℤ_[2]) ^ 3 ∣ u - 1 := by
    rw [← toZModPow_eq, h, map_one]
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


/-# 5.4 THE UNITS CASE FOR p ≠ 2 -/


--*Lemma 5.4.1 : For u, v ∈ ℤ_p, z² = ux² + vy² has a solution with z ≠ 0 (Serre II.2.2, Cor. 2 to Thm 1)*
lemma exists_sol_of_units (hp : Odd p) (u v : ℤ_[p]ˣ) :
∃ z x y : ℤ_[p], z ≠ 0 ∧ z^2 = (u : ℤ_[p]) * x^2 + (v : ℤ_[p]) * y^2 := by
  sorry


/-# 5.5 ℚ_p SOLUTIONS AND PRIMITIVE ℤ_p SOLUTIONS -/


--*Lemma 5.5.1 : Going from a solution in ℚ_p to a solution in ℤ_p*
lemma hilbertSol_padicNum {a b : ℤ_[p]} {z x y t : ℚ_[p]} (ht : t ≠ 0)
(hz : ‖z‖ ≤ ‖t‖) (hx : ‖x‖ ≤ ‖t‖) (hy : ‖y‖ ≤ ‖t‖) (heq : z^2 = a * x^2 + b * y^2) :
∃ u v w : ℤ_[p], (u : ℚ_[p]) = z / t ∧ (v : ℚ_[p]) = x / t ∧ (w : ℚ_[p]) = y / t ∧
u ^2 = a * v^2 + b * w^2 := by sorry
--*Lemma 5.5.2 : Any ℚ_p solution gives a ℤ_p solution with coordinate 1 (Serre III.1.2, proof of Thm 1)*
lemma exists_primitive {a b : ℤ_[p]} (h : HilbertSolvable ℚ_[p] a b) :
∃ z x y : ℤ_[p], (z = 1 ∨ x = 1 ∨ y = 1) ∧ z ^ 2 = a * x ^ 2 + b * y ^ 2 := by sorry
--*Lemma 5.5.3 : A ℤ_p solution with z ≠ 0 is a ℚ_p solution*
lemma hilbertSol_of_padicInt {a b z x y : ℤ_[p]} (hz : z ≠ 0)
(h : z ^ 2 = a * x ^ 2 + b * y ^ 2) : HilbertSolvable ℚ_[p] a b := by
  refine ⟨ z, x, y, ?_, ?_ ⟩
  simp only [ne_eq, PadicInt.coe_eq_zero, not_false_eq_true, true_or, hz]
  have h1 := congrArg (fun t : ℤ_[p] => (t : ℚ_[p])) h
  push_cast at h1
  exact h1
--*Lemma 5.5.4 : Reducing the Hilbert Solvability condiition mod p*
lemma ring_hom_red {R : Type*} [CommRing R] (f : ℤ_[p] →+* R) {z x y a b : ℤ_[p]}
    (h : z ^ 2 = a * x ^ 2 + b * y ^ 2) :
    f z ^ 2 = f a * f x ^ 2 + f b * f y ^ 2 := by
  have h := congrArg f h
  grind


/-# SECTION 6 : THE EXPLICIT FORMULA FOR ODD p (Serre III.1.2, Thm 1, p ≠ 2) -/
/-
**(1) What this section does :** By Lemma 3.5.2 (hilbertSym_v_cases) it suffices to compare
`hilbertSym` and `H_odd` on the three configurations `(v a, v b) ∈ {(0,0),(1,0),(1,1)}`.
We first collect the ingredients:
1) the value of `H_odd` on each configuration → 6.1
2) `legU p (resU b) = ±1` read as "the residue of the unit part of b is / is not a square" → 6.2
3) the two geometric facts Serre's proof rests on: two units always give a solution, and
   `(p, v)` has no solution when the residue of `v` is a non-square (Definitions 2.1.1–2.1.2,
   Lemmas 2.2.1–2.2.2) → 6.3
and then run Serre's cases:
4) case (i) two units, the key case `(p, v)`, case (ii) `(1,0)` and case (iii) `(1,1)` → 6.4
5) the theorem `hilbertSym ℚ_[p] = H_odd` → 6.5

**(2) Why we need it :** With the ingredients in hand each case is a short assembly:
case (i) is "both sides are 1"; the key case `(p,v)` is the dichotomy on whether the residue of
`v` is a square (Hensel for yes, primitivity for no); case (ii) strips the unit from `a` by
Prop 2 (iii) (Lemma 2.5.3) and lands in the key case; case (iii) reduces to (ii) by Prop 2 (iv)
(Lemma 2.5.4), whose formula-side analogue is `H_odd a (−a) = 1` for `v a = 1` (Lemma 6.1.3).
-/


/-# 6.1 VALUES OF H_ODD ON THE THREE CONFIGURATIONS -/


--*Lemma 6.1.1 : Value of H_odd for two units a and b*
lemma H_odd_eq_one_v_zero {a b : ℚ_[p]ˣ} (ha : v a = 0) (hb : v b = 0) : H_odd a b = 1 := by
  simp[H_odd, ha, hb]
--*Lemma 6.1.2 : Value of H_odd for a unit a and the prime p (Serre III.1.2, case (ii))*
lemma H_odd_pU_v_zero {a : ℚ_[p]ˣ} (ha : v a = 0) : H_odd (pU p) a = legU p (resU a) := by
  simp[H_odd, v_pU, ha]
--*Lemma 6.1.3 : Value of H_odd for a and -a when v a = 1 (formula-side Prop 2 (ii))*
lemma H_odd_neg_self_v_one {a : ℚ_[p]ˣ} (ha : v a = 1) : H_odd a (-a) = 1 := by
  have hnega : v (-a) = 1 := by
    rw[v_neg, ha]
  unfold H_odd
  rw[ha, hnega, resU_neg, map_mul, resU_neg_one]
  simp only [mul_one, uzpow_one] -- simp?
  have hleg : legU p (-1) * (legU p (-1) * legU p (resU a)) * legU p (resU a)
  = (legU p (-1) * legU p (-1)) * (legU p (resU a) * legU p (resU a)) := by
    grind
  simp only [Int.units_mul_self, mul_one, hleg]
--*Lemma 6.1.4 : Value of H_odd for a and -ab when v a = 1 (formula-side Prop 2 (iv))*
lemma H_odd_neg_mul_v_one {a : ℚ_[p]ˣ} (ha : v a = 1) (b : ℚ_[p]ˣ) : H_odd a (-a * b) = H_odd a b := by
  rw[H_odd_mul_right, H_odd_neg_self_v_one ha, one_mul]


/-# 6.2 THE LEGENDRE SYMBOL OF THE UNIT PART -/


--*Lemma 6.2.1 : Legendre symbol equals 1 iff the residue of the unit part is a square mod p*
lemma legU_resU_eq_one (a : ℚ_[p]ˣ) : legU p (resU a) = 1
↔ IsSquare (PadicInt.toZMod (unitPart a : ℤ_[p])) := by
  rw[legU_eq_one_iff, coe_resU]
--*Lemma 6.2.2 : Legendre symbol equals -1 iff the residue of the unit part is not a square mod p*
lemma legU_resU_eq_neg_one (a : ℚ_[p]ˣ) : legU p (resU a) = -1
↔ ¬ IsSquare (PadicInt.toZMod (unitPart a : ℤ_[p])) := by
  rw[legU_eq_neg_one_iff, coe_resU]


/-# 6.3 THE GEOMETRIC SIDE : TWO UNITS, AND (p, v) FOR A NON-RESIDUE v -/


--*Lemma 6.3.1 : The Hilbert symbol of two units equals 1 (Serre III.1.2, case (i))*
lemma hilbertSym_eq_one_of_v_zero (hp : Odd p) {a b : ℚ_[p]ˣ} (ha : v a = 0) (hb : v b = 0) :
HilbertSym ℚ_[p] a b = 1 := by
  rw [hilbertSym_eq_one_iff]
  obtain ⟨z, x, y, hz, heq⟩ := exists_sol_of_units hp (unitPart a) (unitPart b)
  have h := hilbertSol_of_padicInt hz heq
  rwa [unitPart_of_v_eq_zero ha, unitPart_of_v_eq_zero hb] at h
--*Lemma 6.3.2 : z² = p x² + w y² is not solvable when the residue of w is a non-square (Serre III.1.2, case (ii), the primitivity argument)*
lemma not_hilbertSolvable_p_of_not_isSquare {w : ℤ_[p]} (h : ¬ IsSquare (PadicInt.toZMod w)) :
¬ HilbertSolvable ℚ_[p] ((p : ℤ_[p]) : ℚ_[p]) w := by sorry


/-# 6.4 SERRE'S CASES FOR ODD p -/


--*Lemma 6.4.1 : Case (i) — two units, (v a, v b) = (0,0)*
lemma hilbertSym_eq_H_odd_v_zero (hp : Odd p) {a b : ℚ_[p]ˣ} (ha : v a = 0) (hb : v b = 0) :
HilbertSym ℚ_[p] a b = H_odd a b := by
  rw[hilbertSym_eq_one_of_v_zero hp ha hb, H_odd_eq_one_v_zero ha hb]
--*Lemma 6.4.2 : The key case (p, v) — split on whether the residue of v is a square*
lemma hilbertSym_pU_eq_H_odd (hp : Odd p) {a : ℚ_[p]ˣ} (ha : v a = 0) :
HilbertSym ℚ_[p] (pU p) a = H_odd (pU p) a := by
  rw[H_odd_pU_v_zero ha]
  by_cases hsq : IsSquare (PadicInt.toZMod (unitPart a : ℤ_[p]))
  · rw[(legU_resU_eq_one a).mpr hsq, hilbertSym_eq_one_iff ] --case that v is a sq so symbol is 1
    obtain ⟨ s, hs ⟩ := (isSquare_iff_isSquare_toZMod hp (unitPart a)).mpr hsq
    refine ⟨(s : ℚ_[p]), 0, 1, Or.inr (Or.inr one_ne_zero), ?_⟩
    rw [← unitPart_of_v_eq_zero ha, hs]
    push_cast
    ring
  · rw [(legU_resU_eq_neg_one a).mpr hsq, hilbertSym_eq_neg_one_iff, coe_pU, ← PadicInt.coe_natCast, ← unitPart_of_v_eq_zero ha]
    exact not_hilbertSolvable_p_of_not_isSquare hsq
--*Lemma 6.4.3 : Case (ii) — (v a, v b) = (1,0); a = u·p with u a unit, stripped by Prop 2 (iii)*
lemma hilbertSym_eq_H_odd_v_one_and_zero (hp : Odd p) {a b : ℚ_[p]ˣ} (ha : v a = 1) (hb : v b = 0) :
HilbertSym ℚ_[p] a b = H_odd a b := by
  have h : v ((pU p)⁻¹ * a) = 0 := by
    rw[v_mul, v_inv, v_pU, ha]
    norm_num
  have hdecomp : (pU p)⁻¹ * a * (pU p) = a := by
    simp only [inv_mul_cancel_comm]
  rw[← hdecomp, hilbertSym_eq_one_cancel (h := hilbertSym_eq_one_of_v_zero hp h hb),
  H_odd_mul_left, H_odd_eq_one_v_zero h hb, one_mul]
  exact hilbertSym_pU_eq_H_odd hp hb
--*Lemma 6.4.4 : Case (iii) — (v a, v b) = (1,1); (a,b) = (a,−ab) by Prop 2 (iv), −ab = c·p² with c a unit*
lemma hilbertSym_eq_H_odd_v_one (hp : Odd p) {a b : ℚ_[p]ˣ} (ha : v a = 1) (hb : v b = 1) :
HilbertSym ℚ_[p] a b = H_odd a b := by
  have h : -a * b = (-( a * b) * (pU p^2)⁻¹) * pU p^2 := by
    rw[neg_mul, inv_mul_cancel_right]
  have hval : v (-( a * b) * (pU p^2)⁻¹) = 0 := by
    rw[v_mul, v_neg, v_mul, v_inv, v_pow, v_pU, ha , hb ]
    norm_num
  rw[← hilbertSym_eq_neg_one_cancel, ← H_odd_neg_mul_v_one ha b, h, hilbertSym_sq_inv_right, H_odd_sq_right]
  exact hilbertSym_eq_H_odd_v_one_and_zero hp ha hval


/-# 6.5 THE EXPLICIT FORMULA FOR ODD p -/


--*Theorem 6.5.1 : hilbertSym = H_odd for odd p (Serre III.1.2, Thm 1, p ≠ 2)*
theorem hilbertSym_eq_odd (hp : Odd p ) : HilbertSym ℚ_[p] = H_odd :=  by
  refine hilbertSym_v_cases H_odd H_odd_symm H_odd_sq_left ?_ ?_ ?_
  · intro a b ha hb
    exact hilbertSym_eq_H_odd_v_zero hp ha hb
  · intro a b ha hb
    exact hilbertSym_eq_H_odd_v_one_and_zero hp ha hb
  · intro a b ha hb
    exact hilbertSym_eq_H_odd_v_one hp ha hb


/-# SECTION 7 : THE EXPLICIT FORMULA FOR p = 2 (Serre III.1.2, Thm 1, p = 2) -/
/-
**(1) What this section does :** At `p = 2` a unit is determined up to squares by its residue
in `(ℤ/8)ˣ = {1,3,5,7}`, which `H2` reads through `ε` (mod 4) and `ω` (mod 8). Ingredients:
1) express `eps2`/`omg2` as functions `e`/`w` of `res8` → 7.1
2) compute the residues of `−1` and prove `H2 a (−a) = 1` for `v a = 1` (formula-side Prop 2 (iv))
   → 7.2
3) convert residue data mod 8 into solutions and non-solutions → 7.3
4) state Serre's case table over `(ℤ/8)ˣ × (ℤ/8)ˣ` and let `decide` verify it → 7.4
then Serre's cases:
5) the three configurations `(0,0)`, `(1,0)`, `(1,1)` → 7.5
6) the theorem `hilbertSym ℚ_[2] = H2` → 7.6

**(2) Why we need it :** Serre's proof at `p = 2` is a table: for each residue pattern either an
explicit witness `≡ 1 (mod 8)` (a square by Lemma 5.3.2) or a congruence obstruction mod 4 or
mod 8. `e`/`w` exist because `decide` needs a statement over a finite type; `eps2`/`omg2` take
a 2-adic unit and cannot appear in it. Once the table is checked, cases (0,0) and (1,0) are
assembly (the table already contains Serre's combination of `(2,v)` and `(u,v)`), and case
(1,1) reduces to (1,0) exactly as for odd p.
-/


/-# 7.1 ε AND ω AS FUNCTIONS OF THE RESIDUE MOD 8 -/


--*Definition 7.1.1 : The function epsilon on (ℤ/8)ˣ*
def e (r : (ZMod 8)ˣ) : ZMod 2 := if ((r : ZMod 8).cast : ZMod 4) = 1 then 0 else 1
--*Definition 7.1.2 : The function omega on (ℤ/8)ˣ*
def w (r : (ZMod 8)ˣ) : ZMod 2 := if r = 1 ∨ r = -1 then 0 else 1
--*Lemma 7.1.1 : res4 is the reduction mod 4 of res8*
lemma res4_eq_one (a : ℚ_[2]ˣ) : res4 a = 1 ↔ ((res8 a : ZMod 8).cast : ZMod 4) = 1 := by
  rw[← Units.val_eq_one, coe_res4, coe_res8, PadicInt.cast_toZModPow 2 3 (by norm_num)]
--*Lemma 7.1.2 : Value of epsilon at a 2-adic number*
lemma eps2_eq_e (a : ℚ_[2]ˣ) : eps2 a = e (res8 a) := by
  grind only [e, eps2, res4_eq_one]
--*Lemma 7.1.3 : Value of omega at a 2-adic number*
lemma omg2_eq_w (a : ℚ_[2]ˣ) : omg2 a = w (res8 a) := by
  rfl


/-# 7.2 THE RESIDUES OF -1 -/


--*Lemma 7.2.1 : Residue mod 4 of -1*
lemma res4_neg_one : res4 (-1 : ℚ_[2]ˣ) = -1 := by
  apply Units.ext
  simp[res4, unitPart_neg_one]
--*Lemma 7.2.2 : Residue mod 8 of -1*
lemma res8_neg_one : res8 (-1 : ℚ_[2]ˣ) = -1 := by
  apply Units.ext
  simp[res8, unitPart_neg_one]
--*Lemma 7.2.3 : Value of epsilon at -1*
lemma eps2_neg_one : eps2 (-1 : ℚ_[2]ˣ) = 1 := by
  rw[eps2, res4_neg_one]
  decide
--*Lemma 7.2.4 : Value of omega at -1*
lemma omg2_neg_one : omg2 (-1 : ℚ_[2]ˣ) = 0:= by
  rw[omg2, res8_neg_one]
  decide
--*Lemma 7.2.5 : Value of H2 at a and -a for v a = 1 (formula-side Prop 2 (ii))*
lemma H2_neg_self_v_one {a : ℚ_[2]ˣ} (ha : v a = 1) : H2 a (-a) = 1 := by
  have hnega : v (-a) = 1 := by
    rw[v_neg, ha]
  have he : eps2 (-a) = 1 + eps2 a := by
    rw[← neg_one_mul, eps2_mul, eps2_neg_one]
  have hw : omg2 (-a) = omg2 a := by
    rw[← neg_one_mul, omg2_mul, omg2_neg_one, zero_add]
  unfold H2
  rw[ha, hnega, he, hw]
  simp only [Int.cast_one, one_mul]
  have h : eps2 a * (1 + eps2 a) + omg2 a + omg2 a = 0 := by
    grind only [eps2, #3649]
  grind only [sgn]
--*Lemma 7.2.6 : Value of H2 at a and -ab for v a = 1 (formula-side Prop 2 (iv))*
lemma H2_neg_mul_v_one {a : ℚ_[2]ˣ} (ha : v a = 1) (b : ℚ_[2]ˣ) : H2 a (-a * b) = H2 a b := by
  rw[H2_mul_right, H2_neg_self_v_one ha, one_mul]


/-# 7.3 FROM RESIDUES MOD 8 TO SOLUTIONS, AND BACK -/


--*Lemma 7.3.1 : A value ≡ 1 mod 8 of the form a x² + b y² is a square, hence a solution*
lemma hilbertSol_of_res_1 {a b x y : ℤ_[2]}
(h : PadicInt.toZModPow 3 ( a * x ^ 2 + b * y ^ 2) = 1 ): HilbertSolvable ℚ_[2] a b := by
  obtain ⟨z, hz⟩ := isSquare_of_toZModPow_three_eq_one h
  have hz0 : z ≠ 0 := by
    intro hz0
    grind
  have heq : z ^ 2 = a * x ^ 2 + b * y ^ 2 := by
    rw [sq]
    exact hz.symm
  exact hilbertSol_of_padicInt hz0 heq
--*Lemma 7.3.2 : No primitive residue solution mod 8 means not Hilbert solvable*
lemma not_hilbertSol_of_res {a b : ℤ_[2]} (h : ∀ z x y : ZMod 8,
(z = 1 ∨ x = 1 ∨ y = 1) → z ^ 2 ≠ PadicInt.toZModPow 3 a * x ^ 2 + PadicInt.toZModPow 3 b * y ^ 2) :
¬ HilbertSolvable ℚ_[2] a b := by
  intro hsol
  obtain ⟨z, x, y, hprim, heq⟩ := exists_primitive hsol
  refine h _ _ _ ?_ (ring_hom_red (PadicInt.toZModPow 3) heq)
  rcases hprim with h1 | h1 | h1
  · left; rw [h1, map_one]
  · right; left; rw [h1, map_one]
  · right; right; rw [h1, map_one]
--*Lemma 7.3.3 : An element of valuation 1 is 2 × (its unit part)*
lemma coeff_eq_two_mul_unitPart {a : ℚ_[2]ˣ} (ha : v a = 1) :
(a : ℚ_[2]) = ((2 * (unitPart a : ℤ_[2]) : ℤ_[2]) : ℚ_[2]) := by
  have h := unitPart_of_v_eq_one ha
  rw [eq_div_iff (by norm_num)] at h
  push_cast
  rw [← h]
  push_cast
  ring_nf
  rfl


/-# 7.4 SERRE'S CASE TABLE -/


--*Lemma 7.4.1 : Two units, (u,v) = (−1)^{ε(u)ε(v)} (Serre III.1.2, case (i) at p = 2)*
lemma hilbert_two_units : ∀ r s : (ZMod 8)ˣ, (sgn (e r * e s) = 1 →
∃ x y : ZMod 8, (r : ZMod 8) * x ^ 2 + (s : ZMod 8) * y ^ 2 = 1) ∧ (sgn (e r * e s) = -1 →
∀ z x y : ZMod 8, (z = 1 ∨ x = 1 ∨ y = 1) → z ^ 2 ≠ (r : ZMod 8) * x ^ 2 + (s : ZMod 8) * y ^ 2) := by decide
--*Lemma 7.4.2 : (2u, v) = (−1)^{ε(u)ε(v) + ω(v)} (Serre III.1.2, case (ii) at p = 2)*
lemma hilbert_two_pU : ∀ r s : (ZMod 8)ˣ, (sgn (e r * e s + w s) = 1 →
∃ x y : ZMod 8, 2 * (r : ZMod 8) * x ^ 2 + (s : ZMod 8) * y ^ 2 = 1) ∧ (sgn (e r * e s + w s) = -1 →
∀ z x y : ZMod 8, (z = 1 ∨ x = 1 ∨ y = 1) →
z ^ 2 ≠ 2 * (r : ZMod 8) * x ^ 2 + (s : ZMod 8) * y ^ 2) := by decide


/-# 7.5 SERRE'S CASES FOR p = 2 -/


--*Lemma 7.5.1 : Two units, (v a, v b) = (0,0)*
lemma hilbertSym_eq_H2_v_zero {a b : ℚ_[2]ˣ} (ha : v a = 0) (hb : v b = 0) :
HilbertSym ℚ_[2] a b = H2 a b := by
  have h : H2 a b = sgn (e (res8 a) * e (res8 b)) := by
    simp[H2, eps2_eq_e, omg2_eq_w, ha, hb]
  have h' : HilbertSolvable ℚ_[2] a b ↔
  HilbertSolvable ℚ_[2] (unitPart a : ℤ_[2]) (unitPart b : ℤ_[2]) := by
    rw[unitPart_of_v_eq_zero ha, unitPart_of_v_eq_zero hb]
  obtain ⟨h1, h2⟩ := hilbert_two_units (res8 a) (res8 b)
  rw[h]
  rcases Int.units_eq_one_or (sgn (e (res8 a) * e (res8 b))) with hx | hy
  · rw [hx, hilbertSym_eq_one_iff, h']
    obtain ⟨x, y, hxy⟩ := h1 hx
    obtain ⟨u, hu⟩ := to_ZModPow_surj (p := 2) 3 x
    obtain ⟨v, hv⟩ := to_ZModPow_surj (p := 2) 3 y
    apply hilbertSol_of_res_1 (x := u) (y := v)
    simp only [map_add, map_mul, map_pow, hu, hv, ← coe_res8]
    exact hxy
  · rw [hy, hilbertSym_eq_neg_one_iff, h']
    apply not_hilbertSol_of_res
    simp only[← coe_res8]
    exact h2 hy
--*Lemma 7.5.2 : (v a, v b) = (1,0); a = 2·(unit part), handled by the table 7.4.2*
lemma hilbertSym_eq_H2_v_one_and_zero {a b : ℚ_[2]ˣ} (ha : v a = 1) (hb : v b = 0) :
HilbertSym ℚ_[2] a b = H2 a b := by
  have h : H2 a b = sgn (e (res8 a) * e (res8 b) + w (res8 b)) := by
    simp[H2, eps2_eq_e, omg2_eq_w, ha, hb]
  have h' : HilbertSolvable ℚ_[2] a b ↔
  HilbertSolvable ℚ_[2] (2 * (unitPart a : ℤ_[2]) : ℤ_[2]) (unitPart b : ℤ_[2]) := by
    rw[← coeff_eq_two_mul_unitPart ha, unitPart_of_v_eq_zero hb]
  obtain ⟨h1, h2⟩ := hilbert_two_pU (res8 a) (res8 b)
  rw[h]
  rcases Int.units_eq_one_or (sgn (e (res8 a) * e (res8 b) + w (res8 b))) with hx | hy
  · rw [hx, hilbertSym_eq_one_iff, h']
    obtain ⟨x, y, hxy⟩ := h1 hx
    obtain ⟨u, hu⟩ := to_ZModPow_surj (p := 2) 3 x
    obtain ⟨v, hv⟩ := to_ZModPow_surj (p := 2) 3 y
    apply hilbertSol_of_res_1 (x := u) (y := v)
    simp only [map_add, map_mul, map_pow, map_ofNat, hu, hv, ← coe_res8]
    exact hxy
  · rw [hy, hilbertSym_eq_neg_one_iff, h']
    apply not_hilbertSol_of_res
    simp only[map_mul, map_ofNat, ← coe_res8]
    exact h2 hy
--*Lemma 7.5.3 : (v a, v b) = (1,1); (a,b) = (a,−ab) by Prop 2 (iv), −ab = c·2² with c a unit*
lemma hilbertSym_eq_H2_v_one {a b : ℚ_[2]ˣ} (ha : v a = 1) (hb : v b = 1) :
    HilbertSym ℚ_[2] a b = H2 a b := by
  have h : -a * b = (-(a * b) * (pU 2 ^ 2)⁻¹) * pU 2 ^ 2 := by
    simp only [neg_mul, inv_mul_cancel_right]
  have hval : v (-(a * b) * (pU 2 ^ 2)⁻¹) = 0 := by
    rw [v_mul, v_neg, v_mul, v_inv, v_pow, v_pU, ha, hb]
    norm_num
  rw [← hilbertSym_eq_neg_one_cancel (a := a) (b := b), ← H2_neg_mul_v_one ha b, h,
    hilbertSym_sq_inv_right, H2_sq_right]
  exact hilbertSym_eq_H2_v_one_and_zero ha hval


/-# 7.6 THE EXPLICIT FORMULA FOR p = 2 -/


--*Theorem 7.6.1 : hilbertSym = H2 (Serre III.1.2, Thm 1, p = 2)*
theorem hilbertSym_eq_2 : HilbertSym ℚ_[2] = H2 := by
  refine hilbertSym_v_cases H2 H2_symm H2_sq_left ?_ ?_ ?_
  · intro a b ha hb
    exact hilbertSym_eq_H2_v_zero ha hb
  · intro a b ha hb
    exact hilbertSym_eq_H2_v_one_and_zero ha hb
  · intro a b ha hb
    exact hilbertSym_eq_H2_v_one ha hb


/-# SECTION 8 : BILINEARITY OF THE HILBERT SYMBOL (Serre III.1.2, Thm 2) -/
/-
**(1) What this section does :** It combines Theorems 6.5.1 and 7.6.1: for every prime `p`
the Hilbert symbol agrees with its respective explicit formula, and the formulas are bimultiplicative
(Lemmas 4.5.3, 4.6.3).
1) `hilbertSym ℚ_[p]` is bimultiplicative → Section 8.1
2) Existence of the bilinear map `ℚ_pˣ/(ℚ_pˣ)² × ℚ_pˣ/(ℚ_pˣ)² → {±1}` → 8.2.

**(2) Why we need it :** This is the goal of the file. Serre states Thm 2 as "the Hilbert symbol
is a nondegenerate bilinear form on the 𝔽₂-vector space `kˣ/kˣ²`"; bilinearity is exactly
`hilbertSym_bimult` while the `hilbertPairing` is the Bilinear form itself more on Section 1 which
explains why this monoid homomorphism is the right formalisation of an 𝔽₂-bilinear form. Bilinearity cannot be
proved at the level of a general field i.e over `ℚ` which is why it is deduced from the local formulas
rather than the definition.
-/


/-# 8.1 THEOREM: BIMULTIPLICATIVITY OF THE HILBERT SYMBOL AT THE p-ADIC PLACE-/
/-
*Note to Readers*
We show Bimultiplicativity for the p-adic place, followed by the real (infinite) place in Section 9.

*General formulation of the proof of bimultiplicativity*
We combine Lemmas 4.4.4 and 4.2.4 proving bimultiplicativity of the Explicit formulas of the Hilbert Symbol for
odd p and p= 2 with Theorems 6.5.1, 7.6.1 proving equivalence between the Hilbert Symbol and its explicit formula
for odd p and p = 2
-/


--*Theorem 8.1.1 : The Hilbert symbol on ℚ_p is bimultiplicative (Serre III.1.2, Thm 2)*
theorem hilbertSym_bimult : IsSqBimult (HilbertSym ℚ_[p]) := by
  rcases Nat.even_or_odd p with ( hp | hp' )
  · have hev : Nat.Prime p := by exact Fact.out
    rw[Nat.Prime.even_iff hev ] at hp
    subst hp
    rw[hilbertSym_eq_2]
    exact H2_isSqBimult
  · rw [hilbertSym_eq_odd hp']
    exact H_odd_isSqBimult


/- # SECTION 9 :-/
