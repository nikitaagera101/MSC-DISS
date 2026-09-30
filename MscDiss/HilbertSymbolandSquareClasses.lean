import Mathlib.Tactic
import Mathlib.Analysis.Normed.Ring.Lemmas
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

/--*Definition 1.1.1 : The subgroup of squares (Kˣ)² ≤ Kˣ*--/
abbrev sqSubgroup (K : Type*) [Field K] : Subgroup Kˣ := (powMonoidHom 2 : Kˣ →* Kˣ).range

/--*Definition 1.1.2 : The square class group SqCl K = Kˣ/(Kˣ)²*--/
abbrev SqCl (K : Type*) [Field K] := Kˣ ⧸ sqSubgroup K

/--*Definition 1.1.3 : The quotient homomorphism Kˣ →* SqCl K*--/
def SqCl.mk : Kˣ →* SqCl K := QuotientGroup.mk' (sqSubgroup K)

/- # 1.2 THE 𝔽₂ STRUCTURE -/

/--*Lemma 1.2.1 : Every square class squares to 1, i.e. SqCl K has exponent 2*-/
lemma SqCl.sq_eq_one (x : SqCl K) : x ^ 2 = 1 := by
  induction x using QuotientGroup.induction_on with
  | H a =>
    rw [← QuotientGroup.mk_pow]
    refine (QuotientGroup.eq_one_iff (a ^ 2)).mpr ?_
    simp

/- # 1.3 HOMOMORPHISMS KILLING SQUARES FACTOR THROUGH THE SQUARE CLASS GROUP -/

/--*Definition 1.3.1 : Universal property — a homomorphism killing squares descends to SqCl K*--/
def SqCl.lift {M : Type*} [CommMonoid M] (f : Kˣ →* M) (hf : ∀ c : Kˣ, f (c ^ 2) = 1) :
    SqCl K →* M := by
  have h : ∀ x ∈ sqSubgroup K, f x = 1 := by
    rintro x ⟨c, rfl⟩
    exact hf c
  exact QuotientGroup.lift (sqSubgroup K) f h

/- # 1.4 BIMULTIPLICATIVE FUNCTIONS -/

/--*Definition 1.4.1 : F : Kˣ → Kˣ → ℤˣ is bimultiplicative*--/
structure IsSqBimult (F : Kˣ → Kˣ → ℤˣ) : Prop where
  mul_left : ∀ a a' b, F (a * a') b = F a b * F a' b
  mul_right : ∀ a b b', F a (b * b') = F a b * F a b'

namespace IsSqBimult

variable {F : Kˣ → Kˣ → ℤˣ}

/--*Lemma 1.4.1 : For a bimultiplicative F, F 1 a = 1*--/
lemma one_left (h : IsSqBimult F) (a : Kˣ) : F 1 a = 1 := by
  have h1 := h.mul_left 1 1 a
  rw [one_mul] at h1
  exact left_eq_mul.mp h1

/--*Lemma 1.4.2 : For a bimultiplicative F, F a 1 = 1*--/
lemma one_right (h : IsSqBimult F) (a : Kˣ) : F a 1 = 1 := by
  have h1 := h.mul_right a 1 1
  rw [one_mul] at h1
  exact left_eq_mul.mp h1

/--*Lemma 1.4.3 : For a bimultiplicative F, F (a²) b = 1*--/
lemma sq_left (h : IsSqBimult F) (a b : Kˣ) : F (a ^ 2) b = 1 := by
  rw [sq, h.mul_left, Int.units_mul_self]

/--*Lemma 1.4.4 : For a bimultiplicative F, F a (b²) = 1*--/
lemma sq_right (h : IsSqBimult F) (a b : Kˣ) : F a (b ^ 2) = 1 := by
  rw [sq, h.mul_right, Int.units_mul_self]

/--*Lemma 1.4.5 : Square invariance in the first variable, F (a c²) b = F a b*--/
lemma mul_sq_left (h : IsSqBimult F) (a b c : Kˣ) : F (a * c ^ 2) b = F a b := by
  rw [h.mul_left, h.sq_left, mul_one]

/--*Lemma 1.4.6 : Square invariance in the second variable, F a (b c²) = F a b*--/
lemma mul_sq_right (h : IsSqBimult F) (a b c : Kˣ) : F a (b * c ^ 2) = F a b := by
  rw [h.mul_right, h.sq_right, mul_one]

/- # 1.5 BUNDLING THE PAIRING -/

/--*Definition 1.5.1 : The homomorphism Kˣ →* (Kˣ →* ℤˣ) attached to F*--/
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

--*Definition 1.5.2 : The descended pairing SqCl K → (SqCl K → ℤˣ)*
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

/--*Definition 2.1.1 : The Hilbert solvability condition — z² = ax² + by² has a nontrivial solution*--/
def HilbertSolvable (K : Type*) [Field K] (a b : K) : Prop :=
  ∃ z x y : K, (z ≠ 0 ∨ x ≠ 0 ∨ y ≠ 0) ∧ z ^ 2 = a * x ^ 2 + b * y ^ 2

/--*Definition 2.1.2 : The Hilbert symbol (a,b) ∈ ℤˣ of two units of a field*--/
noncomputable def hilbertSym (K : Type*) [Field K] (a b : Kˣ) : ℤˣ := by
  classical
  exact if HilbertSolvable K a b then 1 else -1

/- # 2.2 TRANSFER LEMMAS -/

/--*Lemma 2.2.1 : The Hilbert symbol equals 1 iff the conic equation has a nontrivial solution*--/
lemma hilbertSym_eq_one_iff (a b : Kˣ) : hilbertSym K a b = 1 ↔ HilbertSolvable K a b := by
  unfold hilbertSym
  by_cases hs : HilbertSolvable K a b
  · rw [if_pos hs]
    grind
  · rw [if_neg hs]
    simp_all

/--*Lemma 2.2.2 : The Hilbert symbol equals -1 iff the conic equation has no nontrivial solution*--/
lemma hilbertSym_eq_neg_one_iff (a b : Kˣ) :
    hilbertSym K a b = -1 ↔ ¬ HilbertSolvable K a b := by
  unfold hilbertSym
  by_cases hs : HilbertSolvable K a b
  · rw [if_pos hs]
    simp_all
  · rw [if_neg hs]
    simp_all

/--*Lemma 2.2.3 : Solvability is invariant under multiplying the first entry by a square*--/
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

/--*(†) Lemma 2.3.1 : The Hilbert symbol is symmetric*--/
lemma hilbertSym_comm : hilbertSym K a b = hilbertSym K b a := by
  have h : ∀ c d : K, HilbertSolvable K c d → HilbertSolvable K d c := by
    intro c d ⟨z, x, y, hnt, heq⟩
    exact ⟨z, y, x, by grind, by grind⟩
  unfold hilbertSym
  by_cases hab : HilbertSolvable K a b
  · rw [if_pos hab, if_pos (h a b hab)]
  · rw [if_neg hab, if_neg (fun hba => hab (h b a hba))]

/--*Lemma 2.3.2 : The Hilbert symbol with 1 in the first entry equals 1*--/
lemma hilbertSym_one_left : hilbertSym K 1 a = 1 := by
  have h : HilbertSolvable K 1 a := by
    refine ⟨1, 1, 0, ?_, ?_⟩
    simp
    ring
  exact if_pos h

/--*Lemma 2.3.3 : The Hilbert symbol with 1 in the second entry equals 1*--/
lemma hilbertSym_one_right : hilbertSym K b 1 = 1 := by
  have h : HilbertSolvable K b 1 := by
    refine ⟨1, 0, 1, ?_, ?_⟩
    simp
    ring
  exact if_pos h

/--*(†) Lemma 2.3.4 : (a, −a) = 1*--/
lemma hilbertSym_neg_self : hilbertSym K a (-a) = 1 := by
  have h : HilbertSolvable K a (-a) := by
    refine ⟨0, 1, 1, ?_, ?_⟩
    simp
    ring
  exact if_pos h

/--*Lemma 2.3.5 : (a, 1 − a) = 1 for a ≠ 1*--/
lemma hilbertSym_one_sub (ha : a.val ≠ 1) :
    hilbertSym K a (Units.mk0 (1 - a) (by grind)) = 1 := by
  have h : HilbertSolvable K a (1 - a) := by
    refine ⟨1, 1, 1, ?_, ?_⟩
    simp
    ring
  exact if_pos h

/--*Lemma 2.3.6 : (a, b) = 1 whenever a is a square*--/
lemma hilbertSym_of_isSquare (ha : IsSquare a) (b : Kˣ) : hilbertSym K a b = 1 := by
  obtain ⟨c, rfl⟩ := ha
  have h : HilbertSolvable K (c * c) b := by
    refine ⟨c, 1, 0, ?_, ?_⟩
    simp
    ring
  exact if_pos h

/--*Lemma 2.3.7 : (a, a) = (a, −1)*--/
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

/--*Lemma 2.3.8 : Hilbert symbols agree when the two solvability conditions are equivalent*--/
lemma hilbertSym_congr (a b a' b' : Kˣ)
    (h : HilbertSolvable K a b ↔ HilbertSolvable K a' b') :
    hilbertSym K a b = hilbertSym K a' b' := by
  unfold hilbertSym
  grind

--*(†) Lemma 2.3.9 : Square invariance in the first entry, (a c², b) = (a, b)*--/
lemma hilbertSym_mul_sq_left (a b c : Kˣ) : hilbertSym K (a * c ^ 2) b = hilbertSym K a b := by
  grind only [hilbertSym_congr, hilbertSolvable_mul_sq]

/--*(†) Lemma 2.3.10 : Square invariance in the second entry, (a, b c²) = (a, b)*--/
lemma hilbertSym_mul_sq_right (a b c : Kˣ) :
    hilbertSym K a (b * c ^ 2) = hilbertSym K a b := by
  grind only [hilbertSym_comm, hilbertSym_mul_sq_left]


/- # 2.4 THE NORM FORM AND ITS CANCELLATION PROPERTIES -/


/--*Lemma 2.4.1 : Norm form of Definition 2.1.1 — solvable iff b is a square or a = z² − b y²*--/
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

/--*Lemma 2.4.2 : Solvability is closed under multiplication in the first entry (norms form a subgroup)*--/
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

/--*Lemma 2.4.3 : Cancellation 1 – (a,b) = 1 ⇒ (a c, b) = (c, b) (Serre Prop 2 (iii))*--/
lemma hilbertSym_mul_left_of_eq_one {a b : Kˣ} (h : hilbertSym K a b = 1) (c : Kˣ) :
    hilbertSym K (a * c) b = hilbertSym K c b := by
  rw [hilbertSym_eq_one_iff] at h
  apply hilbertSym_congr
  constructor
  · intro hac
    have h2 := hilbertSolvable_mul_left K hac h
    have h3 : a * c * a = c * a ^ 2 := by
      rw [sq, mul_comm a c, mul_assoc]
    rw [h3] at h2
    grind only [hilbertSolvable_mul_sq]
  · intro ha
    grind only [hilbertSolvable_mul_left K h ha]

/--*Lemma 2.4.4 : Cancellation 2 – (a, -a b) = (a, b) (Serre Prop 2 (iv))*--/
lemma hilbertSym_neg_self_mul {a b : Kˣ} : hilbertSym K a (-a * b) = hilbertSym K a b := by
  have h : hilbertSym K (-a) a = 1 := by
    grind only [hilbertSym_comm, hilbertSym_neg_self]
  grind only [hilbertSym_comm, hilbertSym_mul_left_of_eq_one]
