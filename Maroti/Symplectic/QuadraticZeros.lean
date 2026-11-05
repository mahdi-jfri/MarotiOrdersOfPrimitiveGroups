module

public import CFSG.ClassicalGroups.Alternating.PointRadicalFixedCard
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Additive characters and quadratic forms over characteristic-2 fields

This file develops the linear-algebraic and combinatorial tools over a finite field `K` of
characteristic `2` needed for the point-radical minimum-degree bound in `PSp(2n, 2^f)`:

* The lemmas `card_addMonoidHom_zmod_two` and `card_addMonoidHom_vanishing_eq_index`: in any finite
  elementary abelian `2`-group `A`, there are `Nat.card A` additive homomorphisms `A →+ ZMod 2`,
  and `U.index` of them vanish on an additive subgroup `U ≤ A`.
* Given a nonzero additive character `α₀ : K →+ ZMod 2`, every `β : K →+ ZMod 2` is of the form
  `t ↦ α₀ (b * t ^ 2)` (`exists_sq_representation`), and on a nondegenerate alternating space
  `(W, B)` the map `u ↦ (w ↦ α₀ (B w u))` is a bijection `W ≃ (W →+ ZMod 2)`
  (`bilinAddHom_bijective`).
* The theorem `two_pow_le_card_zeros_of_quad`: when `Nat.card K = 2` and
  `Module.finrank K W = 2 * m` (`1 ≤ m`), any quadratic map `η : W → ZMod 2` with polar form
  `α₀ (B · ·)` has at least `2 ^ (2 * m - 1) - 2 ^ (m - 1)` zeros.
-/

@[expose] public section

namespace Maroti

open CFSG.ClassicalGroups.Alternating CFSG.ClassicalGroups
open CFSG.LocalAnalysis.ComponentInitial
open LinearMap (BilinForm)
open Module

section ElementaryAbelianDual

/-- Every `z : ZMod 2` is `0` or `1`. -/
theorem zmod_two_eq_zero_or_one (z : ZMod 2) : z = 0 ∨ z = 1 := by
  revert z; decide

/-- For any finite type `A`, `A →+ ZMod 2` is finite. -/
instance instFiniteAddMonoidHomZModTwo {A : Type*} [AddCommGroup A] [Finite A] :
    Finite (A →+ ZMod 2) :=
  Finite.of_injective DFunLike.coe DFunLike.coe_injective

/-- Helper for `card_addMonoidHom_zmod_two` when `A` is a `ZMod 2`-module. -/
private theorem card_addMonoidHom_zmod_two_of_module (A : Type*) [AddCommGroup A]
    [Module (ZMod 2) A] [Finite A] :
    Nat.card (A →+ ZMod 2) = Nat.card A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Module.Finite (ZMod 2) A := Module.Finite.of_finite
  let e : (A →+ ZMod 2) ≃ Module.Dual (ZMod 2) A :=
    { toFun := fun f =>
        { toAddHom := f.toAddHom
          map_smul' := fun c x => by
            rcases zmod_two_eq_zero_or_one c with rfl | rfl <;> simp }
      invFun := fun f => f.toAddMonoidHom
      left_inv := fun f => by ext; rfl
      right_inv := fun f => by ext; rfl }
  exact Nat.card_congr (e.trans (Module.Free.chooseBasis (ZMod 2) A).toDualEquiv.toEquiv.symm)

/-- For any finite additive group `A` of exponent `2`,
`Nat.card (A →+ ZMod 2) = Nat.card A`. -/
theorem card_addMonoidHom_zmod_two {A : Type*} [AddCommGroup A] [Finite A]
    (h2 : ∀ x : A, 2 • x = 0) :
    Nat.card (A →+ ZMod 2) = Nat.card A :=
  @card_addMonoidHom_zmod_two_of_module A _ (AddCommGroup.zmodModule h2) _

/-- In a finite additive group `A` of exponent `2`, the number of additive homomorphisms
`A →+ ZMod 2` vanishing on `U : AddSubgroup A` equals `U.index`. -/
theorem card_addMonoidHom_vanishing_eq_index {A : Type*} [AddCommGroup A] [Finite A]
    (h2 : ∀ x : A, 2 • x = 0) (U : AddSubgroup A) :
    Nat.card {f : A →+ ZMod 2 // ∀ x ∈ U, f x = 0} = U.index := by
  have h2Q : ∀ y : A ⧸ U, 2 • y = 0 := fun y =>
    Quotient.inductionOn' y fun x => by
      rw [← QuotientAddGroup.mk_nsmul, h2 x, QuotientAddGroup.mk_zero]
  let e : {f : A →+ ZMod 2 // ∀ x ∈ U, f x = 0} ≃ (A ⧸ U →+ ZMod 2) :=
    { toFun := fun f => QuotientAddGroup.lift U f.1 f.2
      invFun := fun g => ⟨g.comp (QuotientAddGroup.mk' U), fun x hx => by
        simp [(QuotientAddGroup.eq_zero_iff x).mpr hx]⟩
      left_inv := fun f => by ext x; rfl
      right_inv := fun g => by ext y; rfl }
  rw [Nat.card_congr e, card_addMonoidHom_zmod_two h2Q]
  exact U.index_eq_card.symm

/-- Helper for `exists_addMonoidHom_vanishing_not_le` when `Q` is a `ZMod 2`-module. -/
private theorem exists_addMonoidHom_eq_one_of_module (Q : Type*) [AddCommGroup Q]
    [Module (ZMod 2) Q] {v : Q} (hv : v ≠ 0) :
    ∃ f : Q →+ ZMod 2, f v = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one (ZMod 2) hv
  exact ⟨f.toAddMonoidHom, hf⟩

/-- In an additive group `A` of exponent `2`, if `¬ (V ≤ U)`, there is an additive
homomorphism `f : A →+ ZMod 2` vanishing on `U` and not vanishing on `V`. -/
theorem exists_addMonoidHom_vanishing_not_le {A : Type*} [AddCommGroup A]
    (h2 : ∀ x : A, 2 • x = 0) {U V : AddSubgroup A} (hnot : ¬ (V ≤ U)) :
    ∃ f : A →+ ZMod 2, (∀ x ∈ U, f x = 0) ∧ ∃ v ∈ V, f v ≠ 0 := by
  obtain ⟨v, hvV, hvU⟩ := Set.not_subset.mp hnot
  have h2Q : ∀ y : A ⧸ U, 2 • y = 0 := fun y =>
    Quotient.inductionOn' y fun x => by
      rw [← QuotientAddGroup.mk_nsmul, h2 x, QuotientAddGroup.mk_zero]
  have hv0 : (QuotientAddGroup.mk v : A ⧸ U) ≠ 0 :=
    fun h => hvU ((QuotientAddGroup.eq_zero_iff v).mp h)
  obtain ⟨f, hf⟩ := @exists_addMonoidHom_eq_one_of_module (A ⧸ U) _
    (AddCommGroup.zmodModule h2Q) _ hv0
  refine ⟨f.comp (QuotientAddGroup.mk' U), fun x hx => ?_, v, hvV, ?_⟩
  · simp [(QuotientAddGroup.eq_zero_iff x).mpr hx]
  · change f (QuotientAddGroup.mk v) ≠ 0
    rw [hf]
    exact one_ne_zero

end ElementaryAbelianDual

section CharTwoField

/-- If `α₀ : K →+ ZMod 2` is nonzero and `∀ c : K, α₀ (a * c) = 0`, then `a = 0`. -/
theorem eq_zero_of_forall_apply_mul_eq_zero {K : Type*} [Field K] {α₀ : K →+ ZMod 2}
    (hα₀ : α₀ ≠ 0) {a : K} (h : ∀ c : K, α₀ (a * c) = 0) : a = 0 := by
  by_contra ha
  apply hα₀
  ext x
  have : x = a * (a⁻¹ * x) := by rw [← mul_assoc, mul_inv_cancel₀ ha, one_mul]
  rw [this, h (a⁻¹ * x), AddMonoidHom.zero_apply]

variable {K : Type*} [Field K] [CharP K 2]

/-- Every module over a characteristic-2 field has additive exponent `2`. -/
theorem two_nsmul_eq_zero_of_char_two {M : Type*} [AddCommGroup M] [Module K M] (x : M) :
    2 • x = 0 := by
  rw [← Nat.cast_smul_eq_nsmul K, CharP.cast_eq_zero, zero_smul]

/-- In characteristic `2`, `a = b ↔ a + b = 0`. -/
theorem char_two_eq_iff_add_eq_zero {M : Type*} [AddCommGroup M] [Module K M] (a b : M) :
    a = b ↔ a + b = 0 := by
  have h2 := two_nsmul_eq_zero_of_char_two (K := K) b
  rw [two_nsmul] at h2
  constructor
  · rintro rfl; exact h2
  · intro h
    have hneg := eq_neg_of_add_eq_zero_left h
    have hneg' := eq_neg_of_add_eq_zero_left h2
    exact hneg.trans hneg'.symm

/-- Every finite field of characteristic `2` has a nonzero additive homomorphism to `ZMod 2`. -/
theorem exists_ne_zero_addMonoidHom_zmod_two [Finite K] : ∃ α₀ : K →+ ZMod 2, α₀ ≠ 0 := by
  have hcard : 1 < Nat.card (K →+ ZMod 2) := by
    rw [card_addMonoidHom_zmod_two (two_nsmul_eq_zero_of_char_two (K := K))]
    exact Finite.one_lt_card
  have : Nontrivial (K →+ ZMod 2) := Finite.one_lt_card_iff_nontrivial.mp hcard
  exact exists_ne 0

/-- In a finite field of characteristic `2`, the squaring map `x ↦ x ^ 2` is bijective. -/
theorem sq_bijective_of_char_two [Finite K] : Function.Bijective (fun x : K => x ^ 2) := by
  refine Finite.injective_iff_bijective.mp fun x y hxy => ?_
  have h1 : (x - y) ^ 2 = 0 := by rw [sub_pow_char, hxy, sub_self]
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp h1)

/-- For a nonzero `α₀ : K →+ ZMod 2` and `b : K`, the map `t ↦ α₀ (b * t ^ 2)` is an additive
homomorphism `K →+ ZMod 2`. -/
def sqMulAddHom (α₀ : K →+ ZMod 2) (b : K) : K →+ ZMod 2 where
  toFun t := α₀ (b * t ^ 2)
  map_zero' := by simp
  map_add' x y := by
    rw [add_pow_char, mul_add, map_add]

@[simp]
theorem sqMulAddHom_apply (α₀ : K →+ ZMod 2) (b t : K) :
    sqMulAddHom α₀ b t = α₀ (b * t ^ 2) := rfl

/-- The map `b ↦ sqMulAddHom α₀ b` from `K` to `K →+ ZMod 2` is bijective. -/
theorem sqMulAddHom_bijective [Finite K] {α₀ : K →+ ZMod 2} (hα₀ : α₀ ≠ 0) :
    Function.Bijective (sqMulAddHom α₀) := by
  have hinj : Function.Injective (sqMulAddHom α₀) := by
    intro b₁ b₂ h
    have h0 : ∀ c : K, α₀ ((b₁ - b₂) * c) = 0 := by
      intro c
      obtain ⟨t, rfl⟩ := sq_bijective_of_char_two.2 c
      have ht : α₀ (b₁ * t ^ 2) = α₀ (b₂ * t ^ 2) := congrArg (fun f => f t) h
      rw [sub_mul, map_sub, ht]
      exact sub_self _
    exact sub_eq_zero.mp (eq_zero_of_forall_apply_mul_eq_zero hα₀ h0)
  have hcard : Nat.card K = Nat.card (K →+ ZMod 2) :=
    (card_addMonoidHom_zmod_two (two_nsmul_eq_zero_of_char_two (K := K))).symm
  let _ := Fintype.ofFinite K
  let _ := Fintype.ofFinite (K →+ ZMod 2)
  exact (Fintype.bijective_iff_injective_and_card (sqMulAddHom α₀)).mpr
    ⟨hinj, by simpa [Nat.card_eq_fintype_card] using hcard⟩

/-- Every `β : K →+ ZMod 2` is of the form `t ↦ α₀ (b * t ^ 2)` for some `b : K`. -/
theorem exists_sq_representation [Finite K] {α₀ : K →+ ZMod 2} (hα₀ : α₀ ≠ 0) (β : K →+ ZMod 2) :
    ∃ b : K, ∀ t : K, β t = α₀ (b * t ^ 2) := by
  obtain ⟨b, hb⟩ := (sqMulAddHom_bijective hα₀).2 β
  exact ⟨b, fun t => by rw [← hb, sqMulAddHom_apply]⟩

/-- In a field of characteristic `2`, `b * r ^ 2 + r = 0 ↔ r = 0 ∨ r = b⁻¹`. -/
theorem mul_sq_add_self_eq_zero_iff (b r : K) :
    b * r ^ 2 + r = 0 ↔ r = 0 ∨ r = b⁻¹ := by
  have h : b * r ^ 2 + r = r * (b * r + 1) := by ring
  rw [h, mul_eq_zero, ← char_two_eq_iff_add_eq_zero (K := K)]
  constructor
  · rintro (rfl | hbr)
    · exact Or.inl rfl
    · by_cases hb : b = 0
      · subst hb; simp at hbr
      · exact Or.inr (eq_inv_of_mul_eq_one_right hbr)
  · rintro (rfl | rfl)
    · exact Or.inl rfl
    · by_cases hb : b = 0
      · subst hb; simp
      · exact Or.inr (mul_inv_cancel₀ hb)

/-- In a field of characteristic `2`,
`b * r₁ ^ 2 + r₁ = b * r₂ ^ 2 + r₂ ↔ r₂ = r₁ ∨ r₂ = r₁ + b⁻¹`. -/
theorem mul_sq_add_self_eq_iff (b r₁ r₂ : K) :
    b * r₁ ^ 2 + r₁ = b * r₂ ^ 2 + r₂ ↔ r₂ = r₁ ∨ r₂ = r₁ + b⁻¹ := by
  rw [char_two_eq_iff_add_eq_zero (K := K)]
  have h : (b * r₁ ^ 2 + r₁) + (b * r₂ ^ 2 + r₂) = b * (r₁ + r₂) ^ 2 + (r₁ + r₂) := by
    rw [add_pow_char]
    ring
  rw [h, mul_sq_add_self_eq_zero_iff, ← char_two_eq_iff_add_eq_zero (K := K), eq_comm (a := r₁)]
  constructor
  · rintro (h1 | h1)
    · exact Or.inl h1
    · right
      have := congrArg (r₁ + ·) h1
      rwa [← add_assoc, CharTwo.add_self_eq_zero, zero_add] at this
  · rintro (rfl | rfl)
    · exact Or.inl rfl
    · right
      rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]

end CharTwoField

section SymplecticSpaceDual

variable {K W : Type*} [Field K] [AddCommGroup W] [Module K W]

/-- Given `α₀ : K →+ ZMod 2` and a bilinear form `B : BilinForm K W`, `u ↦ (w ↦ α₀ (B w u))`
as an additive homomorphism `W →+ ZMod 2`. -/
def bilinAddHom (α₀ : K →+ ZMod 2) (B : BilinForm K W) (u : W) : W →+ ZMod 2 where
  toFun w := α₀ (B w u)
  map_zero' := by simp
  map_add' x y := by rw [map_add, LinearMap.add_apply, map_add]

@[simp]
theorem bilinAddHom_apply (α₀ : K →+ ZMod 2) (B : BilinForm K W) (u w : W) :
    bilinAddHom α₀ B u w = α₀ (B w u) := rfl

/-- When `α₀ ≠ 0` and `B` is nondegenerate, `bilinAddHom α₀ B : W → (W →+ ZMod 2)` is bijective. -/
theorem bilinAddHom_bijective [Finite K] [CharP K 2] [FiniteDimensional K W]
    {α₀ : K →+ ZMod 2} (hα₀ : α₀ ≠ 0) {B : BilinForm K W} (hBn : B.Nondegenerate) :
    Function.Bijective (bilinAddHom α₀ B) := by
  have : Finite W := Module.finite_of_finite K
  have hinj : Function.Injective (bilinAddHom α₀ B) := by
    intro u₁ u₂ h
    by_contra hne
    have hu : u₁ - u₂ ≠ 0 := sub_ne_zero.mpr hne
    obtain ⟨y, hy⟩ : ∃ y : W, B y (u₁ - u₂) ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hu (hBn.2 (u₁ - u₂) hcon)
    apply hy
    refine eq_zero_of_forall_apply_mul_eq_zero hα₀ fun c => ?_
    have hc : bilinAddHom α₀ B u₁ (c • y) = bilinAddHom α₀ B u₂ (c • y) :=
      congrArg (fun f => f (c • y)) h
    simp only [bilinAddHom_apply, map_smul, LinearMap.smul_apply, smul_eq_mul] at hc
    rw [map_sub, sub_mul, mul_comm (B y u₁) c, mul_comm (B y u₂) c, map_sub, hc]
    exact sub_self _
  have hcard : Nat.card W = Nat.card (W →+ ZMod 2) :=
    (card_addMonoidHom_zmod_two (two_nsmul_eq_zero_of_char_two (K := K))).symm
  let _ := Fintype.ofFinite W
  let _ := Fintype.ofFinite (W →+ ZMod 2)
  exact (Fintype.bijective_iff_injective_and_card (bilinAddHom α₀ B)).mpr
    ⟨hinj, by simpa [Nat.card_eq_fintype_card] using hcard⟩

/-- For any additive subgroup `W₀ : AddSubgroup W`, the number of `u : W` such that
`∀ w ∈ W₀, α₀ (B w u) = 0` equals `W₀.index`. -/
theorem card_bilin_annihilator [Finite K] [CharP K 2] [FiniteDimensional K W]
    {α₀ : K →+ ZMod 2} (hα₀ : α₀ ≠ 0) {B : BilinForm K W}
    (hBn : B.Nondegenerate) (W₀ : AddSubgroup W) :
    Nat.card {u : W // ∀ w ∈ W₀, α₀ (B w u) = 0} = W₀.index := by
  have : Finite W := Module.finite_of_finite K
  have hbij := bilinAddHom_bijective hα₀ hBn
  let eW : W ≃ (W →+ ZMod 2) := Equiv.ofBijective (bilinAddHom α₀ B) hbij
  let eSub : {u : W // ∀ w ∈ W₀, α₀ (B w u) = 0} ≃
      {f : W →+ ZMod 2 // ∀ w ∈ W₀, f w = 0} :=
    { toFun := fun u => ⟨eW u.1, u.2⟩
      invFun := fun f => ⟨eW.symm f.1, fun w hw => by
        have := f.2 w hw
        rwa [← eW.apply_symm_apply f.1] at this⟩
      left_inv := fun u => Subtype.ext (eW.symm_apply_apply u.1)
      right_inv := fun f => Subtype.ext (eW.apply_symm_apply f.1) }
  rw [Nat.card_congr eSub]
  exact card_addMonoidHom_vanishing_eq_index (two_nsmul_eq_zero_of_char_two (K := K)) W₀

/-- If `B` is nondegenerate, `B y u₁ = 1`, and `∀ w : W, B w u₁ = 0 → B w u₂ = 0`, then
`u₂ = (B y u₂) • u₁`. -/
theorem eq_smul_of_ker_le {B : BilinForm K W} (hBn : B.Nondegenerate) {u₁ u₂ y : W}
    (hy : B y u₁ = 1) (hker : ∀ w : W, B w u₁ = 0 → B w u₂ = 0) :
    u₂ = (B y u₂) • u₁ := by
  by_contra hne
  have h0 : u₂ - (B y u₂) • u₁ ≠ 0 := sub_ne_zero.mpr hne
  obtain ⟨z, hz⟩ : ∃ z : W, B z (u₂ - (B y u₂) • u₁) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact h0 (hBn.2 _ hcon)
  apply hz
  have hzu₁ : B (z - (B z u₁) • y) u₁ = 0 := by
    rw [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hy, mul_one,
      sub_self]
  have hzu₂ := hker (z - (B z u₁) • y) hzu₁
  rw [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul] at hzu₂
  rw [map_sub, map_smul, smul_eq_mul]
  linear_combination hzu₂

end SymplecticSpaceDual

section QuadraticZeros

/-- On `ZMod 2 × ZMod 2`, for any `a b c : ZMod 2`, the number of pairs `(x, y)` with
`a * x + b * y + x * y = c` is either `1` or `3`. -/
theorem card_hyp_plane_quad_eq (a b c : ZMod 2) :
    (Finset.univ.filter fun p : ZMod 2 × ZMod 2 => a * p.1 + b * p.2 + p.1 * p.2 = c).card = 3 ∧
      (Finset.univ.filter fun p : ZMod 2 × ZMod 2 =>
        a * p.1 + b * p.2 + p.1 * p.2 = c + 1).card = 1 ∨
    (Finset.univ.filter fun p : ZMod 2 × ZMod 2 => a * p.1 + b * p.2 + p.1 * p.2 = c).card = 1 ∧
      (Finset.univ.filter fun p : ZMod 2 × ZMod 2 =>
        a * p.1 + b * p.2 + p.1 * p.2 = c + 1).card = 3 := by
  revert a b c
  decide

/-- For any finite type `Ω` and `f : Ω → ZMod 2`,
`Nat.card {w : Ω // f w = 0} + Nat.card {w : Ω // f w = 1} = Nat.card Ω`. -/
theorem card_zmod_two_fiber_zero_add_one {Ω : Type*} [Finite Ω] (f : Ω → ZMod 2) :
    Nat.card {w : Ω // f w = 0} + Nat.card {w : Ω // f w = 1} = Nat.card Ω := by
  classical
  let _ := Fintype.ofFinite Ω
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext x
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    exact zmod_two_eq_zero_or_one (f x)
  · rw [Finset.disjoint_filter]
    intro x _ h0 h1
    rw [h0] at h1
    exact zero_ne_one h1

/-- Combinatorial step on `(ZMod 2 × ZMod 2) × Ω`: for `q (x, y) = a * x + b * y + x * y`
and `f : Ω → ZMod 2`, if `N₀ = Nat.card {w : Ω // f w = 0}` and
`N₁ = Nat.card {w : Ω // f w = 1}`, then for each `c : ZMod 2`,
`Nat.card {p : (ZMod 2 × ZMod 2) × Ω // q p.1 + f p.2 = c}` is either
`3 * N₀ + N₁` or `N₀ + 3 * N₁`. -/
theorem card_prod_hyp_plane_quad_eq {Ω : Type*} [Finite Ω] (a b : ZMod 2) (f : Ω → ZMod 2)
    (c : ZMod 2) :
    Nat.card {p : (ZMod 2 × ZMod 2) × Ω // (a * p.1.1 + b * p.1.2 + p.1.1 * p.1.2) + f p.2 = c} =
      3 * Nat.card {w : Ω // f w = 0} + Nat.card {w : Ω // f w = 1} ∨
    Nat.card {p : (ZMod 2 × ZMod 2) × Ω // (a * p.1.1 + b * p.1.2 + p.1.1 * p.1.2) + f p.2 = c} =
      Nat.card {w : Ω // f w = 0} + 3 * Nat.card {w : Ω // f w = 1} := by
  classical
  let _ := Fintype.ofFinite Ω
  set q : ZMod 2 × ZMod 2 → ZMod 2 := fun p => a * p.1 + b * p.2 + p.1 * p.2
  set S₀ : Finset (ZMod 2 × ZMod 2) := Finset.univ.filter fun p => q p = c
  set S₁ : Finset (ZMod 2 × ZMod 2) := Finset.univ.filter fun p => q p = c + 1
  set F₀ : Finset Ω := Finset.univ.filter fun w => f w = 0
  set F₁ : Finset Ω := Finset.univ.filter fun w => f w = 1
  have hbij : (Finset.univ.filter fun p : (ZMod 2 × ZMod 2) × Ω => q p.1 + f p.2 = c) =
      (S₀ ×ˢ F₀) ∪ (S₁ ×ˢ F₁) := by
    ext ⟨p, w⟩
    simp only [S₀, S₁, F₀, F₁, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
      Finset.mem_product]
    constructor
    · intro h
      rcases zmod_two_eq_zero_or_one (f w) with h0 | h1
      · left
        rw [h0, add_zero] at h
        exact ⟨h, h0⟩
      · right
        refine ⟨?_, h1⟩
        rw [← h, h1, add_assoc, CharTwo.add_self_eq_zero, add_zero]
    · rintro (⟨hp, hw⟩ | ⟨hp, hw⟩)
      · rw [hp, hw, add_zero]
      · rw [hp, hw, add_assoc, CharTwo.add_self_eq_zero, add_zero]
  have hdisj : Disjoint (S₀ ×ˢ F₀) (S₁ ×ˢ F₁) := by
    rw [Finset.disjoint_iff_ne]
    rintro ⟨p₁, w₁⟩ h₁ ⟨p₂, w₂⟩ h₂ h12
    cases h12
    simp only [F₀, F₁, Finset.mem_product, Finset.mem_filter] at h₁ h₂
    have := h₁.2.2.symm.trans h₂.2.2
    exact zero_ne_one this
  have hcard : Nat.card {p : (ZMod 2 × ZMod 2) × Ω // q p.1 + f p.2 = c} =
      S₀.card * Nat.card {w : Ω // f w = 0} + S₁.card * Nat.card {w : Ω // f w = 1} := by
    simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rw [hbij, Finset.card_union_of_disjoint hdisj, Finset.card_product, Finset.card_product]
  rw [hcard]
  rcases card_hyp_plane_quad_eq a b c with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · left; rw [h0, h1, one_mul]
  · right; rw [h0, h1, one_mul]

/-- In a field `K` with `Nat.card K = 2`, every element is `0` or `1`. -/
theorem eq_zero_or_eq_one_of_natCard_two {K : Type*} [Field K] [Finite K]
    (hK : Nat.card K = 2) (x : K) : x = 0 ∨ x = 1 := by
  classical
  let _ := Fintype.ofFinite K
  have hcard : Fintype.card K = 2 := by rwa [← Nat.card_eq_fintype_card]
  have hpair : ({0, 1} : Finset K).card = 2 := Finset.card_pair zero_ne_one
  have huniv : ({0, 1} : Finset K) = Finset.univ :=
    Finset.eq_univ_of_card _ (hpair.trans hcard.symm)
  have hx : x ∈ ({0, 1} : Finset K) := by rw [huniv]; exact Finset.mem_univ x
  simpa using hx

/-- In a field `K` with `Nat.card K = 2`, any nonzero `α₀ : K →+ ZMod 2` satisfies `α₀ 1 = 1`. -/
theorem apply_one_eq_one_of_card_two {K : Type*} [Field K] [Finite K]
    (hK : Nat.card K = 2) {α₀ : K →+ ZMod 2} (hα₀ : α₀ ≠ 0) : α₀ 1 = 1 := by
  have hne : α₀ 1 ≠ 0 := by
    intro h0
    apply hα₀
    ext x
    rcases eq_zero_or_eq_one_of_natCard_two hK x with rfl | rfl
    · exact map_zero α₀
    · exact h0
  rcases zmod_two_eq_zero_or_one (α₀ 1) with h0 | h1
  · exact absurd h0 hne
  · exact h1

universe uK uW

/-- Simultaneous lower bound on zeros and ones of a quadratic map on a `2m`-dimensional
symplectic space over `𝔽₂`. -/
theorem quad_zeros_and_ones_bound {K : Type uK} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) {α₀ : K →+ ZMod 2} (hα₀ : α₀ ≠ 0) :
    ∀ m : ℕ, 1 ≤ m → ∀ {W : Type uW} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
      (B : BilinForm K W), B.IsAlt → B.Nondegenerate → finrank K W = 2 * m →
      ∀ (η : W → ZMod 2), η 0 = 0 →
      (∀ x y : W, η (x + y) = η x + η y + α₀ (B x y)) →
      2 ^ (2 * m - 1) - 2 ^ (m - 1) ≤ Nat.card {u : W // η u = 0} ∧
        2 ^ (2 * m - 1) - 2 ^ (m - 1) ≤ Nat.card {u : W // η u = 1} := by
  have hα1 : α₀ 1 = 1 := apply_one_eq_one_of_card_two hK hα₀
  have hcast : ∀ z : ZMod 2, α₀ (z.cast : K) = z := by
    intro z
    rcases zmod_two_eq_zero_or_one z with rfl | rfl <;> simp [hα1]
  have hKcast : Function.Bijective (fun z : ZMod 2 => (z.cast : K)) := by
    have hinj : Function.Injective (fun z : ZMod 2 => (z.cast : K)) := by
      intro z₁ z₂ h
      have := congrArg α₀ h
      rwa [hcast, hcast] at this
    let _ := Fintype.ofFinite K
    exact (Fintype.bijective_iff_injective_and_card _).mpr
      ⟨hinj, by rw [ZMod.card, ← Nat.card_eq_fintype_card, hK]⟩
  intro m hm
  induction m, hm using Nat.le_induction with
  | base =>
    intro W _ _ _ B hB hBn hdim η hη0 hηadd
    have : Finite W := Module.finite_of_finite K
    have hpos : 0 < finrank K W := by omega
    obtain ⟨e, he⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
    obtain ⟨⟨f, hef⟩, -⟩ := alternating_hyperbolic_splitting hB hBn he
    set bs := hypBasis hB hef (by simpa using hdim)
    have hbs0 : bs 0 = e := hypBasis_zero hB hef (by simpa using hdim)
    have hbs1 : bs 1 = f := hypBasis_one hB hef (by simpa using hdim)
    let φ : ZMod 2 × ZMod 2 ≃ W :=
      { toFun := fun p => (p.1.cast : K) • e + (p.2.cast : K) • f
        invFun := fun w =>
          (α₀ (bs.repr w 0), α₀ (bs.repr w 1))
        left_inv := fun ⟨x, y⟩ => by
          dsimp only
          rw [← hbs0, ← hbs1]
          simp [hcast]
        right_inv := fun w => by
          dsimp only
          have hw := bs.sum_repr w
          rw [Fin.sum_univ_two, hbs0, hbs1] at hw
          have h0 : ((α₀ (bs.repr w 0)).cast : K) = bs.repr w 0 := by
            obtain ⟨z, hz⟩ := hKcast.2 (bs.repr w 0)
            rw [← hz, hcast]
          have h1 : ((α₀ (bs.repr w 1)).cast : K) = bs.repr w 1 := by
            obtain ⟨z, hz⟩ := hKcast.2 (bs.repr w 1)
            rw [← hz, hcast]
          rw [h0, h1]
          exact hw }
    have hηsmul : ∀ (z : ZMod 2) (v : W), η ((z.cast : K) • v) = z * η v := by
      intro z v
      rcases zmod_two_eq_zero_or_one z with rfl | rfl <;> simp [hη0]
    have hηφ : ∀ p : ZMod 2 × ZMod 2,
        η (φ p) = η e * p.1 + η f * p.2 + p.1 * p.2 := by
      intro ⟨x, y⟩
      show η ((x.cast : K) • e + (y.cast : K) • f) = _
      rw [hηadd, hηsmul x e, hηsmul y f]
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, hef, mul_one]
      have hxy : α₀ ((x.cast : K) * (y.cast : K)) = x * y := by
        rcases zmod_two_eq_zero_or_one x with rfl | rfl <;>
          rcases zmod_two_eq_zero_or_one y with rfl | rfl <;> simp [hα1]
      rw [mul_comm (y.cast : K) (x.cast : K), hxy]
      ring
    have hcard_c : ∀ c : ZMod 2,
        Nat.card {u : W // η u = c} = 3 ∨ Nat.card {u : W // η u = c} = 1 := by
      intro c
      have hsub : Nat.card {u : W // η u = c} =
          Nat.card {p : ZMod 2 × ZMod 2 //
            η e * p.1 + η f * p.2 + p.1 * p.2 = c} := by
        refine Nat.card_congr (Equiv.subtypeEquiv φ.symm fun u => ?_)
        obtain ⟨p, rfl⟩ := φ.surjective u
        rw [Equiv.symm_apply_apply, hηφ p]
      rw [hsub, Nat.card_eq_fintype_card, Fintype.card_subtype]
      rcases card_hyp_plane_quad_eq (η e) (η f) c with ⟨h, -⟩ | ⟨h, -⟩
      · exact Or.inl h
      · exact Or.inr h
    refine ⟨?_, ?_⟩
    · rcases hcard_c 0 with h | h <;> omega
    · rcases hcard_c 1 with h | h <;> omega
  | succ k hk ih =>
    intro W _ _ _ B hB hBn hdim η hη0 hηadd
    have : Finite W := Module.finite_of_finite K
    have hpos : 0 < finrank K W := by omega
    obtain ⟨e, he⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
    obtain ⟨⟨f, hef⟩, hsplit⟩ := alternating_hyperbolic_splitting hB hBn he
    obtain ⟨hdimP, -, hmemW', hcompl, hndW', hdimW'⟩ := hsplit f hef
    set P : Submodule K W := Submodule.span K {e, f}
    set W' : Submodule K W := B.orthogonal P
    have : Finite W' := Subtype.finite
    have horth : ∀ p ∈ P, ∀ w ∈ W', B p w = 0 := fun p hp w hw => by
      have := (hmemW' w).mp hw p hp
      rw [← hB.neg_eq w p, this, neg_zero]
    have hB' : (B.restrict W').IsAlt := isAlt_restrict hB W'
    have hdim' : finrank K W' = 2 * k := by
      rw [hdimW', hdim]; omega
    set η' : W' → ZMod 2 := fun w => η (w : W)
    have hη'0 : η' 0 = 0 := hη0
    have hη'add : ∀ x y : W', η' (x + y) = η' x + η' y + α₀ ((B.restrict W') x y) :=
      fun x y => hηadd x y
    obtain ⟨ih0, ih1⟩ := ih (B.restrict W') hB' hndW' hdim' η' hη'0 hη'add
    have hsum : Nat.card {w : W' // η' w = 0} + Nat.card {w : W' // η' w = 1} = 2 ^ (2 * k) := by
      rw [card_zmod_two_fiber_zero_add_one, Module.natCard_eq_pow_finrank (K := K) (V := W'),
        hK, hdim']
    have heP : e ∈ P := Submodule.subset_span (by simp)
    have hfP : f ∈ P := Submodule.subset_span (by simp)
    have hef' : (B.restrict P) ⟨e, heP⟩ ⟨f, hfP⟩ = 1 := hef
    set bs := hypBasis (isAlt_restrict hB P) hef' hdimP
    have hbs0 : bs 0 = ⟨e, heP⟩ := hypBasis_zero (isAlt_restrict hB P) hef' hdimP
    have hbs1 : bs 1 = ⟨f, hfP⟩ := hypBasis_one (isAlt_restrict hB P) hef' hdimP
    let eP : ZMod 2 × ZMod 2 ≃ P :=
      { toFun := fun p => (p.1.cast : K) • ⟨e, heP⟩ + (p.2.cast : K) • ⟨f, hfP⟩
        invFun := fun p => (α₀ (bs.repr p 0), α₀ (bs.repr p 1))
        left_inv := fun ⟨x, y⟩ => by
          dsimp only
          rw [← hbs0, ← hbs1]
          simp [hcast]
        right_inv := fun p => by
          dsimp only
          have hp := bs.sum_repr p
          rw [Fin.sum_univ_two, hbs0, hbs1] at hp
          have h0 : ((α₀ (bs.repr p 0)).cast : K) = bs.repr p 0 := by
            obtain ⟨z, hz⟩ := hKcast.2 (bs.repr p 0)
            rw [← hz, hcast]
          have h1 : ((α₀ (bs.repr p 1)).cast : K) = bs.repr p 1 := by
            obtain ⟨z, hz⟩ := hKcast.2 (bs.repr p 1)
            rw [← hz, hcast]
          rw [h0, h1]
          exact hp }
    let eProd : P × W' ≃ W :=
      (Submodule.prodEquivOfIsCompl P W' hcompl).toEquiv
    let eAll : (ZMod 2 × ZMod 2) × W' ≃ W :=
      (Equiv.prodCongr eP (Equiv.refl W')).trans eProd
    have hηsmul : ∀ (z : ZMod 2) (v : W), η ((z.cast : K) • v) = z * η v := by
      intro z v
      rcases zmod_two_eq_zero_or_one z with rfl | rfl <;> simp [hη0]
    have hηAll : ∀ p : (ZMod 2 × ZMod 2) × W',
        η (eAll p) = (η e * p.1.1 + η f * p.1.2 + p.1.1 * p.1.2) + η' p.2 := by
      intro ⟨⟨x, y⟩, w⟩
      show η (((x.cast : K) • e + (y.cast : K) • f) + (w : W)) = _
      have hxyP : (x.cast : K) • e + (y.cast : K) • f ∈ P :=
        P.add_mem (P.smul_mem _ heP) (P.smul_mem _ hfP)
      rw [hηadd, horth _ hxyP _ w.2, map_zero, add_zero, hηadd, hηsmul x e, hηsmul y f]
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, hef, mul_one]
      have hxy : α₀ ((x.cast : K) * (y.cast : K)) = x * y := by
        rcases zmod_two_eq_zero_or_one x with rfl | rfl <;>
          rcases zmod_two_eq_zero_or_one y with rfl | rfl <;> simp [hα1]
      rw [mul_comm (y.cast : K) (x.cast : K), hxy]
      ring
    have hcard_c : ∀ c : ZMod 2,
        2 ^ (2 * (k + 1) - 1) - 2 ^ (k + 1 - 1) ≤ Nat.card {u : W // η u = c} := by
      intro c
      have hsub : Nat.card {u : W // η u = c} =
          Nat.card {p : (ZMod 2 × ZMod 2) × W' //
            (η e * p.1.1 + η f * p.1.2 + p.1.1 * p.1.2) + η' p.2 = c} := by
        refine Nat.card_congr (Equiv.subtypeEquiv eAll.symm fun u => ?_)
        obtain ⟨p, rfl⟩ := eAll.surjective u
        rw [Equiv.symm_apply_apply, hηAll p]
      rw [hsub]
      have hpow1 : 2 ^ (2 * (k + 1) - 1) = 2 * 2 ^ (2 * k - 1) + 2 ^ (2 * k) := by
        obtain ⟨d, rfl⟩ : ∃ d, k = d + 1 := ⟨k - 1, by omega⟩
        have e1 : 2 * (d + 1 + 1) - 1 = 2 * d + 3 := by omega
        have e2 : 2 * (d + 1) - 1 = 2 * d + 1 := by omega
        have e3 : 2 * (d + 1) = 2 * d + 2 := by omega
        rw [e1, e2, e3]
        ring
      have hpow2 : 2 ^ (k + 1 - 1) = 2 * 2 ^ (k - 1) := by
        have h1 : k + 1 - 1 = (k - 1) + 1 := by omega
        rw [h1, pow_succ']
      rcases card_prod_hyp_plane_quad_eq (η e) (η f) η' c with h | h
      · rw [h, hpow1, hpow2]
        omega
      · rw [h, hpow1, hpow2]
        omega
    exact ⟨hcard_c 0, hcard_c 1⟩

/-- Lower bound `2 ^ (2 * m - 1) - 2 ^ (m - 1) ≤ Nat.card {u : W // η u = 0}` for any quadratic map
`η : W → ZMod 2` with polar form `α₀ (B · ·)` on a `2m`-dimensional symplectic space over `𝔽₂`. -/
theorem two_pow_le_card_zeros_of_quad {K : Type uK} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) {α₀ : K →+ ZMod 2} (hα₀ : α₀ ≠ 0) {m : ℕ} (hm : 1 ≤ m)
    {W : Type uW} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (B : BilinForm K W) (hB : B.IsAlt) (hBn : B.Nondegenerate) (hdim : finrank K W = 2 * m)
    (η : W → ZMod 2) (hη0 : η 0 = 0)
    (hηadd : ∀ x y : W, η (x + y) = η x + η y + α₀ (B x y)) :
    2 ^ (2 * m - 1) - 2 ^ (m - 1) ≤ Nat.card {u : W // η u = 0} :=
  (quad_zeros_and_ones_bound hK hα₀ m hm B hB hBn hdim η hη0 hηadd).1

end QuadraticZeros

end Maroti
