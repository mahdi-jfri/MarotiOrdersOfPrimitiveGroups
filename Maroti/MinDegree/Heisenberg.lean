module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Maroti.MinDegree.Basic

/-!
# Minimum degree of faithful actions of Heisenberg-like groups

Let `Q` be a finite group with a central subgroup `Z ≤ Subgroup.center Q` satisfying three
properties:
* The derived subgroup satisfies `[Q, Q] ≤ Z` (`∀ x y : Q, ⁅x, y⁆ ∈ Z`).
* Both `Z` and `Q ⧸ Z` have prime exponent `p` (`∀ z ∈ Z, z ^ p = 1` and `∀ x : Q, x ^ p ∈ Z`).
* For every `x ∉ Z`, the commutator map `y ↦ ⁅x, y⁆` is surjective onto `Z`.

Then every subgroup `K ≤ Q` not containing `Z` satisfies the following bounds:
* The relative index satisfies `p ≤ K.relIndex (K ⊔ Z)`, since `K ⊓ Z` is a proper subgroup of the
  elementary abelian `p`-group `Z`.
* The center index satisfies `Z.index ≤ (K ⊔ Z).index ^ 2`, since `K / (K ⊓ Z)` embeds into the
  `F_p`-dual of `Q ⧸ (K ⊔ Z)` via the commutator pairing followed by a coordinate projection on
  `Z ⧸ (K ⊓ Z)`.
* Hence for every `m` with `m ^ 2 ≤ Z.index`, we have `p * m ≤ K.index`.

Consequently, every faithful action of `Q` on a finite type `α` has `p * m ≤ Nat.card α`, and if `Q`
embeds into a finite simple group `G`, every proper subgroup of `G` has index at least `p * m`.
-/

@[expose] public section

namespace Maroti

open Subgroup
open scoped commutatorElement

section ElemAbelianHelpers

variable {p : ℕ} [Fact p.Prime] {A : Type*} [CommGroup A] [Finite A]

/-- In a finite commutative group `A` of prime exponent `p`, any non-identity element `a₀ ≠ 1` has
nontrivial image under some homomorphism `A →* Multiplicative (ZMod p)`. -/
theorem exists_hom_zmod_ne_one (hA : ∀ a : A, a ^ p = 1) {a₀ : A} (ha₀ : a₀ ≠ 1) :
    ∃ π : A →* Multiplicative (ZMod p), π a₀ ≠ 1 := by
  have hnsmul : ∀ v : Additive A, p • v = 0 := fun v => by
    change Additive.ofMul (Additive.toMul v ^ p) = Additive.ofMul 1
    rw [hA]
  have := AddCommGroup.zmodModule hnsmul
  have : Finite (Additive A) := inferInstanceAs (Finite A)
  have : Module.Finite (ZMod p) (Additive A) := Module.Finite.of_finite
  let b := Module.finBasis (ZMod p) (Additive A)
  have hv₀ : (Additive.ofMul a₀ : Additive A) ≠ 0 := by
    change Additive.ofMul a₀ ≠ Additive.ofMul 1
    exact Additive.ofMul.injective.ne ha₀
  have hrepr : b.repr (Additive.ofMul a₀) ≠ 0 :=
    fun h => hv₀ (b.repr.injective (h.trans (map_zero _).symm))
  obtain ⟨j, hj⟩ : ∃ j, b.repr (Additive.ofMul a₀) j ≠ 0 := by
    by_contra! h
    exact hrepr (Finsupp.ext h)
  refine ⟨{
    toFun := fun a => Multiplicative.ofAdd (b.repr (Additive.ofMul a) j)
    map_one' := by
      change Multiplicative.ofAdd (b.repr (0 : Additive A) j) = 1
      rw [map_zero, Finsupp.zero_apply, ofAdd_zero]
    map_mul' := fun x y => by
      change Multiplicative.ofAdd (b.repr (Additive.ofMul x + Additive.ofMul y) j) = _
      rw [map_add, Finsupp.add_apply, ofAdd_add]
  }, ?_⟩
  change Multiplicative.ofAdd (b.repr (Additive.ofMul a₀) j) ≠ Multiplicative.ofAdd 0
  exact Multiplicative.ofAdd.injective.ne hj

/-- If `A` is a finite commutative group of prime exponent `p` and
`f : X → (A →* Multiplicative (ZMod p))` is injective, then `Nat.card X ≤ Nat.card A`. -/
theorem card_le_of_injective_hom_zmod (hA : ∀ a : A, a ^ p = 1) {X : Type*}
    (f : X → (A →* Multiplicative (ZMod p))) (hf : Function.Injective f) :
    Nat.card X ≤ Nat.card A := by
  have hnsmul : ∀ v : Additive A, p • v = 0 := fun v => by
    change Additive.ofMul (Additive.toMul v ^ p) = Additive.ofMul 1
    rw [hA]
  have := AddCommGroup.zmodModule hnsmul
  have : Finite (Additive A) := inferInstanceAs (Finite A)
  have : Module.Finite (ZMod p) (Additive A) := Module.Finite.of_finite
  let b := Module.finBasis (ZMod p) (Additive A)
  let evalB (φ : A →* Multiplicative (ZMod p)) : Additive A :=
    b.equivFun.symm (fun i => Multiplicative.toAdd (φ (Additive.toMul (b i))))
  have hevalB_inj : Function.Injective evalB := by
    intro φ₁ φ₂ h
    have hfun := congrFun (b.equivFun.symm.injective h)
    let L (φ : A →* Multiplicative (ZMod p)) : Additive A →ₗ[ZMod p] ZMod p :=
      AddMonoidHom.toZModLinearMap p
        { toFun := fun v => Multiplicative.toAdd (φ (Additive.toMul v))
          map_zero' := by change Multiplicative.toAdd (φ 1) = 0; rw [map_one, toAdd_one]
          map_add' := fun u v => by
            change Multiplicative.toAdd (φ (Additive.toMul u * Additive.toMul v)) = _
            rw [map_mul, toAdd_mul] }
    have hL : L φ₁ = L φ₂ := b.ext fun i => hfun i
    ext a
    have ha := congrArg (fun g : Additive A →ₗ[ZMod p] ZMod p => g (Additive.ofMul a)) hL
    exact Multiplicative.toAdd.injective ha
  exact Nat.card_le_card_of_injective (fun x => Additive.toMul (evalB (f x)))
    (Additive.toMul.injective.comp (hevalB_inj.comp hf))

end ElemAbelianHelpers

variable {Q : Type*} [Group Q]

section CommutatorIdentities

variable {Z : Subgroup Q} (hZ : Z ≤ center Q) (hcomm : ∀ x y : Q, ⁅x, y⁆ ∈ Z)

include hZ hcomm in
/-- If `[Q, Q] ≤ Z ≤ center Q`, then the commutator is multiplicative in the right argument. -/
theorem commutatorElement_mul_right_of_le_center (x y₁ y₂ : Q) :
    ⁅x, y₁ * y₂⁆ = ⁅x, y₁⁆ * ⁅x, y₂⁆ := by
  have hc := mem_center_iff.mp (hZ (hcomm x y₂)) y₁
  simp only [commutatorElement_def] at hc ⊢
  calc x * (y₁ * y₂) * x⁻¹ * (y₁ * y₂)⁻¹
      = x * y₁ * x⁻¹ * y₁⁻¹ * (y₁ * (x * y₂ * x⁻¹ * y₂⁻¹)) * y₁⁻¹ := by group
    _ = x * y₁ * x⁻¹ * y₁⁻¹ * (x * y₂ * x⁻¹ * y₂⁻¹ * y₁) * y₁⁻¹ := by rw [hc]
    _ = x * y₁ * x⁻¹ * y₁⁻¹ * (x * y₂ * x⁻¹ * y₂⁻¹) := by group

include hZ hcomm in
/-- If `[Q, Q] ≤ Z ≤ center Q`, then the commutator is multiplicative in the left argument. -/
theorem commutatorElement_mul_left_of_le_center (x₁ x₂ y : Q) :
    ⁅x₁ * x₂, y⁆ = ⁅x₁, y⁆ * ⁅x₂, y⁆ := by
  have hc₁ := mem_center_iff.mp (hZ (hcomm x₂ y)) x₁
  have hc₂ := mem_center_iff.mp (hZ (hcomm x₂ y)) ⁅x₁, y⁆
  simp only [commutatorElement_def] at hc₁ hc₂ ⊢
  calc x₁ * x₂ * y * (x₁ * x₂)⁻¹ * y⁻¹
      = x₁ * (x₂ * y * x₂⁻¹ * y⁻¹) * y * x₁⁻¹ * y⁻¹ := by group
    _ = x₂ * y * x₂⁻¹ * y⁻¹ * x₁ * y * x₁⁻¹ * y⁻¹ := by rw [hc₁]
    _ = (x₂ * y * x₂⁻¹ * y⁻¹) * (x₁ * y * x₁⁻¹ * y⁻¹) := by group
    _ = (x₁ * y * x₁⁻¹ * y⁻¹) * (x₂ * y * x₂⁻¹ * y⁻¹) := hc₂.symm

include hcomm in
/-- Every subgroup `L ≤ Q` containing `Z` is normal when `[Q, Q] ≤ Z`. -/
theorem normal_of_le_of_commutator_le (L : Subgroup Q) (hZL : Z ≤ L) : L.Normal := by
  refine ⟨fun n hn g => ?_⟩
  have h1 : g * n * g⁻¹ = ⁅g, n⁆ * n := by simp [commutatorElement_def]
  rw [h1]
  exact mul_mem (hZL (hcomm g n)) hn

end CommutatorIdentities

section IndexBound

variable [Finite Q] {p : ℕ} [hp : Fact p.Prime] {Z : Subgroup Q}
  (hZ : Z ≤ center Q) (hcomm : ∀ x y : Q, ⁅x, y⁆ ∈ Z)
  (hexpZ : ∀ z ∈ Z, z ^ p = 1) (hexpQ : ∀ x : Q, x ^ p ∈ Z)
  (hsurj : ∀ x : Q, x ∉ Z → ∀ z ∈ Z, ∃ y : Q, ⁅x, y⁆ = z)

include hcomm in
/-- When `[Q, Q] ≤ Z` and `Q` is finite, `K.relIndex (K ⊔ Z) = K.relIndex Z`. -/
theorem relIndex_sup_eq_relIndex (K : Subgroup Q) :
    K.relIndex (K ⊔ Z) = K.relIndex Z := by
  have : Z.Normal := normal_of_le_of_commutator_le hcomm Z le_rfl
  have h1 := Subgroup.relIndex_mul_relIndex (K ⊓ Z) K (K ⊔ Z) inf_le_left le_sup_left
  have h2 := Subgroup.relIndex_mul_relIndex (K ⊓ Z) Z (K ⊔ Z) inf_le_right le_sup_right
  have h3 : (K ⊓ Z).relIndex K = Z.relIndex (K ⊔ Z) := by
    rw [inf_comm, Subgroup.inf_relIndex_right, sup_comm, Subgroup.relIndex_sup_left]
  rw [h3] at h1
  rw [Subgroup.inf_relIndex_right, mul_comm (K.relIndex Z)] at h2
  have hpos : 0 < Z.relIndex (K ⊔ Z) := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_left hpos (h1.trans h2.symm)

include hZ hcomm hexpZ in
/-- If `K ≤ Q` does not contain `Z`, then `p ≤ K.relIndex (K ⊔ Z)`. -/
theorem prime_le_relIndex_sup_of_not_le {K : Subgroup Q} (hKZ : ¬ Z ≤ K) :
    p ≤ K.relIndex (K ⊔ Z) := by
  rw [relIndex_sup_eq_relIndex hcomm K, relIndex]
  let _ : CommGroup Z :=
    { (inferInstance : Group Z) with
      mul_comm := fun a b => Subtype.ext (mem_center_iff.mp (hZ b.2) a.1) }
  obtain ⟨z₀, hz₀Z, hz₀K⟩ := Set.not_subset.mp hKZ
  let N : Subgroup Z := K.subgroupOf Z
  let u : Z ⧸ N := QuotientGroup.mk ⟨z₀, hz₀Z⟩
  have hu1 : u ≠ 1 := by
    rw [ne_eq, QuotientGroup.eq_one_iff, mem_subgroupOf]
    exact hz₀K
  have hup : u ^ p = 1 := by
    rw [← QuotientGroup.mk_pow]
    have hpow : (⟨z₀, hz₀Z⟩ : Z) ^ p = 1 := Subtype.ext (hexpZ z₀ hz₀Z)
    rw [hpow, QuotientGroup.mk_one]
  have hord : orderOf u = p := orderOf_eq_prime hup hu1
  have hdvd : p ∣ N.index := by
    rw [Subgroup.index, ← hord]
    exact orderOf_dvd_natCard u
  exact Nat.le_of_dvd Nat.card_pos hdvd

include hZ hcomm hexpZ hexpQ hsurj in
/-- If `K ≤ Q` does not contain `Z`, then `Z.index ≤ (K ⊔ Z).index ^ 2`. -/
theorem index_center_le_sq_index_sup_of_not_le {K : Subgroup Q} (hKZ : ¬ Z ≤ K) :
    Z.index ≤ (K ⊔ Z).index ^ 2 := by
  have hZnorm : Z.Normal := normal_of_le_of_commutator_le hcomm Z le_rfl
  have hKZnorm : (K ⊔ Z).Normal := normal_of_le_of_commutator_le hcomm (K ⊔ Z) le_sup_right
  let _ : CommGroup Z :=
    { (inferInstance : Group Z) with
      mul_comm := fun a b => Subtype.ext (mem_center_iff.mp (hZ b.2) a.1) }
  let _ : CommGroup (Q ⧸ (K ⊔ Z)) :=
    { (inferInstance : Group (Q ⧸ (K ⊔ Z))) with
      mul_comm := fun a b => by
        induction a using QuotientGroup.induction_on with | H x =>
        induction b using QuotientGroup.induction_on with | H y =>
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
        have hxy : (x * y)⁻¹ * (y * x) = ⁅y⁻¹, x⁻¹⁆ := by simp [commutatorElement_def]; group
        rw [hxy]
        exact (le_sup_right : Z ≤ K ⊔ Z) (hcomm y⁻¹ x⁻¹) }
  obtain ⟨z₀, hz₀Z, hz₀K⟩ := Set.not_subset.mp hKZ
  let N : Subgroup Z := K.subgroupOf Z
  have hexpZN : ∀ u : Z ⧸ N, u ^ p = 1 := fun u => by
    induction u using QuotientGroup.induction_on with | H z =>
    rw [← QuotientGroup.mk_pow, show z ^ p = 1 from Subtype.ext (hexpZ z.1 z.2),
      QuotientGroup.mk_one]
  have hu₀ : (QuotientGroup.mk ⟨z₀, hz₀Z⟩ : Z ⧸ N) ≠ 1 := by
    rw [ne_eq, QuotientGroup.eq_one_iff, mem_subgroupOf]
    exact hz₀K
  obtain ⟨π₀, hπ₀⟩ := exists_hom_zmod_ne_one hexpZN hu₀
  let π : Z →* Multiplicative (ZMod p) := π₀.comp (QuotientGroup.mk' N)
  have hπ_K : ∀ z : Z, (z : Q) ∈ K → π z = 1 := fun z hzK => by
    change π₀ (QuotientGroup.mk z) = 1
    rw [(QuotientGroup.eq_one_iff z).mpr hzK, map_one]
  have hπ_z₀ : π ⟨z₀, hz₀Z⟩ ≠ 1 := hπ₀
  let cHom (k : K) : Q →* Multiplicative (ZMod p) :=
    { toFun := fun y => π ⟨⁅(k : Q), y⁆, hcomm k y⟩
      map_one' := by
        rw [← map_one π]
        exact congrArg π (Subtype.ext (commutatorElement_one_right _))
      map_mul' := fun y₁ y₂ => by
        rw [← map_mul π]
        exact congrArg π (Subtype.ext (commutatorElement_mul_right_of_le_center hZ hcomm k y₁ y₂)) }
  have hcHom_ker (k : K) : K ⊔ Z ≤ (cHom k).ker := by
    rw [sup_le_iff]
    constructor
    · intro y hy
      rw [MonoidHom.mem_ker]
      apply hπ_K
      change ⁅(k : Q), y⁆ ∈ K
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem k.2 hy) (inv_mem k.2)) (inv_mem hy)
    · intro z hz
      rw [MonoidHom.mem_ker]
      change π ⟨⁅(k : Q), z⁆, hcomm k z⟩ = 1
      have hcz : ⁅(k : Q), z⁆ = 1 :=
        commutatorElement_eq_one_iff_mul_comm.mpr (mem_center_iff.mp (hZ hz) k.1)
      rw [show (⟨⁅(k : Q), z⁆, hcomm k z⟩ : Z) = 1 from Subtype.ext hcz, map_one]
  let ψ (k : K) : Q ⧸ (K ⊔ Z) →* Multiplicative (ZMod p) :=
    QuotientGroup.lift (K ⊔ Z) (cHom k) (hcHom_ker k)
  have hψ_mk (k : K) (y : Q) : ψ k (QuotientGroup.mk y) = π ⟨⁅(k : Q), y⁆, hcomm k y⟩ := rfl
  have hψ_mul (k₁ k₂ : K) (u : Q ⧸ (K ⊔ Z)) : ψ (k₁ * k₂) u = ψ k₁ u * ψ k₂ u := by
    induction u using QuotientGroup.induction_on with | H y =>
    rw [hψ_mk, hψ_mk, hψ_mk, ← map_mul π]
    exact congrArg π (Subtype.ext (commutatorElement_mul_left_of_le_center hZ hcomm k₁ k₂ y))
  let Φ : K ⧸ Z.subgroupOf K → (Q ⧸ (K ⊔ Z) →* Multiplicative (ZMod p)) :=
    Quotient.lift ψ fun k₁ k₂ h => by
      have h1 : (QuotientGroup.mk k₁ : K ⧸ Z.subgroupOf K) = QuotientGroup.mk k₂ :=
        Quotient.sound h
      rw [QuotientGroup.eq, mem_subgroupOf] at h1
      refine MonoidHom.ext fun u => ?_
      induction u using QuotientGroup.induction_on with | H y =>
      have hk : k₂ = k₁ * (k₁⁻¹ * k₂) := by group
      rw [hk, hψ_mul, hψ_mk (k₁⁻¹ * k₂) y]
      have hcz : ⁅((k₁⁻¹ * k₂ : K) : Q), y⁆ = 1 :=
        commutatorElement_eq_one_iff_mul_comm.mpr (mem_center_iff.mp (hZ h1) y).symm
      rw [show (⟨⁅((k₁⁻¹ * k₂ : K) : Q), y⁆, _⟩ : Z) = 1 from Subtype.ext hcz, map_one, mul_one]
  have hΦ_inj : Function.Injective Φ := by
    intro q₁ q₂ hq
    induction q₁ using QuotientGroup.induction_on with | H k₁ =>
    induction q₂ using QuotientGroup.induction_on with | H k₂ =>
    rw [QuotientGroup.eq, mem_subgroupOf]
    by_contra hkZ
    obtain ⟨y, hy⟩ := hsurj (k₁⁻¹ * k₂ : K) hkZ z₀ hz₀Z
    have hyeq : ψ k₁ (QuotientGroup.mk y) = ψ k₂ (QuotientGroup.mk y) :=
      congrArg (fun f : Q ⧸ (K ⊔ Z) →* Multiplicative (ZMod p) => f (QuotientGroup.mk y)) hq
    have hmul := hψ_mul k₁ (k₁⁻¹ * k₂) (QuotientGroup.mk y)
    rw [mul_inv_cancel_left, hyeq, hψ_mk (k₁⁻¹ * k₂) y] at hmul
    have h1 : π ⟨⁅((k₁⁻¹ * k₂ : K) : Q), y⁆, _⟩ = 1 := mul_eq_left.mp hmul.symm
    exact hπ_z₀ ((congrArg π (Subtype.ext hy.symm)).trans h1)
  have hexpM : ∀ u : Q ⧸ (K ⊔ Z), u ^ p = 1 := fun u => by
    induction u using QuotientGroup.induction_on with | H x =>
    rw [← QuotientGroup.mk_pow]
    exact (QuotientGroup.eq_one_iff _).mpr ((le_sup_right : Z ≤ K ⊔ Z) (hexpQ x))
  have hcard_le : Nat.card (K ⧸ Z.subgroupOf K) ≤ (K ⊔ Z).index := by
    rw [Subgroup.index]
    exact card_le_of_injective_hom_zmod hexpM Φ hΦ_inj
  have hrel : Z.relIndex (K ⊔ Z) = Nat.card (K ⧸ Z.subgroupOf K) := by
    rw [sup_comm, Subgroup.relIndex_sup_left, Subgroup.relIndex, Subgroup.index]
  rw [← Subgroup.relIndex_mul_index (le_sup_right : Z ≤ K ⊔ Z), hrel, sq]
  exact Nat.mul_le_mul_right _ hcard_le

include hZ hcomm hexpZ hexpQ hsurj in
/-- If `K ≤ Q` does not contain `Z` and `m ^ 2 ≤ Z.index`, then `p * m ≤ K.index`. -/
theorem mul_le_index_of_not_le {K : Subgroup Q} (hKZ : ¬ Z ≤ K) {m : ℕ}
    (hm : m ^ 2 ≤ Z.index) :
    p * m ≤ K.index := by
  have hp_le := prime_le_relIndex_sup_of_not_le hZ hcomm hexpZ hKZ
  have hsq := hm.trans (index_center_le_sq_index_sup_of_not_le hZ hcomm hexpZ hexpQ hsurj hKZ)
  have hm_le : m ≤ (K ⊔ Z).index := (Nat.pow_le_pow_iff_left (by norm_num : 2 ≠ 0)).mp hsq
  rw [← Subgroup.relIndex_mul_index (le_sup_left : K ≤ K ⊔ Z)]
  exact Nat.mul_le_mul hp_le hm_le

include hZ hcomm hexpZ hexpQ hsurj in
/-- If `Q` acts faithfully on a finite type `α`, `Z ≠ ⊥`, and `m ^ 2 ≤ Z.index`, then
`p * m ≤ Nat.card α`. -/
theorem mul_le_card_of_faithfulSMul {α : Type*} [Finite α] [MulAction Q α] [FaithfulSMul Q α]
    (hZne : Z ≠ ⊥) {m : ℕ} (hm : m ^ 2 ≤ Z.index) :
    p * m ≤ Nat.card α :=
  le_card_of_forall_not_le_index hZne fun _ hKZ =>
    mul_le_index_of_not_le hZ hcomm hexpZ hexpQ hsurj hKZ hm

include hZ hcomm hexpZ hexpQ hsurj in
/-- If `f : Q →* G` is injective, `G` acts faithfully on a finite type `α`, `Z ≠ ⊥`, and
`m ^ 2 ≤ Z.index`, then `p * m ≤ Nat.card α`. -/
theorem mul_le_card_of_injective_of_faithfulSMul {G α : Type*} [Group G] [Finite α]
    [MulAction G α] [FaithfulSMul G α] (f : Q →* G) (hf : Function.Injective f)
    (hZne : Z ≠ ⊥) {m : ℕ} (hm : m ^ 2 ≤ Z.index) :
    p * m ≤ Nat.card α :=
  le_card_of_injective_of_forall_not_le_index f hf hZne fun _ hKZ =>
    mul_le_index_of_not_le hZ hcomm hexpZ hexpQ hsurj hKZ hm

include hZ hcomm hexpZ hexpQ hsurj in
/-- If `f : Q →* G` is injective, `G` is a finite simple group, `H ≠ ⊤` is a proper subgroup of `G`,
`Z ≠ ⊥`, and `m ^ 2 ≤ Z.index`, then `p * m ≤ H.index`. -/
theorem mul_le_index_of_injective_of_ne_top {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    {H : Subgroup G} (hH : H ≠ ⊤) (f : Q →* G) (hf : Function.Injective f)
    (hZne : Z ≠ ⊥) {m : ℕ} (hm : m ^ 2 ≤ Z.index) :
    p * m ≤ H.index :=
  le_index_of_injective_of_forall_not_le_index hH f hf hZne fun _ hKZ =>
    mul_le_index_of_not_le hZ hcomm hexpZ hexpQ hsurj hKZ hm

include hZ hcomm hexpZ hexpQ hsurj in
/-- If `f : Q →* G` is a group homomorphism with `Z.map f ≠ ⊥`, `G` acts faithfully on a finite
type `α`, and `m ^ 2 ≤ Z.index`, then `p * m ≤ Nat.card α`. -/
theorem mul_le_card_of_map_ne_bot_of_faithfulSMul {G α : Type*} [Group G] [Finite α]
    [MulAction G α] [FaithfulSMul G α] (f : Q →* G) (hZf : Z.map f ≠ ⊥)
    {m : ℕ} (hm : m ^ 2 ≤ Z.index) :
    p * m ≤ Nat.card α :=
  le_card_of_map_ne_bot_of_forall_not_le_index f hZf fun _ hKZ =>
    mul_le_index_of_not_le hZ hcomm hexpZ hexpQ hsurj hKZ hm

include hZ hcomm hexpZ hexpQ hsurj in
/-- If `f : Q →* G` is a group homomorphism with `Z.map f ≠ ⊥`, `G` is a finite simple group,
`H ≠ ⊤` is a proper subgroup of `G`, and `m ^ 2 ≤ Z.index`, then `p * m ≤ H.index`. -/
theorem mul_le_index_of_map_ne_bot_of_ne_top {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    {H : Subgroup G} (hH : H ≠ ⊤) (f : Q →* G) (hZf : Z.map f ≠ ⊥)
    {m : ℕ} (hm : m ^ 2 ≤ Z.index) :
    p * m ≤ H.index :=
  le_index_of_map_ne_bot_of_forall_not_le_index hH f hZf fun _ hKZ =>
    mul_le_index_of_not_le hZ hcomm hexpZ hexpQ hsurj hKZ hm

end IndexBound

section NormalizerIndexBound

variable {P : Type*} [Group P] {Q : Subgroup P}
  {p : ℕ} [hp : Fact p.Prime] {Z : Subgroup Q}
  (hZ : Z ≤ center Q) (hcomm : ∀ x y : Q, ⁅x, y⁆ ∈ Z)
  (hexpZ : ∀ z ∈ Z, z ^ p = 1) (hexpQ : ∀ x : Q, x ^ p ∈ Z)
  (hsurj : ∀ x : Q, x ∉ Z → ∀ z ∈ Z, ∃ y : Q, ⁅x, y⁆ = z)

/-- Conjugation action of `P` on its normal subgroup `Q`. -/
def conjQ (hQ_norm : Q.Normal) (g : P) : Q →* Q where
  toFun q := ⟨g * q.1 * g⁻¹, hQ_norm.conj_mem q.1 q.2 g⟩
  map_one' := Subtype.ext (by simp)
  map_mul' q₁ q₂ := Subtype.ext (by simp [mul_assoc])

@[simp]
theorem coe_conjQ (hQ_norm : Q.Normal) (g : P) (q : Q) :
    (conjQ hQ_norm g q : P) = g * q.1 * g⁻¹ := rfl

@[simp]
theorem conjQ_one (hQ_norm : Q.Normal) (q : Q) : conjQ hQ_norm 1 q = q :=
  Subtype.ext (by simp)

@[simp]
theorem conjQ_mul (hQ_norm : Q.Normal) (g₁ g₂ : P) (q : Q) :
    conjQ hQ_norm (g₁ * g₂) q = conjQ hQ_norm g₁ (conjQ hQ_norm g₂ q) :=
  Subtype.ext (by simp [mul_assoc])

@[simp]
theorem conjQ_inv_apply (hQ_norm : Q.Normal) (g : P) (q : Q) :
    conjQ hQ_norm g⁻¹ (conjQ hQ_norm g q) = q := by
  rw [← conjQ_mul, inv_mul_cancel, conjQ_one]

@[simp]
theorem conjQ_apply_inv (hQ_norm : Q.Normal) (g : P) (q : Q) :
    conjQ hQ_norm g (conjQ hQ_norm g⁻¹ q) = q := by
  rw [← conjQ_mul, mul_inv_cancel, conjQ_one]

include hZ hsurj in
/-- When `Z ≠ ⊥`, the central subgroup `Z` is equal to `Subgroup.center Q`. -/
theorem eq_center_of_ne_bot (hZne : Z ≠ ⊥) : Z = center Q := by
  refine le_antisymm hZ fun x hx => ?_
  by_contra hxZ
  obtain ⟨⟨z₀, hz₀Z⟩, hz₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hZne
  obtain ⟨y, hy⟩ := hsurj x hxZ z₀ hz₀Z
  have hcomm1 : ⁅x, y⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr (mem_center_iff.mp hx y).symm
  exact hz₀1 (Subtype.ext (hy.symm.trans hcomm1))

include hZ hsurj in
/-- When `Z ≠ ⊥`, `Z = center Q` is invariant under conjugation by every `g : P`. -/
theorem conjQ_mem_center (hQ_norm : Q.Normal) (hZne : Z ≠ ⊥) (g : P) {z : Q} (hz : z ∈ Z) :
    conjQ hQ_norm g z ∈ Z := by
  rw [eq_center_of_ne_bot hZ hsurj hZne, mem_center_iff]
  intro q
  have hzc := mem_center_iff.mp (hZ hz) (conjQ hQ_norm g⁻¹ q)
  have h1 := congrArg (conjQ hQ_norm g) hzc
  rwa [map_mul, map_mul, conjQ_apply_inv] at h1

/-- Factorization `(M.comap Q.subtype).index * (M ⊔ Q).index = M.index` for `Q.Normal`. -/
theorem index_comap_mul_index_sup_eq [Finite P] (hQ_norm : Q.Normal) (M : Subgroup P) :
    (M.comap Q.subtype).index * (M ⊔ Q).index = M.index := by
  have h1 : (M ⊓ Q).relIndex Q * Q.relIndex (M ⊔ Q) = (M ⊓ Q).relIndex (M ⊔ Q) :=
    Subgroup.relIndex_mul_relIndex (M ⊓ Q) Q (M ⊔ Q) inf_le_right le_sup_right
  have h2 : (M ⊓ Q).relIndex (M ⊔ Q) * (M ⊔ Q).index = (M ⊓ Q).index :=
    Subgroup.relIndex_mul_index (inf_le_left.trans le_sup_left)
  have h3 : (M ⊓ Q).relIndex M * M.index = (M ⊓ Q).index :=
    Subgroup.relIndex_mul_index inf_le_left
  have h4 : (M ⊓ Q).relIndex M = Q.relIndex (M ⊔ Q) := by
    rw [Subgroup.inf_relIndex_left, ← Subgroup.relIndex_sup_right]
  have h5 : (M ⊓ Q).relIndex Q = (M.comap Q.subtype).index :=
    Subgroup.inf_relIndex_right M Q
  have hpos : 0 < Q.relIndex (M ⊔ Q) := Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_right hpos
  calc (M.comap Q.subtype).index * (M ⊔ Q).index * Q.relIndex (M ⊔ Q)
      = ((M ⊓ Q).relIndex Q * Q.relIndex (M ⊔ Q)) * (M ⊔ Q).index := by rw [← h5]; ring
    _ = (M ⊓ Q).index := by rw [h1, h2]
    _ = M.index * Q.relIndex (M ⊔ Q) := by rw [← h3, h4, mul_comm]

include hZ hcomm in
/-- For any `M : Subgroup P`, the commutator of two elements of `M.comap Q.subtype ⊔ Z` lies in
`M.comap Q.subtype`. -/
theorem commutatorElement_mem_comap_of_mem_sup (M : Subgroup P) {k₁ k₂ : Q}
    (hk₁ : k₁ ∈ M.comap Q.subtype ⊔ Z) (hk₂ : k₂ ∈ M.comap Q.subtype ⊔ Z) :
    ⁅k₁, k₂⁆ ∈ M.comap Q.subtype := by
  let K₀ : Subgroup Q := M.comap Q.subtype
  have hright (x : K₀) : K₀ ⊔ Z ≤
      { carrier := { y : Q | ⁅(x : Q), y⁆ ∈ K₀ }
        one_mem' := by simp [commutatorElement_one_right]
        mul_mem' := fun {y₁ y₂} hy₁ hy₂ => by
          change ⁅(x : Q), y₁ * y₂⁆ ∈ K₀
          rw [commutatorElement_mul_right_of_le_center hZ hcomm]
          exact mul_mem hy₁ hy₂
        inv_mem' := fun {y} hy => by
          change ⁅(x : Q), y⁻¹⁆ ∈ K₀
          have h1 : ⁅(x : Q), y⁆ * ⁅(x : Q), y⁻¹⁆ = 1 := by
            rw [← commutatorElement_mul_right_of_le_center hZ hcomm, mul_inv_cancel,
              commutatorElement_one_right]
          rw [← inv_eq_of_mul_eq_one_right h1]
          exact inv_mem hy } := by
    refine sup_le (fun y hy => ?_) (fun z hz => ?_)
    · change ⁅(x : Q), y⁆ ∈ K₀
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem x.2 hy) (inv_mem x.2)) (inv_mem hy)
    · change ⁅(x : Q), z⁆ ∈ K₀
      rw [commutatorElement_eq_one_iff_mul_comm.mpr (mem_center_iff.mp (hZ hz) x.1)]
      exact one_mem K₀
  have hleft : K₀ ⊔ Z ≤
      { carrier := { x : Q | ⁅x, k₂⁆ ∈ K₀ }
        one_mem' := by simp [commutatorElement_one_left]
        mul_mem' := fun {x₁ x₂} hx₁ hy₂ => by
          change ⁅x₁ * x₂, k₂⁆ ∈ K₀
          rw [commutatorElement_mul_left_of_le_center hZ hcomm]
          exact mul_mem hx₁ hy₂
        inv_mem' := fun {x} hx => by
          change ⁅x⁻¹, k₂⁆ ∈ K₀
          have h1 : ⁅x, k₂⁆ * ⁅x⁻¹, k₂⁆ = 1 := by
            rw [← commutatorElement_mul_left_of_le_center hZ hcomm, mul_inv_cancel,
              commutatorElement_one_left]
          rw [← inv_eq_of_mul_eq_one_right h1]
          exact inv_mem hx } := by
    refine sup_le (fun x hx => hright ⟨x, hx⟩ hk₂) (fun z hz => ?_)
    change ⁅z, k₂⁆ ∈ K₀
    rw [commutatorElement_eq_one_iff_mul_comm.mpr (mem_center_iff.mp (hZ hz) k₂).symm]
    exact one_mem K₀
  exact hleft hk₁

/-- The normalizer in `P` of a subgroup `L : Subgroup Q`. -/
def normalizerInP (hQ_norm : Q.Normal) (L : Subgroup Q) : Subgroup P where
  carrier := { g : P | ∀ x ∈ L, conjQ hQ_norm g x ∈ L ∧ conjQ hQ_norm g⁻¹ x ∈ L }
  one_mem' x hx := by simp [hx]
  mul_mem' {g₁ g₂} hg₁ hg₂ x hx :=
    ⟨by rw [conjQ_mul]; exact (hg₁ _ (hg₂ x hx).1).1,
     by rw [mul_inv_rev, conjQ_mul]; exact (hg₂ _ (hg₁ x hx).2).2⟩
  inv_mem' {g} hg x hx := ⟨(hg x hx).2, by rw [inv_inv]; exact (hg x hx).1⟩

include hZ hcomm hsurj in
/-- Both `M` and `Q` normalize `M.comap Q.subtype ⊔ Z`. -/
theorem sup_le_normalizerInP_sup (hQ_norm : Q.Normal) (hZne : Z ≠ ⊥) (M : Subgroup P) :
    M ⊔ Q ≤ normalizerInP hQ_norm (M.comap Q.subtype ⊔ Z) := by
  let K₀ : Subgroup Q := M.comap Q.subtype
  let K : Subgroup Q := K₀ ⊔ Z
  have hK_norm : K.Normal := normal_of_le_of_commutator_le hcomm K le_sup_right
  have hM_sub : ∀ m ∈ M, K ≤ K.comap (conjQ hQ_norm m) := fun m hm => by
    refine sup_le (fun x hx => ?_) (fun z hz => ?_)
    · exact Subgroup.mem_sup_left (show m * x.1 * m⁻¹ ∈ M from mul_mem (mul_mem hm hx) (inv_mem hm))
    · exact Subgroup.mem_sup_right (conjQ_mem_center hZ hsurj hQ_norm hZne m hz)
  refine sup_le (fun m hm k hk => ⟨hM_sub m hm hk, hM_sub m⁻¹ (inv_mem hm) hk⟩)
    (fun q hq k hk => ?_)
  have h1 : conjQ hQ_norm q k = (⟨q, hq⟩ : Q) * k * (⟨q, hq⟩ : Q)⁻¹ := Subtype.ext rfl
  have h2 : conjQ hQ_norm q⁻¹ k = (⟨q, hq⟩ : Q)⁻¹ * k * (⟨q, hq⟩ : Q)⁻¹⁻¹ :=
    Subtype.ext (by simp)
  rw [h1, h2]
  exact ⟨hK_norm.conj_mem k hk ⟨q, hq⟩, hK_norm.conj_mem k hk (⟨q, hq⟩ : Q)⁻¹⟩

include hZ hsurj in
/-- Both `M` and `Q` normalize `M.comap Q.subtype ⊓ Z`. -/
theorem sup_le_normalizerInP_inf (hQ_norm : Q.Normal) (hZne : Z ≠ ⊥) (M : Subgroup P) :
    M ⊔ Q ≤ normalizerInP hQ_norm (M.comap Q.subtype ⊓ Z) := by
  let Z₀ : Subgroup Q := M.comap Q.subtype ⊓ Z
  have hM_sub : ∀ m ∈ M, ∀ z ∈ Z₀, conjQ hQ_norm m z ∈ Z₀ := fun m hm z hz =>
    ⟨mul_mem (mul_mem hm hz.1) (inv_mem hm), conjQ_mem_center hZ hsurj hQ_norm hZne m hz.2⟩
  refine sup_le (fun m hm z hz => ⟨hM_sub m hm z hz, hM_sub m⁻¹ (inv_mem hm) z hz⟩)
    (fun q hq z hz => ?_)
  have h1 : conjQ hQ_norm q z = z := by
    apply Subtype.ext
    change q * z.1 * q⁻¹ = z.1
    have hc : z.1 * q = q * z.1 :=
      congrArg Subtype.val (mem_center_iff.mp (hZ hz.2) ⟨q, hq⟩).symm
    calc q * z.1 * q⁻¹ = z.1 * q * q⁻¹ := by rw [hc]
      _ = z.1 := by group
  have h2 : conjQ hQ_norm q⁻¹ z = z := by
    have := congrArg (conjQ hQ_norm q⁻¹) h1.symm
    rwa [conjQ_inv_apply] at this
  rw [h1, h2]
  exact ⟨hz, hz⟩

include hZ hcomm hexpZ hexpQ hsurj in
/-- **Factor-of-2 Normalizer Lemma**: If `Z ≠ ⊥`, `2 ≤ m`, `m ^ 2 ≤ Z.index`, and no subgroup
`K ≤ Q` strictly containing `Z` is `P`-invariant with `[K, K]` contained in a proper `P`-invariant
subgroup of `Z` (specifically, if `P` acts transitively on `Z \ {1}` and every `P`-invariant
abelian subgroup of `Q` containing `Z` equals `Z`), then every `M : Subgroup P` not containing `Z`
has `2 * p * m ≤ M.index`. -/
theorem two_mul_le_index_of_not_le [Finite P] (hQ_norm : Q.Normal)
    {M : Subgroup P} (hMZ : ¬ Z ≤ M.comap Q.subtype)
    (hZne : Z ≠ ⊥) {m : ℕ} (hm2 : 2 ≤ m) (hm : m ^ 2 ≤ Z.index)
    (h_Z_trans : ∀ z₁ ∈ Z, z₁ ≠ 1 → ∀ z₂ ∈ Z, z₂ ≠ 1 → ∃ g : P, conjQ hQ_norm g z₁ = z₂)
    (h_no_abel : ∀ K : Subgroup Q, Z ≤ K → (∀ g : P, ∀ k ∈ K, conjQ hQ_norm g k ∈ K) →
      (∀ k₁ ∈ K, ∀ k₂ ∈ K, ⁅k₁, k₂⁆ = 1) → K = Z) :
    2 * p * m ≤ M.index := by
  let K₀ : Subgroup Q := M.comap Q.subtype
  let K : Subgroup Q := K₀ ⊔ Z
  rw [← index_comap_mul_index_sup_eq hQ_norm M]
  by_cases hMQ : M ⊔ Q = ⊤
  · have hK_inv : ∀ g : P, ∀ k ∈ K, conjQ hQ_norm g k ∈ K := fun g k hk =>
      (sup_le_normalizerInP_sup hZ hcomm hsurj hQ_norm hZne M (hMQ ▸ Subgroup.mem_top g) k hk).1
    have hZ₀_inv : ∀ g : P, ∀ z ∈ K₀ ⊓ Z, conjQ hQ_norm g z ∈ K₀ ⊓ Z := fun g z hz =>
      (sup_le_normalizerInP_inf hZ hsurj hQ_norm hZne M (hMQ ▸ Subgroup.mem_top g) z hz).1
    have hZ₀_bot : ∀ z ∈ K₀ ⊓ Z, z = 1 := by
      intro z₁ hz₁
      by_contra hz₁1
      apply hMZ
      intro z₂ hz₂
      by_cases hz₂1 : z₂ = 1
      · exact hz₂1 ▸ one_mem K₀
      · obtain ⟨g, rfl⟩ := h_Z_trans z₁ hz₁.2 hz₁1 z₂ hz₂ hz₂1
        exact (hZ₀_inv g z₁ hz₁).1
    have hK_abel : ∀ k₁ ∈ K, ∀ k₂ ∈ K, ⁅k₁, k₂⁆ = 1 := fun k₁ hk₁ k₂ hk₂ =>
      hZ₀_bot ⁅k₁, k₂⁆ ⟨commutatorElement_mem_comap_of_mem_sup hZ hcomm M hk₁ hk₂, hcomm k₁ k₂⟩
    have hKZ : K = Z := h_no_abel K le_sup_right hK_inv hK_abel
    have hp_le : p ≤ K₀.relIndex K := prime_le_relIndex_sup_of_not_le hZ hcomm hexpZ hMZ
    have hK_idx : 2 * m ≤ K.index := by
      rw [hKZ]
      exact (Nat.mul_le_mul_right m hm2).trans (by rwa [← sq])
    have h1 : 1 ≤ (M ⊔ Q).index := Nat.card_pos
    rw [← Subgroup.relIndex_mul_index (le_sup_left : K₀ ≤ K)]
    calc 2 * p * m = p * (2 * m) := by ring
      _ ≤ (K₀.relIndex K * K.index) * (M ⊔ Q).index :=
        (Nat.mul_le_mul hp_le hK_idx).trans (Nat.le_mul_of_pos_right _ h1)
  · have hMQ_idx : 2 ≤ (M ⊔ Q).index := by
      have hne1 : (M ⊔ Q).index ≠ 1 := mt Subgroup.index_eq_one.mp hMQ
      have hpos : 0 < (M ⊔ Q).index := Nat.card_pos
      omega
    have _ : Finite Q := inferInstance
    have hK₀_idx : p * m ≤ K₀.index :=
      mul_le_index_of_not_le hZ hcomm hexpZ hexpQ hsurj hMZ hm
    calc 2 * p * m = (p * m) * 2 := by ring
      _ ≤ K₀.index * (M ⊔ Q).index := Nat.mul_le_mul hK₀_idx hMQ_idx

include hZ hcomm hexpZ hexpQ hsurj in
/-- Wrapper for `two_mul_le_index_of_not_le` via a group homomorphism `f : P →* G` into a finite
simple group `G`. -/
theorem two_mul_le_index_of_map_ne_bot_of_ne_top [Finite P] (hQ_norm : Q.Normal)
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    {H : Subgroup G} (hH : H ≠ ⊤) (f : P →* G)
    (hZf : (Z.map Q.subtype).map f ≠ ⊥) {m : ℕ} (hm2 : 2 ≤ m) (hm : m ^ 2 ≤ Z.index)
    (h_Z_trans : ∀ z₁ ∈ Z, z₁ ≠ 1 → ∀ z₂ ∈ Z, z₂ ≠ 1 → ∃ g : P, conjQ hQ_norm g z₁ = z₂)
    (h_no_abel : ∀ K : Subgroup Q, Z ≤ K → (∀ g : P, ∀ k ∈ K, conjQ hQ_norm g k ∈ K) →
      (∀ k₁ ∈ K, ∀ k₂ ∈ K, ⁅k₁, k₂⁆ = 1) → K = Z) :
    2 * p * m ≤ H.index := by
  have hZne : Z ≠ ⊥ := by
    rintro rfl
    simp at hZf
  refine le_index_of_map_ne_bot_of_forall_not_le_index hH f hZf fun M hMZ => ?_
  have hMZ' : ¬ Z ≤ M.comap Q.subtype :=
    fun hle => hMZ (Subgroup.map_le_iff_le_comap.mpr hle)
  exact two_mul_le_index_of_not_le hZ hcomm hexpZ hexpQ hsurj hQ_norm hMZ' hZne hm2 hm
    h_Z_trans h_no_abel

include hZ hcomm hexpZ hexpQ hsurj in
/-- **Transitive Normalizer Lemma**: If `Z ≠ ⊥` and `P` acts transitively on `Q \ Z` up to `Z`
(`∀ x ∉ Z, ∀ y ∉ Z, ∃ g : P, ∃ z ∈ Z, conjQ g x * z = y`), then every `M : Subgroup P` not
containing `Z` has `p * Z.index ≤ M.index`. -/
theorem mul_index_center_le_index_of_not_le [Finite P] (hQ_norm : Q.Normal)
    {M : Subgroup P} (hMZ : ¬ Z ≤ M.comap Q.subtype)
    (hZne : Z ≠ ⊥)
    (h_trans : ∀ x : Q, x ∉ Z → ∀ y : Q, y ∉ Z → ∃ g : P, ∃ z ∈ Z, conjQ hQ_norm g x * z = y) :
    p * Z.index ≤ M.index := by
  classical
  set K₀ : Subgroup Q := M.comap Q.subtype
  set K : Subgroup Q := K₀ ⊔ Z
  have hp_le : p ≤ K₀.relIndex K := prime_le_relIndex_sup_of_not_le hZ hcomm hexpZ hMZ
  rw [← index_comap_mul_index_sup_eq hQ_norm M,
    ← Subgroup.relIndex_mul_index (le_sup_left : K₀ ≤ K), mul_assoc]
  refine Nat.mul_le_mul hp_le ?_
  by_cases hKZ : K = Z
  · change Z.index ≤ K.index * (M ⊔ Q).index
    rw [hKZ]
    exact Nat.le_mul_of_pos_right _ Nat.card_pos
  · have hnot : ¬ K ≤ Z := fun h => hKZ (le_antisymm h le_sup_right)
    obtain ⟨x₀, hx₀K, hx₀Z⟩ := Set.not_subset.mp hnot
    let N : Subgroup P := normalizerInP hQ_norm K
    have hMN : M ⊔ Q ≤ N := sup_le_normalizerInP_sup hZ hcomm hsurj hQ_norm hZne M
    have hN_le : N.index ≤ (M ⊔ Q).index := by
      rw [← Subgroup.relIndex_mul_index hMN]
      exact Nat.le_mul_of_pos_left _ Nat.card_pos
    let D := { k : Q // k ∈ K ∧ k ∉ Z }
    let C := { y : Q // y ∉ Z }
    let φ : (P ⧸ N) × D → C := fun ⟨c, k⟩ =>
      ⟨conjQ hQ_norm c.out k.1, fun hmem =>
        k.2.2 (by
          have h1 := conjQ_mem_center hZ hsurj hQ_norm hZne c.out⁻¹ hmem
          rwa [conjQ_inv_apply] at h1)⟩
    have hφ_surj : Function.Surjective φ := by
      rintro ⟨y, hyZ⟩
      obtain ⟨g, z, hzZ, hgz⟩ := h_trans x₀ hx₀Z y hyZ
      let c : P ⧸ N := QuotientGroup.mk g
      have hmemN : c.out⁻¹ * g ∈ N := by
        have h1 : QuotientGroup.mk c.out = c := QuotientGroup.out_eq' c
        exact QuotientGroup.eq.mp h1
      let z' : Q := conjQ hQ_norm c.out⁻¹ z
      have hz'Z : z' ∈ Z := conjQ_mem_center hZ hsurj hQ_norm hZne c.out⁻¹ hzZ
      let k : Q := conjQ hQ_norm (c.out⁻¹ * g) x₀ * z'
      have hkK : k ∈ K := mul_mem (hmemN x₀ hx₀K).1 (Subgroup.mem_sup_right hz'Z)
      have hk_eq : conjQ hQ_norm c.out k = y := by
        change conjQ hQ_norm c.out (conjQ hQ_norm (c.out⁻¹ * g) x₀ * z') = y
        rw [map_mul, ← conjQ_mul, mul_inv_cancel_left, conjQ_apply_inv, hgz]
      have hkZ : k ∉ Z := fun hmem =>
        hyZ (hk_eq ▸ conjQ_mem_center hZ hsurj hQ_norm hZne c.out hmem)
      exact ⟨(c, ⟨k, hkK, hkZ⟩), Subtype.ext hk_eq⟩
    have hcard_le : Nat.card C ≤ N.index * Nat.card D := by
      rw [Subgroup.index, ← Nat.card_prod]
      exact Nat.card_le_card_of_surjective φ hφ_surj
    have hC_sum : Nat.card Z + Nat.card C = Nat.card Q := by
      have h1 := Nat.card_congr (Equiv.sumCompl (· ∈ Z))
      rw [Nat.card_sum] at h1
      exact h1
    let eD : { k : K // k ∉ Z.subgroupOf K } ≃ D :=
      { toFun := fun k => ⟨k.1.1, k.1.2, k.2⟩
        invFun := fun k => ⟨⟨k.1, k.2.1⟩, k.2.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    have hD_sum : Nat.card Z + Nat.card D = Nat.card K := by
      have h1 := Nat.card_congr (Equiv.sumCompl (· ∈ Z.subgroupOf K))
      rw [Nat.card_sum, Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv,
        Nat.card_congr eD] at h1
      exact h1
    set a := Z.relIndex K
    set b := K.index
    set c := N.index
    set z := Nat.card Z
    have hz_pos : 0 < z := Nat.card_pos
    have ha_ge : 2 ≤ a := by
      have ha_pos : 0 < a := Nat.card_pos
      have ha_ne1 : a ≠ 1 := by
        intro h1
        have hZK : Z.subgroupOf K = ⊤ := Subgroup.index_eq_one.mp h1
        apply hnot
        intro k hk
        have : (⟨k, hk⟩ : K) ∈ Z.subgroupOf K := hZK ▸ Subgroup.mem_top _
        exact this
      omega
    have hK_card : Nat.card K = a * z := by
      rw [← (Z.subgroupOf K).index_mul_card,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv]
      rfl
    have hQ_card : Nat.card Q = (a * b) * z := by
      rw [← Subgroup.index_mul_card K, hK_card]
      ring
    have hsum_le : (c + a * b) * z ≤ (1 + c * a) * z :=
      calc (c + a * b) * z = c * z + (z + Nat.card C) := by rw [hC_sum, hQ_card]; ring
        _ ≤ c * z + (z + c * Nat.card D) := by gcongr
        _ = z + c * (z + Nat.card D) := by ring
        _ = (1 + c * a) * z := by rw [hD_sum, hK_card]; ring
    have hab_le : c + a * b ≤ 1 + c * a := Nat.le_of_mul_le_mul_right hsum_le hz_pos
    have hb_le_c : b ≤ c := by
      by_contra! hlt
      have h1 : a * c + a ≤ a * b := by
        calc a * c + a = a * (c + 1) := by ring
          _ ≤ a * b := Nat.mul_le_mul_left a hlt
      have h2 : c * a = a * c := mul_comm c a
      omega
    have hsq : Z.index ≤ b * b := by
      rw [← sq]
      exact index_center_le_sq_index_sup_of_not_le hZ hcomm hexpZ hexpQ hsurj hMZ
    exact hsq.trans (Nat.mul_le_mul_left b (hb_le_c.trans hN_le))

include hZ hcomm hexpZ hexpQ hsurj in
/-- Wrapper for `mul_index_center_le_index_of_not_le` via a group homomorphism `f : P →* G` into a
finite simple group `G`. -/
theorem mul_index_center_le_index_of_map_ne_bot_of_ne_top [Finite P] (hQ_norm : Q.Normal)
    {G : Type*} [Group G] [Finite G]
    [IsSimpleGroup G] {H : Subgroup G} (hH : H ≠ ⊤) (f : P →* G)
    (hZf : (Z.map Q.subtype).map f ≠ ⊥)
    (h_trans : ∀ x : Q, x ∉ Z → ∀ y : Q, y ∉ Z → ∃ g : P, ∃ z ∈ Z, conjQ hQ_norm g x * z = y) :
    p * Z.index ≤ H.index := by
  have hZne : Z ≠ ⊥ := by
    rintro rfl
    simp at hZf
  refine le_index_of_map_ne_bot_of_forall_not_le_index hH f hZf fun M hMZ => ?_
  have hMZ' : ¬ Z ≤ M.comap Q.subtype :=
    fun hle => hMZ (Subgroup.map_le_iff_le_comap.mpr hle)
  exact mul_index_center_le_index_of_not_le hZ hcomm hexpZ hexpQ hsurj hQ_norm hMZ' hZne h_trans

end NormalizerIndexBound

end Maroti
