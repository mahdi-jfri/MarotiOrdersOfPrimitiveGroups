module

public import Maroti.MinDegree.Heisenberg
public import Mathlib.Algebra.CharP.Basic
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Bilinear Heisenberg Construction for Subgroup Index Bounds

This file constructs an abstract Heisenberg-like group `BilinearHeisenberg B` associated to a
bi-additive map `B : U →+ V →+ Z₀` between finite elementary abelian `p`-groups `U, V, Z₀`, and
applies `Maroti.mul_le_index_of_injective_of_ne_top` (`Maroti/MinDegree/Heisenberg.lean`) to obtain
lower bounds `p * m ≤ H.index` on the index of every proper subgroup `H` of a finite simple group
`G` into which `BilinearHeisenberg B` embeds.

We also provide two helper theorems:
* The theorem `mul_le_index_of_rootPairs` packages `k` commuting root-subgroup pairs `(x_i, y_i)`
  with `[x_i(a), y_i(b)] = z(ε_i a b)` over a finite field `K` of characteristic `p` into a
  subgroup of order `|K|^(2k + 1)` and deduces `p * |K| ^ k ≤ H.index`.
* The theorem `succ_le_index_of_not_dvd_factorial` deduces `n₀ + 1 ≤ H.index` when `|G|` does not
  divide `n₀!`.
-/

@[expose] public section

namespace Maroti

open Subgroup
open scoped commutatorElement BigOperators

/-! ### Factorial divisibility lower bound -/

/-- If `G` is a finite simple group, `H ≠ ⊤` is a proper subgroup, and `Nat.card G` does not
divide `n₀.factorial`, then `n₀ + 1 ≤ H.index`. -/
theorem succ_le_index_of_not_dvd_factorial {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    {H : Subgroup G} (hH : H ≠ ⊤) {n₀ : ℕ} (hndvd : ¬ Nat.card G ∣ n₀.factorial) :
    n₀ + 1 ≤ H.index := by
  by_contra! hlt
  have hle : H.index ≤ n₀ := Nat.lt_succ_iff.mp hlt
  exact hndvd ((card_dvd_index_factorial_of_ne_top hH).trans (Nat.factorial_dvd_factorial hle))

/-! ### Abstract bilinear Heisenberg group -/

/-- The Heisenberg-like group on `U × V × Z₀` defined by a bi-additive pairing
`B : U →+ V →+ Z₀`, with multiplication
`(u₁, v₁, z₁) * (u₂, v₂, z₂) = (u₁ + u₂, v₁ + v₂, z₁ + z₂ + B u₁ v₂)`. -/
@[ext]
structure BilinearHeisenberg {U V Z₀ : Type*} [AddCommGroup U] [AddCommGroup V]
    [AddCommGroup Z₀] (B : U →+ V →+ Z₀) where
  /-- First coordinate in `U`. -/
  u : U
  /-- Second coordinate in `V`. -/
  v : V
  /-- Central coordinate in `Z₀`. -/
  z : Z₀

namespace BilinearHeisenberg

variable {U V Z₀ : Type*} [AddCommGroup U] [AddCommGroup V] [AddCommGroup Z₀]
  {B : U →+ V →+ Z₀}

/-- Equivalence between `BilinearHeisenberg B` and `U × V × Z₀`. -/
def equivProd (B : U →+ V →+ Z₀) : BilinearHeisenberg B ≃ U × V × Z₀ where
  toFun q := (q.u, q.v, q.z)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance [Finite U] [Finite V] [Finite Z₀] : Finite (BilinearHeisenberg B) :=
  Finite.of_equiv (U × V × Z₀) (equivProd B).symm

instance : One (BilinearHeisenberg B) := ⟨⟨0, 0, 0⟩⟩

instance : Mul (BilinearHeisenberg B) :=
  ⟨fun a b => ⟨a.u + b.u, a.v + b.v, a.z + b.z + B a.u b.v⟩⟩

instance : Inv (BilinearHeisenberg B) :=
  ⟨fun a => ⟨-a.u, -a.v, -a.z + B a.u a.v⟩⟩

@[simp] theorem one_u : (1 : BilinearHeisenberg B).u = 0 := rfl
@[simp] theorem one_v : (1 : BilinearHeisenberg B).v = 0 := rfl
@[simp] theorem one_z : (1 : BilinearHeisenberg B).z = 0 := rfl

@[simp] theorem mul_u (a b : BilinearHeisenberg B) : (a * b).u = a.u + b.u := rfl
@[simp] theorem mul_v (a b : BilinearHeisenberg B) : (a * b).v = a.v + b.v := rfl
@[simp] theorem mul_z (a b : BilinearHeisenberg B) :
    (a * b).z = a.z + b.z + B a.u b.v := rfl

@[simp] theorem inv_u (a : BilinearHeisenberg B) : a⁻¹.u = -a.u := rfl
@[simp] theorem inv_v (a : BilinearHeisenberg B) : a⁻¹.v = -a.v := rfl
@[simp] theorem inv_z (a : BilinearHeisenberg B) : a⁻¹.z = -a.z + B a.u a.v := rfl

instance : Group (BilinearHeisenberg B) where
  mul_assoc a b c := by
    ext <;> simp [map_add, add_assoc, add_left_comm, add_comm]
  one_mul a := by
    ext <;> simp
  mul_one a := by
    ext <;> simp
  inv_mul_cancel a := by
    ext <;> simp [add_assoc]

/-- The projection homomorphism `BilinearHeisenberg B →* Multiplicative (U × V)`. -/
def fstHom (B : U →+ V →+ Z₀) : BilinearHeisenberg B →* Multiplicative (U × V) where
  toFun q := Multiplicative.ofAdd (q.u, q.v)
  map_one' := rfl
  map_mul' _ _ := rfl

theorem fstHom_surjective (B : U →+ V →+ Z₀) : Function.Surjective (fstHom B) := by
  intro x
  exact ⟨⟨(Multiplicative.toAdd x).1, (Multiplicative.toAdd x).2, 0⟩, rfl⟩

/-- The central subgroup `{(0, 0, z) | z : Z₀}` of `BilinearHeisenberg B`, defined as the kernel
of `fstHom B`. -/
def centerSubgroup (B : U →+ V →+ Z₀) : Subgroup (BilinearHeisenberg B) :=
  (fstHom B).ker

@[simp]
theorem mem_centerSubgroup_iff {q : BilinearHeisenberg B} :
    q ∈ centerSubgroup B ↔ q.u = 0 ∧ q.v = 0 := by
  change Multiplicative.ofAdd (q.u, q.v) = Multiplicative.ofAdd (0, 0) ↔ _
  rw [Multiplicative.ofAdd.injective.eq_iff, Prod.mk.injEq]

/-- The central subgroup `centerSubgroup B` is contained in
`Subgroup.center (BilinearHeisenberg B)`. -/
theorem centerSubgroup_le_center :
    centerSubgroup B ≤ Subgroup.center (BilinearHeisenberg B) := by
  intro z hz
  rw [mem_centerSubgroup_iff] at hz
  rw [Subgroup.mem_center_iff]
  intro g
  ext <;> simp [hz.1, hz.2, add_comm]

/-- If `Z₀` is nontrivial, then `centerSubgroup B ≠ ⊥`. -/
theorem centerSubgroup_ne_bot [Nontrivial Z₀] : centerSubgroup B ≠ ⊥ := by
  obtain ⟨z, hz⟩ := exists_ne (0 : Z₀)
  intro hbot
  have hmem : (⟨0, 0, z⟩ : BilinearHeisenberg B) ∈ centerSubgroup B := by
    simp
  rw [hbot, Subgroup.mem_bot] at hmem
  exact hz (congrArg BilinearHeisenberg.z hmem)

/-- The index of `centerSubgroup B` is `Nat.card U * Nat.card V`. -/
theorem index_centerSubgroup :
    (centerSubgroup B).index = Nat.card U * Nat.card V := by
  rw [centerSubgroup, Subgroup.index_ker,
    MonoidHom.range_eq_top.mpr (fstHom_surjective B), Subgroup.card_top,
    Nat.card_congr Multiplicative.toAdd, Nat.card_prod]

/-- Explicit formula for the commutator in `BilinearHeisenberg B`. -/
theorem commutatorElement_eq (a b : BilinearHeisenberg B) :
    ⁅a, b⁆ = ⟨0, 0, B a.u b.v - B b.u a.v⟩ := by
  change a * b * a⁻¹ * b⁻¹ = _
  ext
  · simp
  · simp
  · simp only [mul_z, mul_u, inv_z, inv_u, inv_v, map_add, AddMonoidHom.add_apply,
      map_neg, AddMonoidHom.neg_apply]
    abel

/-- Every commutator in `BilinearHeisenberg B` lies in `centerSubgroup B`. -/
theorem commutatorElement_mem_centerSubgroup (a b : BilinearHeisenberg B) :
    ⁅a, b⁆ ∈ centerSubgroup B := by
  rw [commutatorElement_eq, mem_centerSubgroup_iff]
  exact ⟨rfl, rfl⟩

/-- The inclusion homomorphism `Multiplicative Z₀ →* BilinearHeisenberg B` sending `z` to
`⟨0, 0, z⟩`. -/
def inlZ (B : U →+ V →+ Z₀) : Multiplicative Z₀ →* BilinearHeisenberg B where
  toFun z := ⟨0, 0, Multiplicative.toAdd z⟩
  map_one' := rfl
  map_mul' a b := by
    ext <;> simp [toAdd_mul]

/-- If `p • z = 0` for all `z : Z₀`, then `q ^ p = 1` for all `q ∈ centerSubgroup B`. -/
theorem pow_eq_one_of_mem_centerSubgroup {p : ℕ} (hZ₀ : ∀ z : Z₀, p • z = 0)
    {q : BilinearHeisenberg B} (hq : q ∈ centerSubgroup B) : q ^ p = 1 := by
  rw [mem_centerSubgroup_iff] at hq
  have hq_eq : q = inlZ B (Multiplicative.ofAdd q.z) := by
    ext <;> simp [inlZ, hq.1, hq.2]
  rw [hq_eq, ← map_pow]
  have hpow : (Multiplicative.ofAdd q.z) ^ p = 1 := by
    change Multiplicative.ofAdd (p • q.z) = Multiplicative.ofAdd 0
    rw [hZ₀]
  rw [hpow, map_one]

/-- If `p • u = 0` for all `u : U` and `p • v = 0` for all `v : V`, then `q ^ p ∈ centerSubgroup B`
for all `q : BilinearHeisenberg B`. -/
theorem pow_mem_centerSubgroup {p : ℕ} (hU : ∀ u : U, p • u = 0) (hV : ∀ v : V, p • v = 0)
    (q : BilinearHeisenberg B) : q ^ p ∈ centerSubgroup B := by
  change fstHom B (q ^ p) = 1
  rw [map_pow]
  change Multiplicative.ofAdd (p • (q.u, q.v)) = Multiplicative.ofAdd (0, 0)
  rw [Prod.smul_mk, hU q.u, hV q.v]

/-- If `B` is nondegenerate on both sides, then for every `x ∉ centerSubgroup B` and every
`z ∈ centerSubgroup B`, there exists `y : BilinearHeisenberg B` with `⁅x, y⁆ = z`. -/
theorem exists_commutatorElement_eq_of_not_mem
    (hsurjR : ∀ u : U, u ≠ 0 → Function.Surjective (B u))
    (hsurjL : ∀ v : V, v ≠ 0 → Function.Surjective (fun u => B u v))
    {x : BilinearHeisenberg B} (hx : x ∉ centerSubgroup B)
    {z : BilinearHeisenberg B} (hz : z ∈ centerSubgroup B) :
    ∃ y : BilinearHeisenberg B, ⁅x, y⁆ = z := by
  rw [mem_centerSubgroup_iff] at hx hz
  by_cases hxu : x.u ≠ 0
  · obtain ⟨v, hv⟩ := hsurjR x.u hxu z.z
    refine ⟨⟨0, v, 0⟩, ?_⟩
    rw [commutatorElement_eq]
    ext
    · exact hz.1.symm
    · exact hz.2.symm
    · simp [hv]
  · push Not at hxu
    have hxv : x.v ≠ 0 := fun h => hx ⟨hxu, h⟩
    obtain ⟨u, hu⟩ := hsurjL x.v hxv (-z.z)
    refine ⟨⟨u, 0, 0⟩, ?_⟩
    rw [commutatorElement_eq]
    ext
    · exact hz.1.symm
    · exact hz.2.symm
    · simp [hu]

/-- Given maps `xMap : U → G`, `yMap : V → G`, `zMap : Z₀ → G` satisfying the Heisenberg
commutation relations, `(u, v, z) ↦ yMap v * xMap u * zMap z` is a group homomorphism
`BilinearHeisenberg B →* G`. -/
def liftHom {G : Type*} [Group G] (B : U →+ V →+ Z₀)
    (xMap : U → G) (yMap : V → G) (zMap : Z₀ → G)
    (hx_add : ∀ u₁ u₂, xMap (u₁ + u₂) = xMap u₁ * xMap u₂)
    (hy_add : ∀ v₁ v₂, yMap (v₁ + v₂) = yMap v₁ * yMap v₂)
    (hz_add : ∀ z₁ z₂, zMap (z₁ + z₂) = zMap z₁ * zMap z₂)
    (hxz : ∀ u z, xMap u * zMap z = zMap z * xMap u)
    (hyz : ∀ v z, yMap v * zMap z = zMap z * yMap v)
    (hxy : ∀ u v, xMap u * yMap v = yMap v * xMap u * zMap (B u v)) :
    BilinearHeisenberg B →* G where
  toFun q := yMap q.v * xMap q.u * zMap q.z
  map_one' := by
    have hx0 : xMap 0 = 1 := by simpa using (hx_add 0 0).symm
    have hy0 : yMap 0 = 1 := by simpa using (hy_add 0 0).symm
    have hz0 : zMap 0 = 1 := by simpa using (hz_add 0 0).symm
    simp [hx0, hy0, hz0]
  map_mul' a b := by
    have hzz : ∀ z₁ z₂, zMap z₁ * zMap z₂ = zMap z₂ * zMap z₁ := fun z₁ z₂ => by
      rw [← hz_add, add_comm, hz_add]
    have h1 : xMap b.u * (zMap a.z * (zMap b.z * zMap (B a.u b.v))) =
        zMap (B a.u b.v) * (xMap b.u * (zMap a.z * zMap b.z)) := by
      rw [← hzz (B a.u b.v) b.z, ← mul_assoc (zMap a.z), ← hzz (B a.u b.v) a.z,
        mul_assoc (zMap (B a.u b.v)), ← mul_assoc (xMap b.u), hxz b.u (B a.u b.v), mul_assoc]
    have h2 : yMap b.v * (xMap b.u * (zMap a.z * zMap b.z)) =
        zMap a.z * (yMap b.v * (xMap b.u * zMap b.z)) := by
      rw [← mul_assoc (xMap b.u), hxz b.u a.z, mul_assoc (zMap a.z),
        ← mul_assoc (yMap b.v), hyz b.v a.z, mul_assoc]
    simp only [mul_u, mul_v, mul_z, hx_add, hy_add, hz_add]
    calc yMap a.v * yMap b.v * (xMap a.u * xMap b.u) * (zMap a.z * zMap b.z * zMap (B a.u b.v))
        = yMap a.v * (yMap b.v * xMap a.u * zMap (B a.u b.v)) * xMap b.u * zMap a.z * zMap b.z := by
          simp only [mul_assoc, h1]
      _ = yMap a.v * (xMap a.u * yMap b.v) * xMap b.u * zMap a.z * zMap b.z := by
          rw [← hxy a.u b.v]
      _ = yMap a.v * xMap a.u * zMap a.z * (yMap b.v * xMap b.u * zMap b.z) := by
          simp only [mul_assoc, h2]

/-- Main index bound from a bilinear Heisenberg subgroup inside a finite simple group `G`. -/
theorem mul_le_index_of_liftHom {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    {H : Subgroup G} (hH : H ≠ ⊤)
    [Finite U] [Finite V] [Finite Z₀] [Nontrivial Z₀]
    {p : ℕ} [Fact p.Prime]
    (hU : ∀ u : U, p • u = 0) (hV : ∀ v : V, p • v = 0) (hZ₀ : ∀ z : Z₀, p • z = 0)
    (hsurjR : ∀ u : U, u ≠ 0 → Function.Surjective (B u))
    (hsurjL : ∀ v : V, v ≠ 0 → Function.Surjective (fun u => B u v))
    (xMap : U → G) (yMap : V → G) (zMap : Z₀ → G)
    (hx_add : ∀ u₁ u₂, xMap (u₁ + u₂) = xMap u₁ * xMap u₂)
    (hy_add : ∀ v₁ v₂, yMap (v₁ + v₂) = yMap v₁ * yMap v₂)
    (hz_add : ∀ z₁ z₂, zMap (z₁ + z₂) = zMap z₁ * zMap z₂)
    (hxz : ∀ u z, xMap u * zMap z = zMap z * xMap u)
    (hyz : ∀ v z, yMap v * zMap z = zMap z * yMap v)
    (hxy : ∀ u v, xMap u * yMap v = yMap v * xMap u * zMap (B u v))
    (hinj : Function.Injective (fun q : U × V × Z₀ => yMap q.2.1 * xMap q.1 * zMap q.2.2))
    {m : ℕ} (hm : m ^ 2 ≤ Nat.card U * Nat.card V) :
    p * m ≤ H.index := by
  let f := liftHom B xMap yMap zMap hx_add hy_add hz_add hxz hyz hxy
  have hf_inj : Function.Injective f := hinj.comp (equivProd B).injective
  refine mul_le_index_of_injective_of_ne_top centerSubgroup_le_center
    commutatorElement_mem_centerSubgroup
    (fun z hz => pow_eq_one_of_mem_centerSubgroup hZ₀ hz)
    (pow_mem_centerSubgroup hU hV)
    (fun x hx z hz => exists_commutatorElement_eq_of_not_mem hsurjR hsurjL hx hz)
    hH f hf_inj centerSubgroup_ne_bot ?_
  rwa [index_centerSubgroup]

end BilinearHeisenberg

/-! ### Specialization to `k` commuting root-subgroup pairs over a finite field -/

section RootPairs

variable {K : Type*} [Field K]

/-- The weighted dot-product pairing `(u, v) ↦ ∑ i, ε i * u i * v i` on `(Fin k → K)`. -/
def dotPairing {k : ℕ} (ε : Fin k → Kˣ) : (Fin k → K) →+ (Fin k → K) →+ K where
  toFun u :=
    { toFun := fun v => ∑ i : Fin k, (ε i : K) * u i * v i
      map_zero' := by simp
      map_add' := fun v₁ v₂ => by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp [mul_add] }
  map_zero' := by
    refine AddMonoidHom.ext fun v => ?_
    simp
  map_add' u₁ u₂ := by
    refine AddMonoidHom.ext fun v => ?_
    change (∑ i : Fin k, (ε i : K) * (u₁ i + u₂ i) * v i) =
      (∑ i : Fin k, (ε i : K) * u₁ i * v i) + (∑ i : Fin k, (ε i : K) * u₂ i * v i)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring

@[simp]
theorem dotPairing_apply {k : ℕ} (ε : Fin k → Kˣ) (u v : Fin k → K) :
    dotPairing ε u v = ∑ i : Fin k, (ε i : K) * u i * v i := rfl

theorem dotPairing_surjective_right {k : ℕ} (ε : Fin k → Kˣ) {u : Fin k → K} (hu : u ≠ 0) :
    Function.Surjective (dotPairing ε u) := by
  obtain ⟨i₀, hi₀⟩ : ∃ i₀ : Fin k, u i₀ ≠ 0 := by
    by_contra! h
    exact hu (funext h)
  intro c
  classical
  refine ⟨Pi.single i₀ (((ε i₀ : K) * u i₀)⁻¹ * c), ?_⟩
  rw [dotPairing_apply, Finset.sum_eq_single i₀]
  · rw [Pi.single_eq_same, ← mul_assoc, mul_inv_cancel₀ (mul_ne_zero (ε i₀).ne_zero hi₀), one_mul]
  · intro j _ hj
    rw [Pi.single_eq_of_ne hj, mul_zero]
  · intro habs
    exact absurd (Finset.mem_univ i₀) habs

theorem dotPairing_surjective_left {k : ℕ} (ε : Fin k → Kˣ) {v : Fin k → K} (hv : v ≠ 0) :
    Function.Surjective (fun u => dotPairing ε u v) := by
  obtain ⟨i₀, hi₀⟩ : ∃ i₀ : Fin k, v i₀ ≠ 0 := by
    by_contra! h
    exact hv (funext h)
  intro c
  classical
  refine ⟨Pi.single i₀ (((ε i₀ : K) * v i₀)⁻¹ * c), ?_⟩
  dsimp only
  rw [dotPairing_apply, Finset.sum_eq_single i₀]
  · rw [Pi.single_eq_same]
    calc (ε i₀ : K) * (((ε i₀ : K) * v i₀)⁻¹ * c) * v i₀
        = ((ε i₀ : K) * v i₀) * ((ε i₀ : K) * v i₀)⁻¹ * c := by ring
      _ = c := by rw [mul_inv_cancel₀ (mul_ne_zero (ε i₀).ne_zero hi₀), one_mul]
  · intro j _ hj
    rw [Pi.single_eq_of_ne hj, mul_zero, zero_mul]
  · intro habs
    exact absurd (Finset.mem_univ i₀) habs

section ListProdHelpers

variable {G : Type*} [Group G] {α : Type*}

/-- If an element `g` commutes with every element of a list `l`, it commutes with `l.prod`. -/
private theorem mul_list_prod_comm {g : G} {l : List G} (h : ∀ x ∈ l, g * x = x * g) :
    g * l.prod = l.prod * g := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.prod_cons, ← mul_assoc, h a List.mem_cons_self, mul_assoc,
      ih (fun x hx => h x (List.mem_cons_of_mem a hx)), ← mul_assoc]

/-- If `f` and `g` commute pairwise on a list `l`, then
`(l.map fun i => f i * g i).prod = (l.map f).prod * (l.map g).prod`. -/
private theorem list_map_mul_prod (l : List α) (f g : α → G)
    (hcomm : ∀ a ∈ l, ∀ b ∈ l, f a * g b = g b * f a) :
    (l.map fun i => f i * g i).prod = (l.map f).prod * (l.map g).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons, List.map_cons,
      List.prod_cons, ih (fun x hx y hy => hcomm x (List.mem_cons_of_mem a hx) y
        (List.mem_cons_of_mem a hy))]
    have hcomm' : g a * (l.map f).prod = (l.map f).prod * g a := by
      refine mul_list_prod_comm fun x hx => ?_
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
      exact (hcomm b (List.mem_cons_of_mem a hb) a List.mem_cons_self).symm
    calc f a * g a * ((l.map f).prod * (l.map g).prod)
        = f a * (g a * (l.map f).prod) * (l.map g).prod := by group
      _ = f a * ((l.map f).prod * g a) * (l.map g).prod := by rw [hcomm']
      _ = f a * (l.map f).prod * (g a * (l.map g).prod) := by group

/-- Commutation of a single element `x i₀` past a product `(l.map y).prod` when `x i₀` commutes
with `y j` for `j ≠ i₀` and `x i₀ * y i₀ = y i₀ * x i₀ * z c`. -/
private theorem single_mul_list_prod_comm [DecidableEq α] (l : List α) (hl : l.Nodup)
    (x y : α → G) (z : K → G) (c : α → K)
    (hz_add : ∀ a b, z (a + b) = z a * z b)
    (hyz : ∀ j b, y j * z b = z b * y j)
    (hxy_ne : ∀ i j, i ≠ j → x i * y j = y j * x i)
    (hxy_eq : ∀ i, x i * y i = y i * x i * z (c i))
    (i₀ : α) :
    x i₀ * (l.map y).prod =
      (l.map y).prod * x i₀ * z (if i₀ ∈ l then c i₀ else 0) := by
  have hz0 : z 0 = 1 := by simpa using (hz_add 0 0).symm
  induction l with
  | nil => simp [hz0]
  | cons a l ih =>
    obtain ⟨ha_not_mem, hl_nodup⟩ := List.nodup_cons.mp hl
    rw [List.map_cons, List.prod_cons]
    have hcomm_z : ∀ b, z b * (l.map y).prod = (l.map y).prod * z b := fun b =>
      mul_list_prod_comm fun g hg => by
        obtain ⟨j, _, rfl⟩ := List.mem_map.mp hg
        exact (hyz j b).symm
    by_cases hia : i₀ = a
    · subst hia
      have hcomm_x : i₀ ∉ l := ha_not_mem
      have hx_l : x i₀ * (l.map y).prod = (l.map y).prod * x i₀ := by
        refine mul_list_prod_comm fun g hg => ?_
        obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hg
        exact hxy_ne i₀ j (fun h => hcomm_x (h ▸ hj))
      simp only [List.mem_cons, true_or, ↓reduceIte]
      calc x i₀ * (y i₀ * (l.map y).prod)
          = (x i₀ * y i₀) * (l.map y).prod := by group
        _ = (y i₀ * x i₀ * z (c i₀)) * (l.map y).prod := by rw [hxy_eq i₀]
        _ = y i₀ * x i₀ * (z (c i₀) * (l.map y).prod) := by group
        _ = y i₀ * x i₀ * ((l.map y).prod * z (c i₀)) := by rw [hcomm_z]
        _ = y i₀ * (x i₀ * (l.map y).prod) * z (c i₀) := by group
        _ = y i₀ * ((l.map y).prod * x i₀) * z (c i₀) := by rw [hx_l]
        _ = y i₀ * (l.map y).prod * x i₀ * z (c i₀) := by group
    · simp only [List.mem_cons, hia, false_or]
      calc x i₀ * (y a * (l.map y).prod)
          = (x i₀ * y a) * (l.map y).prod := by group
        _ = (y a * x i₀) * (l.map y).prod := by rw [hxy_ne i₀ a hia]
        _ = y a * (x i₀ * (l.map y).prod) := by group
        _ = y a * ((l.map y).prod * x i₀ * z (if i₀ ∈ l then c i₀ else 0)) := by
            rw [ih hl_nodup]
        _ = y a * (l.map y).prod * x i₀ * z (if i₀ ∈ l then c i₀ else 0) := by group

/-- Commutation of `(l.map x).prod` past `(l.map y).prod`. -/
private theorem list_prod_mul_list_prod_comm [DecidableEq α] (l₁ l₂ : List α) (hl₂ : l₂.Nodup)
    (x y : α → G) (z : K → G) (c : α → K)
    (hz_add : ∀ a b, z (a + b) = z a * z b)
    (hxz : ∀ i b, x i * z b = z b * x i)
    (hyz : ∀ j b, y j * z b = z b * y j)
    (hxy_ne : ∀ i j, i ≠ j → x i * y j = y j * x i)
    (hxy_eq : ∀ i, x i * y i = y i * x i * z (c i)) :
    (l₁.map x).prod * (l₂.map y).prod =
      (l₂.map y).prod * (l₁.map x).prod *
        z (l₁.map fun i => if i ∈ l₂ then c i else 0).sum := by
  have hz0 : z 0 = 1 := by simpa using (hz_add 0 0).symm
  induction l₁ with
  | nil => simp [hz0]
  | cons a l₁ ih =>
    rw [List.map_cons, List.prod_cons, List.map_cons, List.sum_cons, hz_add]
    have hcomm_z : ∀ b, z b * (l₁.map x).prod = (l₁.map x).prod * z b := fun b =>
      mul_list_prod_comm fun g hg => by
        obtain ⟨i, _, rfl⟩ := List.mem_map.mp hg
        exact (hxz i b).symm
    calc x a * (l₁.map x).prod * (l₂.map y).prod
        = x a * ((l₁.map x).prod * (l₂.map y).prod) := by group
      _ = x a * ((l₂.map y).prod * (l₁.map x).prod *
            z (l₁.map fun i => if i ∈ l₂ then c i else 0).sum) := by rw [ih]
      _ = (x a * (l₂.map y).prod) * (l₁.map x).prod *
            z (l₁.map fun i => if i ∈ l₂ then c i else 0).sum := by group
      _ = ((l₂.map y).prod * x a * z (if a ∈ l₂ then c a else 0)) * (l₁.map x).prod *
            z (l₁.map fun i => if i ∈ l₂ then c i else 0).sum := by
          rw [single_mul_list_prod_comm l₂ hl₂ x y z c hz_add hyz hxy_ne hxy_eq a]
      _ = (l₂.map y).prod * x a * (z (if a ∈ l₂ then c a else 0) * (l₁.map x).prod) *
            z (l₁.map fun i => if i ∈ l₂ then c i else 0).sum := by group
      _ = (l₂.map y).prod * x a * ((l₁.map x).prod * z (if a ∈ l₂ then c a else 0)) *
            z (l₁.map fun i => if i ∈ l₂ then c i else 0).sum := by rw [hcomm_z]
      _ = (l₂.map y).prod * (x a * (l₁.map x).prod) *
            (z (if a ∈ l₂ then c a else 0) *
              z (l₁.map fun i => if i ∈ l₂ then c i else 0).sum) := by group

end ListProdHelpers

/-- Given `k` commuting root-subgroup pairs `x i, y i : K → G` over a finite field `K` of prime
characteristic `p` satisfying `x i a * y i b = y i b * x i a * z (ε i * a * b)`, together with
product injectivity of `(u, v, c) ↦ (ofFn (y i (v i))).prod * (ofFn (x i (u i))).prod * z c`,
every proper subgroup `H ≠ ⊤` of a finite simple group `G` has index at least `p * |K| ^ k`. -/
theorem mul_le_index_of_rootPairs {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    {H : Subgroup G} (hH : H ≠ ⊤)
    [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p]
    {k : ℕ} (x y : Fin k → K → G) (z : K → G) (ε : Fin k → Kˣ)
    (hx_add : ∀ i a b, x i (a + b) = x i a * x i b)
    (hy_add : ∀ i a b, y i (a + b) = y i a * y i b)
    (hz_add : ∀ a b, z (a + b) = z a * z b)
    (hxx : ∀ i j a b, x i a * x j b = x j b * x i a)
    (hyy : ∀ i j a b, y i a * y j b = y j b * y i a)
    (hxz : ∀ i a c, x i a * z c = z c * x i a)
    (hyz : ∀ i b c, y i b * z c = z c * y i b)
    (hxy_ne : ∀ i j, i ≠ j → ∀ a b, x i a * y j b = y j b * x i a)
    (hxy_eq : ∀ i a b, x i a * y i b = y i b * x i a * z ((ε i : K) * a * b))
    (hinj : Function.Injective (fun q : (Fin k → K) × (Fin k → K) × K =>
      (List.ofFn fun i => y i (q.2.1 i)).prod *
        (List.ofFn fun i => x i (q.1 i)).prod * z q.2.2)) :
    p * (Nat.card K) ^ k ≤ H.index := by
  let xMap (u : Fin k → K) : G := ((List.finRange k).map fun i => x i (u i)).prod
  let yMap (v : Fin k → K) : G := ((List.finRange k).map fun i => y i (v i)).prod
  have hxMap_eq : ∀ u, xMap u = (List.ofFn fun i => x i (u i)).prod :=
    fun u => congrArg List.prod List.ofFn_eq_map.symm
  have hyMap_eq : ∀ v, yMap v = (List.ofFn fun i => y i (v i)).prod :=
    fun v => congrArg List.prod List.ofFn_eq_map.symm
  have hK_exp : ∀ c : K, p • c = 0 := fun c => by
    rw [nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]
  have hU_exp : ∀ u : Fin k → K, p • u = 0 := fun u => funext fun i => hK_exp (u i)
  have hxMap_add : ∀ u₁ u₂ : Fin k → K, xMap (u₁ + u₂) = xMap u₁ * xMap u₂ := by
    intro u₁ u₂
    simp only [xMap, Pi.add_apply, hx_add]
    exact list_map_mul_prod (List.finRange k) (fun i => x i (u₁ i)) (fun i => x i (u₂ i))
      fun i _ j _ => hxx i j (u₁ i) (u₂ j)
  have hyMap_add : ∀ v₁ v₂ : Fin k → K, yMap (v₁ + v₂) = yMap v₁ * yMap v₂ := by
    intro v₁ v₂
    simp only [yMap, Pi.add_apply, hy_add]
    exact list_map_mul_prod (List.finRange k) (fun i => y i (v₁ i)) (fun i => y i (v₂ i))
      fun i _ j _ => hyy i j (v₁ i) (v₂ j)
  have hxMap_z : ∀ u c, xMap u * z c = z c * xMap u := fun u c => by
    symm
    refine mul_list_prod_comm fun g hg => ?_
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hg
    exact (hxz i (u i) c).symm
  have hyMap_z : ∀ v c, yMap v * z c = z c * yMap v := fun v c => by
    symm
    refine mul_list_prod_comm fun g hg => ?_
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hg
    exact (hyz i (v i) c).symm
  have hxyMap : ∀ u v, xMap u * yMap v = yMap v * xMap u * z (dotPairing ε u v) := by
    intro u v
    have hcomm := list_prod_mul_list_prod_comm (List.finRange k) (List.finRange k)
      (List.nodup_finRange k) (fun i => x i (u i)) (fun i => y i (v i)) z
      (fun i => (ε i : K) * u i * v i) hz_add (fun i c => hxz i (u i) c)
      (fun j c => hyz j (v j) c) (fun i j hij => hxy_ne i j hij (u i) (v j))
      (fun i => hxy_eq i (u i) (v i))
    have hsum : ((List.finRange k).map fun i =>
        if i ∈ List.finRange k then (ε i : K) * u i * v i else 0).sum =
        dotPairing ε u v := by
      have hmem : ∀ i : Fin k, i ∈ List.finRange k := List.mem_finRange
      rw [dotPairing_apply, Fin.sum_univ_def]
      simp only [hmem, ↓reduceIte]
    rwa [hsum] at hcomm
  have hinj' : Function.Injective (fun q : (Fin k → K) × (Fin k → K) × K =>
      yMap q.2.1 * xMap q.1 * z q.2.2) := by
    simpa only [hxMap_eq, hyMap_eq] using hinj
  refine BilinearHeisenberg.mul_le_index_of_liftHom hH hU_exp hU_exp hK_exp
    (fun u hu => dotPairing_surjective_right ε hu)
    (fun v hv => dotPairing_surjective_left ε hv)
    xMap yMap z hxMap_add hyMap_add hz_add hxMap_z hyMap_z hxyMap hinj' ?_
  rw [Nat.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin, sq]

end RootPairs

end Maroti
