module

public import Maroti.Linear.OrderAut
public import Maroti.Alternating.SubsetAction
public import Maroti.MinDegree.Basic

/-!
# Basic permutation action properties for almost simple groups

This file develops the basic permutation group lemmas used in the proof of Lemma 2.2 (Maróti,
Section 2, page 634):

* The theorem `Maroti.alternatingGroup_le_of_factorial_le_two_mul_card` shows that if
  `(Nat.card α)! ≤ 2 * |G|`, then `alternatingGroup α ≤ G`.
* The definition `Maroti.ptStab` gives the point stabilizer in a model group `S` via an
  isomorphism `T ≃* S`, together with index, divisibility, faithfulness, and relative-index
  bounds.
* The theorem `Maroti.card_le_card_of_ptStab_mem_extremalParabolics_two` shows that if `n ≥ 3`,
  `Nat.card K = 2`, and a point stabilizer in `projectiveSL n K` is an extremal parabolic
  subgroup, then `Nat.card G ≤ Nat.card (projectiveSL n K)`.
-/

@[expose] public section

namespace Maroti

open Subgroup Equiv
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

/-- The cardinality of `Equiv.Perm α` is `(Nat.card α).factorial`. -/
theorem card_perm_eq_factorial (α : Type*) [Finite α] :
    Nat.card (Perm α) = (Nat.card α).factorial := by
  classical
  let _ : Fintype α := Fintype.ofFinite α
  rw [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.card_eq_fintype_card]

/-- For any subgroup `H : Subgroup (Perm α)`, `Nat.card H ∣ (Nat.card α).factorial`. -/
theorem card_subgroup_dvd_factorial {α : Type*} [Finite α] (H : Subgroup (Perm α)) :
    Nat.card H ∣ (Nat.card α).factorial := by
  rw [← card_perm_eq_factorial α]
  exact Subgroup.card_subgroup_dvd_card H

/-- If `(Nat.card α).factorial ≤ 2 * Nat.card G` for `G : Subgroup (Perm α)`, then
`alternatingGroup α ≤ G`. -/
theorem alternatingGroup_le_of_factorial_le_two_mul_card {α : Type*} [Fintype α] [DecidableEq α]
    (G : Subgroup (Perm α)) (h : (Nat.card α).factorial ≤ 2 * Nat.card G) :
    alternatingGroup α ≤ G := by
  apply Equiv.Perm.alternatingGroup_le_of_index_le_two
  have hmul : Nat.card G * G.index = (Nat.card α).factorial := by
    rw [Subgroup.card_mul_index, card_perm_eq_factorial]
  have hpos : 0 < Nat.card G := Nat.card_pos
  nlinarith

/-- The point stabilizer of `x : α` in `S` via an isomorphism `e : T ≃* S`. -/
def ptStab {α S : Type*} [Group S] {T : Subgroup (Perm α)} (e : T ≃* S) (x : α) : Subgroup S :=
  (MulAction.stabilizer T x).map e.toMonoidHom

theorem mem_ptStab_iff {α S : Type*} [Group S] {T : Subgroup (Perm α)} (e : T ≃* S)
    (x : α) (s : S) :
    s ∈ ptStab e x ↔ (e.symm s : Perm α) x = x := by
  simp only [ptStab, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAction.mem_stabilizer_iff]
  constructor
  · rintro ⟨t, ht, rfl⟩
    rw [MulEquiv.symm_apply_apply]
    exact ht
  · intro hs
    exact ⟨e.symm s, hs, by simp⟩

/-- When `T` acts pretransitively on `α`, `(ptStab e x).index = Nat.card α`. -/
theorem index_ptStab_eq_card {α S : Type*} [Finite α] [Group S] {T : Subgroup (Perm α)}
    [MulAction.IsPretransitive T α] (e : T ≃* S) (x : α) :
    (ptStab e x).index = Nat.card α := by
  have hmap : (ptStab e x).index = (MulAction.stabilizer T x).index :=
    Subgroup.index_map_equiv (MulAction.stabilizer T x) e
  have horb : (MulAction.orbit T x : Set α) = Set.univ := MulAction.orbit_eq_univ T x
  rw [hmap, Subgroup.index, ← Nat.card_congr (MulAction.orbitEquivQuotientStabilizer T x),
    horb, Nat.card_congr (Equiv.Set.univ α)]

theorem card_ptStab_mul_card {α S : Type*} [Finite α] [Group S] {T : Subgroup (Perm α)}
    [MulAction.IsPretransitive T α] (e : T ≃* S) (x : α) :
    Nat.card (ptStab e x) * Nat.card α = Nat.card S := by
  rw [← index_ptStab_eq_card e x, Subgroup.card_mul_index]

theorem card_dvd_card_of_pretransitive {α S : Type*} [Finite α] [Group S] {T : Subgroup (Perm α)}
    [MulAction.IsPretransitive T α] (e : T ≃* S) (x : α) :
    Nat.card α ∣ Nat.card S := by
  rw [← card_ptStab_mul_card e x]
  exact dvd_mul_left (Nat.card α) (Nat.card (ptStab e x))

theorem card_dvd_factorial_of_equiv {α S : Type*} [Finite α] [Group S] {T : Subgroup (Perm α)}
    (e : T ≃* S) :
    Nat.card S ∣ (Nat.card α).factorial := by
  rw [← Nat.card_congr e.toEquiv]
  exact card_subgroup_dvd_factorial T

/-- For any non-identity element `s : S`, there exists `x : α` such that `s ∉ ptStab e x`. -/
theorem exists_not_mem_ptStab_of_ne_one {α S : Type*} [Group S] {T : Subgroup (Perm α)}
    (e : T ≃* S) {s : S} (hs : s ≠ 1) :
    ∃ x : α, s ∉ ptStab e x := by
  have ht1 : (e.symm s : Perm α) ≠ 1 := by
    intro h1
    apply hs
    apply e.symm.injective
    rw [map_one]
    exact Subtype.ext h1
  by_contra! hfix
  apply ht1
  ext x
  exact (mem_ptStab_iff e x s).mp (hfix x)

/-- For any nontrivial subgroup `P ≤ S`, there exists `x : α` such that `¬ (P ≤ ptStab e x)`. -/
theorem exists_not_le_ptStab_of_ne_bot {α S : Type*} [Group S] {T : Subgroup (Perm α)}
    (e : T ≃* S) {P : Subgroup S} (hP : P ≠ ⊥) :
    ∃ x : α, ¬ (P ≤ ptStab e x) := by
  by_contra! hle
  apply hP
  rw [eq_bot_iff]
  intro s hs
  rw [Subgroup.mem_bot]
  by_contra hs1
  obtain ⟨x, hx⟩ := exists_not_mem_ptStab_of_ne_one e hs1
  exact hx (hle x hs)

/-- For any subgroup `H ≤ S` and `x : α`, the relative index `(ptStab e x).relIndex H` is at most
`Nat.card α`, divides `Nat.card H`, and satisfies
`Nat.card ↥(H ⊓ ptStab e x) * (ptStab e x).relIndex H = Nat.card H`. -/
theorem relIndex_ptStab_props {α S : Type*} [Finite α] [Group S] [Finite S]
    {T : Subgroup (Perm α)} (e : T ≃* S) (H : Subgroup S) (x : α) :
    (ptStab e x).relIndex H ≤ Nat.card α ∧
      (ptStab e x).relIndex H ∣ Nat.card H ∧
      Nat.card ↥(H ⊓ ptStab e x) * (ptStab e x).relIndex H = Nat.card H ∧
      Nat.card H ≤ Nat.card α * Nat.card ↥(H ⊓ ptStab e x) := by
  let H' : Subgroup T := H.comap e.toMonoidHom
  let eH : H' ≃* H :=
    { toFun := fun t => ⟨e t.1, t.2⟩
      invFun := fun s => ⟨e.symm s.1, by simp [H', s.2]⟩
      left_inv := fun t => Subtype.ext (e.left_inv t.1)
      right_inv := fun s => Subtype.ext (e.right_inv s.1)
      map_mul' := fun a b => Subtype.ext (map_mul e a.1 b.1) }
  have hindex_eq : (ptStab e x).relIndex H = (MulAction.stabilizer H' x).index := by
    rw [Subgroup.relIndex, ← Subgroup.index_map_equiv (MulAction.stabilizer H' x) eH]
    congr 1
    ext ⟨s, hs⟩
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map, MulAction.mem_stabilizer_iff]
    constructor
    · intro hsx
      refine ⟨⟨e.symm s, by simp [H', hs]⟩, (mem_ptStab_iff e x s).mp hsx, ?_⟩
      ext
      exact e.apply_symm_apply s
    · rintro ⟨⟨t, htH⟩, htx, hts⟩
      have hs_eq : e t = s := congrArg Subtype.val hts
      rw [← hs_eq, mem_ptStab_iff, MulEquiv.symm_apply_apply]
      exact htx
  have horb_le : (MulAction.stabilizer H' x).index ≤ Nat.card α := by
    rw [Subgroup.index, ← Nat.card_congr (MulAction.orbitEquivQuotientStabilizer H' x)]
    exact Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  have hrel_le : (ptStab e x).relIndex H ≤ Nat.card α := hindex_eq ▸ horb_le
  have eSub : ↥(H ⊓ ptStab e x) ≃ ↥((ptStab e x).subgroupOf H) :=
    { toFun := fun s => ⟨⟨s.1, s.2.1⟩, s.2.2⟩
      invFun := fun s => ⟨s.1.1, ⟨s.1.2, s.2⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hmul : Nat.card ↥(H ⊓ ptStab e x) * (ptStab e x).relIndex H = Nat.card H := by
    rw [Nat.card_congr eSub, Subgroup.relIndex, Subgroup.card_mul_index]
  have hdvd : (ptStab e x).relIndex H ∣ Nat.card H :=
    ⟨Nat.card ↥(H ⊓ ptStab e x), by rw [← hmul, mul_comm]⟩
  have hcard_le : Nat.card H ≤ Nat.card α * Nat.card ↥(H ⊓ ptStab e x) := by
    rw [← hmul, mul_comm]
    exact Nat.mul_le_mul_right _ hrel_le
  exact ⟨hrel_le, hdvd, hmul, hcard_le⟩

/-- In a pretransitive action of `T` on `α`, any two point stabilizers `ptStab e x` and
`ptStab e y` are conjugate in `S`. -/
theorem exists_conj_ptStab {α S : Type*} [Group S] {T : Subgroup (Perm α)}
    [MulAction.IsPretransitive T α] (e : T ≃* S) (x y : α) :
    ∃ s : S, ptStab e y = (ptStab e x).map (MulAut.conj s : S →* S) := by
  obtain ⟨t, rfl⟩ := MulAction.exists_smul_eq T x y
  refine ⟨e t, ?_⟩
  ext s
  simp only [ptStab, Subgroup.mem_map, MulAction.mem_stabilizer_iff]
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨e (t⁻¹ * u * t), ⟨t⁻¹ * u * t, ?_, rfl⟩, ?_⟩
    · change (t⁻¹.1 * u.1 * t.1) x = x
      have h1 : (u.1 * t.1) x = t.1 x := hu
      calc (t⁻¹.1 * u.1 * t.1) x = t⁻¹.1 ((u.1 * t.1) x) := rfl
        _ = t⁻¹.1 (t.1 x) := by rw [h1]
        _ = x := by simp
    · change e t * e (t⁻¹ * u * t) * (e t)⁻¹ = e u
      simp [mul_assoc]
  · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    refine ⟨t * u * t⁻¹, ?_, ?_⟩
    · change (t.1 * u.1 * t⁻¹.1) (t.1 x) = t.1 x
      have h1 : u.1 x = x := hu
      calc (t.1 * u.1 * t⁻¹.1) (t.1 x) = t.1 (u.1 (t⁻¹.1 (t.1 x))) := rfl
        _ = t.1 (u.1 x) := by simp
        _ = t.1 x := by rw [h1]
    · change e (t * u * t⁻¹) = e t * e u * (e t)⁻¹
      simp [mul_assoc]

/-- If `n ≥ 3`, `Nat.card K = 2`, and `ptStab e x` is an extremal parabolic subgroup of
`projectiveSL n K`, then `Nat.card G ≤ Nat.card (projectiveSL n K)`. -/
theorem card_le_card_of_ptStab_mem_extremalParabolics_two {α : Type*} {K : Type} [Finite α]
    [Field K] [Finite K] {G T : Subgroup (Perm α)} [MulAction.IsPretransitive T α]
    (hnorm : ∀ g ∈ G, ∀ t ∈ T, g * t * g⁻¹ ∈ T)
    (hcent : ∀ g ∈ G, (∀ t ∈ T, g * t = t * g) → g = 1)
    {n : ℕ} (hn : 3 ≤ n) (hK : Nat.card K = 2)
    (e : T ≃* projectiveSL n K) {x : α}
    (hM : ptStab e x ∈ extremalParabolics (projectiveSL n K) 2) :
    Nat.card G ≤ Nat.card (projectiveSL n K) := by
  let ψ : G →* MulAut (projectiveSL n K) :=
    (MulAut.congr e).toMonoidHom.comp (conjHom hnorm)
  have hψ_inj : Function.Injective ψ :=
    (MulAut.congr e).injective.comp (conjHom_injective hnorm hcent)
  let innSub : Subgroup (MulAut (projectiveSL n K)) :=
    (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range
  have hψ_mem : ∀ g : G, ψ g ∈ innSub := by
    intro g
    have hmap : (ptStab e x).map (ψ g : projectiveSL n K →* projectiveSL n K) =
        ptStab e (g.1 x) := by
      ext s
      simp only [ptStab, Subgroup.mem_map, MulAction.mem_stabilizer_iff]
      constructor
      · rintro ⟨_, ⟨t, ht, rfl⟩, rfl⟩
        refine ⟨conjAut hnorm g t, ?_, ?_⟩
        · change (g.1 * t.1 * g.1⁻¹) (g.1 x) = g.1 x
          have h1 : t.1 x = x := ht
          calc (g.1 * t.1 * g.1⁻¹) (g.1 x) = g.1 (t.1 (g.1⁻¹ (g.1 x))) := rfl
            _ = g.1 (t.1 x) := by simp
            _ = g.1 x := by rw [h1]
        · simp [ψ, MulAut.congr_apply, conjHom]
      · rintro ⟨t, ht, rfl⟩
        refine ⟨e ((conjAut hnorm g).symm t),
          ⟨(conjAut hnorm g).symm t, ?_, rfl⟩, ?_⟩
        · change (g.1⁻¹ * t.1 * g.1) x = x
          have h1 : t.1 (g.1 x) = g.1 x := ht
          calc (g.1⁻¹ * t.1 * g.1) x = g.1⁻¹ (t.1 (g.1 x)) := rfl
            _ = g.1⁻¹ (g.1 x) := by rw [h1]
            _ = x := by simp
        · simp [ψ, MulAut.congr_apply, conjHom]
    obtain ⟨s, hs⟩ := exists_conj_ptStab e x (g.1 x)
    exact mem_inner_of_map_extremalParabolic_conj_of_card_two hn hK (ψ g) hM (hmap.trans hs)
  let ψ' : G →* innSub := ψ.codRestrict innSub hψ_mem
  have hψ'_inj : Function.Injective ψ' := fun a b hab =>
    hψ_inj (congrArg Subtype.val hab)
  have h1 : Nat.card G ≤ Nat.card innSub :=
    Nat.card_le_card_of_injective ψ' hψ'_inj
  have h2 : Nat.card innSub ≤ Nat.card (projectiveSL n K) := by
    refine Nat.le_of_dvd Nat.card_pos ?_
    exact Subgroup.card_dvd_of_surjective
      (f := (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).rangeRestrict)
      (MonoidHom.rangeRestrict_surjective _)
  exact le_trans h1 h2

end Maroti
