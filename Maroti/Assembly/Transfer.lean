module

public import Maroti.Reduction.Step1
public import Maroti.Assembly.Ranges

/-!
# Transfer of permutation group properties along equivalences and universe change

This file transfers the permutation group properties in Theorem 1.1 of A. Maróti,
*On the orders of primitive groups*, J. Algebra 258 (2002), pages 631–640, along an arbitrary
equivalence `e : α ≃ β` between types in any universes.

Given a permutation group `G : Subgroup (Perm α)`, the subgroup `mapPermCongr e G` is its image in
`Perm β` under `permCongrMulEquiv e`. Pretransitivity, `n`-pretransitivity, and preprimitivity are
preserved by `mapPermCongr e` (`isPretransitive_mapPermCongr_iff`,
`isMultiplyPretransitive_mapPermCongr_iff`, `isPreprimitive_mapPermCongr_iff`), as are
`IsProductActionType`, `IsWreathType`, `IsMathieuType`, and `Conclusion`
(`isProductActionType_mapPermCongr_iff`, `isWreathType_mapPermCongr_iff`,
`isMathieuType_mapPermCongr_iff`, `conclusion_mapPermCongr_iff`).

Transferring `Maroti.step1` from `Type 0` to `Type u` along
`Finite.equivFin α : α ≃ Fin (Nat.card α)` and combining the wreath case with
`IsWreathType.isProductActionType` and the bound case with `bound_lt_pow` when `2 ≤ Nat.card α`
gives `step1_univ` and `theorem_1_1_of_step1`.
-/

@[expose] public section

universe u v

namespace Maroti

open Equiv MulAction

variable {α : Type u} {β : Type v}

/-- The image of `G : Subgroup (Perm α)` in `Perm β` under `permCongrMulEquiv e`. -/
abbrev mapPermCongr (e : α ≃ β) (G : Subgroup (Perm α)) : Subgroup (Perm β) :=
  G.map (permCongrMulEquiv e).toMonoidHom

@[simp]
theorem mapPermCongr_symm (e : α ≃ β) (G : Subgroup (Perm α)) :
    mapPermCongr e.symm (mapPermCongr e G) = G := by
  dsimp [mapPermCongr]
  rw [Subgroup.map_map]
  convert Subgroup.map_id G
  ext g x
  simp [permCongrMulEquiv]

/-- The multiplicative equivalence `G ≃* mapPermCongr e G` induced by `e : α ≃ β`. -/
noncomputable def equivMapPermCongr (e : α ≃ β) (G : Subgroup (Perm α)) :
    G ≃* mapPermCongr e G :=
  G.equivMapOfInjective (permCongrMulEquiv e).toMonoidHom (permCongrMulEquiv e).injective

@[simp]
theorem card_mapPermCongr (e : α ≃ β) (G : Subgroup (Perm α)) :
    Nat.card (mapPermCongr e G) = Nat.card G :=
  Nat.card_congr (equivMapPermCongr e G).symm.toEquiv

/-- The equivariant bijection `α →ₑ[equivMapPermCongr e G] β` induced by `e : α ≃ β`. -/
noncomputable def permCongrActionHom (e : α ≃ β) (G : Subgroup (Perm α)) :
    α →ₑ[equivMapPermCongr e G] β where
  toFun := e
  map_smul' g x := by
    change e ((g : Perm α) x) = (e.permCongr (g : Perm α)) (e x)
    simp

theorem permCongrActionHom_bijective (e : α ≃ β) (G : Subgroup (Perm α)) :
    Function.Bijective (permCongrActionHom e G) :=
  e.bijective

@[simp]
theorem isPretransitive_mapPermCongr_iff (e : α ≃ β) (G : Subgroup (Perm α)) :
    IsPretransitive (mapPermCongr e G) β ↔ IsPretransitive G α :=
  (isPretransitive_congr (f := permCongrActionHom e G)
    (equivMapPermCongr e G).surjective (permCongrActionHom_bijective e G)).symm

theorem isPretransitive_mapPermCongr (e : α ≃ β) (G : Subgroup (Perm α))
    [IsPretransitive G α] : IsPretransitive (mapPermCongr e G) β :=
  (isPretransitive_mapPermCongr_iff e G).mpr inferInstance

@[simp]
theorem isMultiplyPretransitive_mapPermCongr_iff (e : α ≃ β) (G : Subgroup (Perm α)) (n : ℕ) :
    IsMultiplyPretransitive (mapPermCongr e G) β n ↔ IsMultiplyPretransitive G α n :=
  (IsPretransitive.of_embedding_congr (f := permCongrActionHom e G)
    (equivMapPermCongr e G).surjective (permCongrActionHom_bijective e G)).symm

theorem isMultiplyPretransitive_mapPermCongr (e : α ≃ β) (G : Subgroup (Perm α)) (n : ℕ)
    [IsMultiplyPretransitive G α n] : IsMultiplyPretransitive (mapPermCongr e G) β n :=
  (isMultiplyPretransitive_mapPermCongr_iff e G n).mpr inferInstance

@[simp]
theorem isPreprimitive_mapPermCongr_iff (e : α ≃ β) (G : Subgroup (Perm α)) :
    IsPreprimitive (mapPermCongr e G) β ↔ IsPreprimitive G α :=
  (isPreprimitive_congr (f := permCongrActionHom e G)
    (equivMapPermCongr e G).surjective (permCongrActionHom_bijective e G)).symm

theorem isPreprimitive_mapPermCongr (e : α ≃ β) (G : Subgroup (Perm α))
    [IsPreprimitive G α] : IsPreprimitive (mapPermCongr e G) β :=
  (isPreprimitive_mapPermCongr_iff e G).mpr inferInstance

/-- Transfer `IsProductActionType` forward along an equivalence `e : α ≃ β`. -/
theorem IsProductActionType.mapPermCongr (e : α ≃ β) {G : Subgroup (Perm α)}
    (h : IsProductActionType G) : IsProductActionType (Maroti.mapPermCongr e G) := by
  obtain ⟨m, k, r, e₀, hm, hk, h2k, hr, hg, ha⟩ := h
  refine ⟨m, k, r, e.symm.trans e₀, hm, hk, h2k, hr, ?_, ?_⟩
  · rintro _ ⟨g, hgG, rfl⟩
    obtain ⟨σ, h_perm, hgh⟩ := hg g hgG
    refine ⟨σ, h_perm, ?_⟩
    rw [← hgh]
    ext x
    simp [permCongrMulEquiv]
  · intro a
    refine ⟨e₀.symm.permCongr (productActionPerm 1 fun i => (a i : Perm (Fin m))), ha a, ?_⟩
    ext x
    simp [permCongrMulEquiv]

/-- Transfer `IsProductActionType` back along an equivalence `e : α ≃ β`. -/
theorem IsProductActionType.of_mapPermCongr (e : α ≃ β) {G : Subgroup (Perm α)}
    (h : IsProductActionType (Maroti.mapPermCongr e G)) : IsProductActionType G := by
  simpa using h.mapPermCongr e.symm

@[simp]
theorem isProductActionType_mapPermCongr_iff (e : α ≃ β) (G : Subgroup (Perm α)) :
    IsProductActionType (mapPermCongr e G) ↔ IsProductActionType G :=
  ⟨IsProductActionType.of_mapPermCongr e, IsProductActionType.mapPermCongr e⟩

/-- Transfer `IsWreathType` forward along an equivalence `e : α ≃ β`. -/
theorem IsWreathType.mapPermCongr (e : α ≃ β) {G : Subgroup (Perm α)}
    (h : IsWreathType G) : IsWreathType (Maroti.mapPermCongr e G) := by
  obtain ⟨m, k, r, e₀, hm, hg, ha⟩ := h
  refine ⟨m, k, r, e.symm.trans e₀, hm, ?_, ?_⟩
  · rintro _ ⟨g, hgG, rfl⟩
    obtain ⟨σ, h_perm, hgh⟩ := hg g hgG
    refine ⟨σ, h_perm, ?_⟩
    rw [← hgh]
    ext x
    simp [permCongrMulEquiv]
  · intro a
    refine ⟨e₀.symm.permCongr (productActionPerm 1 fun i => (a i : Perm (Fin m))), ha a, ?_⟩
    ext x
    simp [permCongrMulEquiv]

/-- Transfer `IsWreathType` back along an equivalence `e : α ≃ β`. -/
theorem IsWreathType.of_mapPermCongr (e : α ≃ β) {G : Subgroup (Perm α)}
    (h : IsWreathType (Maroti.mapPermCongr e G)) : IsWreathType G := by
  simpa using h.mapPermCongr e.symm

@[simp]
theorem isWreathType_mapPermCongr_iff (e : α ≃ β) (G : Subgroup (Perm α)) :
    IsWreathType (mapPermCongr e G) ↔ IsWreathType G :=
  ⟨IsWreathType.of_mapPermCongr e, IsWreathType.mapPermCongr e⟩

/-- Transfer `IsMathieuType` forward along an equivalence `e : α ≃ β`. -/
theorem IsMathieuType.mapPermCongr (e : α ≃ β) {G : Subgroup (Perm α)}
    (h : IsMathieuType G) : IsMathieuType (Maroti.mapPermCongr e G) := by
  obtain ⟨s, hs, hcard, h4, ⟨eG⟩⟩ := h
  refine ⟨s, hs, (Nat.card_congr e.symm).trans hcard,
    (isMultiplyPretransitive_mapPermCongr_iff e G 4).mpr h4,
    ⟨(equivMapPermCongr e G).symm.trans eG⟩⟩

/-- Transfer `IsMathieuType` back along an equivalence `e : α ≃ β`. -/
theorem IsMathieuType.of_mapPermCongr (e : α ≃ β) {G : Subgroup (Perm α)}
    (h : IsMathieuType (Maroti.mapPermCongr e G)) : IsMathieuType G := by
  simpa using h.mapPermCongr e.symm

@[simp]
theorem isMathieuType_mapPermCongr_iff (e : α ≃ β) (G : Subgroup (Perm α)) :
    IsMathieuType (mapPermCongr e G) ↔ IsMathieuType G :=
  ⟨IsMathieuType.of_mapPermCongr e, IsMathieuType.mapPermCongr e⟩

/-- Transfer `Conclusion` forward along an equivalence `e : α ≃ β`. -/
theorem Conclusion.mapPermCongr (e : α ≃ β) {G : Subgroup (Perm α)}
    (h : Conclusion G) : Conclusion (Maroti.mapPermCongr e G) := by
  rcases h with h1 | h2 | h3
  · exact Or.inl (h1.mapPermCongr e)
  · exact Or.inr (Or.inl (h2.mapPermCongr e))
  · refine Or.inr (Or.inr ?_)
    rwa [card_mapPermCongr, Nat.card_congr e.symm]

/-- Transfer `Conclusion` back along an equivalence `e : α ≃ β`. -/
theorem Conclusion.of_mapPermCongr (e : α ≃ β) {G : Subgroup (Perm α)}
    (h : Conclusion (Maroti.mapPermCongr e G)) : Conclusion G := by
  simpa using h.mapPermCongr e.symm

@[simp]
theorem conclusion_mapPermCongr_iff (e : α ≃ β) (G : Subgroup (Perm α)) :
    Conclusion (mapPermCongr e G) ↔ Conclusion G :=
  ⟨Conclusion.of_mapPermCongr e, Conclusion.mapPermCongr e⟩

/-- Universe-polymorphic form of `Maroti.step1`, obtained by transferring along
`Finite.equivFin α : α ≃ Fin (Nat.card α)`. -/
theorem step1_univ (hAS : AlmostSimpleCase fun _ _ => True) (hAut : AutBound IsNonabelianSimple)
    {α : Type u} [Finite α] [Nontrivial α] (G : Subgroup (Perm α)) [IsPreprimitive G α] :
    Conclusion G := by
  let e : α ≃ Fin (Nat.card α) := Finite.equivFin α
  have : Nontrivial (Fin (Nat.card α)) := e.symm.nontrivial
  have : IsPreprimitive (mapPermCongr e G) (Fin (Nat.card α)) :=
    isPreprimitive_mapPermCongr e G
  exact (step1 hAS hAut (mapPermCongr e G)).of_mapPermCongr e

/-- Theorem 1.1 of Maróti (2002) for a finite primitive permutation group `G ≤ Perm α` of degree at
least `2` in any universe, assuming the almost simple case (`AlmostSimpleCase fun _ _ => True`) and
the automorphism bound (`AutBound IsNonabelianSimple`). -/
theorem theorem_1_1_of_step1 (hAS : AlmostSimpleCase fun _ _ => True)
    (hAut : AutBound IsNonabelianSimple)
    {α : Type u} [Finite α] [Nontrivial α] (G : Subgroup (Perm α)) [IsPreprimitive G α] :
    IsProductActionType G ∨ IsMathieuType G ∨
      (Nat.card G ≤ bound (Nat.card α) ∧
        bound (Nat.card α) < Nat.card α ^ (1 + Nat.log 2 (Nat.card α))) := by
  rcases step1_univ hAS hAut G with h1 | h2 | h3
  · exact Or.inl h1.isProductActionType
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr ⟨h3, bound_lt_pow Finite.one_lt_card⟩)

end Maroti
