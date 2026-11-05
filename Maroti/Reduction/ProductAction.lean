module

public import Maroti.Alternating.SubsetAction
public import Maroti.Reduction.ProductType
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import CFSG.Sporadic.Bridge.M11
public import CFSG.Sporadic.Bridge.M12
public import CFSG.Sporadic.Presentation.M23
public import CFSG.Sporadic.Presentation.M24Exact

/-!
# Product action reduction

This file completes the product action case of Step 1 in Section 2 of A. Maróti,
*On the orders of primitive groups*, J. Algebra 258 (2002), pages 633–634, where a minimal normal
subgroup `N` of `G` has `r ≥ 2` simple factors `F.S i`, `stabilizer N ω ≠ ⊥`, and every
projection `R i = (stabilizer N ω).map (F.proj i)` is a proper subgroup of `F.S i`.

The normalizer of `F.S i` in `G` induces a permutation group `SimpleFactors.H` on the coordinate
space `Δ i = F.S i ⧸ R i`. The group `G` embeds into the wreath product of `H 0` by `Perm (Fin r)`,
so `|G| ≤ r! · |H 0|^r` and `|α| = |Δ 0|^r` (`SimpleFactors.card_le_factorial_mul_card_H_pow`,
`SimpleFactors.card_α_eq_pow_card_Δ`). Furthermore, `H i` acts primitively on `Δ i`
(`SimpleFactors.isPreprimitive_H`) and is almost simple with socle `F.S i`
(`SimpleFactors.isAlmostSimpleWith_H`).

Applying the almost simple hypothesis `hAS` to `H 0` yields `Conclusion G`
(`SimpleFactors.conclusion_of_forall_map_proj_ne_top`). When `H 0` has subset action type on
`Δ 0`, the group `G` has wreath type on `α`
(`SimpleFactors.isWreathType_of_isSubsetActionType_H`). When `H 0` has Mathieu type on
`Δ 0` (using the order bounds from `CFSG/Sporadic/Bridge/M11.lean`,
`CFSG/Sporadic/Bridge/M12.lean`, `CFSG/Sporadic/Presentation/M23.lean`, and
`CFSG/Sporadic/Presentation/M24Exact.lean`) or satisfies `|H 0| ≤ bound |Δ 0|`, the wreath product
inequalities `factorial_mul_pow_le_bound_of_mathieu` and `factorial_mul_bound_pow_le` give
`|G| ≤ bound |α|`.
-/

@[expose] public section

namespace Maroti

open Equiv MulAction CFSG.Holt.General.AltRecPrim

/-- The equivalence `Equiv.permCongr` packaged as a multiplicative equivalence
`Perm β ≃* Perm γ`. -/
def permCongrMulEquiv {β γ : Type*} (e : β ≃ γ) : Perm β ≃* Perm γ :=
  { e.permCongr with
    map_mul' := fun _ _ => by
      ext x
      simp }

namespace SimpleFactors

variable {α : Type} {G : Subgroup (Perm α)} {N : Subgroup G} (F : SimpleFactors N)

theorem proj_coe_S (i : Fin F.r) (s : F.S i) :
    F.proj i ⟨(s : G), F.le i s.2⟩ = s := by
  have he : F.e (Pi.mulSingle i s) = ⟨(s : G), F.le i s.2⟩ :=
    Subtype.ext (F.e_mulSingle i s)
  rw [← he, SimpleFactors.proj_apply, MulEquiv.symm_apply_apply, Pi.mulSingle_eq_same]

theorem mk_eq_one_iff (ω : α) (i : Fin F.r) (s : F.S i) :
    (QuotientGroup.mk s : Δ F ω i) = QuotientGroup.mk 1 ↔ s ∈ R F ω i := by
  rw [QuotientGroup.eq, mul_one, inv_mem_iff]

theorem coordPermHom_inv_apply (hN : N.Normal) {g : G} {i j : Fin F.r}
    (hij : coordPermHom F hN g i = j) :
    coordPermHom F hN g⁻¹ j = i := by
  rw [map_inv, Perm.inv_def]
  exact (coordPermHom F hN g).injective (by simp [hij])

/-- Conjugation homomorphism `F.S i →* F.S j` when `coordPermHom F hN g i = j`. -/
def conjSHom (hN : N.Normal) {g : G} {i j : Fin F.r} (hij : coordPermHom F hN g i = j) :
    F.S i →* F.S j where
  toFun s := ⟨g * (s : G) * g⁻¹, conj_mem_S_of_coordPermHom F hN hij s.2⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' a b := by
    apply Subtype.ext
    simp [mul_assoc]

/-- The subgroup of `G` stabilizing the coordinate `i : Fin F.r` under `coordPermHom`. -/
noncomputable def normFactor (hN : N.Normal) (i : Fin F.r) : Subgroup G :=
  (stabilizer (Perm (Fin F.r)) i).comap (coordPermHom F hN)

theorem mem_normFactor_iff (hN : N.Normal) (i : Fin F.r) {g : G} :
    g ∈ normFactor F hN i ↔ coordPermHom F hN g i = i := Iff.rfl

/-- The image of `F.S i` in `Perm (Δ F ω i)`. -/
noncomputable def T₀ (ω : α) (i : Fin F.r) : Subgroup (Perm (Δ F ω i)) :=
  (MulAction.toPermHom (F.S i) (Δ F ω i)).range

theorem five_le_card_Δ [Finite α] (ω : α) (hR : ∀ l : Fin F.r, R F ω l ≠ ⊤) (i : Fin F.r) :
    5 ≤ Nat.card (Δ F ω i) := by
  rw [← Subgroup.index_eq_card]
  exact five_le_index_of_isNonabelianSimple (isNonabelianSimple_S F i) (R F ω i) (hR i)

theorem nontrivial_Δ [Finite α] (ω : α) (hR : ∀ l : Fin F.r, R F ω l ≠ ⊤) (i : Fin F.r) :
    Nontrivial (Δ F ω i) := by
  have : Finite (Δ F ω i) := inferInstance
  have h5 := five_le_card_Δ F ω hR i
  exact Finite.one_lt_card_iff_nontrivial.mp (by omega)

theorem toPermHom_S_injective (ω : α) (hR : ∀ l : Fin F.r, R F ω l ≠ ⊤) (i : Fin F.r) :
    Function.Injective (MulAction.toPermHom (F.S i) (Δ F ω i)) := by
  have := F.isSimpleGroup i
  rw [← MonoidHom.ker_eq_bot_iff]
  rcases (MulAction.toPermHom (F.S i) (Δ F ω i)).normal_ker.eq_bot_or_eq_top with hbot | htop
  · exact hbot
  · exfalso
    apply hR i
    rw [eq_top_iff]
    intro s _
    have hs : s ∈ (MulAction.toPermHom (F.S i) (Δ F ω i)).ker := htop ▸ Subgroup.mem_top s
    have hfix : (QuotientGroup.mk (s * 1) : Δ F ω i) = QuotientGroup.mk 1 :=
      congrArg (fun p : Perm (Δ F ω i) => p (QuotientGroup.mk 1)) (MonoidHom.mem_ker.mp hs)
    rw [mul_one] at hfix
    exact (mk_eq_one_iff F ω i s).mp hfix

section ActionOnDelta

variable [IsPreprimitive G α] [Nontrivial α]

theorem actCoord_coe_S (hN : N.Normal) (ω : α) (hR : ∀ l : Fin F.r, R F ω l ≠ ⊤)
    (i : Fin F.r) (s : F.S i) (d : Δ F ω i) :
    actCoord F hN ω hR (s : G) i i d = s • d := by
  have := coordEquiv_of_mem_N F hN ω hR ⟨(s : G), F.le i s.2⟩ i d
  rwa [coordEquiv_apply, proj_coe_S] at this

theorem actCoord_smul (hN : N.Normal) (ω : α) (hR : ∀ l : Fin F.r, R F ω l ≠ ⊤)
    (g : G) {i j : Fin F.r} (hij : coordPermHom F hN g i = j) (s : F.S i) (d : Δ F ω i) :
    actCoord F hN ω hR g i j (s • d) =
      (⟨g * (s : G) * g⁻¹, conj_mem_S_of_coordPermHom F hN hij s.2⟩ : F.S j) •
        actCoord F hN ω hR g i j d := by
  let s' : F.S j := ⟨g * (s : G) * g⁻¹, conj_mem_S_of_coordPermHom F hN hij s.2⟩
  have hs_i : coordPermHom F hN (s : G) i = i := by
    rw [coordPermHom_eq_of_mem_N F hN (F.le i s.2), Perm.one_apply]
  have hs_j : coordPermHom F hN (s' : G) j = j := by
    rw [coordPermHom_eq_of_mem_N F hN (F.le j s'.2), Perm.one_apply]
  have hmul : g * (s : G) = (s' : G) * g := by
    simp [s', mul_assoc]
  calc actCoord F hN ω hR g i j (s • d)
      = actCoord F hN ω hR g i j (actCoord F hN ω hR (s : G) i i d) := by
          rw [actCoord_coe_S]
    _ = actCoord F hN ω hR (g * (s : G)) i j d :=
          (actCoord_mul F hN ω hR g (s : G) hs_i hij d).symm
    _ = actCoord F hN ω hR ((s' : G) * g) i j d := by rw [hmul]
    _ = actCoord F hN ω hR (s' : G) j j (actCoord F hN ω hR g i j d) :=
          actCoord_mul F hN ω hR (s' : G) g hij hs_j d
    _ = s' • actCoord F hN ω hR g i j d := actCoord_coe_S F hN ω hR j s' _

/-- The homomorphism from `normFactor F hN i` to `Perm (Δ F ω i)`. -/
noncomputable def coordHom (hN : N.Normal) (ω : α) (hR : ∀ l : Fin F.r, R F ω l ≠ ⊤)
    (i : Fin F.r) : normFactor F hN i →* Perm (Δ F ω i) where
  toFun g := coordEquiv F hN ω hR g.1 g.2
  map_one' := Equiv.ext (actCoord_one F hN ω hR i)
  map_mul' g₁ g₂ := Equiv.ext (actCoord_mul F hN ω hR g₁.1 g₂.1 g₂.2 g₁.2)

/-- The permutation group `H i ≤ Perm (Δ F ω i)` induced by `normFactor F hN i`. -/
noncomputable def H (hN : N.Normal) (ω : α) (hR : ∀ l : Fin F.r, R F ω l ≠ ⊤)
    (i : Fin F.r) : Subgroup (Perm (Δ F ω i)) :=
  (coordHom F hN ω hR i).range

theorem toPerm_eq_coordHom_coe_S (hN : N.Normal) (ω : α) (hR : ∀ l : Fin F.r, R F ω l ≠ ⊤)
    (i : Fin F.r) (s : F.S i) :
    MulAction.toPermHom (F.S i) (Δ F ω i) s =
      coordHom F hN ω hR i ⟨(s : G), by
        rw [mem_normFactor_iff, coordPermHom_eq_of_mem_N F hN (F.le i s.2), Perm.one_apply]⟩ := by
  ext d
  exact (actCoord_coe_S F hN ω hR i s d).symm

theorem toPerm_mem_H (hN : N.Normal) (ω : α) (hR : ∀ l : Fin F.r, R F ω l ≠ ⊤)
    (i : Fin F.r) (s : F.S i) :
    MulAction.toPermHom (F.S i) (Δ F ω i) s ∈ H F hN ω hR i :=
  ⟨⟨(s : G), by
    rw [mem_normFactor_iff, coordPermHom_eq_of_mem_N F hN (F.le i s.2), Perm.one_apply]⟩,
    (toPerm_eq_coordHom_coe_S F hN ω hR i s).symm⟩

theorem T₀_le_H (hN : N.Normal) (ω : α) (hR : ∀ l : Fin F.r, R F ω l ≠ ⊤)
    (i : Fin F.r) : T₀ F ω i ≤ H F hN ω hR i := by
  rintro _ ⟨s, rfl⟩
  exact toPerm_mem_H F hN ω hR i s

theorem coordEquiv_conj_toPerm (hN : N.Normal) (ω : α) (hR : ∀ l : Fin F.r, R F ω l ≠ ⊤)
    (g : G) {i j : Fin F.r} (hij : coordPermHom F hN g i = j) (s : F.S i) :
    (coordEquiv F hN ω hR g hij).permCongr (MulAction.toPermHom (F.S i) (Δ F ω i) s) =
      MulAction.toPermHom (F.S j) (Δ F ω j)
        ⟨g * (s : G) * g⁻¹, conj_mem_S_of_coordPermHom F hN hij s.2⟩ := by
  ext d
  change actCoord F hN ω hR g i j (s • (coordEquiv F hN ω hR g hij).symm d) = _
  rw [actCoord_smul F hN ω hR g hij s]
  exact congrArg _ ((coordEquiv F hN ω hR g hij).apply_symm_apply d)

theorem H_conj_mem_T₀ (hN : N.Normal) (ω : α) (hR : ∀ l : Fin F.r, R F ω l ≠ ⊤)
    (i : Fin F.r) :
    ∀ h ∈ H F hN ω hR i, ∀ t ∈ T₀ F ω i, h * t * h⁻¹ ∈ T₀ F ω i := by
  rintro _ ⟨g, rfl⟩ _ ⟨s, rfl⟩
  refine ⟨⟨g.1 * (s : G) * g.1⁻¹, conj_mem_S_of_coordPermHom F hN g.2 s.2⟩, ?_⟩
  exact (coordEquiv_conj_toPerm F hN ω hR g.1 g.2 s).symm

/-- Conjugation by `coordEquiv F hN ω hR g hij` maps `H F hN ω hR i` onto `H F hN ω hR j`. -/
theorem map_permCongr_H (hN : N.Normal) (ω : α) (hR : ∀ l : Fin F.r, R F ω l ≠ ⊤)
    (g : G) {i j : Fin F.r} (hij : coordPermHom F hN g i = j) :
    (H F hN ω hR i).map (permCongrMulEquiv (coordEquiv F hN ω hR g hij)).toMonoidHom =
      H F hN ω hR j := by
  have hij' : coordPermHom F hN g⁻¹ j = i := coordPermHom_inv_apply F hN hij
  apply le_antisymm
  · rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    have hx : coordPermHom F hN x.1 i = i := x.2
    have hgx : g * x.1 * g⁻¹ ∈ normFactor F hN j := by
      rw [mem_normFactor_iff, map_mul, map_mul, Perm.mul_apply, Perm.mul_apply, hij', hx, hij]
    refine ⟨⟨g * x.1 * g⁻¹, hgx⟩, ?_⟩
    ext d
    change actCoord F hN ω hR (g * x.1 * g⁻¹) j j d =
      actCoord F hN ω hR g i j (actCoord F hN ω hR x.1 i i (actCoord F hN ω hR g⁻¹ j i d))
    rw [actCoord_mul F hN ω hR (g * x.1) g⁻¹ hij' (by rw [map_mul, Perm.mul_apply, hx, hij]),
      actCoord_mul F hN ω hR g x.1 hx hij]
  · rintro _ ⟨y, rfl⟩
    have hy : coordPermHom F hN y.1 j = j := y.2
    have hgy : g⁻¹ * y.1 * g ∈ normFactor F hN i := by
      rw [mem_normFactor_iff, map_mul, map_mul, Perm.mul_apply, Perm.mul_apply, hij, hy, hij']
    refine ⟨coordHom F hN ω hR i ⟨g⁻¹ * y.1 * g, hgy⟩, ⟨⟨g⁻¹ * y.1 * g, hgy⟩, rfl⟩, ?_⟩
    ext d
    change actCoord F hN ω hR g i j
        (actCoord F hN ω hR (g⁻¹ * y.1 * g) i i (actCoord F hN ω hR g⁻¹ j i d)) =
      actCoord F hN ω hR y.1 j j d
    have hgy' : coordPermHom F hN (g⁻¹ * y.1 * g) i = i := hgy
    rw [← actCoord_mul F hN ω hR (g⁻¹ * y.1 * g) g⁻¹ hij' hgy',
      ← actCoord_mul F hN ω hR g (g⁻¹ * y.1 * g * g⁻¹)
        (by rw [map_mul, Perm.mul_apply, hij', hgy']) hij]
    have hgrp : g * (g⁻¹ * y.1 * g * g⁻¹) = y.1 := by group
    rw [hgrp]

/-- The homomorphism from `(coordPermHom F hN).ker` to `∀ i, H F hN ω hR i`. -/
noncomputable def kerToPiH (hN : N.Normal) (ω : α) (hR : ∀ l : Fin F.r, R F ω l ≠ ⊤) :
    (coordPermHom F hN).ker →* ∀ i : Fin F.r, H F hN ω hR i :=
  MonoidHom.pi fun i =>
    (coordHom F hN ω hR i).rangeRestrict.comp
      (Subgroup.inclusion fun _ hk => by
        rw [mem_normFactor_iff, MonoidHom.mem_ker.mp hk, Perm.one_apply])

theorem kerToPiH_injective (hN : N.Normal) (ω : α) (hR : ∀ l : Fin F.r, R F ω l ≠ ⊤) :
    Function.Injective (kerToPiH F hN ω hR) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro k hk
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  apply Subtype.ext
  ext x
  change (k.1 : G) • x = x
  apply (toCoord F hN ω hR).injective
  funext i
  have hki : coordPermHom F hN k.1 i = i := by
    rw [MonoidHom.mem_ker.mp k.2, Perm.one_apply]
  rw [toCoord_smul_eq_coordEquiv F hN ω hR k.1 hki x]
  have h1 := congrArg (fun f : ∀ j, H F hN ω hR j =>
    ((f i : Perm (Δ F ω i)) (toCoord F hN ω hR x i))) (MonoidHom.mem_ker.mp hk)
  exact h1

theorem card_Δ_eq [Finite α] (hN : N.Normal) (ω : α) (hR : ∀ l : Fin F.r, R F ω l ≠ ⊤)
    (i j : Fin F.r) : Nat.card (Δ F ω i) = Nat.card (Δ F ω j) := by
  obtain ⟨g, hij⟩ := exists_coordPermHom_eq F hN i j
  exact Nat.card_congr (coordEquiv F hN ω hR g hij)

theorem card_α_eq_pow_card_Δ [Finite α] (hN : N.Normal) (ω : α)
    (hR : ∀ l : Fin F.r, R F ω l ≠ ⊤) :
    Nat.card α = Nat.card (Δ F ω ⟨0, F.one_le⟩) ^ F.r := by
  rw [Nat.card_congr (toCoord F hN ω hR), Nat.card_pi]
  have hcongr : ∀ i : Fin F.r, Nat.card (Δ F ω i) = Nat.card (Δ F ω ⟨0, F.one_le⟩) :=
    fun i => card_Δ_eq F hN ω hR i ⟨0, F.one_le⟩
  simp [hcongr]

theorem card_H_eq [Finite α] (hN : N.Normal) (ω : α) (hR : ∀ l : Fin F.r, R F ω l ≠ ⊤)
    (i j : Fin F.r) : Nat.card (H F hN ω hR i) = Nat.card (H F hN ω hR j) := by
  obtain ⟨g, hij⟩ := exists_coordPermHom_eq F hN i j
  let e := permCongrMulEquiv (coordEquiv F hN ω hR g hij)
  have hequiv : H F hN ω hR i ≃* H F hN ω hR j :=
    ((H F hN ω hR i).equivMapOfInjective e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr (map_permCongr_H F hN ω hR g hij))
  exact Nat.card_congr hequiv.toEquiv

/-- In the product action case, `|G| ≤ r! · |H 0|^r`. -/
theorem card_le_factorial_mul_card_H_pow [Finite α] (hN : N.Normal) (ω : α)
    (hR : ∀ l : Fin F.r, R F ω l ≠ ⊤) :
    Nat.card G ≤ F.r.factorial * Nat.card (H F hN ω hR ⟨0, F.one_le⟩) ^ F.r := by
  let K := (coordPermHom F hN).ker
  have hidx : K.index ≤ F.r.factorial := by
    rw [Subgroup.index_ker]
    have := Nat.card_le_card_of_injective (coordPermHom F hN).range.subtype Subtype.val_injective
    rw [Nat.card_eq_fintype_card (α := Perm (Fin F.r)), Fintype.card_perm, Fintype.card_fin] at this
    exact this
  have hker : Nat.card K ≤ Nat.card (H F hN ω hR ⟨0, F.one_le⟩) ^ F.r := by
    have hinj := Nat.card_le_card_of_injective (kerToPiH F hN ω hR) (kerToPiH_injective F hN ω hR)
    have hpi : Nat.card (∀ i : Fin F.r, H F hN ω hR i) =
        Nat.card (H F hN ω hR ⟨0, F.one_le⟩) ^ F.r := by
      simp only [Nat.card_pi]
      have hcongr : ∀ i : Fin F.r,
          Nat.card (H F hN ω hR i) = Nat.card (H F hN ω hR ⟨0, F.one_le⟩) :=
        fun i => card_H_eq F hN ω hR i ⟨0, F.one_le⟩
      simp [hcongr]
    exact hinj.trans hpi.le
  calc Nat.card G = K.index * Nat.card K := by rw [mul_comm, K.card_mul_index]
    _ ≤ F.r.factorial * Nat.card (H F hN ω hR ⟨0, F.one_le⟩) ^ F.r :=
        Nat.mul_le_mul hidx hker

theorem isPretransitive_H (hN : N.Normal) (ω : α) (hR : ∀ l : Fin F.r, R F ω l ≠ ⊤)
    (i : Fin F.r) : IsPretransitive (H F hN ω hR i) (Δ F ω i) := by
  refine ⟨fun x y => ?_⟩
  obtain ⟨s₁, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨s₂, rfl⟩ := QuotientGroup.mk_surjective y
  refine ⟨⟨MulAction.toPermHom (F.S i) (Δ F ω i) (s₂ * s₁⁻¹),
    toPerm_mem_H F hN ω hR i (s₂ * s₁⁻¹)⟩, ?_⟩
  change (s₂ * s₁⁻¹) • (QuotientGroup.mk s₁ : Δ F ω i) = QuotientGroup.mk s₂
  change QuotientGroup.mk (s₂ * s₁⁻¹ * s₁) = QuotientGroup.mk s₂
  rw [inv_mul_cancel_right]

/-- The component group `H F hN ω hR i₀` acts preprimitively on `Δ F ω i₀`. -/
theorem isPreprimitive_H [Finite α] (hN : N.Normal) (ω : α) (hR : ∀ l : Fin F.r, R F ω l ≠ ⊤)
    (i₀ : Fin F.r) : IsPreprimitive (H F hN ω hR i₀) (Δ F ω i₀) := by
  have : IsPretransitive (H F hN ω hR i₀) (Δ F ω i₀) := isPretransitive_H F hN ω hR i₀
  have : Nontrivial (Δ F ω i₀) := nontrivial_Δ F ω hR i₀
  have : IsPretransitive N α := isPretransitive_N F hN
  let d₀ : Δ F ω i₀ := QuotientGroup.mk 1
  rw [← isCoatom_stabilizer_iff_preprimitive (G := H F hN ω hR i₀) d₀]
  let M₀ := stabilizer (H F hN ω hR i₀) d₀
  refine ⟨?_, fun L hML => ?_⟩
  · intro htop
    obtain ⟨d, hd⟩ := exists_ne d₀
    obtain ⟨h, rfl⟩ := exists_smul_eq (H F hN ω hR i₀) d₀ d
    exact hd (mem_stabilizer_iff.mp (htop ▸ Subgroup.mem_top h))
  · let tHom : F.S i₀ →* H F hN ω hR i₀ :=
      (MulAction.toPermHom (F.S i₀) (Δ F ω i₀)).codRestrict (H F hN ω hR i₀)
        (toPerm_mem_H F hN ω hR i₀)
    have htHom_smul : ∀ s : F.S i₀, tHom s • d₀ = QuotientGroup.mk s := by
      intro s
      change QuotientGroup.mk (s * 1) = QuotientGroup.mk s
      rw [mul_one]
    let Q₀ : Subgroup (F.S i₀) := L.comap tHom
    have hmem_L_iff : ∀ (h : H F hN ω hR i₀) (s : F.S i₀),
        h • d₀ = QuotientGroup.mk s → (h ∈ L ↔ s ∈ Q₀) := by
      intro h s hsd
      have hstab : (tHom s)⁻¹ * h ∈ M₀ := by
        rw [mem_stabilizer_iff, mul_smul, inv_smul_eq_iff, hsd, htHom_smul]
      have hL_mem : (tHom s)⁻¹ * h ∈ L := le_of_lt hML hstab
      have hmul : h = tHom s * ((tHom s)⁻¹ * h) := (mul_inv_cancel_left (tHom s) h).symm
      constructor
      · intro hh
        have hts : tHom s ∈ L := by
          have := mul_mem hh (inv_mem hL_mem)
          simpa [mul_assoc] using this
        exact hts
      · intro hs
        rw [hmul]
        exact mul_mem hs hL_mem
    have hR_le_Q₀ : R F ω i₀ ≤ Q₀ := by
      intro s hs
      have h1 : (QuotientGroup.mk s : Δ F ω i₀) = d₀ :=
        (mk_eq_one_iff F ω i₀ s).mpr hs
      have hstab : tHom s ∈ M₀ := by
        rw [mem_stabilizer_iff, htHom_smul, h1]
      exact le_of_lt hML hstab
    have hQ₀_inv : ∀ {g : G}, g ∈ stabilizer G ω →
        ∀ (hg : coordPermHom F hN g i₀ = i₀) {s : F.S i₀}, s ∈ Q₀ →
        conjSHom F hN hg s ∈ Q₀ := by
      intro g hgω hg s hs
      let gH : H F hN ω hR i₀ := ⟨coordHom F hN ω hR i₀ ⟨g, hg⟩, ⟨g, hg⟩, rfl⟩
      have hgH_stab : gH ∈ M₀ := by
        rw [mem_stabilizer_iff]
        change coordEquiv F hN ω hR g hg (QuotientGroup.mk 1) = QuotientGroup.mk 1
        rw [coordEquiv_of_mem_stabilizer F hN ω hR hgω hg 1]
        congr 1
        apply Subtype.ext
        simp
      have hgH_L : gH ∈ L := le_of_lt hML hgH_stab
      have hconj_L : gH * tHom s * gH⁻¹ ∈ L :=
        mul_mem (mul_mem hgH_L hs) (inv_mem hgH_L)
      have hconj_eq : gH * tHom s * gH⁻¹ = tHom (conjSHom F hN hg s) := by
        apply Subtype.ext
        exact coordEquiv_conj_toPerm F hN ω hR g hg s
      rwa [hconj_eq] at hconj_L
    choose g_stab hg_stab hg_coord using fun i : Fin F.r =>
      exists_mem_stabilizer_coordPermHom_eq F hN ω i₀ i
    have hg_inv_coord : ∀ i : Fin F.r, coordPermHom F hN (g_stab i)⁻¹ i = i₀ :=
      fun i => coordPermHom_inv_apply F hN (hg_coord i)
    let Q : ∀ i : Fin F.r, Subgroup (F.S i) :=
      fun i => Q₀.comap (conjSHom F hN (hg_inv_coord i))
    have hQi₀ : Q i₀ = Q₀ := by
      ext s
      simp only [Q, Subgroup.mem_comap]
      constructor
      · intro hs
        have h1 := hQ₀_inv (hg_stab i₀) (hg_coord i₀) hs
        have heq : conjSHom F hN (hg_coord i₀) (conjSHom F hN (hg_inv_coord i₀) s) = s := by
          apply Subtype.ext
          simp only [conjSHom, MonoidHom.coe_mk, OneHom.coe_mk]
          group
        rwa [heq] at h1
      · intro hs
        exact hQ₀_inv (inv_mem (hg_stab i₀)) (hg_inv_coord i₀) hs
    have hRQ : ∀ i : Fin F.r, R F ω i ≤ Q i := by
      intro i s hs
      simp only [Q, Subgroup.mem_comap]
      exact hR_le_Q₀ (conj_mem_R F hN ω (inv_mem (hg_stab i)) (hg_inv_coord i) hs)
    have hQ_inv : IsStabInvariant F hN ω Q := by
      intro g hgω i j hij s hs
      simp only [Q, Subgroup.mem_comap] at hs ⊢
      let u : G := (g_stab j)⁻¹ * g * g_stab i
      have huω : u ∈ stabilizer G ω :=
        mul_mem (mul_mem (inv_mem (hg_stab j)) hgω) (hg_stab i)
      have hu_coord : coordPermHom F hN u i₀ = i₀ := by
        rw [map_mul, map_mul, Perm.mul_apply, Perm.mul_apply,
          hg_coord i, hij, hg_inv_coord j]
      have huQ := hQ₀_inv huω hu_coord hs
      have heq : conjSHom F hN hu_coord (conjSHom F hN (hg_inv_coord i) s) =
          conjSHom F hN (hg_inv_coord j)
            ⟨g * (s : G) * g⁻¹, conj_mem_S_of_coordPermHom F hN hij s.2⟩ := by
        apply Subtype.ext
        simp only [conjSHom, MonoidHom.coe_mk, OneHom.coe_mk, u]
        group
      rwa [heq] at huQ
    rcases prodSubgroup_le_stabilizer_or_eq_top F hN ω Q hQ_inv hRQ with hle | htop
    · exfalso
      have hQ₀_le_R : Q₀ ≤ R F ω i₀ := by
        rw [← hQi₀]
        intro s hs
        let n : N := F.e (Pi.mulSingle i₀ s)
        have hnQ : n ∈ prodSubgroup F Q := by
          rw [mem_prodSubgroup_iff]
          intro j
          rw [SimpleFactors.proj_apply, MulEquiv.symm_apply_apply]
          by_cases hj : j = i₀
          · subst hj
            simpa using hs
          · rw [Pi.mulSingle_eq_of_ne hj]
            exact one_mem (Q j)
        have hn_stab : n ∈ stabilizer N ω := hle hnQ
        have hproj : F.proj i₀ n = s := by
          rw [SimpleFactors.proj_apply, MulEquiv.symm_apply_apply, Pi.mulSingle_eq_same]
        exact hproj ▸ ⟨n, hn_stab, rfl⟩
      have hLM : L ≤ M₀ := by
        intro h hh
        obtain ⟨s, hs⟩ := QuotientGroup.mk_surjective (h • d₀)
        have hsQ : s ∈ Q₀ := (hmem_L_iff h s hs.symm).mp hh
        have hsR : s ∈ R F ω i₀ := hQ₀_le_R hsQ
        rw [mem_stabilizer_iff, ← hs]
        exact (mk_eq_one_iff F ω i₀ s).mpr hsR
      exact hML.not_ge hLM
    · have hQ₀_top : Q₀ = ⊤ := hQi₀ ▸ htop i₀
      rw [eq_top_iff]
      intro h _
      obtain ⟨s, hs⟩ := QuotientGroup.mk_surjective (h • d₀)
      exact (hmem_L_iff h s hs.symm).mpr (hQ₀_top ▸ Subgroup.mem_top s)

omit [Nontrivial α] in
theorem R_ne_bot_of_stabilizer_ne_bot (hN : N.Normal) (ω : α)
    (hK : stabilizer N ω ≠ ⊥) (i : Fin F.r) :
    R F ω i ≠ ⊥ := by
  have : IsPretransitive N α := isPretransitive_N F hN
  intro hbot
  apply hK
  rw [eq_bot_iff]
  intro k hk
  rw [Subgroup.mem_bot]
  apply F.eq_one_of_forall_proj_eq_one
  intro j
  obtain ⟨g, hg, hij⟩ := exists_mem_stabilizer_coordPermHom_eq F hN ω j i
  have hj : F.proj j k ∈ R F ω j := ⟨k, hk, rfl⟩
  have hi := conj_mem_R F hN ω hg hij hj
  rw [hbot, Subgroup.mem_bot] at hi
  apply Subtype.ext
  have hval : g * (F.proj j k : G) * g⁻¹ = 1 := congrArg Subtype.val hi
  calc ((F.proj j k : F.S j) : G) = g⁻¹ * (g * (F.proj j k : G) * g⁻¹) * g := by group
    _ = 1 := by rw [hval]; group

/-- When `stabilizer N ω ≠ ⊥`, `H F hN ω hR i₀` is almost simple with socle `F.S i₀`. -/
theorem isAlmostSimpleWith_H [Finite α] (hN : N.Normal) (ω : α)
    (hR : ∀ l : Fin F.r, R F ω l ≠ ⊤) (hK : stabilizer N ω ≠ ⊥) (i₀ : Fin F.r) :
    IsAlmostSimpleWith (H F hN ω hR i₀) (F.S i₀) := by
  have : IsPreprimitive (H F hN ω hR i₀) (Δ F ω i₀) := isPreprimitive_H F hN ω hR i₀
  have hinj := toPermHom_S_injective F ω hR i₀
  let eT : F.S i₀ ≃* T₀ F ω i₀ :=
    MulEquiv.ofBijective (MulAction.toPermHom (F.S i₀) (Δ F ω i₀)).rangeRestrict
      ⟨fun a b h => hinj (congrArg Subtype.val h),
        (MulAction.toPermHom (F.S i₀) (Δ F ω i₀)).rangeRestrict_surjective⟩
  have : IsSimpleGroup (F.S i₀) := F.isSimpleGroup i₀
  refine ⟨T₀ F ω i₀, T₀_le_H F hN ω hR i₀, H_conj_mem_T₀ F hN ω hR i₀,
    eT.symm.isSimpleGroup, ?_, ?_, ⟨eT.symm⟩⟩
  · obtain ⟨a, ha, b, hb, hab⟩ := F.not_commute i₀
    refine ⟨eT ⟨a, ha⟩, eT ⟨b, hb⟩, fun h => hab ?_⟩
    rw [← map_mul, ← map_mul] at h
    exact congrArg Subtype.val (eT.injective h)
  · intro h hh hcomm
    let T_sub : Subgroup (H F hN ω hR i₀) := (T₀ F ω i₀).subgroupOf (H F hN ω hR i₀)
    let C : Subgroup (H F hN ω hR i₀) := Subgroup.centralizer (T_sub : Set (H F hN ω hR i₀))
    have hC_norm : C.Normal := by
      refine ⟨fun c hc g => Subgroup.mem_centralizer_iff.mpr fun t ht => ?_⟩
      have ht' : g⁻¹ * t * g ∈ T_sub := by
        change (g⁻¹ * t * g : H F hN ω hR i₀).1 ∈ T₀ F ω i₀
        have ht0 : t.1 ∈ T₀ F ω i₀ := ht
        simpa [mul_assoc] using H_conj_mem_T₀ F hN ω hR i₀ (g⁻¹).1 (g⁻¹).2 t.1 ht0
      have hc' := Subgroup.mem_centralizer_iff.mp hc (g⁻¹ * t * g) ht'
      calc t * (g * c * g⁻¹) = g * ((g⁻¹ * t * g) * c) * g⁻¹ := by group
        _ = g * (c * (g⁻¹ * t * g)) * g⁻¹ := by rw [hc']
        _ = (g * c * g⁻¹) * t := by group
    have hhC : (⟨h, hh⟩ : H F hN ω hR i₀) ∈ C := by
      rw [Subgroup.mem_centralizer_iff]
      intro t ht
      apply Subtype.ext
      exact (hcomm t.1 ht).symm
    have hC_bot : C = ⊥ := by
      by_contra hCne
      have htrC : IsPretransitive (C.map (H F hN ω hR i₀).subtype) (Δ F ω i₀) := by
        have htr : IsPretransitive C (Δ F ω i₀) := isPretransitive_of_normal_ne_bot hCne
        refine ⟨fun x y => ?_⟩
        obtain ⟨c, rfl⟩ := htr.exists_smul_eq x y
        exact ⟨⟨(c : Perm (Δ F ω i₀)), (c : H F hN ω hR i₀), c.2, rfl⟩, rfl⟩
      obtain ⟨s, hsR, hs1⟩ :=
        (Subgroup.bot_or_exists_ne_one (R F ω i₀)).resolve_left
          (R_ne_bot_of_stabilizer_ne_bot F hN ω hK i₀)
      let ts : Perm (Δ F ω i₀) := MulAction.toPermHom (F.S i₀) (Δ F ω i₀) s
      have hts_T : ts ∈ T₀ F ω i₀ := ⟨s, rfl⟩
      have hts_fix : ts • (QuotientGroup.mk 1 : Δ F ω i₀) = QuotientGroup.mk 1 := by
        change (QuotientGroup.mk (s * 1) : Δ F ω i₀) = QuotientGroup.mk 1
        rw [mul_one]
        exact (mk_eq_one_iff F ω i₀ s).mpr hsR
      have hts_one : ts = 1 := by
        refine eq_one_of_commute_transitive (N := C.map (H F hN ω hR i₀).subtype) hts_fix ?_
        rintro _ ⟨c, hc, rfl⟩
        have hcT := Subgroup.mem_centralizer_iff.mp hc ⟨ts, T₀_le_H F hN ω hR i₀ hts_T⟩ hts_T
        exact congrArg Subtype.val hcT
      exact hs1 (hinj (hts_one.trans (map_one _).symm))
    rw [hC_bot, Subgroup.mem_bot] at hhC
    exact congrArg Subtype.val hhC

theorem alt_le_T₀_of_isSubsetActionType_H [Finite α] (hN : N.Normal) (ω : α)
    (hR : ∀ l : Fin F.r, R F ω l ≠ ⊤) {i₀ : Fin F.r} {m k : ℕ}
    {e₀ : Δ F ω i₀ ≃ KSubset m k} (hm5 : 5 ≤ m)
    (hH_sub : ∀ h ∈ H F hN ω hR i₀, ∃ σ : Perm (Fin m), e₀.permCongr h = kSubsetPerm σ)
    (hAlt_le : ∀ a : alternatingGroup (Fin m),
      e₀.symm.permCongr (kSubsetPerm (a : Perm (Fin m))) ∈ H F hN ω hR i₀)
    (b : alternatingGroup (Fin m)) :
    e₀.symm.permCongr (kSubsetPerm (b : Perm (Fin m))) ∈ T₀ F ω i₀ := by
  let ψ : Perm (Fin m) →* Perm (Δ F ω i₀) :=
    (permCongrMulEquiv e₀.symm).toMonoidHom.comp (kSubsetPermHom m k)
  have hψ_apply : ∀ σ : Perm (Fin m), ψ σ = e₀.symm.permCongr (kSubsetPerm σ) := fun _ => rfl
  have hH_le_range : H F hN ω hR i₀ ≤ ψ.range := by
    intro h hh
    obtain ⟨σ, hσ⟩ := hH_sub h hh
    refine ⟨σ, ?_⟩
    rw [hψ_apply, ← hσ]
    ext d
    simp
  let ψ_alt : alternatingGroup (Fin m) →* Perm (Δ F ω i₀) :=
    ψ.comp (alternatingGroup (Fin m)).subtype
  let K_alt : Subgroup (alternatingGroup (Fin m)) := (T₀ F ω i₀).comap ψ_alt
  have hK_norm : K_alt.Normal := by
    refine ⟨fun a ha b => ?_⟩
    rw [Subgroup.mem_comap] at ha ⊢
    rw [map_mul, map_mul, map_inv]
    exact H_conj_mem_T₀ F hN ω hR i₀ (ψ_alt b) (hAlt_le b) (ψ_alt a) ha
  have hK_ne_bot : K_alt ≠ ⊥ := by
    obtain ⟨a, ha, b, hb, hab⟩ := F.not_commute i₀
    let ta := MulAction.toPermHom (F.S i₀) (Δ F ω i₀) ⟨a, ha⟩
    let tb := MulAction.toPermHom (F.S i₀) (Δ F ω i₀) ⟨b, hb⟩
    have hta_T : ta ∈ T₀ F ω i₀ := ⟨⟨a, ha⟩, rfl⟩
    have htb_T : tb ∈ T₀ F ω i₀ := ⟨⟨b, hb⟩, rfl⟩
    obtain ⟨σ₁, hσ₁⟩ := hH_le_range (T₀_le_H F hN ω hR i₀ hta_T)
    obtain ⟨σ₂, hσ₂⟩ := hH_le_range (T₀_le_H F hN ω hR i₀ htb_T)
    let c_perm : Perm (Fin m) := σ₁ * σ₂ * σ₁⁻¹ * σ₂⁻¹
    have hc_alt : c_perm ∈ alternatingGroup (Fin m) := by
      rw [Perm.mem_alternatingGroup]
      simp only [c_perm, map_mul, map_inv]
      rw [mul_right_comm (Perm.sign σ₁) (Perm.sign σ₂), mul_inv_cancel, one_mul, mul_inv_cancel]
    let c : alternatingGroup (Fin m) := ⟨c_perm, hc_alt⟩
    have hψc : ψ_alt c = ta * tb * ta⁻¹ * tb⁻¹ := by
      change ψ (σ₁ * σ₂ * σ₁⁻¹ * σ₂⁻¹) = _
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hσ₁, hσ₂]
    have hc_mem : c ∈ K_alt := by
      rw [Subgroup.mem_comap, hψc]
      exact mul_mem (mul_mem (mul_mem hta_T htb_T) (inv_mem hta_T)) (inv_mem htb_T)
    have hc_ne : c ≠ 1 := by
      intro hc1
      rw [hc1, map_one] at hψc
      have hinj := toPermHom_S_injective F ω hR i₀
      have hcomm : (⟨a, ha⟩ : F.S i₀) * ⟨b, hb⟩ * (⟨a, ha⟩)⁻¹ * (⟨b, hb⟩)⁻¹ = 1 := by
        apply hinj
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hψc, map_one]
      have hab_eq : (⟨a, ha⟩ : F.S i₀) * ⟨b, hb⟩ = ⟨b, hb⟩ * ⟨a, ha⟩ := by
        calc (⟨a, ha⟩ : F.S i₀) * ⟨b, hb⟩
            = ((⟨a, ha⟩ : F.S i₀) * ⟨b, hb⟩ * (⟨a, ha⟩)⁻¹ * (⟨b, hb⟩)⁻¹) *
                (⟨b, hb⟩ * ⟨a, ha⟩) := by group
          _ = ⟨b, hb⟩ * ⟨a, ha⟩ := by rw [hcomm, one_mul]
      exact hab (congrArg Subtype.val hab_eq)
    intro hbot
    exact hc_ne (Subgroup.mem_bot.mp (hbot ▸ hc_mem))
  have hAlt_simple : IsSimpleGroup (alternatingGroup (Fin m)) :=
    alternatingGroup.isSimpleGroup (by simpa using hm5)
  have hK_top : K_alt = ⊤ := hK_norm.eq_bot_or_eq_top.resolve_left hK_ne_bot
  have hb : b ∈ K_alt := hK_top ▸ Subgroup.mem_top b
  exact hb

/-- The product equivalence `α ≃ (Fin F.r → KSubset m k)` constructed from
`e₀ : Δ F ω i₀ ≃ KSubset m k` and elements `g_i i : G` with `coordPermHom F hN (g_i i) i₀ = i`. -/
noncomputable def productEquiv (hN : N.Normal) (ω : α) (hR : ∀ l : Fin F.r, R F ω l ≠ ⊤)
    {i₀ : Fin F.r} {m k : ℕ} (e₀ : Δ F ω i₀ ≃ KSubset m k) (g_i : Fin F.r → G)
    (hg_i : ∀ i : Fin F.r, coordPermHom F hN (g_i i) i₀ = i) :
    α ≃ (Fin F.r → KSubset m k) :=
  (toCoord F hN ω hR).trans
    (Equiv.piCongrRight fun i => (coordEquiv F hN ω hR (g_i i) (hg_i i)).symm.trans e₀)

theorem productEquiv_apply (hN : N.Normal) (ω : α) (hR : ∀ l : Fin F.r, R F ω l ≠ ⊤)
    {i₀ : Fin F.r} {m k : ℕ} (e₀ : Δ F ω i₀ ≃ KSubset m k) (g_i : Fin F.r → G)
    (hg_i : ∀ i : Fin F.r, coordPermHom F hN (g_i i) i₀ = i) (x : α) (i : Fin F.r) :
    productEquiv F hN ω hR e₀ g_i hg_i x i =
      e₀ (actCoord F hN ω hR (g_i i)⁻¹ i i₀ (toCoord F hN ω hR x i)) := rfl

theorem toCoord_productEquiv_symm (hN : N.Normal) (ω : α) (hR : ∀ l : Fin F.r, R F ω l ≠ ⊤)
    {i₀ : Fin F.r} {m k : ℕ} (e₀ : Δ F ω i₀ ≃ KSubset m k) (g_i : Fin F.r → G)
    (hg_i : ∀ i : Fin F.r, coordPermHom F hN (g_i i) i₀ = i)
    (y : Fin F.r → KSubset m k) (j : Fin F.r) :
    toCoord F hN ω hR ((productEquiv F hN ω hR e₀ g_i hg_i).symm y) j =
      actCoord F hN ω hR (g_i j) i₀ j (e₀.symm (y j)) := by
  simp only [productEquiv, Equiv.symm_trans_apply, Equiv.apply_symm_apply]
  rfl

theorem isWreathType_of_isSubsetActionType_H_aux [Finite α] (hN : N.Normal) (ω : α)
    (hR : ∀ l : Fin F.r, R F ω l ≠ ⊤) {i₀ : Fin F.r} {m k : ℕ}
    (e₀ : Δ F ω i₀ ≃ KSubset m k) (hm5 : 5 ≤ m)
    (hH_sub : ∀ h ∈ H F hN ω hR i₀, ∃ σ : Perm (Fin m), e₀.permCongr h = kSubsetPerm σ)
    (hAlt_le : ∀ a : alternatingGroup (Fin m),
      e₀.symm.permCongr (kSubsetPerm (a : Perm (Fin m))) ∈ H F hN ω hR i₀)
    (g_i : Fin F.r → G) (hg_i : ∀ i : Fin F.r, coordPermHom F hN (g_i i) i₀ = i) :
    IsWreathType G := by
  have hg_inv_i : ∀ i : Fin F.r, coordPermHom F hN (g_i i)⁻¹ i = i₀ :=
    fun i => coordPermHom_inv_apply F hN (hg_i i)
  refine ⟨m, k, F.r, productEquiv F hN ω hR e₀ g_i hg_i, hm5, ?_, ?_⟩
  · intro g hgG
    let g' : G := ⟨g, hgG⟩
    let σ : Perm (Fin F.r) := coordPermHom F hN g'
    have hu_mem : ∀ i : Fin F.r,
        (g_i i)⁻¹ * g' * g_i (σ.symm i) ∈ normFactor F hN i₀ := by
      intro i
      rw [mem_normFactor_iff]
      have hgs : coordPermHom F hN g' (σ.symm i) = i := σ.apply_symm_apply i
      rw [map_mul, map_mul, Perm.mul_apply, Perm.mul_apply,
        hg_i (σ.symm i), hgs, hg_inv_i i]
    obtain ⟨h, hh⟩ := Classical.axiomOfChoice fun i : Fin F.r =>
      hH_sub (coordHom F hN ω hR i₀ ⟨(g_i i)⁻¹ * g' * g_i (σ.symm i), hu_mem i⟩)
        (MonoidHom.mem_range.mpr ⟨⟨(g_i i)⁻¹ * g' * g_i (σ.symm i), hu_mem i⟩, rfl⟩)
    refine ⟨σ, h, ?_⟩
    apply Equiv.ext
    intro y
    funext i
    let j := σ.symm i
    have hij : coordPermHom F hN g' j = i := σ.apply_symm_apply i
    change productEquiv F hN ω hR e₀ g_i hg_i
        (g' • (productEquiv F hN ω hR e₀ g_i hg_i).symm y) i =
      kSubsetPerm (h i) (y j)
    rw [productEquiv_apply, toCoord_smul F hN ω hR g' hij,
      toCoord_productEquiv_symm F hN ω hR e₀ g_i hg_i y j,
      ← actCoord_mul F hN ω hR g' (g_i j) (hg_i j) hij,
      ← actCoord_mul F hN ω hR (g_i i)⁻¹ (g' * g_i j)
        (by rw [map_mul, Perm.mul_apply, hg_i j, hij]) (hg_inv_i i)]
    exact congrArg (fun p : Perm (KSubset m k) => p (y j)) (hh i)
  · intro a
    obtain ⟨s₀, hs₀⟩ := Classical.axiomOfChoice fun i : Fin F.r =>
      alt_le_T₀_of_isSubsetActionType_H F hN ω hR hm5 hH_sub hAlt_le (a i)
    let s : ∀ i : Fin F.r, F.S i := fun i =>
      ⟨g_i i * (s₀ i : G) * (g_i i)⁻¹, conj_mem_S_of_coordPermHom F hN (hg_i i) (s₀ i).2⟩
    let n : N := F.e s
    suffices h_eq : (productEquiv F hN ω hR e₀ g_i hg_i).symm.permCongr
        (productActionPerm 1 fun i => (a i : Perm (Fin m))) = ((n : G) : Perm α) by
      rw [h_eq]
      exact (n : G).2
    apply Equiv.ext
    intro x
    apply (productEquiv F hN ω hR e₀ g_i hg_i).injective
    rw [Equiv.permCongr_apply, Equiv.symm_symm, Equiv.apply_symm_apply]
    funext i
    have hn_coord : coordPermHom F hN (n : G) i = i := by
      rw [coordPermHom_eq_of_mem_N F hN n.2, Perm.one_apply]
    have hproj_n : F.proj i n = s i := by
      rw [SimpleFactors.proj_apply, MulEquiv.symm_apply_apply]
    change kSubsetPerm (a i : Perm (Fin m)) (productEquiv F hN ω hR e₀ g_i hg_i x i) =
      productEquiv F hN ω hR e₀ g_i hg_i ((n : G) • x) i
    have h_step1 : toCoord F hN ω hR ((n : G) • x) i = s i • toCoord F hN ω hR x i := by
      rw [toCoord_smul_eq_coordEquiv F hN ω hR (n : G) hn_coord x,
        coordEquiv_of_mem_N F hN ω hR n i, hproj_n]
    have h_step2 : actCoord F hN ω hR (g_i i)⁻¹ i i₀ (s i • toCoord F hN ω hR x i) =
        s₀ i • actCoord F hN ω hR (g_i i)⁻¹ i i₀ (toCoord F hN ω hR x i) := by
      rw [actCoord_smul F hN ω hR (g_i i)⁻¹ (hg_inv_i i) (s i)]
      congr 1
      apply Subtype.ext
      simp only [s]
      group
    have h_step3 : e₀ (s₀ i • actCoord F hN ω hR (g_i i)⁻¹ i i₀ (toCoord F hN ω hR x i)) =
        kSubsetPerm (a i : Perm (Fin m)) (productEquiv F hN ω hR e₀ g_i hg_i x i) := by
      have h1 := congrArg (fun p : Perm (Δ F ω i₀) =>
        e₀ (p (actCoord F hN ω hR (g_i i)⁻¹ i i₀ (toCoord F hN ω hR x i)))) (hs₀ i)
      simpa [productEquiv_apply] using h1
    rw [productEquiv_apply F hN ω hR e₀ g_i hg_i ((n : G) • x) i, h_step1, h_step2, h_step3]

/-- If `H F hN ω hR 0` is of subset action type on `Δ F ω 0`, then `G` is of wreath type
on `α`. -/
theorem isWreathType_of_isSubsetActionType_H [Finite α] (hN : N.Normal) (ω : α)
    (hR : ∀ l : Fin F.r, R F ω l ≠ ⊤) {i₀ : Fin F.r}
    (hSub : IsSubsetActionType (H F hN ω hR i₀)) :
    IsWreathType G := by
  obtain ⟨m, k, e₀, hm5, hH_sub, hAlt_le⟩ := hSub
  obtain ⟨g_i, hg_i⟩ := Classical.axiomOfChoice fun i : Fin F.r => exists_coordPermHom_eq F hN i₀ i
  exact isWreathType_of_isSubsetActionType_H_aux F hN ω hR e₀ hm5 hH_sub hAlt_le g_i hg_i

/-- If `H F hN ω hR 0` is of Mathieu type on `Δ F ω 0` and `r ≥ 2`, then `|G| ≤ bound |α|`. -/
theorem card_le_bound_of_isMathieuType_H [Finite α] (hN : N.Normal) (ω : α)
    (hR : ∀ l : Fin F.r, R F ω l ≠ ⊤) (hr : 2 ≤ F.r)
    (hMath : IsMathieuType (H F hN ω hR ⟨0, F.one_le⟩)) :
    Nat.card G ≤ bound (Nat.card α) := by
  obtain ⟨s, hs_mem, hm_eq, -, ⟨eH⟩⟩ := hMath
  have hcard_H : Nat.card (H F hN ω hR ⟨0, F.one_le⟩) = Nat.card s.1.Group :=
    Nat.card_congr eH.toEquiv
  have hmath_ineq : 8 ≤ Nat.card (Δ F ω ⟨0, F.one_le⟩) ∧
      Nat.card (H F hN ω hR ⟨0, F.one_le⟩) ≤
        Nat.card (Δ F ω ⟨0, F.one_le⟩) ^ (2 * Nat.log 2 (Nat.card (Δ F ω ⟨0, F.one_le⟩)) - 1) := by
    simp only [fourTransitiveMathieu, List.mem_cons, List.not_mem_nil, or_false] at hs_mem
    rcases hs_mem with rfl | rfl | rfl | rfl
    · have hc := CFSG.Sporadic.Bridge.M11.tauCeti_finite_card_le.2
      rw [hm_eq, hcard_H]
      exact ⟨by decide, hc.trans (by decide)⟩
    · have hc := CFSG.Sporadic.Bridge.M12.tauCeti_finite_card_le.2
      rw [hm_eq, hcard_H]
      exact ⟨by decide, hc.trans (by decide)⟩
    · have hc : Nat.card TauCeti.SporadicName.M23.Group ≤ 10200960 :=
        CFSG.Sporadic.Presentation.M23.finite_card_le.2
      rw [hm_eq, hcard_H]
      exact ⟨by decide, hc.trans (by decide)⟩
    · have hc : Nat.card TauCeti.SporadicName.M24.Group ≤ 244823040 :=
        CFSG.Sporadic.Presentation.M24.finite_card_le.2
      rw [hm_eq, hcard_H]
      exact ⟨by decide, hc.trans (by decide)⟩
  calc Nat.card G ≤ F.r.factorial * Nat.card (H F hN ω hR ⟨0, F.one_le⟩) ^ F.r :=
        card_le_factorial_mul_card_H_pow F hN ω hR
    _ ≤ bound (Nat.card (Δ F ω ⟨0, F.one_le⟩) ^ F.r) :=
        factorial_mul_pow_le_bound_of_mathieu hmath_ineq.1 hr hmath_ineq.2
    _ = bound (Nat.card α) := by rw [card_α_eq_pow_card_Δ F hN ω hR]

/-- In the product action case (`r ≥ 2`, `stabilizer N ω ≠ ⊥`, and every projection `R i` is
proper), assuming `hAS` for almost simple groups gives `Conclusion G`. -/
theorem conclusion_of_forall_map_proj_ne_top [Finite α]
    (hAS : AlmostSimpleCase fun _ _ => True) (hN : N.Normal) (hr : 2 ≤ F.r) (ω : α)
    (hK : stabilizer N ω ≠ ⊥) (hR : ∀ l : Fin F.r, R F ω l ≠ ⊤) :
    Conclusion G := by
  let i₀ : Fin F.r := ⟨0, F.one_le⟩
  have hprim : IsPreprimitive (H F hN ω hR i₀) (Δ F ω i₀) := isPreprimitive_H F hN ω hR i₀
  have has : IsAlmostSimpleWith (H F hN ω hR i₀) (F.S i₀) :=
    isAlmostSimpleWith_H F hN ω hR hK i₀
  rcases hAS (Δ F ω i₀) (H F hN ω hR i₀) (F.S i₀) hprim has trivial with hSub | hMath | hBound
  · exact Or.inl (isWreathType_of_isSubsetActionType_H F hN ω hR hSub)
  · exact Or.inr (Or.inr (card_le_bound_of_isMathieuType_H F hN ω hR hr hMath))
  · refine Or.inr (Or.inr ?_)
    have hm5 : 5 ≤ Nat.card (Δ F ω i₀) := five_le_card_Δ F ω hR i₀
    calc Nat.card G ≤ F.r.factorial * Nat.card (H F hN ω hR i₀) ^ F.r :=
          card_le_factorial_mul_card_H_pow F hN ω hR
      _ ≤ F.r.factorial * bound (Nat.card (Δ F ω i₀)) ^ F.r :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hBound F.r)
      _ ≤ bound (Nat.card (Δ F ω i₀) ^ F.r) :=
          factorial_mul_bound_pow_le (by omega) hr
      _ = bound (Nat.card α) := by rw [card_α_eq_pow_card_Δ F hN ω hR]

end ActionOnDelta

end SimpleFactors

end Maroti
