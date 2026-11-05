module

public import Maroti.Exceptional.TrialityD4Heis
public import Maroti.Exceptional.ChevalleyE
import CFSG.Timmesfeld.RankTwo.ModelD43Comm
import CFSG.LieType.Chevalley.TrialityCoverTorus
import CFSG.LieType.Chevalley.TrialityCoverWeights
import CFSG.LieType.Chevalley.OddExceptionalOuterTwoRank
import CFSG.Timmesfeld.Orders.Exceptional

/-!
# Triality Exceptional Groups `³D₄(q)`

This file proves the subgroup index lower bounds and Maróti's bound `|G| ≤ bound |α|` for
primitive almost simple groups `G ≤ Perm α` with socle `³D₄(q)` (`q = p ^ f`, Maróti, Section 2,
Step 2, pages 634–635):
* For all `q = p ^ f`, `index_ge_of_chevalley_trialityD4` (`Maroti.Exceptional.TrialityD4Heis`)
  gives `p * q ^ 4 ≤ H.index` for every proper subgroup `H` of `³D₄(q)`.
* For `q = 2` (`p = 2, f = 1`), the normalizer in `³D₄(2)` of the long-root Heisenberg subgroup
  `Q ≅ 2^(1+8)` contains torus elements `ho(a)` (`a ∈ GF(8)ˣ`), the outer Weyl reflection
  `w_outer`, and the short-orbit unipotent element `x₁(1)`. Their conjugation action on `Q/Z`
  rules out any normalizer-invariant abelian subgroup strictly containing `Z`, so
  `PolarizedHeisenbergData.two_mul_card_le_index_of_ne_top` yields `2 * 2 * 16 = 64 ≤ H.index`
  (`index_ge_64_of_chevalley_trialityD4_two`).
* Combining these minimum degree bounds with `|Out(³D₄(q))| = 3f` (`card_outerAut_trialityD4`)
  proves `card_le_bound_of_chevalley_trialityD4`.
-/

@[expose] public section

open scoped commutatorElement

namespace Maroti

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial (finite_field_prime_power_characteristic)
open CFSG.SignalizerFunctorTheorem.NonLocal
open CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4 CFSG.Timmesfeld.RankTwo

/-! ### Identities for `fixX`, `orb3`, `d4X`, `d4Y`, `d4Z` -/

section BasicIdentities

variable {K : Type} [Field K] (σ : K →+* K)

theorem fixX_zero {j : Fin 6} (hj : j = 1 ∨ j = 4 ∨ j = 5) :
    fixX σ hj 0 = 1 :=
  Subtype.ext (pinnedX_zero TwistTag.D4.tag K (trialityRoot j))

theorem orb3_zero {j : Fin 6} (hj : j = 0 ∨ j = 2 ∨ j = 3) (hσ : σ ^ 3 = 1) :
    orb3 σ hj hσ 0 = 1 := by
  have h := orb3_add σ hj hσ 0 0
  rw [add_zero] at h
  exact mul_eq_left.1 h.symm

theorem fixX_one_eq_d4X (hσ : σ ^ 3 = 1) (b : trialityFixedField K σ) :
    fixX σ (j := 1) (by decide) b = d4X σ hσ (b, 0) := by
  rw [d4X, orb3_zero, mul_one]

theorem orb3_two_eq_d4X (hσ : σ ^ 3 = 1) (c : K) :
    orb3 σ (j := 2) (by decide) hσ c = d4X σ hσ (0, c) := by
  rw [d4X, fixX_zero, one_mul]

theorem orb3_three_eq_d4Y (hσ : σ ^ 3 = 1) (d : K) :
    orb3 σ (j := 3) (by decide) hσ d = d4Y σ hσ (0, d) := by
  rw [d4Y, fixX_zero, mul_one]

theorem fixX_four_eq_d4Y (hσ : σ ^ 3 = 1) (e : trialityFixedField K σ) :
    fixX σ (j := 4) (by decide) e = d4Y σ hσ (e, 0) := by
  rw [d4Y, orb3_zero, one_mul]

theorem fixX_five_eq_d4Z (f : trialityFixedField K σ) :
    fixX σ (j := 5) (by decide) f = d4Z σ f := rfl

end BasicIdentities

/-! ### Steinberg root-operator bridge in characteristic `2` -/

section BridgeCharTwo

variable {K : Type} [Field K] [CharP K 2]

private theorem coe_xPar_d4 {γ : Fin TwistTag.D4.tag.rank → ℤ} (hγ : IsRoot TwistTag.D4.tag γ)
    (c : K) : ((xPar (rootOperatorFamily d4) γ c : adjointGroup d4 K) : ModGL TwistTag.D4.tag K) =
      pinnedX TwistTag.D4.tag K γ c := by
  have hs : ((rootOperatorFamily d4).pinnedFamilySign γ : K) = 1 := by
    rcases (rootOperatorFamily d4).pinnedFamilySign_eq γ with h | h <;> rw [h]
    · exact Int.cast_one
    · rw [Int.cast_neg, Int.cast_one, CharTwo.neg_eq]
  have h := (rootOperatorFamily d4).pinnedX_eq_eltUnit K hγ c
  rw [hs, one_mul] at h
  rw [xPar_of_isRoot hγ, h]
  rfl

private theorem coe_xOrbit_d4 (σ : K →+* K) {γ : Fin TwistTag.D4.tag.rank → ℤ}
    (hγ : IsRoot TwistTag.D4.tag γ) (c : K) :
    ((xOrbit σ γ c : adjointGroup d4 K) : ModGL TwistTag.D4.tag K) =
      pinnedX TwistTag.D4.tag K γ c *
        pinnedX TwistTag.D4.tag K (permLattice TwistTag.D4.perm γ) (σ c) *
          pinnedX TwistTag.D4.tag K (permLattice (TwistTag.D4.perm ^ 2) γ) (σ (σ c)) := by
  rw [xOrbit_eq σ γ c, Subgroup.coe_mul, Subgroup.coe_mul, coe_xPar_d4 hγ,
    coe_xPar_d4 (isRoot_rho hγ), coe_xPar_d4 (isRoot_rho (isRoot_rho hγ)),
    ← permLattice_D4_perm_perm]

private theorem trialityRoot_eq_d4Root :
    trialityRoot 0 = d4Root 0 ∧ trialityRoot 1 = d4Root 2 ∧ trialityRoot 2 = d4Root 5 ∧
      trialityRoot 3 = d4Root 15 ∧ trialityRoot 4 = d4Root 19 ∧ trialityRoot 5 = d4Root 22 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> funext k <;> fin_cases k <;> decide +kernel

variable (σ : K →+* K) (hσ : σ ^ 3 = 1)

private theorem coe_orb3_zero (c : K) :
    (orb3 σ (j := 0) (by decide) hσ c : ModGL TwistTag.D4.tag K) =
      ((xOrbit σ (d4Root 0) c : adjointGroup d4 K) : ModGL TwistTag.D4.tag K) := by
  change orb3Val σ (trialityRoot 0) c = _
  rw [orb3Val_eq_trialityOrbitProd, coe_trialityOrbitProd,
    coe_xOrbit_d4 σ (isRoot_d4Root (by decide)), trialityRoot_eq_d4Root.1]

private theorem coe_orb3_two (c : K) :
    (orb3 σ (j := 2) (by decide) hσ c : ModGL TwistTag.D4.tag K) =
      ((xOrbit σ (d4Root 5) c : adjointGroup d4 K) : ModGL TwistTag.D4.tag K) := by
  change orb3Val σ (trialityRoot 2) c = _
  rw [orb3Val_eq_trialityOrbitProd, coe_trialityOrbitProd,
    coe_xOrbit_d4 σ (isRoot_d4Root (by decide)), trialityRoot_eq_d4Root.2.2.1]

private theorem coe_orb3_three (c : K) :
    (orb3 σ (j := 3) (by decide) hσ c : ModGL TwistTag.D4.tag K) =
      ((xOrbit σ (d4Root 15) c : adjointGroup d4 K) : ModGL TwistTag.D4.tag K) := by
  change orb3Val σ (trialityRoot 3) c = _
  rw [orb3Val_eq_trialityOrbitProd, coe_trialityOrbitProd,
    coe_xOrbit_d4 σ (isRoot_d4Root (by decide)), trialityRoot_eq_d4Root.2.2.2.1]

private theorem coe_fixX_one (b : trialityFixedField K σ) :
    (fixX σ (j := 1) (by decide) b : ModGL TwistTag.D4.tag K) =
      ((xPar (rootOperatorFamily d4) (d4Root 2) b.1 : adjointGroup d4 K) :
        ModGL TwistTag.D4.tag K) := by
  change pinnedX TwistTag.D4.tag K (trialityRoot 1) b.1 = _
  rw [coe_xPar_d4 (isRoot_d4Root (by decide)), trialityRoot_eq_d4Root.2.1]

private theorem coe_fixX_four (e : trialityFixedField K σ) :
    (fixX σ (j := 4) (by decide) e : ModGL TwistTag.D4.tag K) =
      ((xPar (rootOperatorFamily d4) (d4Root 19) e.1 : adjointGroup d4 K) :
        ModGL TwistTag.D4.tag K) := by
  change pinnedX TwistTag.D4.tag K (trialityRoot 4) e.1 = _
  rw [coe_xPar_d4 (isRoot_d4Root (by decide)), trialityRoot_eq_d4Root.2.2.2.2.1]

private theorem coe_fixX_five (f : trialityFixedField K σ) :
    (fixX σ (j := 5) (by decide) f : ModGL TwistTag.D4.tag K) =
      ((xPar (rootOperatorFamily d4) (d4Root 22) f.1 : adjointGroup d4 K) :
        ModGL TwistTag.D4.tag K) := by
  change pinnedX TwistTag.D4.tag K (trialityRoot 5) f.1 = _
  rw [coe_xPar_d4 (isRoot_d4Root (by decide)), trialityRoot_eq_d4Root.2.2.2.2.2]

/-! ### Commutator and commutation relations for `x₁(1)` in characteristic `2` -/

theorem commute_orb3_zero_fixX_four (s : K) (e : trialityFixedField K σ) :
    Commute (orb3 σ (j := 0) (by decide) hσ s) (fixX σ (j := 4) (by decide) e) := by
  apply Subtype.ext
  change (orb3 σ (j := 0) (by decide) hσ s : ModGL TwistTag.D4.tag K) *
      (fixX σ (j := 4) (by decide) e : ModGL TwistTag.D4.tag K) =
    (fixX σ (j := 4) (by decide) e : ModGL TwistTag.D4.tag K) *
      (orb3 σ (j := 0) (by decide) hσ s : ModGL TwistTag.D4.tag K)
  rw [coe_orb3_zero, coe_fixX_four]
  exact (d43_commute01 (σ := σ) s e.1).map (adjointGroup d4 K).subtype

theorem commute_orb3_zero_fixX_five (s : K) (f : trialityFixedField K σ) :
    Commute (orb3 σ (j := 0) (by decide) hσ s) (fixX σ (j := 5) (by decide) f) := by
  apply Subtype.ext
  change (orb3 σ (j := 0) (by decide) hσ s : ModGL TwistTag.D4.tag K) *
      (fixX σ (j := 5) (by decide) f : ModGL TwistTag.D4.tag K) =
    (fixX σ (j := 5) (by decide) f : ModGL TwistTag.D4.tag K) *
      (orb3 σ (j := 0) (by decide) hσ s : ModGL TwistTag.D4.tag K)
  rw [coe_orb3_zero, coe_fixX_five]
  exact (d43_commute03 (σ := σ) s f.1).map (adjointGroup d4 K).subtype

theorem comm_orb3_zero_orb3_three (s d : K) :
    ⁅orb3 σ (j := 0) (by decide) hσ s, orb3 σ (j := 3) (by decide) hσ d⁆ =
      fixX σ (j := 4) (by decide) (trialityTrace K σ hσ (s * d)) := by
  have hcube : ∀ c, σ (σ (σ c)) = c := ringHom_apply_apply_apply_of_pow_three hσ
  apply Subtype.ext
  change ⁅(orb3 σ (j := 0) (by decide) hσ s : ModGL TwistTag.D4.tag K),
      (orb3 σ (j := 3) (by decide) hσ d : ModGL TwistTag.D4.tag K)⁆ =
    (fixX σ (j := 4) (by decide) (trialityTrace K σ hσ (s * d)) : ModGL TwistTag.D4.tag K)
  rw [coe_orb3_zero, coe_orb3_three, coe_fixX_four]
  exact congrArg (adjointGroup d4 K).subtype (d43_comm02 hcube s d)

theorem comm_orb3_zero_orb3_two (s c : K) :
    ∃ (e : trialityFixedField K σ) (d : K) (f : trialityFixedField K σ),
      ⁅orb3 σ (j := 0) (by decide) hσ s, orb3 σ (j := 2) (by decide) hσ c⁆ =
        fixX σ (j := 4) (by decide) e * orb3 σ (j := 3) (by decide) hσ d *
          fixX σ (j := 5) (by decide) f := by
  have hcube : ∀ x, σ (σ (σ x)) = x := ringHom_apply_apply_apply_of_pow_three hσ
  refine ⟨trialityTrace K σ hσ (d43Sharp σ s * c), d43Cross σ s c,
    trialityTrace K σ hσ (s * d43Sharp σ c), Subtype.ext ?_⟩
  change ⁅(orb3 σ (j := 0) (by decide) hσ s : ModGL TwistTag.D4.tag K),
      (orb3 σ (j := 2) (by decide) hσ c : ModGL TwistTag.D4.tag K)⁆ =
    (fixX σ (j := 4) (by decide) _ : ModGL TwistTag.D4.tag K) *
      (orb3 σ (j := 3) (by decide) hσ _ : ModGL TwistTag.D4.tag K) *
      (fixX σ (j := 5) (by decide) _ : ModGL TwistTag.D4.tag K)
  rw [coe_orb3_zero, coe_orb3_two, coe_fixX_four, coe_orb3_three, coe_fixX_five]
  exact congrArg (adjointGroup d4 K).subtype (d43_comm04 hcube s c)

theorem comm_orb3_zero_one_fixX_one (b : trialityFixedField K σ) :
    ⁅orb3 σ (j := 0) (by decide) hσ 1, fixX σ (j := 1) (by decide) b⁆ =
      fixX σ (j := 4) (by decide) b * orb3 σ (j := 3) (by decide) hσ b.1 *
        fixX σ (j := 5) (by decide) (b ^ 2) * orb3 σ (j := 2) (by decide) hσ b.1 := by
  have hcube : ∀ x, σ (σ (σ x)) = x := ringHom_apply_apply_apply_of_pow_three hσ
  apply Subtype.ext
  change ⁅(orb3 σ (j := 0) (by decide) hσ 1 : ModGL TwistTag.D4.tag K),
      (fixX σ (j := 1) (by decide) b : ModGL TwistTag.D4.tag K)⁆ =
    (fixX σ (j := 4) (by decide) b : ModGL TwistTag.D4.tag K) *
      (orb3 σ (j := 3) (by decide) hσ b.1 : ModGL TwistTag.D4.tag K) *
      (fixX σ (j := 5) (by decide) (b ^ 2) : ModGL TwistTag.D4.tag K) *
      (orb3 σ (j := 2) (by decide) hσ b.1 : ModGL TwistTag.D4.tag K)
  rw [coe_orb3_zero, coe_fixX_one, coe_fixX_four, coe_orb3_three, coe_fixX_five, coe_orb3_two]
  have h := congrArg (adjointGroup d4 K).subtype
    (d43_comm05 hcube 1 b.1 (mem_trialityFixedField.1 b.2))
  simp only [map_one, mul_one] at h
  exact h

end BridgeCharTwo

/-! ### Normalizer elements of `D.heisSubgroup` in characteristic `2` -/

section NormalizerCharTwo

variable {K : Type} [Field K] [CharP K 2] (σ : K ≃+* K)

/-- Criterion for membership in `Subgroup.normalizer (H : Set G)`. -/
private theorem mem_normalizer_of_conj_mem {G : Type*} [Group G] {H : Subgroup G} {g : G}
    (h1 : ∀ q ∈ H, g * q * g⁻¹ ∈ H) (h2 : ∀ q ∈ H, g⁻¹ * q * g ∈ H) :
    g ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨h1 h, fun hh => ?_⟩
  have := h2 (g * h * g⁻¹) hh
  have heq : g⁻¹ * (g * h * g⁻¹) * g = h := by group
  rwa [heq] at this

private theorem d4X_mem_heisSubgroup {hσ3 : σ.toRingHom ^ 3 = 1} (hne : ∃ u, σ.toRingHom u ≠ u)
    (u : trialityFixedField K σ.toRingHom × K) :
    d4X σ.toRingHom hσ3 u ∈ (polarizedHeisenbergData_d4_charTwo σ.toRingHom hσ3 hne).heisSubgroup :=
  ⟨u, 0, 0, by
    have D := polarizedHeisenbergData_d4_charTwo σ.toRingHom hσ3 hne
    rw [D.Y_zero, D.z_zero, mul_one, mul_one]⟩

private theorem d4Y_mem_heisSubgroup {hσ3 : σ.toRingHom ^ 3 = 1} (hne : ∃ u, σ.toRingHom u ≠ u)
    (v : trialityFixedField K σ.toRingHom × K) :
    d4Y σ.toRingHom hσ3 v ∈ (polarizedHeisenbergData_d4_charTwo σ.toRingHom hσ3 hne).heisSubgroup :=
  ⟨0, v, 0, by
    have D := polarizedHeisenbergData_d4_charTwo σ.toRingHom hσ3 hne
    rw [D.X_zero, D.z_zero, one_mul, mul_one]⟩

private theorem d4Z_mem_heisSubgroup {hσ3 : σ.toRingHom ^ 3 = 1} (hne : ∃ u, σ.toRingHom u ≠ u)
    (s : trialityFixedField K σ.toRingHom) :
    d4Z σ.toRingHom s ∈ (polarizedHeisenbergData_d4_charTwo σ.toRingHom hσ3 hne).heisSubgroup :=
  ⟨0, 0, s, by
    have D := polarizedHeisenbergData_d4_charTwo σ.toRingHom hσ3 hne
    rw [D.X_zero, D.Y_zero, one_mul, one_mul]⟩

section Torus

variable [Finite K]

/-- Outer torus element `trialityTorus σ (a, 1)` in `graphFixedRootGroup TwistTag.D4`. -/
private noncomputable def d4Torus (hσ : σ ^ 3 = 1) (a : Kˣ) :
    ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
  ⟨TrialityCover.trialityTorus σ (a, 1),
    TrialityCover.trialityTorus_mem_graphFixedRootGroup σ hσ (a, 1)⟩

private theorem d4Torus_inv (hσ : σ ^ 3 = 1) (a : Kˣ) :
    (d4Torus σ hσ a)⁻¹ = d4Torus σ hσ a⁻¹ := by
  apply Subtype.ext
  change (TrialityCover.trialityTorus σ (a, 1))⁻¹ = TrialityCover.trialityTorus σ (a⁻¹, 1)
  rw [← map_inv]
  exact congrArg (TrialityCover.trialityTorus σ) (Prod.ext rfl inv_one)

private theorem d4Torus_conj_fixX_one (hσ : σ ^ 3 = 1) {a : Kˣ}
    (ha : a * TrialityCover.unitsSigma σ a *
      TrialityCover.unitsSigma σ (TrialityCover.unitsSigma σ a) = 1)
    (b : trialityFixedField K σ.toRingHom) :
    d4Torus σ hσ a * fixX σ.toRingHom (j := 1) (by decide) b * (d4Torus σ hσ a)⁻¹ =
      fixX σ.toRingHom (j := 1) (by decide) b := by
  obtain ⟨-, h1, -, -, -, -⟩ := TrialityCover.weights_normOne σ ha
  apply Subtype.ext
  change TrialityCover.trialityTorus σ (a, 1) *
      pinnedX TwistTag.D4.tag K (trialityRoot 1) b.1 *
      (TrialityCover.trialityTorus σ (a, 1))⁻¹ =
      pinnedX TwistTag.D4.tag K (trialityRoot 1) b.1
  rw [TrialityCover.trialityTorus_conj_pinnedX σ (isRoot_trialityRoot' 1), h1, Units.val_one,
    one_mul]

private theorem d4Torus_conj_fixX_four (hσ : σ ^ 3 = 1) {a : Kˣ}
    (ha : a * TrialityCover.unitsSigma σ a *
      TrialityCover.unitsSigma σ (TrialityCover.unitsSigma σ a) = 1)
    (e : trialityFixedField K σ.toRingHom) :
    d4Torus σ hσ a * fixX σ.toRingHom (j := 4) (by decide) e * (d4Torus σ hσ a)⁻¹ =
      fixX σ.toRingHom (j := 4) (by decide) e := by
  obtain ⟨-, -, -, -, h4, -⟩ := TrialityCover.weights_normOne σ ha
  apply Subtype.ext
  change TrialityCover.trialityTorus σ (a, 1) *
      pinnedX TwistTag.D4.tag K (trialityRoot 4) e.1 *
      (TrialityCover.trialityTorus σ (a, 1))⁻¹ =
      pinnedX TwistTag.D4.tag K (trialityRoot 4) e.1
  rw [TrialityCover.trialityTorus_conj_pinnedX σ (isRoot_trialityRoot' 4), h4, Units.val_one,
    one_mul]

private theorem d4Torus_conj_fixX_five (hσ : σ ^ 3 = 1) {a : Kˣ}
    (ha : a * TrialityCover.unitsSigma σ a *
      TrialityCover.unitsSigma σ (TrialityCover.unitsSigma σ a) = 1)
    (f : trialityFixedField K σ.toRingHom) :
    d4Torus σ hσ a * fixX σ.toRingHom (j := 5) (by decide) f * (d4Torus σ hσ a)⁻¹ =
      fixX σ.toRingHom (j := 5) (by decide) f := by
  obtain ⟨-, -, -, -, -, h5⟩ := TrialityCover.weights_normOne σ ha
  apply Subtype.ext
  change TrialityCover.trialityTorus σ (a, 1) *
      pinnedX TwistTag.D4.tag K (trialityRoot 5) f.1 *
      (TrialityCover.trialityTorus σ (a, 1))⁻¹ =
      pinnedX TwistTag.D4.tag K (trialityRoot 5) f.1
  rw [TrialityCover.trialityTorus_conj_pinnedX σ (isRoot_trialityRoot' 5), h5, Units.val_one,
    one_mul]

private theorem d4Torus_conj_orb3_two (hσ : σ ^ 3 = 1) (hσ3 : σ.toRingHom ^ 3 = 1) {a : Kˣ}
    (ha : a * TrialityCover.unitsSigma σ a *
      TrialityCover.unitsSigma σ (TrialityCover.unitsSigma σ a) = 1)
    (c : K) :
    d4Torus σ hσ a * orb3 σ.toRingHom (j := 2) (by decide) hσ3 c * (d4Torus σ hσ a)⁻¹ =
      orb3 σ.toRingHom (j := 2) (by decide) hσ3 ((a : K) ^ 2 * c) := by
  obtain ⟨-, -, h2, -, -, -⟩ := TrialityCover.weights_normOne σ ha
  apply Subtype.ext
  change TrialityCover.trialityTorus σ (a, 1) *
      orb3Val σ.toRingHom (trialityRoot 2) c *
      (TrialityCover.trialityTorus σ (a, 1))⁻¹ =
    orb3Val σ.toRingHom (trialityRoot 2) ((a : K) ^ 2 * c)
  rw [orb3Val_eq_trialityOrbitProd, orb3Val_eq_trialityOrbitProd,
    TrialityCover.trialityTorus_conj_orbitProd σ hσ (isRoot_trialityRoot 2), h2,
    Units.val_pow_eq_pow_val]

private theorem d4Torus_conj_orb3_three (hσ : σ ^ 3 = 1) (hσ3 : σ.toRingHom ^ 3 = 1) {a : Kˣ}
    (ha : a * TrialityCover.unitsSigma σ a *
      TrialityCover.unitsSigma σ (TrialityCover.unitsSigma σ a) = 1)
    (d : K) :
    d4Torus σ hσ a * orb3 σ.toRingHom (j := 3) (by decide) hσ3 d * (d4Torus σ hσ a)⁻¹ =
      orb3 σ.toRingHom (j := 3) (by decide) hσ3 (((a : K) ^ 2)⁻¹ * d) := by
  obtain ⟨-, -, -, h3, -, -⟩ := TrialityCover.weights_normOne σ ha
  apply Subtype.ext
  change TrialityCover.trialityTorus σ (a, 1) *
      orb3Val σ.toRingHom (trialityRoot 3) d *
      (TrialityCover.trialityTorus σ (a, 1))⁻¹ =
    orb3Val σ.toRingHom (trialityRoot 3) (((a : K) ^ 2)⁻¹ * d)
  rw [orb3Val_eq_trialityOrbitProd, orb3Val_eq_trialityOrbitProd,
    TrialityCover.trialityTorus_conj_orbitProd σ hσ (isRoot_trialityRoot 3), h3,
    Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val]

private theorem d4Torus_conj_d4X (hσ : σ ^ 3 = 1) (hσ3 : σ.toRingHom ^ 3 = 1) {a : Kˣ}
    (ha : a * TrialityCover.unitsSigma σ a *
      TrialityCover.unitsSigma σ (TrialityCover.unitsSigma σ a) = 1)
    (b : trialityFixedField K σ.toRingHom) (c : K) :
    d4Torus σ hσ a * d4X σ.toRingHom hσ3 (b, c) * (d4Torus σ hσ a)⁻¹ =
      d4X σ.toRingHom hσ3 (b, (a : K) ^ 2 * c) := by
  unfold d4X
  calc d4Torus σ hσ a * (fixX σ.toRingHom (j := 1) (by decide) b *
        orb3 σ.toRingHom (j := 2) (by decide) hσ3 c) * (d4Torus σ hσ a)⁻¹
      = (d4Torus σ hσ a * fixX σ.toRingHom (j := 1) (by decide) b * (d4Torus σ hσ a)⁻¹) *
          (d4Torus σ hσ a * orb3 σ.toRingHom (j := 2) (by decide) hσ3 c * (d4Torus σ hσ a)⁻¹) := by
        group
    _ = _ := by rw [d4Torus_conj_fixX_one σ hσ ha, d4Torus_conj_orb3_two σ hσ hσ3 ha]

private theorem d4Torus_conj_d4Y (hσ : σ ^ 3 = 1) (hσ3 : σ.toRingHom ^ 3 = 1) {a : Kˣ}
    (ha : a * TrialityCover.unitsSigma σ a *
      TrialityCover.unitsSigma σ (TrialityCover.unitsSigma σ a) = 1)
    (e : trialityFixedField K σ.toRingHom) (d : K) :
    d4Torus σ hσ a * d4Y σ.toRingHom hσ3 (e, d) * (d4Torus σ hσ a)⁻¹ =
      d4Y σ.toRingHom hσ3 (e, ((a : K) ^ 2)⁻¹ * d) := by
  unfold d4Y
  calc d4Torus σ hσ a * (orb3 σ.toRingHom (j := 3) (by decide) hσ3 d *
        fixX σ.toRingHom (j := 4) (by decide) e) * (d4Torus σ hσ a)⁻¹
      = (d4Torus σ hσ a * orb3 σ.toRingHom (j := 3) (by decide) hσ3 d * (d4Torus σ hσ a)⁻¹) *
          (d4Torus σ hσ a * fixX σ.toRingHom (j := 4) (by decide) e * (d4Torus σ hσ a)⁻¹) := by
        group
    _ = _ := by rw [d4Torus_conj_orb3_three σ hσ hσ3 ha, d4Torus_conj_fixX_four σ hσ ha]

private theorem d4Torus_conj_d4Z (hσ : σ ^ 3 = 1) {a : Kˣ}
    (ha : a * TrialityCover.unitsSigma σ a *
      TrialityCover.unitsSigma σ (TrialityCover.unitsSigma σ a) = 1)
    (f : trialityFixedField K σ.toRingHom) :
    d4Torus σ hσ a * d4Z σ.toRingHom f * (d4Torus σ hσ a)⁻¹ =
      d4Z σ.toRingHom f :=
  d4Torus_conj_fixX_five σ hσ ha f

private theorem d4Torus_mem_normalizer (hσ : σ ^ 3 = 1) (hσ3 : σ.toRingHom ^ 3 = 1)
    (hne : ∃ u, σ.toRingHom u ≠ u)
    (hnorm : ∀ a : Kˣ, a * TrialityCover.unitsSigma σ a *
      TrialityCover.unitsSigma σ (TrialityCover.unitsSigma σ a) = 1)
    (a : Kˣ) :
    d4Torus σ hσ a ∈ Subgroup.normalizer
      ((polarizedHeisenbergData_d4_charTwo σ.toRingHom hσ3 hne).heisSubgroup :
        Set ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) := by
  have hconj : ∀ (a' : Kˣ) (q : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)),
      q ∈ (polarizedHeisenbergData_d4_charTwo σ.toRingHom hσ3 hne).heisSubgroup →
      d4Torus σ hσ a' * q * (d4Torus σ hσ a')⁻¹ ∈
        (polarizedHeisenbergData_d4_charTwo σ.toRingHom hσ3 hne).heisSubgroup := by
    rintro a' _ ⟨⟨b, c⟩, ⟨e, d⟩, f, rfl⟩
    have heq : d4Torus σ hσ a' * (d4X σ.toRingHom hσ3 (b, c) * d4Y σ.toRingHom hσ3 (e, d) *
          d4Z σ.toRingHom f) * (d4Torus σ hσ a')⁻¹ =
        (d4Torus σ hσ a' * d4X σ.toRingHom hσ3 (b, c) * (d4Torus σ hσ a')⁻¹) *
          (d4Torus σ hσ a' * d4Y σ.toRingHom hσ3 (e, d) * (d4Torus σ hσ a')⁻¹) *
          (d4Torus σ hσ a' * d4Z σ.toRingHom f * (d4Torus σ hσ a')⁻¹) := by
      group
    rw [heq, d4Torus_conj_d4X σ hσ hσ3 (hnorm a'), d4Torus_conj_d4Y σ hσ hσ3 (hnorm a'),
      d4Torus_conj_d4Z σ hσ (hnorm a')]
    exact ⟨(b, (a' : K) ^ 2 * c), (e, ((a' : K) ^ 2)⁻¹ * d), f, rfl⟩
  refine mem_normalizer_of_conj_mem (hconj a) fun q hq => ?_
  have := hconj a⁻¹ q hq
  rwa [← d4Torus_inv σ hσ a, inv_inv] at this

end Torus

/-- Outer Weyl reflection `trialityOuterRep K` inside `graphFixedRootGroup TwistTag.D4`. -/
private noncomputable def d4Weyl : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
  ⟨trialityOuterRep K, by
    rw [trialityOuterRep, canonicalRep_orbitReflection_eq_orbitN TwistTag.D4 σ.toRingHom]
    exact orbitN_mem_graphFixedRootGroup _ σ.toRingHom _ 1⟩

private theorem canonicalRep_conj_trialityOrbitProd (w : WeylGroup TwistTag.D4.tag)
    {α β : Fin TwistTag.D4.tag.rank → ℤ} (hα₀ : IsRoot TwistTag.D4.tag α)
    (hα₁ : IsRoot TwistTag.D4.tag (permLattice TwistTag.D4.perm α))
    (hα₂ : IsRoot TwistTag.D4.tag (permLattice (TwistTag.D4.perm ^ 2) α)) (h₀ : w • α = β)
    (h₁ : w • permLattice TwistTag.D4.perm α = permLattice TwistTag.D4.perm β)
    (h₂ : w • permLattice (TwistTag.D4.perm ^ 2) α = permLattice (TwistTag.D4.perm ^ 2) β)
    (c : K) :
    canonicalRep (coxeterSystem TwistTag.D4.tag) K w *
        (trialityOrbitProd K σ.toRingHom α c : ModGL TwistTag.D4.tag K) *
        (canonicalRep (coxeterSystem TwistTag.D4.tag) K w)⁻¹ =
      (trialityOrbitProd K σ.toRingHom β c : ModGL TwistTag.D4.tag K) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have e : ∀ (n a b c : ModGL TwistTag.D4.tag K),
      n * (a * b * c) * n⁻¹ = n * a * n⁻¹ * (n * b * n⁻¹) * (n * c * n⁻¹) := by
    intro n a b c; group
  rw [coe_trialityOrbitProd, coe_trialityOrbitProd, e,
    canonicalRep_mul_pinnedX_mul_inv_of_two h2 w hα₀,
    canonicalRep_mul_pinnedX_mul_inv_of_two h2 w hα₁,
    canonicalRep_mul_pinnedX_mul_inv_of_two h2 w hα₂, h₀, h₁, h₂]

private theorem d4Weyl_conj_fixX_one (b : trialityFixedField K σ.toRingHom) :
    d4Weyl σ * fixX σ.toRingHom (j := 1) (by decide) b * (d4Weyl σ)⁻¹ =
      fixX σ.toRingHom (j := 4) (by decide) b := by
  apply Subtype.ext
  change trialityOuterRep K * pinnedX TwistTag.D4.tag K (trialityRoot 1) b.1 *
      (trialityOuterRep K)⁻¹ = pinnedX TwistTag.D4.tag K (trialityRoot 4) b.1
  rw [trialityOuterRep,
    canonicalRep_mul_pinnedX_mul_inv_of_two CharTwo.two_eq_zero _ (isRoot_trialityRoot' 1)]
  congr 1
  rw [TwistTag.orbitReflection_smul]
  decide +kernel

private theorem d4Weyl_conj_fixX_four (e : trialityFixedField K σ.toRingHom) :
    d4Weyl σ * fixX σ.toRingHom (j := 4) (by decide) e * (d4Weyl σ)⁻¹ =
      fixX σ.toRingHom (j := 1) (by decide) e := by
  apply Subtype.ext
  change trialityOuterRep K * pinnedX TwistTag.D4.tag K (trialityRoot 4) e.1 *
      (trialityOuterRep K)⁻¹ = pinnedX TwistTag.D4.tag K (trialityRoot 1) e.1
  rw [trialityOuterRep,
    canonicalRep_mul_pinnedX_mul_inv_of_two CharTwo.two_eq_zero _ (isRoot_trialityRoot' 4)]
  congr 1
  rw [TwistTag.orbitReflection_smul]
  decide +kernel

private theorem d4Weyl_conj_fixX_five (f : trialityFixedField K σ.toRingHom) :
    d4Weyl σ * fixX σ.toRingHom (j := 5) (by decide) f * (d4Weyl σ)⁻¹ =
      fixX σ.toRingHom (j := 5) (by decide) f := by
  apply Subtype.ext
  change trialityOuterRep K * pinnedX TwistTag.D4.tag K (trialityRoot 5) f.1 *
      (trialityOuterRep K)⁻¹ = pinnedX TwistTag.D4.tag K (trialityRoot 5) f.1
  rw [trialityOuterRep,
    canonicalRep_mul_pinnedX_mul_inv_of_two CharTwo.two_eq_zero _ (isRoot_trialityRoot' 5)]
  congr 1
  rw [TwistTag.orbitReflection_smul]
  decide +kernel

private theorem d4Weyl_conj_orb3_two (hσ3 : σ.toRingHom ^ 3 = 1) (c : K) :
    d4Weyl σ * orb3 σ.toRingHom (j := 2) (by decide) hσ3 c * (d4Weyl σ)⁻¹ =
      orb3 σ.toRingHom (j := 3) (by decide) hσ3 c := by
  apply Subtype.ext
  change trialityOuterRep K * orb3Val σ.toRingHom (trialityRoot 2) c * (trialityOuterRep K)⁻¹ =
    orb3Val σ.toRingHom (trialityRoot 3) c
  rw [orb3Val_eq_trialityOrbitProd, orb3Val_eq_trialityOrbitProd]
  exact canonicalRep_conj_trialityOrbitProd σ _ (isRoot_trialityRoot 2 0).1
    (isRoot_trialityRoot 2 1).1 (isRoot_trialityRoot 2 2).1
    (by rw [TwistTag.orbitReflection_smul]; decide +kernel)
    (by rw [TwistTag.orbitReflection_smul]; decide +kernel)
    (by rw [TwistTag.orbitReflection_smul]; decide +kernel) c

private theorem d4Weyl_conj_orb3_three (hσ3 : σ.toRingHom ^ 3 = 1) (d : K) :
    d4Weyl σ * orb3 σ.toRingHom (j := 3) (by decide) hσ3 d * (d4Weyl σ)⁻¹ =
      orb3 σ.toRingHom (j := 2) (by decide) hσ3 d := by
  apply Subtype.ext
  change trialityOuterRep K * orb3Val σ.toRingHom (trialityRoot 3) d * (trialityOuterRep K)⁻¹ =
    orb3Val σ.toRingHom (trialityRoot 2) d
  rw [orb3Val_eq_trialityOrbitProd, orb3Val_eq_trialityOrbitProd]
  exact canonicalRep_conj_trialityOrbitProd σ _ (isRoot_trialityRoot 3 0).1
    (isRoot_trialityRoot 3 1).1 (isRoot_trialityRoot 3 2).1
    (by rw [TwistTag.orbitReflection_smul]; decide +kernel)
    (by rw [TwistTag.orbitReflection_smul]; decide +kernel)
    (by rw [TwistTag.orbitReflection_smul]; decide +kernel) d

private theorem d4Weyl_conj_d4X (hσ3 : σ.toRingHom ^ 3 = 1)
    (u : trialityFixedField K σ.toRingHom × K) :
    d4Weyl σ * d4X σ.toRingHom hσ3 u * (d4Weyl σ)⁻¹ = d4Y σ.toRingHom hσ3 u := by
  unfold d4X d4Y
  have e : d4Weyl σ * (fixX σ.toRingHom (j := 1) (by decide) u.1 *
        orb3 σ.toRingHom (j := 2) (by decide) hσ3 u.2) * (d4Weyl σ)⁻¹ =
      (d4Weyl σ * fixX σ.toRingHom (j := 1) (by decide) u.1 * (d4Weyl σ)⁻¹) *
        (d4Weyl σ * orb3 σ.toRingHom (j := 2) (by decide) hσ3 u.2 * (d4Weyl σ)⁻¹) := by
    group
  rw [e, d4Weyl_conj_fixX_one, d4Weyl_conj_orb3_two]
  exact (commute_orb3_fixX σ.toRingHom (i := 3) (j := 4) (by decide) (by decide) (by decide)
    hσ3 u.2 u.1).symm.eq

private theorem d4Weyl_conj_d4Y (hσ3 : σ.toRingHom ^ 3 = 1)
    (v : trialityFixedField K σ.toRingHom × K) :
    d4Weyl σ * d4Y σ.toRingHom hσ3 v * (d4Weyl σ)⁻¹ = d4X σ.toRingHom hσ3 v := by
  unfold d4X d4Y
  have e : d4Weyl σ * (orb3 σ.toRingHom (j := 3) (by decide) hσ3 v.2 *
        fixX σ.toRingHom (j := 4) (by decide) v.1) * (d4Weyl σ)⁻¹ =
      (d4Weyl σ * orb3 σ.toRingHom (j := 3) (by decide) hσ3 v.2 * (d4Weyl σ)⁻¹) *
        (d4Weyl σ * fixX σ.toRingHom (j := 4) (by decide) v.1 * (d4Weyl σ)⁻¹) := by
    group
  rw [e, d4Weyl_conj_orb3_three, d4Weyl_conj_fixX_four]
  exact (commute_fixX_orb3 σ.toRingHom (i := 1) (j := 2) (by decide) (by decide) (by decide)
    hσ3 v.1 v.2).symm.eq

private theorem d4Weyl_conj_d4Z (f : trialityFixedField K σ.toRingHom) :
    d4Weyl σ * d4Z σ.toRingHom f * (d4Weyl σ)⁻¹ = d4Z σ.toRingHom f :=
  d4Weyl_conj_fixX_five σ f

private theorem d4Weyl_mem_normalizer (hσ3 : σ.toRingHom ^ 3 = 1) (hne : ∃ u, σ.toRingHom u ≠ u) :
    d4Weyl σ ∈ Subgroup.normalizer
      ((polarizedHeisenbergData_d4_charTwo σ.toRingHom hσ3 hne).heisSubgroup :
        Set ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) := by
  let D := polarizedHeisenbergData_d4_charTwo σ.toRingHom hσ3 hne
  have h1 : ∀ u v s, d4Weyl σ * (d4X σ.toRingHom hσ3 u * d4Y σ.toRingHom hσ3 v *
        d4Z σ.toRingHom s) * (d4Weyl σ)⁻¹ =
      d4X σ.toRingHom hσ3 v * d4Y σ.toRingHom hσ3 u *
        d4Z σ.toRingHom (s - d4B σ.toRingHom hσ3 1 1 v u) := by
    intro u v s
    have e : d4Weyl σ * (d4X σ.toRingHom hσ3 u * d4Y σ.toRingHom hσ3 v *
          d4Z σ.toRingHom s) * (d4Weyl σ)⁻¹ =
        (d4Weyl σ * d4X σ.toRingHom hσ3 u * (d4Weyl σ)⁻¹) *
          (d4Weyl σ * d4Y σ.toRingHom hσ3 v * (d4Weyl σ)⁻¹) *
          (d4Weyl σ * d4Z σ.toRingHom s * (d4Weyl σ)⁻¹) := by
      group
    rw [e, d4Weyl_conj_d4X, d4Weyl_conj_d4Y, d4Weyl_conj_d4Z, D.Y_mul_X, mul_assoc,
      ← D.z_add]
    have hs : -d4B σ.toRingHom hσ3 1 1 v u + s = s - d4B σ.toRingHom hσ3 1 1 v u := by ring
    rw [hs]
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · rintro ⟨u, v, s, rfl⟩
    rw [h1]
    exact ⟨v, u, s - d4B σ.toRingHom hσ3 1 1 v u, rfl⟩
  · rintro ⟨u, v, s, hs⟩
    have h2 := h1 v u (s + d4B σ.toRingHom hσ3 1 1 u v)
    rw [add_sub_cancel_right] at h2
    have heq : d4Weyl σ * (d4X σ.toRingHom hσ3 v * d4Y σ.toRingHom hσ3 u *
        d4Z σ.toRingHom (s + d4B σ.toRingHom hσ3 1 1 u v)) * (d4Weyl σ)⁻¹ =
      d4Weyl σ * h * (d4Weyl σ)⁻¹ := h2.trans hs
    have h_eq : h = d4X σ.toRingHom hσ3 v * d4Y σ.toRingHom hσ3 u *
        d4Z σ.toRingHom (s + d4B σ.toRingHom hσ3 1 1 u v) := by
      calc h = (d4Weyl σ)⁻¹ * (d4Weyl σ * h * (d4Weyl σ)⁻¹) * d4Weyl σ := by group
        _ = (d4Weyl σ)⁻¹ * (d4Weyl σ * (d4X σ.toRingHom hσ3 v * d4Y σ.toRingHom hσ3 u *
              d4Z σ.toRingHom (s + d4B σ.toRingHom hσ3 1 1 u v)) * (d4Weyl σ)⁻¹) * d4Weyl σ := by
            rw [heq]
        _ = _ := by group
    rw [h_eq]
    exact ⟨v, u, s + d4B σ.toRingHom hσ3 1 1 u v, rfl⟩

/-- Short-orbit unipotent element `x₁(1)` in `graphFixedRootGroup TwistTag.D4`. -/
private noncomputable def d4X1 (hσ3 : σ.toRingHom ^ 3 = 1) :
    ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
  orb3 σ.toRingHom (j := 0) (by decide) hσ3 1

private theorem d4X1_inv (hσ3 : σ.toRingHom ^ 3 = 1) : (d4X1 σ hσ3)⁻¹ = d4X1 σ hσ3 := by
  refine inv_eq_of_mul_eq_one_right ?_
  unfold d4X1
  rw [← orb3_add, CharTwo.add_self_eq_zero, orb3_zero]

private theorem d4X1_conj_fixX_one (hσ3 : σ.toRingHom ^ 3 = 1)
    (b : trialityFixedField K σ.toRingHom) :
    d4X1 σ hσ3 * fixX σ.toRingHom (j := 1) (by decide) b * (d4X1 σ hσ3)⁻¹ =
      d4Y σ.toRingHom hσ3 (b, b.1) * d4Z σ.toRingHom (b ^ 2) * d4X σ.toRingHom hσ3 (b, b.1) := by
  have hcomm := comm_orb3_zero_one_fixX_one σ.toRingHom hσ3 b
  have hconj : d4X1 σ hσ3 * fixX σ.toRingHom (j := 1) (by decide) b * (d4X1 σ hσ3)⁻¹ =
      ⁅d4X1 σ hσ3, fixX σ.toRingHom (j := 1) (by decide) b⁆ *
        fixX σ.toRingHom (j := 1) (by decide) b := by
    rw [commutatorElement_def]
    group
  rw [hconj, d4X1, hcomm, fixX_four_eq_d4Y σ.toRingHom hσ3, orb3_three_eq_d4Y σ.toRingHom hσ3,
    fixX_five_eq_d4Z, orb3_two_eq_d4X σ.toRingHom hσ3, fixX_one_eq_d4X σ.toRingHom hσ3,
    ← d4Y_add, mul_assoc (d4Y _ _ _ * _), ← d4X_add]
  simp only [Prod.mk_add_mk, add_zero, zero_add]

private theorem d4X1_conj_d4X_zero_d4Y_zero (hσ3 : σ.toRingHom ^ 3 = 1)
    (hne : ∃ u, σ.toRingHom u ≠ u) (b e : trialityFixedField K σ.toRingHom) :
    d4X1 σ hσ3 * (d4X σ.toRingHom hσ3 (b, 0) * d4Y σ.toRingHom hσ3 (e, 0)) * (d4X1 σ hσ3)⁻¹ =
      d4X σ.toRingHom hσ3 (b, b.1) * d4Y σ.toRingHom hσ3 (b + e, b.1) *
        d4Z σ.toRingHom (b ^ 2 - d4B σ.toRingHom hσ3 1 1 (b, b.1) (b, b.1)) := by
  let D := polarizedHeisenbergData_d4_charTwo σ.toRingHom hσ3 hne
  have hc4 : d4X1 σ hσ3 * fixX σ.toRingHom (j := 4) (by decide) e * (d4X1 σ hσ3)⁻¹ =
      fixX σ.toRingHom (j := 4) (by decide) e := by
    unfold d4X1
    rw [(commute_orb3_zero_fixX_four σ.toRingHom hσ3 1 e).eq, mul_inv_cancel_right]
  rw [← fixX_one_eq_d4X, ← fixX_four_eq_d4Y]
  have e1 : d4X1 σ hσ3 * (fixX σ.toRingHom (j := 1) (by decide) b *
        fixX σ.toRingHom (j := 4) (by decide) e) * (d4X1 σ hσ3)⁻¹ =
      (d4X1 σ hσ3 * fixX σ.toRingHom (j := 1) (by decide) b * (d4X1 σ hσ3)⁻¹) *
        (d4X1 σ hσ3 * fixX σ.toRingHom (j := 4) (by decide) e * (d4X1 σ hσ3)⁻¹) := by
    group
  rw [e1, d4X1_conj_fixX_one, hc4, fixX_four_eq_d4Y σ.toRingHom hσ3]
  have hczX : d4Z σ.toRingHom (b ^ 2) * d4X σ.toRingHom hσ3 (b, b.1) =
      d4X σ.toRingHom hσ3 (b, b.1) * d4Z σ.toRingHom (b ^ 2) :=
    (D.commute_X_z (b, b.1) (b ^ 2)).symm.eq
  have hczY : d4Z σ.toRingHom (-d4B σ.toRingHom hσ3 1 1 (b, b.1) (b, b.1) + b ^ 2) *
        d4Y σ.toRingHom hσ3 (e, 0) =
      d4Y σ.toRingHom hσ3 (e, 0) *
        d4Z σ.toRingHom (-d4B σ.toRingHom hσ3 1 1 (b, b.1) (b, b.1) + b ^ 2) :=
    (D.commute_Y_z (e, 0) _).symm.eq
  calc d4Y σ.toRingHom hσ3 (b, b.1) * d4Z σ.toRingHom (b ^ 2) *
        d4X σ.toRingHom hσ3 (b, b.1) * d4Y σ.toRingHom hσ3 (e, 0)
      = (d4Y σ.toRingHom hσ3 (b, b.1) * d4X σ.toRingHom hσ3 (b, b.1)) *
          d4Z σ.toRingHom (b ^ 2) * d4Y σ.toRingHom hσ3 (e, 0) := by
        rw [mul_assoc (d4Y _ _ _), hczX, ← mul_assoc]
    _ = d4X σ.toRingHom hσ3 (b, b.1) * d4Y σ.toRingHom hσ3 (b, b.1) *
          d4Z σ.toRingHom (-d4B σ.toRingHom hσ3 1 1 (b, b.1) (b, b.1) + b ^ 2) *
          d4Y σ.toRingHom hσ3 (e, 0) := by
        rw [D.Y_mul_X, mul_assoc (d4X _ _ _ * d4Y _ _ _), ← D.z_add]
    _ = d4X σ.toRingHom hσ3 (b, b.1) *
          (d4Y σ.toRingHom hσ3 (b, b.1) * d4Y σ.toRingHom hσ3 (e, 0)) *
          d4Z σ.toRingHom (-d4B σ.toRingHom hσ3 1 1 (b, b.1) (b, b.1) + b ^ 2) := by
        rw [mul_assoc (d4X _ _ _ * d4Y _ _ _), hczY]
        group
    _ = d4X σ.toRingHom hσ3 (b, b.1) * d4Y σ.toRingHom hσ3 (b + e, b.1) *
          d4Z σ.toRingHom (b ^ 2 - d4B σ.toRingHom hσ3 1 1 (b, b.1) (b, b.1)) := by
        have hp : ((b, b.1) + (e, 0) : trialityFixedField K σ.toRingHom × K) = (b + e, b.1) :=
          Prod.ext rfl (add_zero b.1)
        have hs : -d4B σ.toRingHom hσ3 1 1 (b, b.1) (b, b.1) + b ^ 2 =
            b ^ 2 - d4B σ.toRingHom hσ3 1 1 (b, b.1) (b, b.1) := by ring
        rw [← D.Y_add, hp, hs]

private theorem d4X1_mem_normalizer (hσ3 : σ.toRingHom ^ 3 = 1) (hne : ∃ u, σ.toRingHom u ≠ u) :
    d4X1 σ hσ3 ∈ Subgroup.normalizer
      ((polarizedHeisenbergData_d4_charTwo σ.toRingHom hσ3 hne).heisSubgroup :
        Set ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) := by
  let Q₀ := (polarizedHeisenbergData_d4_charTwo σ.toRingHom hσ3 hne).heisSubgroup
  have h_gen : ∀ q ∈ Q₀, d4X1 σ hσ3 * q * (d4X1 σ hσ3)⁻¹ ∈ Q₀ := by
    rintro _ ⟨⟨b, c⟩, ⟨e, d⟩, f, rfl⟩
    have heq : d4X1 σ hσ3 * (d4X σ.toRingHom hσ3 (b, c) * d4Y σ.toRingHom hσ3 (e, d) *
          d4Z σ.toRingHom f) * (d4X1 σ hσ3)⁻¹ =
        (d4X1 σ hσ3 * fixX σ.toRingHom (j := 1) (by decide) b * (d4X1 σ hσ3)⁻¹) *
          (d4X1 σ hσ3 * orb3 σ.toRingHom (j := 2) (by decide) hσ3 c * (d4X1 σ hσ3)⁻¹) *
          (d4X1 σ hσ3 * orb3 σ.toRingHom (j := 3) (by decide) hσ3 d * (d4X1 σ hσ3)⁻¹) *
          (d4X1 σ hσ3 * fixX σ.toRingHom (j := 4) (by decide) e * (d4X1 σ hσ3)⁻¹) *
          (d4X1 σ hσ3 * fixX σ.toRingHom (j := 5) (by decide) f * (d4X1 σ hσ3)⁻¹) := by
      unfold d4X d4Y d4Z
      group
    rw [heq]
    have h1 : d4X1 σ hσ3 * fixX σ.toRingHom (j := 1) (by decide) b * (d4X1 σ hσ3)⁻¹ ∈ Q₀ := by
      rw [d4X1_conj_fixX_one]
      exact mul_mem (mul_mem (d4Y_mem_heisSubgroup σ hne _) (d4Z_mem_heisSubgroup σ hne _))
        (d4X_mem_heisSubgroup σ hne _)
    have h2 : d4X1 σ hσ3 * orb3 σ.toRingHom (j := 2) (by decide) hσ3 c * (d4X1 σ hσ3)⁻¹ ∈ Q₀ := by
      obtain ⟨e', d', f', hc⟩ := comm_orb3_zero_orb3_two σ.toRingHom hσ3 1 c
      have hconj : d4X1 σ hσ3 * orb3 σ.toRingHom (j := 2) (by decide) hσ3 c * (d4X1 σ hσ3)⁻¹ =
          ⁅d4X1 σ hσ3, orb3 σ.toRingHom (j := 2) (by decide) hσ3 c⁆ *
            orb3 σ.toRingHom (j := 2) (by decide) hσ3 c := by
        rw [commutatorElement_def]; group
      rw [hconj, d4X1, hc, fixX_four_eq_d4Y σ.toRingHom hσ3, orb3_three_eq_d4Y σ.toRingHom hσ3,
        fixX_five_eq_d4Z, orb3_two_eq_d4X σ.toRingHom hσ3]
      exact mul_mem (mul_mem (mul_mem (d4Y_mem_heisSubgroup σ hne _) (d4Y_mem_heisSubgroup σ hne _))
        (d4Z_mem_heisSubgroup σ hne _)) (d4X_mem_heisSubgroup σ hne _)
    have h3 : d4X1 σ hσ3 * orb3 σ.toRingHom (j := 3) (by decide) hσ3 d * (d4X1 σ hσ3)⁻¹ ∈ Q₀ := by
      have hc := comm_orb3_zero_orb3_three σ.toRingHom hσ3 1 d
      have hconj : d4X1 σ hσ3 * orb3 σ.toRingHom (j := 3) (by decide) hσ3 d * (d4X1 σ hσ3)⁻¹ =
          ⁅d4X1 σ hσ3, orb3 σ.toRingHom (j := 3) (by decide) hσ3 d⁆ *
            orb3 σ.toRingHom (j := 3) (by decide) hσ3 d := by
        rw [commutatorElement_def]; group
      rw [hconj, d4X1, hc, fixX_four_eq_d4Y σ.toRingHom hσ3, orb3_three_eq_d4Y σ.toRingHom hσ3]
      exact mul_mem (d4Y_mem_heisSubgroup σ hne _) (d4Y_mem_heisSubgroup σ hne _)
    have h4 : d4X1 σ hσ3 * fixX σ.toRingHom (j := 4) (by decide) e * (d4X1 σ hσ3)⁻¹ ∈ Q₀ := by
      unfold d4X1
      rw [(commute_orb3_zero_fixX_four σ.toRingHom hσ3 1 e).eq, mul_inv_cancel_right,
        fixX_four_eq_d4Y σ.toRingHom hσ3]
      exact d4Y_mem_heisSubgroup σ hne _
    have h5 : d4X1 σ hσ3 * fixX σ.toRingHom (j := 5) (by decide) f * (d4X1 σ hσ3)⁻¹ ∈ Q₀ := by
      unfold d4X1
      rw [(commute_orb3_zero_fixX_five σ.toRingHom hσ3 1 f).eq, mul_inv_cancel_right,
        fixX_five_eq_d4Z]
      exact d4Z_mem_heisSubgroup σ hne _
    exact mul_mem (mul_mem (mul_mem (mul_mem h1 h2) h3) h4) h5
  refine mem_normalizer_of_conj_mem h_gen fun q hq => ?_
  have := h_gen q hq
  rwa [← d4X1_inv σ hσ3, inv_inv] at this

/-! ### Ruling out normalizer-invariant abelian subgroups for `q = 2` -/

/-- If `∀ c : K, σ c = c ^ 2` and `σ ^ 3 = 1`, any `x : K` with `σ x ≠ x` satisfies
`x ≠ 0`, `x + 1 ≠ 0`, and `x⁻¹ + (x + 1)⁻¹ + 1 ≠ 0`. -/
private theorem coeff_ne_zero_of_sigma_ne (hσ : σ ^ 3 = 1) (hsq : ∀ c : K, σ c = c ^ 2)
    {x : K} (hx : σ x ≠ x) :
    x ≠ 0 ∧ x + 1 ≠ 0 ∧ x⁻¹ + (x + 1)⁻¹ + 1 ≠ 0 := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hx (map_zero σ)
  have hx1 : x + 1 ≠ 0 := by
    intro h
    have hx_eq : x = 1 := by
      have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
      linear_combination h - h2
    subst hx_eq
    exact hx (map_one σ)
  refine ⟨hx0, hx1, fun hμ => ?_⟩
  have hpoly : x ^ 2 + x + 1 = 0 := by
    have h1 : x * x⁻¹ = 1 := mul_inv_cancel₀ hx0
    have h2 : (x + 1) * (x + 1)⁻¹ = 1 := mul_inv_cancel₀ hx1
    have h3 : (2 : K) = 0 := CharTwo.two_eq_zero
    linear_combination x * (x + 1) * hμ - (x + 1) * h1 - x * h2 - x * h3
  have hσx : σ x = x + 1 := by
    rw [hsq x]
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    linear_combination hpoly - (x + 1) * h2
  have hσ2x : σ (σ x) = x := by
    rw [hσx, map_add, map_one, hσx]
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    linear_combination h2
  have hσ3x : σ (σ (σ x)) = x := TrialityCover.pow_three_apply_eq σ hσ x
  rw [hσ2x] at hσ3x
  exact hx hσ3x

variable [Finite K]

/-- In a finite characteristic-`2` field `K`, every nonzero element is the square of a unit. -/
private theorem exists_units_sq_eq {y : K} (hy : y ≠ 0) : ∃ a : Kˣ, (a : K) ^ 2 = y := by
  have hodd := TrialityCover.odd_card_units_of_charTwo K
  let sqHom : Kˣ →* Kˣ :=
    { toFun := fun a => a ^ 2
      map_one' := one_pow 2
      map_mul' := fun a b => mul_pow a b 2 }
  have hinj : Function.Injective sqHom := by
    rw [injective_iff_map_eq_one]
    intro a ha
    by_contra hne
    exact TrialityCover.sq_ne_one_of_odd hodd hne ha
  have hsurj : Function.Surjective sqHom := Finite.surjective_of_injective hinj
  obtain ⟨a, ha⟩ := hsurj (Units.mk0 y hy)
  refine ⟨a, ?_⟩
  have := congrArg (fun u : Kˣ => (u : K)) ha
  simpa [sqHom, Units.val_pow_eq_pow_val] using this

/-- Every `D.heisSubgroup.normalizer`-invariant abelian subgroup `K_sub` containing `d4Z` has
`d4X u * d4Y v ∈ K_sub → u = 0 ∧ v = 0` when `Nat.card F = 2` and `∀ c, σ c = c ^ 2`. -/
theorem eq_zero_of_mem_normalizer_invariant_abelian (hσ : σ ^ 3 = 1) (hσ3 : σ.toRingHom ^ 3 = 1)
    (hne : ∃ u, σ.toRingHom u ≠ u) (hsq : ∀ c : K, σ c = c ^ 2)
    (hcardF : Nat.card (trialityFixedField K σ.toRingHom) = 2)
    (K_sub : Subgroup ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hz : ∀ s : trialityFixedField K σ.toRingHom, d4Z σ.toRingHom s ∈ K_sub)
    (hinv : ∀ g ∈ Subgroup.normalizer
      ((polarizedHeisenbergData_d4_charTwo σ.toRingHom hσ3 hne).heisSubgroup :
        Set ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)),
      ∀ k ∈ K_sub, g * k * g⁻¹ ∈ K_sub)
    (habel : ∀ k₁ ∈ K_sub, ∀ k₂ ∈ K_sub, ⁅k₁, k₂⁆ = 1)
    (u v : trialityFixedField K σ.toRingHom × K)
    (huv : d4X σ.toRingHom hσ3 u * d4Y σ.toRingHom hσ3 v ∈ K_sub) :
    u = 0 ∧ v = 0 := by
  let F := ↥(trialityFixedField K σ.toRingHom)
  have : CharP F 2 := Subfield.charP (trialityFixedField K σ.toRingHom) 2
  let D := polarizedHeisenbergData_d4_charTwo σ.toRingHom hσ3 hne
  have hF_sub : Subsingleton Fˣ := by
    apply Finite.card_le_one_iff_subsingleton.1
    rw [Nat.card_units, hcardF]
  have hnorm : ∀ a : Kˣ, a * TrialityCover.unitsSigma σ a *
      TrialityCover.unitsSigma σ (TrialityCover.unitsSigma σ a) = 1 := fun a => by
    rw [← trialityFixedUnit_norm hσ,
      Subsingleton.elim (trialityNorm σ hσ a) 1, map_one]
  let inK : (F × K) → (F × K) → Prop := fun u' v' =>
    d4X σ.toRingHom hσ3 u' * d4Y σ.toRingHom hσ3 v' ∈ K_sub
  have inK_add : ∀ {u₁ v₁ u₂ v₂}, inK u₁ v₁ → inK u₂ v₂ → inK (u₁ + u₂) (v₁ + v₂) := by
    intro u₁ v₁ u₂ v₂ h1 h2
    have hmul : (d4X σ.toRingHom hσ3 u₁ * d4Y σ.toRingHom hσ3 v₁ * d4Z σ.toRingHom 0) *
        (d4X σ.toRingHom hσ3 u₂ * d4Y σ.toRingHom hσ3 v₂ * d4Z σ.toRingHom 0) ∈ K_sub := by
      rw [D.z_zero, mul_one, mul_one]
      exact mul_mem h1 h2
    rw [D.mul_normalForm] at hmul
    exact (Subgroup.mul_mem_cancel_right K_sub (hz _)).1 hmul
  have inK_comm : ∀ {u₁ v₁ u₂ v₂}, inK u₁ v₁ → inK u₂ v₂ →
      d4B σ.toRingHom hσ3 1 1 u₁ v₂ = d4B σ.toRingHom hσ3 1 1 u₂ v₁ := by
    intro u₁ v₁ u₂ v₂ h1 h2
    have hc := habel (d4X σ.toRingHom hσ3 u₁ * d4Y σ.toRingHom hσ3 v₁ * d4Z σ.toRingHom 0)
      (by rw [D.z_zero, mul_one]; exact h1)
      (d4X σ.toRingHom hσ3 u₂ * d4Y σ.toRingHom hσ3 v₂ * d4Z σ.toRingHom 0)
      (by rw [D.z_zero, mul_one]; exact h2)
    rw [D.comm_normalForm, D.X_zero, D.Y_zero, one_mul, one_mul] at hc
    exact sub_eq_zero.1 (D.z_eq_one _ hc)
  have inK_ho : ∀ (a : Kˣ) {b e : F} {c d : K}, inK (b, c) (e, d) →
      inK (b, (a : K) ^ 2 * c) (e, ((a : K) ^ 2)⁻¹ * d) := by
    intro a b e c d h
    have hc := hinv (d4Torus σ hσ a) (d4Torus_mem_normalizer σ hσ hσ3 hne hnorm a) _ h
    have e1 : d4Torus σ hσ a * (d4X σ.toRingHom hσ3 (b, c) * d4Y σ.toRingHom hσ3 (e, d)) *
          (d4Torus σ hσ a)⁻¹ =
        (d4Torus σ hσ a * d4X σ.toRingHom hσ3 (b, c) * (d4Torus σ hσ a)⁻¹) *
          (d4Torus σ hσ a * d4Y σ.toRingHom hσ3 (e, d) * (d4Torus σ hσ a)⁻¹) := by
      group
    rwa [e1, d4Torus_conj_d4X σ hσ hσ3 (hnorm a), d4Torus_conj_d4Y σ hσ hσ3 (hnorm a)] at hc
  have inK_swap : ∀ {u' v'}, inK u' v' → inK v' u' := by
    intro u' v' h
    have hc := hinv (d4Weyl σ) (d4Weyl_mem_normalizer σ hσ3 hne) _ h
    have e1 : d4Weyl σ * (d4X σ.toRingHom hσ3 u' * d4Y σ.toRingHom hσ3 v') * (d4Weyl σ)⁻¹ =
        (d4Weyl σ * d4X σ.toRingHom hσ3 u' * (d4Weyl σ)⁻¹) *
          (d4Weyl σ * d4Y σ.toRingHom hσ3 v' * (d4Weyl σ)⁻¹) := by
      group
    rw [e1, d4Weyl_conj_d4X, d4Weyl_conj_d4Y, D.Y_mul_X] at hc
    exact (Subgroup.mul_mem_cancel_right K_sub (hz _)).1 hc
  have inK_x1 : ∀ {b e : F}, inK (b, 0) (e, 0) → inK (b, b.1) (b + e, b.1) := by
    intro b e h
    have hc := hinv (d4X1 σ hσ3) (d4X1_mem_normalizer σ hσ3 hne) _ h
    rw [d4X1_conj_d4X_zero_d4Y_zero σ hσ3 hne] at hc
    exact (Subgroup.mul_mem_cancel_right K_sub (hz _)).1 hc
  have step1 : ∀ {b e : F} {c d : K}, inK (b, c) (e, d) → c = 0 := by
    intro b e c d h
    by_contra hc0
    obtain ⟨x, hx⟩ := hne
    obtain ⟨hx0, hx1, hμ⟩ := coeff_ne_zero_of_sigma_ne σ hσ hsq hx
    obtain ⟨a₀, ha₀⟩ := exists_units_sq_eq (K := K) hx1
    have h_a₀ := inK_ho a₀ h
    rw [ha₀] at h_a₀
    have h_q1 := inK_add h_a₀ h
    have h_q1_1 : (b, (x + 1) * c) + (b, c) = (0, x * c) := by
      refine Prod.ext (CharTwo.add_self_eq_zero b) ?_
      change (x + 1) * c + c = x * c
      have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
      linear_combination c * h2
    have h_q1_2 : (e, (x + 1)⁻¹ * d) + (e, d) = (0, (x + 1)⁻¹ * d + d) :=
      Prod.ext (CharTwo.add_self_eq_zero e) rfl
    rw [h_q1_1, h_q1_2] at h_q1
    set d₁ := (x + 1)⁻¹ * d + d
    obtain ⟨b₁, hb₁⟩ := exists_units_sq_eq (K := K) (inv_ne_zero hx0)
    obtain ⟨b₂, hb₂⟩ := exists_units_sq_eq (K := K) (inv_ne_zero hx1)
    have h_b1 := inK_ho b₁ h_q1
    have h_b2 := inK_ho b₂ h_q1
    rw [hb₁, inv_inv] at h_b1
    rw [hb₂, inv_inv] at h_b2
    have h_q2 := inK_add (inK_add h_b1 h_b2) h_q1
    set μ := x⁻¹ + (x + 1)⁻¹ + 1
    have h_q2_1 : ((0 : F), x⁻¹ * (x * c)) + (0, (x + 1)⁻¹ * (x * c)) + (0, x * c) =
        (0, μ * (x * c)) := by
      refine Prod.ext (by simp) ?_
      change x⁻¹ * (x * c) + (x + 1)⁻¹ * (x * c) + x * c = (x⁻¹ + (x + 1)⁻¹ + 1) * (x * c)
      ring
    have h_q2_2 : ((0 : F), x * d₁) + (0, (x + 1) * d₁) + (0, d₁) = (0, 0) := by
      refine Prod.ext (by simp) ?_
      change x * d₁ + (x + 1) * d₁ + d₁ = 0
      have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
      linear_combination (x + 1) * d₁ * h2
    rw [h_q2_1, h_q2_2] at h_q2
    have hw0 : μ * (x * c) ≠ 0 := mul_ne_zero hμ (mul_ne_zero hx0 hc0)
    obtain ⟨a₃, ha₃⟩ := exists_units_sq_eq (K := K) (inv_ne_zero hw0)
    have h_q3 := inK_ho a₃ h_q2
    rw [ha₃, inv_mul_cancel₀ hw0, mul_zero] at h_q3
    have h_q4 := inK_swap h_q3
    have hB_eq := inK_comm h_q3 h_q4
    change d4B σ.toRingHom hσ3 1 1 (0, 1) (0, 1) = d4B σ.toRingHom hσ3 1 1 0 0 at hB_eq
    rw [D.B_zero_left] at hB_eq
    have hB1 : d4B σ.toRingHom hσ3 1 1 (0, 1) (0, 1) = 1 := by
      unfold d4B
      apply Subtype.ext
      simp only [Subfield.coe_mul, Subfield.coe_one, coe_trialityTrace,
        mul_zero, zero_add, mul_one, map_one]
      have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
      linear_combination h2
    exact one_ne_zero (hB1.symm.trans hB_eq)
  rcases u with ⟨b, c⟩
  rcases v with ⟨e, d⟩
  have hc0 : c = 0 := step1 huv
  have hd0 : d = 0 := step1 (inK_swap huv)
  subst hc0 hd0
  have hb0 : b = 0 := Subtype.ext (step1 (inK_x1 huv))
  subst hb0
  have he0 : e = 0 := Subtype.ext (step1 (inK_x1 (inK_swap huv)))
  subst he0
  exact ⟨rfl, rfl⟩

end NormalizerCharTwo

/-! ### Subgroup index bound `64 ≤ H.index` for `³D₄(2)` -/

/-- Every proper subgroup `H` of `³D₄(2)` has index at least `64`. -/
theorem index_ge_64_of_chevalley_trialityD4_two {S : Type} [Group S] [IsSimpleGroup S]
    (h : ChevalleyExceptionalModel S .trialityD4 2 1) (H : Subgroup S) (hH : H ≠ ⊤) :
    64 ≤ H.index := by
  classical
  obtain ⟨⟨hp, hf, -⟩, hm⟩ := h
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ := exists_mulEquiv_graphFixedRootGroup_card .D4 hp hf hm
  obtain ⟨σ', hσ', hord, -, -, k, hk, hkcard, -⟩ :=
    finite_graph_field_parameter_fields .D4 hp hf K hK
  have hσσ' : σ = σ' := RingEquiv.ext fun c => by rw [hσ, hσ']
  subst hσσ'
  have : Fact (Nat.Prime 2) := ⟨hp⟩
  have hK_pow : Nat.card K = 2 ^ 3 := by
    rw [hK]
    rfl
  have : CharP K 2 := finite_field_prime_power_characteristic hp (by decide) hK_pow
  let F := ↥(trialityFixedField K σ.toRingHom)
  have : CharP F 2 := Subfield.charP (trialityFixedField K σ.toRingHom) 2
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have : Finite (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := Subtype.finite
  have : IsSimpleGroup ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := e.symm.isSimpleGroup
  have hσ_cube : σ ^ 3 = 1 := by
    change σ ^ TwistTag.D4.order = 1
    rw [← hord]
    exact pow_orderOf_eq_one σ
  have hσ3 : σ.toRingHom ^ 3 = 1 := RingHom.ext fun c => by
    have hc := congrArg (fun φ : K ≃+* K => φ c) hσ_cube
    simpa [pow_succ, RingAut.mul_apply, RingHom.coe_pow] using hc
  have hne : ∃ u, σ.toRingHom u ≠ u := by
    by_contra! hcon
    have h1 : σ = 1 := RingEquiv.ext hcon
    rw [h1, orderOf_one] at hord
    exact absurd hord (by decide)
  let D := polarizedHeisenbergData_d4_charTwo σ.toRingHom hσ3 hne
  have hV2 : ∀ u : F × K, (2 : ℕ) • u = 0 := fun ⟨b, c⟩ =>
    Prod.ext (by change (2 : ℕ) • b = 0; rw [nsmul_eq_mul, CharP.cast_eq_zero F 2, zero_mul])
      (by change (2 : ℕ) • c = 0; rw [nsmul_eq_mul, CharP.cast_eq_zero K 2, zero_mul])
  have hF_eq : trialityFixedField K σ.toRingHom = k := by
    refine SetLike.ext' ?_
    rw [hk]
    ext c
    simp only [SetLike.mem_coe, mem_trialityFixedField, Set.mem_ofPred_eq]
    rw [← hσ]
    rfl
  have hcardF : Nat.card F = 2 := by
    change Nat.card (trialityFixedField K σ.toRingHom) = 2
    rw [hF_eq, hkcard, pow_one]
  have hcardV : Nat.card (F × K) = 16 := by
    rw [Nat.card_prod, hcardF, hK_pow]
    rfl
  have hcardV_ge : 2 ≤ Nat.card (F × K) := by omega
  have hsq : ∀ c : K, σ c = c ^ 2 := fun c => by
    rw [hσ c, pow_one]
  have hM : H.map (e : S →* ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) ≠ ⊤ := by
    intro htop
    apply hH
    apply Subgroup.map_injective (f := (e : S →* ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)))
      e.injective
    rw [htop, Subgroup.map_top_of_surjective _ e.surjective]
  have hle := D.two_mul_card_le_index_of_ne_top hV2 hcardF hcardV_ge
    (eq_zero_of_mem_normalizer_invariant_abelian σ hσ_cube hσ3 hne hsq hcardF) hM
  rwa [Subgroup.index_map_equiv, hcardV] at hle

/-! ### Main Maróti bound for `³D₄(q)` -/

/-- **Maróti's bound for `³D₄(q)`** (Maróti, Section 2, Step 2, pages 634–635): every primitive
almost simple group `G ≤ Perm α` with socle `S` satisfying
`ChevalleyExceptionalModel S .trialityD4 p f` satisfies `Nat.card G ≤ bound (Nat.card α)`. -/
theorem card_le_bound_of_chevalley_trialityD4 {α : Type} [Finite α]
    {G : Subgroup (Equiv.Perm α)} [MulAction.IsPreprimitive G α]
    {S : Type} [Group S] {p f : ℕ} (hAS : IsAlmostSimpleWith G S)
    (h : ChevalleyExceptionalModel S .trialityD4 p f) :
    Nat.card G ≤ bound (Nat.card α) := by
  have : IsSimpleGroup S := hAS.isSimpleGroup
  have hcard : Nat.card S = ordTrialityD4 (p ^ f) := card_chevalleyExceptionalModel h
  have hout : Nat.card (OuterAut S) ≤ 3 * f := (card_outerAut_trialityD4 h).le
  have ⟨⟨hp, hf, _⟩, _⟩ := h
  have hp2 : 2 ≤ p := hp.two_le
  have hq2 : 2 ≤ p ^ f :=
    (Nat.pow_le_pow_left hp2 1).trans (Nat.pow_le_pow_right hp.pos hf)
  have hfq : f ≤ p ^ f := (Nat.lt_pow_self hp.one_lt).le
  by_cases hq4 : 4 ≤ p ^ f
  · have hidx : ∀ H : Subgroup S, H ≠ ⊤ → (p ^ f) ^ 4 ≤ H.index := by
      intro H hH
      calc (p ^ f) ^ 4 = 1 * (p ^ f) ^ 4 := (one_mul _).symm
        _ ≤ p * (p ^ f) ^ 4 := Nat.mul_le_mul_right _ (by omega)
        _ ≤ H.index := index_ge_of_chevalley_trialityD4 h H hH
    refine hAS.card_le_bound_of_outerAut_le hidx hout ?_
    rw [hcard]
    have hL : 2 ^ 8 ≤ (p ^ f) ^ 4 := by
      calc 2 ^ 8 = 4 ^ 4 := by decide
        _ ≤ (p ^ f) ^ 4 := Nat.pow_le_pow_left hq4 4
    calc ordTrialityD4 (p ^ f) * (3 * f)
        ≤ (p ^ f) ^ 28 * (6 * (p ^ f)) :=
          Nat.mul_le_mul (ordTrialityD4_le_pow (p ^ f)) (Nat.mul_le_mul (by decide) hfq)
      _ ≤ bound ((p ^ f) ^ 4) := pow_mul_six_le_bound hq2 hL (by decide)
  · have hf1 : f = 1 := by
      by_contra hf_ne
      have hf2 : 2 ≤ f := by omega
      have : 4 ≤ p ^ f := by
        calc 4 = 2 ^ 2 := by decide
          _ ≤ p ^ 2 := Nat.pow_le_pow_left hp2 2
          _ ≤ p ^ f := Nat.pow_le_pow_right hp.pos hf2
      omega
    subst hf1
    rw [pow_one] at hq4
    have hp_cases : p = 2 ∨ p = 3 := by omega
    rcases hp_cases with rfl | rfl
    · refine hAS.card_le_bound_of_outerAut_le (index_ge_64_of_chevalley_trialityD4_two h) hout ?_
      rw [hcard]
      decide
    · refine hAS.card_le_bound_of_outerAut_le (index_ge_of_chevalley_trialityD4 h) hout ?_
      rw [hcard]
      decide

end Maroti
