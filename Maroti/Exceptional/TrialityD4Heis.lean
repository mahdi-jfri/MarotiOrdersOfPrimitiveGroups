module

public import Maroti.MinDegree.PolarizedHeisenberg
public import Maroti.Exceptional.AutBound
public import CFSG.SignalizerFunctorTheorem.NonLocal.D4Relations
public import CFSG.LieType.Chevalley.E6GraphInvertedRootRotation
public import CFSG.LieType.Chevalley.GraphFixedParameterFields
import CFSG.LieType.Chevalley.OddExceptionalOuterTwoRank

/-!
# Polarized Heisenberg Subgroup for `³D₄(q)` in All Characteristics

This file constructs a `PolarizedHeisenbergData` configuration inside
`graphFixedRootGroup TwistTag.D4 K σ` over any field `K` with a period-`3` automorphism `σ`
(`σ ^ 3 = 1` and `∃ u, σ u ≠ u`), where `F = trialityFixedField K σ` is the fixed subfield:
* The isotropic factors are `d4X (b, c) = x₂(b) * x₃(c)` and `d4Y (e, d) = x₄(d) * x₅(e)` for
  `(b, c), (e, d) ∈ F × K`.
* The central factor is `d4Z f = x₆(f)` for `f ∈ F`.
* The commutator law is
  `⁅d4X (b, c), d4Y (e, d)⁆ = d4Z (η₂₅ * b * e + η₃₄ * trialityTrace K σ hσ (c * d))`
  for signs `η₂₅, η₃₄ ∈ {1, -1}`.

When `K` is a finite field of order `(p ^ f) ^ 3` (`q = p ^ f`), `V = F × K` has order `q ^ 4`,
so `PolarizedHeisenbergData.mul_card_le_index_of_ne_top` yields `p * (p ^ f) ^ 4 ≤ H.index` for
every proper subgroup `H` of `³D₄(p ^ f)` (Maróti, Section 2, Step 2, pages 634–635).
-/

@[expose] public section

open scoped commutatorElement

namespace Maroti

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial (finite_field_prime_power_characteristic)
open CFSG.SignalizerFunctorTheorem.NonLocal

/-! ### Action of `twistHom TwistTag.D4` on root subgroups in all characteristics -/

section TwistD4

variable {K : Type} [Field K] (σ : K →+* K)

/-- For any root `α` of `D₄`, `twistHom TwistTag.D4 K σ` maps `pinnedX α c` to
`pinnedX (permLattice perm α) (ε * σ c)` for a sign `ε = ±1`. -/
theorem twistHom_D4_pinnedX {α : Fin TwistTag.D4.tag.rank → ℤ}
    (hα : IsRoot TwistTag.D4.tag α) :
    ∃ ε : K, ε * ε = 1 ∧ ∀ c : K,
      twistHom TwistTag.D4 K σ (pinnedX TwistTag.D4.tag K α c) =
        pinnedX TwistTag.D4.tag K (permLattice TwistTag.D4.perm α) (ε * σ c) := by
  obtain ⟨ε, hε, h⟩ := diagramMap_conj_pinnedX (K := K) TwistTag.D4 hα
  refine ⟨ε, hε, fun c => ?_⟩
  rw [twistHom_apply, show Units.map (entrywiseHom σ) (pinnedX TwistTag.D4.tag K α c) =
    pinnedX TwistTag.D4.tag K α (σ c) from Units.ext (entrywise_pinnedX σ α c), h (σ c)]

/-- For any graph-fixed root `β` of `D₄`, `diagramMap TwistTag.D4 K` centralizes `pinnedX β c` in
all characteristics (since `diagramMap ^ 3 = 1` and `ε ^ 2 = 1` force `ε = 1`). -/
theorem diagramMap_conj_pinnedX_D4_fixed {β : Fin TwistTag.D4.tag.rank → ℤ}
    (hβ : IsRoot TwistTag.D4.tag β) (hfix : permLattice TwistTag.D4.perm β = β) (c : K) :
    diagramMap TwistTag.D4 K * pinnedX TwistTag.D4.tag K β c * (diagramMap TwistTag.D4 K)⁻¹ =
      pinnedX TwistTag.D4.tag K β c := by
  obtain ⟨ε, hε, hP⟩ := diagramMap_conj_pinnedX (K := K) TwistTag.D4 hβ
  rw [hfix] at hP
  have hP3 : diagramMap TwistTag.D4 K ^ 3 = 1 := diagramMap_pow_order TwistTag.D4 K
  have e : ∀ k : ℕ, ∀ d : K, diagramMap TwistTag.D4 K ^ k * pinnedX TwistTag.D4.tag K β d *
      (diagramMap TwistTag.D4 K ^ k)⁻¹ = pinnedX TwistTag.D4.tag K β (ε ^ k * d) := by
    intro k d
    induction k generalizing d with
    | zero => simp
    | succ k ih =>
      have hstep : diagramMap TwistTag.D4 K ^ (k + 1) * pinnedX TwistTag.D4.tag K β d *
          (diagramMap TwistTag.D4 K ^ (k + 1))⁻¹ =
          diagramMap TwistTag.D4 K * (diagramMap TwistTag.D4 K ^ k * pinnedX TwistTag.D4.tag K β d *
            (diagramMap TwistTag.D4 K ^ k)⁻¹) * (diagramMap TwistTag.D4 K)⁻¹ := by
        rw [pow_succ', mul_inv_rev]
        group
      rw [hstep, ih, hP]
      congr 1
      ring
  have h1 := e 3 1
  simp only [hP3, inv_one, one_mul, mul_one] at h1
  have h2 := pinnedX_injective TwistTag.D4.tag K β h1
  have h3 : ε ^ 3 = ε := by linear_combination ε * hε
  have hε1 : ε = 1 := by
    rw [h3] at h2
    exact h2.symm
  rw [hP, hε1, one_mul]

/-- For any graph-fixed root `β` of `D₄`, `twistHom TwistTag.D4 K σ` acts on `pinnedX β c` by
applying `σ` to `c`, in all characteristics. -/
theorem twistHom_D4_pinnedX_fixed {β : Fin TwistTag.D4.tag.rank → ℤ}
    (hβ : IsRoot TwistTag.D4.tag β) (hfix : permLattice TwistTag.D4.perm β = β) (c : K) :
    twistHom TwistTag.D4 K σ (pinnedX TwistTag.D4.tag K β c) =
      pinnedX TwistTag.D4.tag K β (σ c) := by
  rw [twistHom_apply, show Units.map (entrywiseHom σ) (pinnedX TwistTag.D4.tag K β c) =
    pinnedX TwistTag.D4.tag K β (σ c) from Units.ext (entrywise_pinnedX σ β c)]
  exact diagramMap_conj_pinnedX_D4_fixed hβ hfix (σ c)

/-- If `σ ^ 3 = 1`, iterating `twistHom TwistTag.D4 K σ` three times is the identity. -/
theorem twistHom_D4_pow_three (hσ : σ ^ 3 = 1) (g : ModGL TwistTag.D4.tag K) :
    twistHom TwistTag.D4 K σ (twistHom TwistTag.D4 K σ (twistHom TwistTag.D4 K σ g)) = g :=
  twistHom_iterate_order_of_pow_eq_one (t := TwistTag.D4) σ hσ g

/-! ### Fixed-root and short-orbit elements in `graphFixedRootGroup TwistTag.D4` -/

theorem pinnedX_trialityRoot_mem_all {j : Fin 6} (hj : j = 1 ∨ j = 4 ∨ j = 5)
    (c : trialityFixedField K σ) :
    pinnedX TwistTag.D4.tag K (trialityRoot j) c.1 ∈
      graphFixedRootGroup TwistTag.D4 K σ := by
  refine graphFixedPosUnipotent_le_graphFixedRootGroup TwistTag.D4 K σ
    (rootSpan_trialityOrbit_le j ?_)
  refine Subgroup.mem_inf.2 ⟨pinnedX_mem_rootSpan_trialityOrbit j c.1,
    (mem_twistedFixedGroup_iff_twistHom _ _ _).2 ⟨pinnedX_mem_adjointGroup _ _, ?_⟩⟩
  rw [twistHom_D4_pinnedX_fixed σ (isRoot_trialityRoot' j) (trialityRoot_fixed hj),
    mem_trialityFixedField.1 c.2]

/-- Fixed-root element `x_j(c) ∈ graphFixedRootGroup TwistTag.D4 K σ` for `j ∈ {1, 4, 5}` and
`c ∈ trialityFixedField K σ`. -/
noncomputable def fixX {j : Fin 6} (hj : j = 1 ∨ j = 4 ∨ j = 5)
    (c : trialityFixedField K σ) : ↥(graphFixedRootGroup TwistTag.D4 K σ) :=
  ⟨pinnedX TwistTag.D4.tag K (trialityRoot j) c.1, pinnedX_trialityRoot_mem_all σ hj c⟩

theorem fixX_add {j : Fin 6} (hj : j = 1 ∨ j = 4 ∨ j = 5)
    (c d : trialityFixedField K σ) :
    fixX σ hj (c + d) = fixX σ hj c * fixX σ hj d :=
  Subtype.ext (pinnedX_add TwistTag.D4.tag K (trialityRoot j) c.1 d.1)

theorem fixX_eq_one {j : Fin 6} (hj : j = 1 ∨ j = 4 ∨ j = 5)
    (c : trialityFixedField K σ) (h : fixX σ hj c = 1) : c = 0 := by
  have h1 : pinnedX TwistTag.D4.tag K (trialityRoot j) c.1 =
      pinnedX TwistTag.D4.tag K (trialityRoot j) 0 := by
    rw [pinnedX_zero]
    exact congrArg Subtype.val h
  exact Subtype.ext (pinnedX_injective TwistTag.D4.tag K (trialityRoot j) h1)

/-- Characteristic-free size-`3` orbit product `g * T g * T (T g)` for `g = pinnedX α c` and
`T = twistHom TwistTag.D4 K σ`. -/
noncomputable def orb3Val (α : Fin TwistTag.D4.tag.rank → ℤ) (c : K) :
    ModGL TwistTag.D4.tag K :=
  pinnedX TwistTag.D4.tag K α c *
    twistHom TwistTag.D4 K σ (pinnedX TwistTag.D4.tag K α c) *
      twistHom TwistTag.D4 K σ (twistHom TwistTag.D4 K σ (pinnedX TwistTag.D4.tag K α c))

theorem twistHom_pinnedX_mem_rootSubgroup (j : Fin 6) (c : K) :
    twistHom TwistTag.D4 K σ (pinnedX TwistTag.D4.tag K (trialityRoot j) c) ∈
      rootSubgroup TwistTag.D4.tag K (permLattice TwistTag.D4.perm (trialityRoot j)) := by
  obtain ⟨ε, -, hF⟩ := twistHom_D4_pinnedX σ (isRoot_trialityRoot' j)
  rw [hF c]
  exact mem_rootSubgroup.2 ⟨_, rfl⟩

theorem twistHom_twistHom_pinnedX_mem_rootSubgroup (j : Fin 6) (c : K) :
    twistHom TwistTag.D4 K σ
        (twistHom TwistTag.D4 K σ (pinnedX TwistTag.D4.tag K (trialityRoot j) c)) ∈
      rootSubgroup TwistTag.D4.tag K (permLattice (TwistTag.D4.perm ^ 2) (trialityRoot j)) := by
  obtain ⟨ε₀, -, hF₀⟩ := twistHom_D4_pinnedX σ (isRoot_trialityRoot' j)
  obtain ⟨ε₁, -, hF₁⟩ := twistHom_D4_pinnedX σ (isRoot_trialityRoot j 1).1
  rw [pow_one] at hF₁
  rw [hF₀ c, hF₁, permLattice_D4_perm_perm]
  exact mem_rootSubgroup.2 ⟨_, rfl⟩

theorem rootSubgroup_perm_le_rootSpan_trialityOrbit (j : Fin 6) (h : Fin 3) :
    rootSubgroup TwistTag.D4.tag K (permLattice (TwistTag.D4.perm ^ (h : ℕ)) (trialityRoot j)) ≤
      rootSpan TwistTag.D4.tag K (trialityOrbit j : Set (Fin TwistTag.D4.tag.rank → ℤ)) := by
  rw [← rootSpan_singleton_eq_rootSubgroup]
  refine rootSpan_mono ?_
  rw [Set.singleton_subset_iff, trialityOrbit, coe_diagramOrbit_D4]
  exact ⟨h, rfl⟩

theorem twistHom_pinnedX_mem_rootSpan_trialityOrbit (j : Fin 6) (c : K) :
    twistHom TwistTag.D4 K σ (pinnedX TwistTag.D4.tag K (trialityRoot j) c) ∈
      rootSpan TwistTag.D4.tag K (trialityOrbit j : Set (Fin TwistTag.D4.tag.rank → ℤ)) := by
  have h1 := rootSubgroup_perm_le_rootSpan_trialityOrbit (K := K) j 1
  rw [Fin.val_one, pow_one] at h1
  exact h1 (twistHom_pinnedX_mem_rootSubgroup σ j c)

theorem twistHom_twistHom_pinnedX_mem_rootSpan_trialityOrbit (j : Fin 6) (c : K) :
    twistHom TwistTag.D4 K σ
        (twistHom TwistTag.D4 K σ (pinnedX TwistTag.D4.tag K (trialityRoot j) c)) ∈
      rootSpan TwistTag.D4.tag K (trialityOrbit j : Set (Fin TwistTag.D4.tag.rank → ℤ)) := by
  have h2 := rootSubgroup_perm_le_rootSpan_trialityOrbit (K := K) j 2
  exact h2 (twistHom_twistHom_pinnedX_mem_rootSubgroup σ j c)

theorem orb3Val_mem_rootSpan (j : Fin 6) (c : K) :
    orb3Val σ (trialityRoot j) c ∈
      rootSpan TwistTag.D4.tag K (trialityOrbit j : Set (Fin TwistTag.D4.tag.rank → ℤ)) :=
  mul_mem (mul_mem (pinnedX_mem_rootSpan_trialityOrbit j c)
    (twistHom_pinnedX_mem_rootSpan_trialityOrbit σ j c))
    (twistHom_twistHom_pinnedX_mem_rootSpan_trialityOrbit σ j c)

theorem commute_rootSpan_trialityOrbit_self {j : Fin 6} (hj : j = 0 ∨ j = 2 ∨ j = 3)
    {x y : ModGL TwistTag.D4.tag K}
    (hx : x ∈ rootSpan TwistTag.D4.tag K (trialityOrbit j : Set (Fin TwistTag.D4.tag.rank → ℤ)))
    (hy : y ∈ rootSpan TwistTag.D4.tag K (trialityOrbit j : Set (Fin TwistTag.D4.tag.rank → ℤ))) :
    Commute x y := by
  refine commute_of_mem_rootSpan (fun α hα β hβ s t => ?_) hx hy
  rw [trialityOrbit, coe_diagramOrbit_D4] at hα hβ
  obtain ⟨h, rfl⟩ := hα
  obtain ⟨h', rfl⟩ := hβ
  exact trialityTriple_commute (isRoot_trialityRoot j) (trialityRoot_triple_orthogonal j hj)
    h h' s t

private theorem hom_orb3_add {G : Type*} [Group G] (T : G →* G) (g c d : G)
    (hc01 : Commute d (T c)) (hc02 : Commute d (T (T c))) (hc12 : Commute (T d) (T (T c)))
    (hg : g = c * d) :
    g * T g * T (T g) = (c * T c * T (T c)) * (d * T d * T (T d)) := by
  rw [hg]
  simp only [map_mul, mul_assoc]
  rw [hc01.left_comm, hc12.left_comm, hc02.left_comm]

theorem orb3Val_add {j : Fin 6} (hj : j = 0 ∨ j = 2 ∨ j = 3) (c d : K) :
    orb3Val σ (trialityRoot j) (c + d) =
      orb3Val σ (trialityRoot j) c * orb3Val σ (trialityRoot j) d := by
  unfold orb3Val
  exact hom_orb3_add (twistHom TwistTag.D4 K σ)
    (pinnedX TwistTag.D4.tag K (trialityRoot j) (c + d))
    (pinnedX TwistTag.D4.tag K (trialityRoot j) c)
    (pinnedX TwistTag.D4.tag K (trialityRoot j) d)
    (commute_rootSpan_trialityOrbit_self hj (pinnedX_mem_rootSpan_trialityOrbit j d)
      (twistHom_pinnedX_mem_rootSpan_trialityOrbit σ j c))
    (commute_rootSpan_trialityOrbit_self hj (pinnedX_mem_rootSpan_trialityOrbit j d)
      (twistHom_twistHom_pinnedX_mem_rootSpan_trialityOrbit σ j c))
    (commute_rootSpan_trialityOrbit_self hj (twistHom_pinnedX_mem_rootSpan_trialityOrbit σ j d)
      (twistHom_twistHom_pinnedX_mem_rootSpan_trialityOrbit σ j c))
    (pinnedX_add TwistTag.D4.tag K (trialityRoot j) c d)

theorem twistHom_orb3Val {j : Fin 6} (hj : j = 0 ∨ j = 2 ∨ j = 3) (hσ : σ ^ 3 = 1) (c : K) :
    twistHom TwistTag.D4 K σ (orb3Val σ (trialityRoot j) c) = orb3Val σ (trialityRoot j) c := by
  unfold orb3Val
  rw [map_mul, map_mul, twistHom_D4_pow_three σ hσ]
  have hc : Commute
      (twistHom TwistTag.D4 K σ (pinnedX TwistTag.D4.tag K (trialityRoot j) c) *
        twistHom TwistTag.D4 K σ
          (twistHom TwistTag.D4 K σ (pinnedX TwistTag.D4.tag K (trialityRoot j) c)))
      (pinnedX TwistTag.D4.tag K (trialityRoot j) c) :=
    commute_rootSpan_trialityOrbit_self hj
      (mul_mem (twistHom_pinnedX_mem_rootSpan_trialityOrbit σ j c)
        (twistHom_twistHom_pinnedX_mem_rootSpan_trialityOrbit σ j c))
      (pinnedX_mem_rootSpan_trialityOrbit j c)
  rw [hc.eq, ← mul_assoc]

theorem orb3Val_mem {j : Fin 6} (hj : j = 0 ∨ j = 2 ∨ j = 3) (hσ : σ ^ 3 = 1) (c : K) :
    orb3Val σ (trialityRoot j) c ∈ graphFixedRootGroup TwistTag.D4 K σ := by
  refine graphFixedPosUnipotent_le_graphFixedRootGroup TwistTag.D4 K σ
    (rootSpan_trialityOrbit_le j ?_)
  refine Subgroup.mem_inf.2 ⟨orb3Val_mem_rootSpan σ j c,
    (mem_twistedFixedGroup_iff_twistHom _ _ _).2 ⟨?_, twistHom_orb3Val σ hj hσ c⟩⟩
  obtain ⟨_, h1⟩ := mem_rootSubgroup.1 (twistHom_pinnedX_mem_rootSubgroup σ j c)
  obtain ⟨_, h2⟩ := mem_rootSubgroup.1 (twistHom_twistHom_pinnedX_mem_rootSubgroup σ j c)
  unfold orb3Val
  rw [← h2, ← h1]
  exact mul_mem (mul_mem (pinnedX_mem_adjointGroup _ _) (pinnedX_mem_adjointGroup _ _))
    (pinnedX_mem_adjointGroup _ _)

/-- Short-orbit element `x_j(c) ∈ graphFixedRootGroup TwistTag.D4 K σ` for `j ∈ {0, 2, 3}` and
`c ∈ K`. -/
noncomputable def orb3 {j : Fin 6} (hj : j = 0 ∨ j = 2 ∨ j = 3) (hσ : σ ^ 3 = 1) (c : K) :
    ↥(graphFixedRootGroup TwistTag.D4 K σ) :=
  ⟨orb3Val σ (trialityRoot j) c, orb3Val_mem σ hj hσ c⟩

theorem orb3_add {j : Fin 6} (hj : j = 0 ∨ j = 2 ∨ j = 3) (hσ : σ ^ 3 = 1) (c d : K) :
    orb3 σ hj hσ (c + d) = orb3 σ hj hσ c * orb3 σ hj hσ d :=
  Subtype.ext (orb3Val_add σ hj c d)

/-- In characteristic `2`, `orb3Val` coincides with `trialityOrbitProd`. -/
theorem orb3Val_eq_trialityOrbitProd [CharP K 2] (j : Fin 6) (c : K) :
    orb3Val σ (trialityRoot j) c =
      (trialityOrbitProd K σ (trialityRoot j) c : ModGL TwistTag.D4.tag K) := by
  have h0 : IsRoot TwistTag.D4.tag (trialityRoot j) := isRoot_trialityRoot' j
  have h1 : IsRoot TwistTag.D4.tag (permLattice TwistTag.D4.perm (trialityRoot j)) := by
    simpa [pow_one] using (isRoot_trialityRoot j 1).1
  unfold orb3Val
  rw [even_diagram_root_parameters TwistTag.D4 σ h0,
    even_diagram_root_parameters TwistTag.D4 σ h1,
    permLattice_D4_perm_perm, coe_trialityOrbitProd]

/-! ### Commutator relations in all characteristics -/

theorem exists_commutator_fixX_1_4 :
    ∃ η₂₅ : trialityFixedField K σ, (η₂₅ = 1 ∨ η₂₅ = -1) ∧
      ∀ b e : trialityFixedField K σ,
        ⁅fixX σ (j := 1) (by decide) b, fixX σ (j := 4) (by decide) e⁆ =
          fixX σ (j := 5) (by decide) (η₂₅ * b * e) := by
  have h := triality_sum_25
  simp only [d4SumB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hα, hβ⟩, hne⟩, hne'⟩, hsum⟩, hγ⟩ := h
  obtain ⟨hε, hf⟩ := (simply_laced_root_commutator_unit TwistTag.D4.tag (Or.inl rfl)
    (d4IsRootB_iff.1 hα) (d4IsRootB_iff.1 hβ) hne hne').1 (by rw [hsum]; exact d4IsRootB_iff.1 hγ)
  refine ⟨(commConst TwistTag.D4.tag (trialityRoot 1) (trialityRoot 4) (1, 1) :
      trialityFixedField K σ), ?_, fun b e => Subtype.ext ?_⟩
  · rcases hε with h1 | h1 <;> [left; right] <;> rw [h1] <;> simp
  · change ⁅pinnedX TwistTag.D4.tag K (trialityRoot 1) b.1,
        pinnedX TwistTag.D4.tag K (trialityRoot 4) e.1⁆ =
      pinnedX TwistTag.D4.tag K (trialityRoot 5) _
    rw [hf K b.1 e.1, hsum]
    congr 1

private theorem commutator_triple_of_hom {G : Type*} [Group G] {Z : Subgroup G}
    (hZ : ∀ x ∈ Z, ∀ y ∈ Z, Commute x y) (g₀ g₁ g₂ w₀ w₁ w₂ z₀ z₁ z₂ : G)
    (hz0 : z₀ ∈ Z) (hz1 : z₁ ∈ Z) (hz2 : z₂ ∈ Z)
    (hgZ : ∀ c ∈ Z, Commute g₀ c ∧ Commute g₁ c ∧ Commute g₂ c)
    (hwZ : ∀ c ∈ Z, Commute w₀ c ∧ Commute w₁ c ∧ Commute w₂ c)
    (hc0 : ⁅g₀, w₀⁆ = z₀) (hc1 : ⁅g₁, w₁⁆ = z₁) (hc2 : ⁅g₂, w₂⁆ = z₂)
    (hc01 : Commute g₀ w₁) (hc02 : Commute g₀ w₂) (hc10 : Commute g₁ w₀)
    (hc12 : Commute g₁ w₂) (hc20 : Commute g₂ w₀) (hc21 : Commute g₂ w₁) :
    ⁅g₀ * g₁ * g₂, w₀ * w₁ * w₂⁆ = z₀ * z₁ * z₂ := by
  set zs := [g₀, g₁, g₂]
  set ws := [w₀, w₁, w₂]
  have ez : g₀ * g₁ * g₂ = zs.prod := by
    simp only [zs, List.prod_cons, List.prod_nil, mul_one, mul_assoc]
  have ew : w₀ * w₁ * w₂ = ws.prod := by
    simp only [ws, List.prod_cons, List.prod_nil, mul_one, mul_assoc]
  have h1 : ∀ {x y : G}, Commute x y → ⁅x, y⁆ = 1 := fun h =>
    commutatorElement_eq_one_iff_mul_comm.2 h
  have key := commutator_list_prod_of_central hZ zs ws
    (by
      intro z hz c hc
      simp only [zs, List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl | rfl
      · exact (hgZ c hc).1
      · exact (hgZ c hc).2.1
      · exact (hgZ c hc).2.2)
    (by
      intro w hw c hc
      simp only [ws, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl
      · exact (hwZ c hc).1
      · exact (hwZ c hc).2.1
      · exact (hwZ c hc).2.2)
    (by
      intro z hz w hw
      simp only [zs, ws, List.mem_cons, List.not_mem_nil, or_false] at hz hw
      rcases hz with rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl
      · rw [hc0]; exact hz0
      · rw [h1 hc01]; exact Subgroup.one_mem _
      · rw [h1 hc02]; exact Subgroup.one_mem _
      · rw [h1 hc10]; exact Subgroup.one_mem _
      · rw [hc1]; exact hz1
      · rw [h1 hc12]; exact Subgroup.one_mem _
      · rw [h1 hc20]; exact Subgroup.one_mem _
      · rw [h1 hc21]; exact Subgroup.one_mem _
      · rw [hc2]; exact hz2)
  rw [ez, ew, key.2]
  simp only [zs, ws, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    hc0, hc1, hc2, h1 hc01, h1 hc02, h1 hc10, h1 hc12, h1 hc20, h1 hc21, one_mul, mul_assoc]

theorem exists_commutator_orb3_2_3 (hσ : σ ^ 3 = 1) :
    ∃ η₃₄ : trialityFixedField K σ, (η₃₄ = 1 ∨ η₃₄ = -1) ∧
      ∀ c d : K,
        ⁅orb3 σ (j := 2) (by decide) hσ c, orb3 σ (j := 3) (by decide) hσ d⁆ =
          fixX σ (j := 5) (by decide) (η₃₄ * trialityTrace K σ hσ (c * d)) := by
  have hp := trialityPairCheck_34
  simp only [trialityPairCheck, Bool.and_eq_true] at hp
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hs0, _⟩, _⟩, hc01⟩, hc02⟩, hc10⟩, hc12⟩, hc20⟩, hc21⟩, hz0⟩, hz1⟩,
    hz2⟩, hw0⟩, hw1⟩, hw2⟩ := hp
  have hs0' := hs0
  simp only [d4SumB, Bool.and_eq_true, decide_eq_true_eq] at hs0'
  obtain ⟨⟨⟨⟨⟨hα, hβ⟩, hne⟩, hne'⟩, hsum⟩, hγ⟩ := hs0'
  obtain ⟨hε, hf⟩ := (simply_laced_root_commutator_unit TwistTag.D4.tag (Or.inl rfl)
    (d4IsRootB_iff.1 hα) (d4IsRootB_iff.1 hβ) hne hne').1 (by rw [hsum]; exact d4IsRootB_iff.1 hγ)
  set m : ℤ := commConst TwistTag.D4.tag (trialityRoot 2) (trialityRoot 3) (1, 1)
  refine ⟨(m : trialityFixedField K σ), ?_, fun c d => Subtype.ext ?_⟩
  · rcases hε with h1 | h1 <;> [left; right] <;> rw [h1] <;> simp
  · have hg0 : pinnedX TwistTag.D4.tag K (trialityRoot 2) c ∈
        rootSubgroup TwistTag.D4.tag K (trialityRoot 2) := mem_rootSubgroup.2 ⟨c, rfl⟩
    have hg1 := twistHom_pinnedX_mem_rootSubgroup σ 2 c
    have hg2 := twistHom_twistHom_pinnedX_mem_rootSubgroup σ 2 c
    have hw0_mem : pinnedX TwistTag.D4.tag K (trialityRoot 3) d ∈
        rootSubgroup TwistTag.D4.tag K (trialityRoot 3) := mem_rootSubgroup.2 ⟨d, rfl⟩
    have hw1_mem := twistHom_pinnedX_mem_rootSubgroup σ 3 d
    have hw2_mem := twistHom_twistHom_pinnedX_mem_rootSubgroup σ 3 d
    have hcomm_sub : ∀ {δ₁ δ₂ : Fin TwistTag.D4.tag.rank → ℤ}, d4CommB δ₁ δ₂ = true →
        ∀ {x y : ModGL TwistTag.D4.tag K},
          x ∈ rootSubgroup TwistTag.D4.tag K δ₁ →
          y ∈ rootSubgroup TwistTag.D4.tag K δ₂ → Commute x y := by
      intro δ₁ δ₂ hδ x y hx hy
      obtain ⟨s, rfl⟩ := mem_rootSubgroup.1 hx
      obtain ⟨t, rfl⟩ := mem_rootSubgroup.1 hy
      exact commute_of_d4CommB_nc hδ s t
    have hc0 : ⁅pinnedX TwistTag.D4.tag K (trialityRoot 2) c,
          pinnedX TwistTag.D4.tag K (trialityRoot 3) d⁆ =
        pinnedX TwistTag.D4.tag K (trialityRoot 5) ((m : K) * c * d) := by
      have := hf K c d
      rwa [hsum] at this
    have hT5 : ∀ x : K,
        twistHom TwistTag.D4 K σ (pinnedX TwistTag.D4.tag K (trialityRoot 5) x) =
          pinnedX TwistTag.D4.tag K (trialityRoot 5) (σ x) :=
      twistHom_D4_pinnedX_fixed σ (isRoot_trialityRoot' 5) (trialityRoot_fixed (by decide))
    have hc1 : ⁅twistHom TwistTag.D4 K σ (pinnedX TwistTag.D4.tag K (trialityRoot 2) c),
          twistHom TwistTag.D4 K σ (pinnedX TwistTag.D4.tag K (trialityRoot 3) d)⁆ =
        pinnedX TwistTag.D4.tag K (trialityRoot 5) ((m : K) * σ (c * d)) := by
      rw [← map_commutatorElement, hc0, hT5, mul_assoc, map_mul, map_intCast]
    have hc2 : ⁅twistHom TwistTag.D4 K σ
          (twistHom TwistTag.D4 K σ (pinnedX TwistTag.D4.tag K (trialityRoot 2) c)),
          twistHom TwistTag.D4 K σ
            (twistHom TwistTag.D4 K σ (pinnedX TwistTag.D4.tag K (trialityRoot 3) d))⁆ =
        pinnedX TwistTag.D4.tag K (trialityRoot 5) ((m : K) * σ (σ (c * d))) := by
      rw [← map_commutatorElement, hc1, hT5, map_mul, map_intCast]
    change ⁅orb3Val σ (trialityRoot 2) c, orb3Val σ (trialityRoot 3) d⁆ =
      pinnedX TwistTag.D4.tag K (trialityRoot 5) _
    unfold orb3Val
    rw [commutator_triple_of_hom (commute_rootSubgroup (trialityRoot 5))
      _ _ _ _ _ _ _ _ _
      (mem_rootSubgroup.2 ⟨_, rfl⟩) (mem_rootSubgroup.2 ⟨_, rfl⟩) (mem_rootSubgroup.2 ⟨_, rfl⟩)
      (fun x hx => ⟨hcomm_sub hz0 hg0 hx, hcomm_sub hz1 hg1 hx, hcomm_sub hz2 hg2 hx⟩)
      (fun x hx => ⟨hcomm_sub hw0 hw0_mem hx, hcomm_sub hw1 hw1_mem hx, hcomm_sub hw2 hw2_mem hx⟩)
      hc0 hc1 hc2
      (hcomm_sub hc01 hg0 hw1_mem) (hcomm_sub hc02 hg0 hw2_mem) (hcomm_sub hc10 hg1 hw0_mem)
      (hcomm_sub hc12 hg1 hw2_mem) (hcomm_sub hc20 hg2 hw0_mem) (hcomm_sub hc21 hg2 hw1_mem)]
    rw [← pinnedX_add, ← pinnedX_add]
    congr 1
    simp only [Subfield.coe_mul, coe_trialityTrace]
    change (m : K) * c * d + (m : K) * σ (c * d) + (m : K) * σ (σ (c * d)) =
      (m : K) * (c * d + σ (c * d) + σ (σ (c * d)))
    ring

/-! ### Linearity and surjectivity of `trialityTrace` in all characteristics -/

theorem trialityTrace_add (hσ : σ ^ 3 = 1) (x y : K) :
    trialityTrace K σ hσ (x + y) = trialityTrace K σ hσ x + trialityTrace K σ hσ y :=
  Subtype.ext (by simp only [coe_trialityTrace, map_add, Subfield.coe_add]; ring)

theorem trialityTrace_smul (hσ : σ ^ 3 = 1) (c : trialityFixedField K σ) (x : K) :
    trialityTrace K σ hσ ((c : K) * x) = c * trialityTrace K σ hσ x :=
  Subtype.ext (by
    simp only [coe_trialityTrace, map_mul, mem_trialityFixedField.1 c.2, Subfield.coe_mul]
    ring)

/-- If `σ ^ 3 = 1` and `σ` is not the identity on `K`, there exists `c₀ ∈ K` with
`trialityTrace K σ hσ c₀ ≠ 0`. -/
theorem exists_trialityTrace_ne_zero (hσ : σ ^ 3 = 1) (hne : ∃ u : K, σ u ≠ u) :
    ∃ c₀ : K, trialityTrace K σ hσ c₀ ≠ 0 := by
  obtain ⟨u, hu_ne⟩ := hne
  by_contra! h0
  have hval : ∀ c : K, c + σ c + σ (σ c) = 0 := fun c => by
    have := congrArg Subtype.val (h0 c)
    simpa [coe_trialityTrace] using this
  have h1 := hval 1
  have hu := hval u
  have hw := hval (σ (σ u))
  have hwu := hval (σ (σ u) * u)
  simp only [map_one, map_mul, ringHom_apply_apply_apply_of_pow_three hσ] at h1 hu hw hwu
  have hsq : (u - σ u) * (u - σ u) = 0 := by
    linear_combination -hwu + σ u * hu + u * hw - u * σ u * h1
  exact hu_ne (sub_eq_zero.1 (mul_self_eq_zero.1 hsq)).symm

/-- For any nonzero `c ∈ K` and any `s ∈ trialityFixedField K σ`, there exists `d ∈ K` such that
`trialityTrace K σ hσ (c * d) = s`. -/
theorem exists_trialityTrace_mul_eq_left (hσ : σ ^ 3 = 1) (hne : ∃ u : K, σ u ≠ u)
    {c : K} (hc : c ≠ 0) (s : trialityFixedField K σ) :
    ∃ d : K, trialityTrace K σ hσ (c * d) = s := by
  obtain ⟨c₀, hc₀⟩ := exists_trialityTrace_ne_zero σ hσ hne
  let a : trialityFixedField K σ := s / trialityTrace K σ hσ c₀
  refine ⟨c⁻¹ * (a.1 * c₀), ?_⟩
  rw [mul_inv_cancel_left₀ hc, trialityTrace_smul, div_mul_cancel₀ _ hc₀]

/-- For any nonzero `d ∈ K` and any `s ∈ trialityFixedField K σ`, there exists `c ∈ K` such that
`trialityTrace K σ hσ (c * d) = s`. -/
theorem exists_trialityTrace_mul_eq_right (hσ : σ ^ 3 = 1) (hne : ∃ u : K, σ u ≠ u)
    {d : K} (hd : d ≠ 0) (s : trialityFixedField K σ) :
    ∃ c : K, trialityTrace K σ hσ (c * d) = s := by
  obtain ⟨c, hc⟩ := exists_trialityTrace_mul_eq_left σ hσ hne hd s
  exact ⟨c, by rw [mul_comm, hc]⟩

/-! ### Polarized Heisenberg data for `graphFixedRootGroup TwistTag.D4` -/

/-- First isotropic factor `d4X (b, c) = x₂(b) * x₃(c)` in `graphFixedRootGroup TwistTag.D4 K σ`. -/
noncomputable def d4X (hσ : σ ^ 3 = 1) (u : trialityFixedField K σ × K) :
    ↥(graphFixedRootGroup TwistTag.D4 K σ) :=
  fixX σ (j := 1) (by decide) u.1 * orb3 σ (j := 2) (by decide) hσ u.2

/-- Second isotropic factor `d4Y (e, d) = x₄(d) * x₅(e)` in
`graphFixedRootGroup TwistTag.D4 K σ`. -/
noncomputable def d4Y (hσ : σ ^ 3 = 1) (v : trialityFixedField K σ × K) :
    ↥(graphFixedRootGroup TwistTag.D4 K σ) :=
  orb3 σ (j := 3) (by decide) hσ v.2 * fixX σ (j := 4) (by decide) v.1

/-- Central factor `d4Z f = x₆(f)` in `graphFixedRootGroup TwistTag.D4 K σ`. -/
noncomputable def d4Z (s : trialityFixedField K σ) :
    ↥(graphFixedRootGroup TwistTag.D4 K σ) :=
  fixX σ (j := 5) (by decide) s

/-- Symplectic pairing `B (b, c) (e, d) = η₂₅ * b * e + η₃₄ * trialityTrace K σ hσ (c * d)`. -/
noncomputable def d4B (hσ : σ ^ 3 = 1) (η₂₅ η₃₄ : trialityFixedField K σ)
    (u v : trialityFixedField K σ × K) : trialityFixedField K σ :=
  η₂₅ * u.1 * v.1 + η₃₄ * trialityTrace K σ hσ (u.2 * v.2)

theorem commute_fixX_orb3 {i j : Fin 6} (hp : (i, j) ∈ trialityCommPairs)
    (hi : i = 1 ∨ i = 4 ∨ i = 5) (hj : j = 0 ∨ j = 2 ∨ j = 3) (hσ : σ ^ 3 = 1)
    (b : trialityFixedField K σ) (c : K) :
    Commute (fixX σ hi b) (orb3 σ hj hσ c) :=
  Subtype.ext (commute_trialityOrbit_nc hp
    (pinnedX_mem_rootSpan_trialityOrbit i b.1) (orb3Val_mem_rootSpan σ j c))

theorem commute_orb3_fixX {i j : Fin 6} (hp : (i, j) ∈ trialityCommPairs)
    (hi : i = 0 ∨ i = 2 ∨ i = 3) (hj : j = 1 ∨ j = 4 ∨ j = 5) (hσ : σ ^ 3 = 1)
    (c : K) (b : trialityFixedField K σ) :
    Commute (orb3 σ hi hσ c) (fixX σ hj b) :=
  Subtype.ext (commute_trialityOrbit_nc hp
    (orb3Val_mem_rootSpan σ i c) (pinnedX_mem_rootSpan_trialityOrbit j b.1))

theorem commute_fixX_fixX {i j : Fin 6} (hp : (i, j) ∈ trialityCommPairs)
    (hi : i = 1 ∨ i = 4 ∨ i = 5) (hj : j = 1 ∨ j = 4 ∨ j = 5)
    (b e : trialityFixedField K σ) :
    Commute (fixX σ hi b) (fixX σ hj e) :=
  Subtype.ext (commute_trialityOrbit_nc hp
    (pinnedX_mem_rootSpan_trialityOrbit i b.1) (pinnedX_mem_rootSpan_trialityOrbit j e.1))

theorem d4X_add (hσ : σ ^ 3 = 1) (u₁ u₂ : trialityFixedField K σ × K) :
    d4X σ hσ (u₁ + u₂) = d4X σ hσ u₁ * d4X σ hσ u₂ := by
  unfold d4X
  rw [Prod.fst_add, Prod.snd_add, fixX_add, orb3_add]
  have hc : Commute (fixX σ (j := 1) (by decide) u₂.1) (orb3 σ (j := 2) (by decide) hσ u₁.2) :=
    commute_fixX_orb3 σ (i := 1) (j := 2) (by decide) (by decide) (by decide) hσ u₂.1 u₁.2
  simp only [mul_assoc]
  rw [hc.symm.left_comm]

theorem d4Y_add (hσ : σ ^ 3 = 1) (v₁ v₂ : trialityFixedField K σ × K) :
    d4Y σ hσ (v₁ + v₂) = d4Y σ hσ v₁ * d4Y σ hσ v₂ := by
  unfold d4Y
  rw [Prod.fst_add, Prod.snd_add, orb3_add, fixX_add]
  have hc : Commute (orb3 σ (j := 3) (by decide) hσ v₂.2) (fixX σ (j := 4) (by decide) v₁.1) :=
    commute_orb3_fixX σ (i := 3) (j := 4) (by decide) (by decide) (by decide) hσ v₂.2 v₁.1
  simp only [mul_assoc]
  rw [hc.symm.left_comm]

theorem commute_d4X_d4Z (hσ : σ ^ 3 = 1) (u : trialityFixedField K σ × K)
    (s : trialityFixedField K σ) :
    Commute (d4X σ hσ u) (d4Z σ s) :=
  (commute_fixX_fixX σ (i := 1) (j := 5) (by decide) (by decide) (by decide) u.1 s).mul_left
    (commute_orb3_fixX σ (i := 2) (j := 5) (by decide) (by decide) (by decide) hσ u.2 s)

theorem commute_d4Y_d4Z (hσ : σ ^ 3 = 1) (v : trialityFixedField K σ × K)
    (s : trialityFixedField K σ) :
    Commute (d4Y σ hσ v) (d4Z σ s) :=
  (commute_orb3_fixX σ (i := 3) (j := 5) (by decide) (by decide) (by decide) hσ v.2 s).mul_left
    (commute_fixX_fixX σ (i := 4) (j := 5) (by decide) (by decide) (by decide) v.1 s)

/-- Given commutator relations for `(fixX 1, fixX 4)` and `(orb3 2, orb3 3)` with unit signs
`η₂₅, η₃₄`, `(d4X, d4Y, d4Z, d4B)` forms a `PolarizedHeisenbergData`. -/
theorem polarizedHeisenbergData_d4 (hσ : σ ^ 3 = 1) (hne : ∃ u : K, σ u ≠ u)
    {η₂₅ η₃₄ : trialityFixedField K σ} (hη₂₅ : η₂₅ ≠ 0) (hη₃₄ : η₃₄ ≠ 0)
    (hc14 : ∀ b e : trialityFixedField K σ,
      ⁅fixX σ (j := 1) (by decide) b, fixX σ (j := 4) (by decide) e⁆ =
        fixX σ (j := 5) (by decide) (η₂₅ * b * e))
    (hc23 : ∀ c d : K,
      ⁅orb3 σ (j := 2) (by decide) hσ c, orb3 σ (j := 3) (by decide) hσ d⁆ =
        fixX σ (j := 5) (by decide) (η₃₄ * trialityTrace K σ hσ (c * d))) :
    PolarizedHeisenbergData (d4X σ hσ) (d4Y σ hσ) (d4Z σ) (d4B σ hσ η₂₅ η₃₄) where
  X_add := d4X_add σ hσ
  Y_add := d4Y_add σ hσ
  z_add s₁ s₂ := fixX_add σ (by decide) s₁ s₂
  z_eq_one s hs := fixX_eq_one σ (by decide) s hs
  commute_X_z := commute_d4X_d4Z σ hσ
  commute_Y_z := commute_d4Y_d4Z σ hσ
  comm_X_Y u v := by
    let a₁ := fixX σ (j := 1) (by decide) u.1
    let a₂ := orb3 σ (j := 2) (by decide) hσ u.2
    let b₁ := orb3 σ (j := 3) (by decide) hσ v.2
    let b₂ := fixX σ (j := 4) (by decide) v.1
    have hca1b1 : Commute a₁ b₁ :=
      commute_fixX_orb3 σ (i := 1) (j := 3) (by decide) (by decide) (by decide) hσ u.1 v.2
    have hca2b2 : Commute a₂ b₂ :=
      commute_orb3_fixX σ (i := 2) (j := 4) (by decide) (by decide) (by decide) hσ u.2 v.1
    let z₁ := d4Z σ (η₂₅ * u.1 * v.1)
    let z₂ := d4Z σ (η₃₄ * trialityTrace K σ hσ (u.2 * v.2))
    have hz1 : a₁ * b₂ = z₁ * b₂ * a₁ := by
      have h := hc14 u.1 v.1
      change ⁅a₁, b₂⁆ = z₁ at h
      rw [commutatorElement_def] at h
      calc a₁ * b₂ = (a₁ * b₂ * a₁⁻¹ * b₂⁻¹) * b₂ * a₁ := by group
        _ = z₁ * b₂ * a₁ := by rw [h]
    have hz2 : a₂ * b₁ = z₂ * b₁ * a₂ := by
      have h := hc23 u.2 v.2
      change ⁅a₂, b₁⁆ = z₂ at h
      rw [commutatorElement_def] at h
      calc a₂ * b₁ = (a₂ * b₁ * a₂⁻¹ * b₁⁻¹) * b₁ * a₂ := by group
        _ = z₂ * b₁ * a₂ := by rw [h]
    have hcz1_b1 : Commute z₁ b₁ :=
      (commute_orb3_fixX σ (i := 3) (j := 5) (by decide) (by decide) (by decide) hσ v.2 _).symm
    have hcz2_a1 : Commute z₂ a₁ :=
      (commute_fixX_fixX σ (i := 1) (j := 5) (by decide) (by decide) (by decide) u.1 _).symm
    have hcz1z2 : z₂ * z₁ = z₁ * z₂ := by
      change d4Z σ _ * d4Z σ _ = d4Z σ _ * d4Z σ _
      unfold d4Z
      rw [← fixX_add, ← fixX_add, add_comm]
    have hmul : (a₁ * a₂) * (b₁ * b₂) = (z₁ * z₂) * (b₁ * b₂) * (a₁ * a₂) := by
      calc (a₁ * a₂) * (b₁ * b₂)
          = a₁ * (a₂ * b₁) * b₂ := by group
        _ = a₁ * (z₂ * b₁ * a₂) * b₂ := by rw [hz2]
        _ = (a₁ * z₂) * b₁ * (a₂ * b₂) := by group
        _ = z₂ * (a₁ * b₁) * (b₂ * a₂) := by rw [hcz2_a1.symm.eq, hca2b2.eq]; group
        _ = z₂ * b₁ * (a₁ * b₂) * a₂ := by rw [hca1b1.eq]; group
        _ = z₂ * b₁ * (z₁ * b₂ * a₁) * a₂ := by rw [hz1]
        _ = z₂ * (b₁ * z₁) * b₂ * (a₁ * a₂) := by group
        _ = (z₂ * z₁) * b₁ * b₂ * (a₁ * a₂) := by rw [hcz1_b1.symm.eq]; group
        _ = (z₁ * z₂) * (b₁ * b₂) * (a₁ * a₂) := by rw [hcz1z2]; group
    change ⁅a₁ * a₂, b₁ * b₂⁆ = d4Z σ (d4B σ hσ η₂₅ η₃₄ u v)
    rw [commutatorElement_def, hmul]
    have hcancel : (z₁ * z₂) * (b₁ * b₂) * (a₁ * a₂) * (a₁ * a₂)⁻¹ * (b₁ * b₂)⁻¹ = z₁ * z₂ := by
      group
    rw [hcancel]
    exact (fixX_add σ (by decide) _ _).symm
  B_add_left u₁ u₂ v := by
    unfold d4B
    rw [Prod.fst_add, Prod.snd_add, add_mul (u₁.2) (u₂.2), trialityTrace_add]
    ring
  B_add_right u v₁ v₂ := by
    unfold d4B
    rw [Prod.fst_add, Prod.snd_add, mul_add (u.2) (v₁.2), trialityTrace_add]
    ring
  B_surj_left u hu s := by
    by_cases hu1 : u.1 ≠ 0
    · refine ⟨(s / (η₂₅ * u.1), 0), ?_⟩
      unfold d4B
      have h0 : trialityTrace K σ hσ (u.2 * 0) = 0 := by
        rw [mul_zero]
        exact Subtype.ext (by simp [coe_trialityTrace])
      rw [h0, mul_zero, add_zero, mul_div_cancel₀ _ (mul_ne_zero hη₂₅ hu1)]
    · push Not at hu1
      have hu2 : u.2 ≠ 0 := fun h => hu (Prod.ext hu1 h)
      obtain ⟨d, hd⟩ := exists_trialityTrace_mul_eq_left σ hσ hne hu2 (s / η₃₄)
      refine ⟨(0, d), ?_⟩
      simp only [d4B, hu1, mul_zero, zero_add, hd, mul_div_cancel₀ _ hη₃₄]
  B_surj_right v hv s := by
    by_cases hv1 : v.1 ≠ 0
    · refine ⟨(s / (η₂₅ * v.1), 0), ?_⟩
      unfold d4B
      have h0 : trialityTrace K σ hσ (0 * v.2) = 0 := by
        rw [zero_mul]
        exact Subtype.ext (by simp [coe_trialityTrace])
      rw [h0, mul_zero, add_zero, mul_right_comm, mul_div_cancel₀ _ (mul_ne_zero hη₂₅ hv1)]
    · push Not at hv1
      have hv2 : v.2 ≠ 0 := fun h => hv (Prod.ext hv1 h)
      obtain ⟨c, hc⟩ := exists_trialityTrace_mul_eq_right σ hσ hne hv2 (s / η₃₄)
      refine ⟨(0, c), ?_⟩
      simp only [d4B, hv1, mul_zero, zero_add, hc, mul_div_cancel₀ _ hη₃₄]

/-- Existence of a `PolarizedHeisenbergData` configuration on
`graphFixedRootGroup TwistTag.D4 K σ` in all characteristics. -/
theorem exists_polarizedHeisenbergData_d4 (hσ : σ ^ 3 = 1) (hne : ∃ u : K, σ u ≠ u) :
    ∃ η₂₅ η₃₄ : trialityFixedField K σ,
      PolarizedHeisenbergData (d4X σ hσ) (d4Y σ hσ) (d4Z σ) (d4B σ hσ η₂₅ η₃₄) := by
  obtain ⟨η₂₅, hη₂₅, hc14⟩ := exists_commutator_fixX_1_4 σ
  obtain ⟨η₃₄, hη₃₄, hc23⟩ := exists_commutator_orb3_2_3 σ hσ
  have h25_ne : η₂₅ ≠ 0 := by rcases hη₂₅ with rfl | rfl <;> simp
  have h34_ne : η₃₄ ≠ 0 := by rcases hη₃₄ with rfl | rfl <;> simp
  exact ⟨η₂₅, η₃₄, polarizedHeisenbergData_d4 σ hσ hne h25_ne h34_ne hc14 hc23⟩

/-- In characteristic `2`, `(d4X, d4Y, d4Z, d4B σ hσ 1 1)` forms a `PolarizedHeisenbergData`. -/
theorem polarizedHeisenbergData_d4_charTwo [CharP K 2] (hσ : σ ^ 3 = 1)
    (hne : ∃ u : K, σ u ≠ u) :
    PolarizedHeisenbergData (d4X σ hσ) (d4Y σ hσ) (d4Z σ) (d4B σ hσ 1 1) := by
  obtain ⟨η₂₅, hη₂₅, hc14⟩ := exists_commutator_fixX_1_4 σ
  obtain ⟨η₃₄, hη₃₄, hc23⟩ := exists_commutator_orb3_2_3 σ hσ
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hneg1 : (-1 : trialityFixedField K σ) = 1 :=
    Subtype.ext (by
      rw [Subfield.coe_neg, Subfield.coe_one]
      linear_combination -h2)
  have h25_1 : η₂₅ = 1 := by rcases hη₂₅ with rfl | rfl <;> [rfl; exact hneg1]
  have h34_1 : η₃₄ = 1 := by rcases hη₃₄ with rfl | rfl <;> [rfl; exact hneg1]
  subst h25_1 h34_1
  exact polarizedHeisenbergData_d4 σ hσ hne one_ne_zero one_ne_zero hc14 hc23

end TwistD4

/-! ### Subgroup index bound `p * (p ^ f) ^ 4 ≤ H.index` for `³D₄(p ^ f)` -/

/-- Every proper subgroup `H` of `³D₄(p ^ f)` has index at least `p * (p ^ f) ^ 4`. -/
theorem index_ge_of_chevalley_trialityD4 {S : Type} [Group S] [IsSimpleGroup S] {p f : ℕ}
    (h : ChevalleyExceptionalModel S .trialityD4 p f) (H : Subgroup S) (hH : H ≠ ⊤) :
    p * (p ^ f) ^ 4 ≤ H.index := by
  classical
  obtain ⟨⟨hp, hf, -⟩, hm⟩ := h
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ := exists_mulEquiv_graphFixedRootGroup_card .D4 hp hf hm
  obtain ⟨σ', hσ', hord, -, -, k, hk, hkcard, hone⟩ :=
    finite_graph_field_parameter_fields .D4 hp hf K hK
  have hσσ' : σ = σ' := RingEquiv.ext fun c => by rw [hσ, hσ']
  subst hσσ'
  have : Fact p.Prime := ⟨hp⟩
  have hK_pow : Nat.card K = p ^ (f * 3) := by
    rw [hK]
    change (p ^ f) ^ 3 = p ^ (f * 3)
    exact (pow_mul p f 3).symm
  have : CharP K p := finite_field_prime_power_characteristic hp (by omega) hK_pow
  let F := ↥(trialityFixedField K σ.toRingHom)
  have : CharP F p := Subfield.charP (trialityFixedField K σ.toRingHom) p
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have : Finite (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := Subtype.finite
  have : IsSimpleGroup ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := e.symm.isSimpleGroup
  have hσ3 : σ.toRingHom ^ 3 = 1 := RingHom.ext fun c => by
    have h3 : σ ^ 3 = 1 := by
      change σ ^ TwistTag.D4.order = 1
      rw [← hord]
      exact pow_orderOf_eq_one σ
    have hc := congrArg (fun φ : K ≃+* K => φ c) h3
    simpa [pow_succ, RingAut.mul_apply, RingHom.coe_pow] using hc
  have hne : ∃ u, σ.toRingHom u ≠ u := by
    by_contra! hcon
    have h1 : σ = 1 := RingEquiv.ext hcon
    rw [h1, orderOf_one] at hord
    exact absurd hord (by decide)
  obtain ⟨η₂₅, η₃₄, D⟩ := exists_polarizedHeisenbergData_d4 σ.toRingHom hσ3 hne
  have hV : ∀ u : F × K, p • u = 0 := fun ⟨b, c⟩ =>
    Prod.ext (by change p • b = 0; rw [nsmul_eq_mul, CharP.cast_eq_zero F p, zero_mul])
      (by change p • c = 0; rw [nsmul_eq_mul, CharP.cast_eq_zero K p, zero_mul])
  have hF_eq : trialityFixedField K σ.toRingHom = k := by
    refine SetLike.ext' ?_
    rw [hk]
    ext c
    simp only [SetLike.mem_coe, mem_trialityFixedField, Set.mem_ofPred_eq]
    rw [← hσ]
    rfl
  have hcardF : Nat.card F = p ^ f := by
    change Nat.card (trialityFixedField K σ.toRingHom) = p ^ f
    rw [hF_eq, hkcard]
  have hcardV : Nat.card (F × K) = (p ^ f) ^ 4 := by
    rw [Nat.card_prod, hcardF, hK]
    change (p ^ f) * (p ^ f) ^ 3 = (p ^ f) ^ 4
    ring
  have hM : H.map (e : S →* ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) ≠ ⊤ := by
    intro htop
    apply hH
    apply Subgroup.map_injective (f := (e : S →* ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)))
      e.injective
    rw [htop, Subgroup.map_top_of_surjective _ e.surjective]
  have hle := D.mul_card_le_index_of_ne_top (p := p) hV hM
  rwa [Subgroup.index_map_equiv, hcardV] at hle

/-- **Factor-of-2 Normalizer Bound for `PolarizedHeisenbergData`**:
When `p = 2`, `Nat.card F = 2`, `2 ≤ Nat.card V`, and every `D.heisSubgroup.normalizer`-invariant
abelian subgroup `K ≤ G` containing `z` has `X u * Y v ∈ K → u = 0 ∧ v = 0`, every proper subgroup
`H` of a finite simple group `G` has index `2 * 2 * Nat.card V ≤ H.index`. -/
theorem PolarizedHeisenbergData.two_mul_card_le_index_of_ne_top
    {G V F : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    [AddCommGroup V] [Finite V] [Field F] [Finite F] [CharP F 2]
    {X Y : V → G} {z : F → G} {B : V → V → F}
    (D : PolarizedHeisenbergData X Y z B)
    (hV2 : ∀ u : V, (2 : ℕ) • u = 0)
    (hcardF : Nat.card F = 2) (hcardV : 2 ≤ Nat.card V)
    (h_no_abel : ∀ K : Subgroup G,
      (∀ s : F, z s ∈ K) →
      (∀ g ∈ Subgroup.normalizer (D.heisSubgroup : Set G), ∀ k ∈ K, g * k * g⁻¹ ∈ K) →
      (∀ k₁ ∈ K, ∀ k₂ ∈ K, ⁅k₁, k₂⁆ = 1) →
      ∀ u v : V, X u * Y v ∈ K → u = 0 ∧ v = 0)
    {H : Subgroup G} (hH : H ≠ ⊤) :
    2 * 2 * Nat.card V ≤ H.index := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Q₀ : Subgroup G := D.heisSubgroup
  let Z₀ : Subgroup Q₀ := D.centerSubgroup
  let N : Subgroup G := Subgroup.normalizer (Q₀ : Set G)
  let P := ↥N
  let Q : Subgroup P := Q₀.subgroupOf N
  have hQ_norm : Q.Normal := Subgroup.normal_in_normalizer
  let eQ : Q₀ ≃* Q := (Subgroup.subgroupOfEquivOfLe Subgroup.le_normalizer).symm
  let Z : Subgroup Q := Z₀.comap eQ.symm.toMonoidHom
  have hZ : Z ≤ Subgroup.center Q := fun w hw => by
    rw [Subgroup.mem_center_iff]
    intro q
    apply eQ.symm.injective
    rw [map_mul, map_mul]
    exact Subgroup.mem_center_iff.1 (D.centerSubgroup_le_center hw) (eQ.symm q)
  have hcomm : ∀ x y : Q, ⁅x, y⁆ ∈ Z := fun x y => by
    change eQ.symm ⁅x, y⁆ ∈ Z₀
    rw [map_commutatorElement]
    exact D.commutator_mem_centerSubgroup (eQ.symm x) (eQ.symm y)
  have hexpZ : ∀ w ∈ Z, w ^ 2 = 1 := fun w hw => by
    apply eQ.symm.injective
    rw [map_pow, map_one]
    exact D.pow_p_eq_one_of_mem_centerSubgroup hw
  have hexpQ : ∀ x : Q, x ^ 2 ∈ Z := fun x => by
    change eQ.symm (x ^ 2) ∈ Z₀
    rw [map_pow]
    exact D.pow_p_mem_centerSubgroup hV2 (eQ.symm x)
  have hsurj : ∀ x : Q, x ∉ Z → ∀ w ∈ Z, ∃ y : Q, ⁅x, y⁆ = w := fun x hx w hw => by
    obtain ⟨y₀, hy₀⟩ := D.exists_commutator_eq_of_not_mem hx hw
    refine ⟨eQ y₀, eQ.symm.injective ?_⟩
    rw [map_commutatorElement, eQ.symm_apply_apply]
    exact hy₀
  have hz_mem_Q₀ : ∀ s : F, z s ∈ Q₀ := fun s =>
    ⟨0, 0, s, by rw [D.X_zero, D.Y_zero, one_mul, one_mul]⟩
  have hZf : (Z.map Q.subtype).map N.subtype ≠ ⊥ := by
    rw [Subgroup.ne_bot_iff_exists_ne_one]
    let z₁ : Q₀ := ⟨z 1, hz_mem_Q₀ 1⟩
    have hz₁ : eQ z₁ ∈ Z := by
      change eQ.symm (eQ z₁) ∈ Z₀
      rw [eQ.symm_apply_apply]
      exact ⟨1, by rw [D.X_zero, D.Y_zero, one_mul, one_mul]⟩
    refine ⟨⟨z 1, Subgroup.mem_map.2
      ⟨Q.subtype (eQ z₁), Subgroup.mem_map.2 ⟨eQ z₁, hz₁, rfl⟩, rfl⟩⟩, ?_⟩
    intro h1
    exact one_ne_zero (D.z_eq_one 1 (congrArg Subtype.val h1))
  have hm : Nat.card V ^ 2 ≤ Z.index := by
    have hidx : Z.index = Z₀.index := Subgroup.index_comap_of_surjective Z₀ eQ.symm.surjective
    rw [hidx, D.index_centerSubgroup]
  have hF_sub : Subsingleton Fˣ := by
    apply Finite.card_le_one_iff_subsingleton.1
    rw [Nat.card_units, hcardF]
  have h_Z_trans : ∀ z₁ ∈ Z, z₁ ≠ 1 → ∀ z₂ ∈ Z, z₂ ≠ 1 → ∃ g : P, conjQ hQ_norm g z₁ = z₂ := by
    intro z₁ hz₁ hz₁1 z₂ hz₂ hz₂1
    obtain ⟨s₁, hs₁⟩ : ∃ s₁ : F, X 0 * Y 0 * z s₁ = (eQ.symm z₁ : G) := hz₁
    obtain ⟨s₂, hs₂⟩ : ∃ s₂ : F, X 0 * Y 0 * z s₂ = (eQ.symm z₂ : G) := hz₂
    have hs₁0 : s₁ ≠ 0 := by
      rintro rfl
      apply hz₁1
      apply eQ.symm.injective
      apply Subtype.ext
      rw [← hs₁, D.X_zero, D.Y_zero, D.z_zero, mul_one, mul_one, map_one, Subgroup.coe_one]
    have hs₂0 : s₂ ≠ 0 := by
      rintro rfl
      apply hz₂1
      apply eQ.symm.injective
      apply Subtype.ext
      rw [← hs₂, D.X_zero, D.Y_zero, D.z_zero, mul_one, mul_one, map_one, Subgroup.coe_one]
    have hs_eq : s₁ = s₂ := by
      have hu : Units.mk0 s₁ hs₁0 = Units.mk0 s₂ hs₂0 := Subsingleton.elim _ _
      exact congrArg Units.val hu
    have hz_eq : z₁ = z₂ := by
      apply eQ.symm.injective
      apply Subtype.ext
      rw [← hs₁, ← hs₂, hs_eq]
    exact ⟨1, by rw [conjQ_one, hz_eq]⟩
  refine two_mul_le_index_of_map_ne_bot_of_ne_top hZ hcomm hexpZ hexpQ hsurj hQ_norm hH N.subtype
    hZf hcardV hm h_Z_trans ?_
  intro K_Q hZK hK_inv hK_abel
  let φ : Q →* G := N.subtype.comp Q.subtype
  let K_G : Subgroup G := K_Q.map φ
  have hz_mem : ∀ s : F, z s ∈ K_G := fun s => by
    let zs : Q₀ := ⟨z s, hz_mem_Q₀ s⟩
    have hzs : eQ zs ∈ Z := by
      change eQ.symm (eQ zs) ∈ Z₀
      rw [eQ.symm_apply_apply]
      exact ⟨s, by rw [D.X_zero, D.Y_zero, one_mul, one_mul]⟩
    exact Subgroup.mem_map.2 ⟨eQ zs, hZK hzs, rfl⟩
  have hK_G_inv : ∀ g ∈ N, ∀ k ∈ K_G, g * k * g⁻¹ ∈ K_G := by
    intro g hg k hk
    obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.1 hk
    exact Subgroup.mem_map.2 ⟨conjQ hQ_norm ⟨g, hg⟩ q, hK_inv ⟨g, hg⟩ q hq, rfl⟩
  have hK_G_abel : ∀ k₁ ∈ K_G, ∀ k₂ ∈ K_G, ⁅k₁, k₂⁆ = 1 := by
    intro k₁ hk₁ k₂ hk₂
    obtain ⟨q₁, hq₁, rfl⟩ := Subgroup.mem_map.1 hk₁
    obtain ⟨q₂, hq₂, rfl⟩ := Subgroup.mem_map.1 hk₂
    rw [← map_commutatorElement, hK_abel q₁ hq₁ q₂ hq₂, map_one]
  have h_triv := h_no_abel K_G hz_mem hK_G_inv hK_G_abel
  refine le_antisymm (fun q hq => ?_) hZK
  have hqQ₀ : φ q ∈ Q₀ := q.2
  obtain ⟨u, v, s, huvs⟩ := hqQ₀
  have hφK : φ q ∈ K_G := Subgroup.mem_map_of_mem φ hq
  rw [← huvs] at hφK
  have hXY : X u * Y v ∈ K_G := (Subgroup.mul_mem_cancel_right K_G (hz_mem s)).1 hφK
  obtain ⟨rfl, rfl⟩ := h_triv u v hXY
  change eQ.symm q ∈ Z₀
  exact ⟨s, huvs⟩

end Maroti
