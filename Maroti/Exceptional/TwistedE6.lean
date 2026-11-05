module

public import Maroti.Exceptional.ChevalleyE
import CFSG.SignalizerFunctorTheorem.NonLocal.E6Heis
import CFSG.LieType.Chevalley.OddExceptionalOuterTwoRank

/-!
# Twisted Exceptional Groups of Type `²E₆(q)`

This file proves the subgroup index lower bounds and Maróti's bound `|G| ≤ bound |α|` for
primitive almost simple groups `G ≤ Perm α` with socle `²E₆(q)` (`q = p^f`, Maróti, Section 2,
Step 2, pages 634–635).

Combining the `3` size-`2` graph orbits `(e6B j, e6R j)` (`j : Fin 3`) from
`CFSG.SignalizerFunctorTheorem.NonLocal.E6Heis` (parameterized by `K` of order `q ^ 2`) with `2`
graph-fixed roots `e6F l` (`l : Fin 2`, parameterized by the fixed subfield `fixField σ` of order
`q`), we obtain a `HeisFam` on `graphFixedRootGroup TwistTag.E6 K σ` of total parameter cardinality
`(q ^ 2) ^ 3 * q ^ 2 = q ^ 8`. Hence every proper subgroup `H` of `²E₆(q)` has index at least
`q ^ 8`, and at least `2 * q ^ 8 = 512` when `q = 2`.
-/

@[expose] public section

open scoped commutatorElement

namespace Maroti

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial (finite_field_prime_power_characteristic)
open CFSG.SignalizerFunctorTheorem.NonLocal
open CFSG.SignalizerFunctorTheorem.NonLocalExc

/-! ### Fixed roots in `heisS .E6` under the graph involution -/

private def e6FCodes : Fin 2 → ℕ := ![8947864, 8951960]

private def e6F (l : Fin 2) : Fin TwistTag.E6.tag.rank → ℤ := decodeVec (e6FCodes l)

private theorem e6F_mem (l : Fin 2) : e6F l ∈ heisS TwistTag.E6.tag :=
  mem_heisS.2 ⟨e6FCodes l, by fin_cases l <;> decide, rfl⟩

private theorem permLattice_e6F (l : Fin 2) :
    permLattice TwistTag.E6.perm (e6F l) = e6F l := by
  fin_cases l <;> decide +kernel

private theorem e6F_distinct : ∀ l l' : Fin 2, l ≠ l' → e6F l ≠ e6F l' := by
  decide +kernel

private theorem e6B_ne_e6F : ∀ (j : Fin 3) (l : Fin 2),
    e6B j ≠ e6F l ∧ e6R j ≠ e6F l := by
  decide +kernel

/-! ### Commutation between size-`2` orbits and single roots -/

private theorem commute_orb_pinnedX_S {k : Type} [Field k] (σ : k →+* k)
    {x y : Fin TwistTag.E6.tag.rank → ℤ} (hx : x ∈ heisS TwistTag.E6.tag)
    (hx' : permLattice TwistTag.E6.perm x ∈ heisS TwistTag.E6.tag)
    (hy : y ∈ heisS TwistTag.E6.tag) (c d : k) :
    orb σ x c * pinnedX TwistTag.E6.tag k y d =
      pinnedX TwistTag.E6.tag k y d * orb σ x c := by
  obtain ⟨εx, -, hFx⟩ := twist_pinnedX σ (hF6.isRoot_of_mem x hx)
  unfold orb
  rw [hFx c]
  exact ((commute_of_eq' (commute_S hx hy _ _)).mul_left
    (commute_of_eq' (commute_S hx' hy _ _))).eq

private theorem commute_orb_pinnedX_T {k : Type} [Field k] (σ : k →+* k)
    {x y : Fin TwistTag.E6.tag.rank → ℤ} (hx : x ∈ heisS TwistTag.E6.tag)
    (hx' : permLattice TwistTag.E6.perm x ∈ heisS TwistTag.E6.tag)
    (hy : y ∈ heisS TwistTag.E6.tag) (c d : k) :
    orb σ (heisα0 TwistTag.E6.tag - x) c *
        pinnedX TwistTag.E6.tag k (heisα0 TwistTag.E6.tag - y) d =
      pinnedX TwistTag.E6.tag k (heisα0 TwistTag.E6.tag - y) d *
        orb σ (heisα0 TwistTag.E6.tag - x) c := by
  obtain ⟨εx, -, hFx⟩ := twist_pinnedX σ (hF6.isRoot_sub x hx)
  rw [permLattice_sub_heisα0] at hFx
  unfold orb
  rw [hFx c]
  exact ((commute_of_eq' (commute_T hx hy _ _)).mul_left
    (commute_of_eq' (commute_T hx' hy _ _))).eq

private theorem commute_orb_T_pinnedX_S {k : Type} [Field k] (σ : k →+* k)
    {x y : Fin TwistTag.E6.tag.rank → ℤ} (hx : x ∈ heisS TwistTag.E6.tag)
    (hx' : permLattice TwistTag.E6.perm x ∈ heisS TwistTag.E6.tag)
    (hy : y ∈ heisS TwistTag.E6.tag) (h1 : x ≠ y)
    (h2 : permLattice TwistTag.E6.perm x ≠ y) (c d : k) :
    orb σ (heisα0 TwistTag.E6.tag - x) c * pinnedX TwistTag.E6.tag k y d =
      pinnedX TwistTag.E6.tag k y d * orb σ (heisα0 TwistTag.E6.tag - x) c := by
  obtain ⟨εx, -, hFx⟩ := twist_pinnedX σ (hF6.isRoot_sub x hx)
  rw [permLattice_sub_heisα0] at hFx
  unfold orb
  rw [hFx c]
  exact ((commute_of_eq' (commute_T_S hx hy h1 _ _)).mul_left
    (commute_of_eq' (commute_T_S hx' hy h2 _ _))).eq

private theorem commute_pinnedX_T_orb_S {k : Type} [Field k] (σ : k →+* k)
    {x y : Fin TwistTag.E6.tag.rank → ℤ} (hx : x ∈ heisS TwistTag.E6.tag)
    (hy : y ∈ heisS TwistTag.E6.tag)
    (hy' : permLattice TwistTag.E6.perm y ∈ heisS TwistTag.E6.tag)
    (h1 : x ≠ y) (h2 : x ≠ permLattice TwistTag.E6.perm y) (c d : k) :
    pinnedX TwistTag.E6.tag k (heisα0 TwistTag.E6.tag - x) c * orb σ y d =
      orb σ y d * pinnedX TwistTag.E6.tag k (heisα0 TwistTag.E6.tag - x) c := by
  obtain ⟨εy, -, hFy⟩ := twist_pinnedX σ (hF6.isRoot_of_mem y hy)
  unfold orb
  rw [hFy d]
  exact ((commute_of_eq' (commute_T_S hx hy h1 _ _)).mul_right
    (commute_of_eq' (commute_T_S hx hy' h2 _ _))).eq

/-! ### Fixed-subfield parameterization of fixed root subgroups -/

private abbrev fixField {k : Type} [Field k] (σ : k →+* k) : Subfield k :=
  orbitField TwistTag.E6 k σ ⟨2, by decide⟩

private theorem mem_fixField_iff {k : Type} [Field k] (σ : k →+* k) (x : k) :
    x ∈ fixField σ ↔ σ x = x := by
  rw [fixField, mem_orbitField]
  have h1 : (TwistTag.E6.orbit ⟨2, by decide⟩).card = 1 := by decide
  rw [h1, pow_one]

private noncomputable def scaleSign {k : Type} [Field k] (σ : k →+* k) (δ ε : k)
    (x : fixField σ) : k := by
  classical
  exact (if ε = 1 then 1 else δ) * x.1

private theorem twist_scaleSign {k : Type} [Field k] (σ : k →+* k) {δ : k}
    (hσδ : σ δ = -δ) {ε : k} (hε : ε * ε = 1) (x : fixField σ) :
    ε * σ (scaleSign σ δ ε x) = scaleSign σ δ ε x := by
  classical
  have hx : σ x.1 = x.1 := (mem_fixField_iff σ x.1).1 x.2
  rcases sign_cases hε with rfl | rfl
  · simp [scaleSign, hx]
  · by_cases h1 : (-1 : k) = 1
    · simp [scaleSign, h1, hx]
    · simp only [scaleSign, ite_eq_right_iff.2 (fun h => (h1 h).elim), map_mul, hx, hσδ]
      ring

private noncomputable def fixOrb {k : Type} [Field k] (σ : k →+* k) (δ : k)
    (γ : Fin TwistTag.E6.tag.rank → ℤ) (ε : k) (x : fixField σ) : ModGL TwistTag.E6.tag k :=
  pinnedX TwistTag.E6.tag k γ (scaleSign σ δ ε x)

private theorem twist_fixOrb_eq {k : Type} [Field k] (σ : k →+* k) {δ : k} (hσδ : σ δ = -δ)
    {γ : Fin TwistTag.E6.tag.rank → ℤ} (hγ_fix : permLattice TwistTag.E6.perm γ = γ)
    {ε : k} (hε : ε * ε = 1)
    (hFγ : ∀ c : k, twistHom TwistTag.E6 k σ (pinnedX TwistTag.E6.tag k γ c) =
      pinnedX TwistTag.E6.tag k (permLattice TwistTag.E6.perm γ) (ε * σ c))
    (x : fixField σ) :
    twistHom TwistTag.E6 k σ (fixOrb σ δ γ ε x) = fixOrb σ δ γ ε x := by
  unfold fixOrb
  rw [hFγ, hγ_fix, twist_scaleSign σ hσδ hε x]

private theorem fixOrb_mem {k : Type} [Field k] (σ : k →+* k) {δ : k} (hσδ : σ δ = -δ)
    {γ : Fin TwistTag.E6.tag.rank → ℤ} (hγ : IsRoot TwistTag.E6.tag γ) (hpos : 0 < height γ)
    (hγ_fix : permLattice TwistTag.E6.perm γ = γ) {ε : k} (hε : ε * ε = 1)
    (hFγ : ∀ c : k, twistHom TwistTag.E6 k σ (pinnedX TwistTag.E6.tag k γ c) =
      pinnedX TwistTag.E6.tag k (permLattice TwistTag.E6.perm γ) (ε * σ c))
    (x : fixField σ) :
    fixOrb σ δ γ ε x ∈ graphFixedRootGroup TwistTag.E6 k σ := by
  refine graphFixedPosUnipotent_le_graphFixedRootGroup TwistTag.E6 k σ ?_
  refine Subgroup.mem_inf.2 ⟨?_, (mem_twistedFixedGroup_iff_twistHom _ _ _).2
    ⟨pinnedX_mem_adjointGroup _ _, twist_fixOrb_eq σ hσδ hγ_fix hε hFγ x⟩⟩
  exact rootSpan_le_posUnipotent (S := {x | IsRoot TwistTag.E6.tag x ∧ 0 < height x})
    (fun _ h => h) (pinnedX_mem_rootSpan (S := {x | IsRoot TwistTag.E6.tag x ∧ 0 < height x})
      ⟨hγ, hpos⟩ _)

private theorem fix_pair_comm {k : Type} [Field k] (σ : k →+* k) {δ : k} (hδ0 : δ ≠ 0)
    (hσδ : σ δ = -δ) {ε₀ : k} (_hε₀ : ε₀ * ε₀ = 1)
    (hF₀ : ∀ w : k, twistHom TwistTag.E6 k σ
        (pinnedX TwistTag.E6.tag k (heisα0 TwistTag.E6.tag) w) =
      pinnedX TwistTag.E6.tag k (heisα0 TwistTag.E6.tag) (ε₀ * σ w))
    (l : Fin 2) :
    ∃ εβ εγ m : k, εβ * εβ = 1 ∧ εγ * εγ = 1 ∧ m ≠ 0 ∧ ε₀ * σ m = m ∧
      (∀ d : fixField σ,
        fixOrb σ δ (e6F l) εβ d ∈ graphFixedRootGroup TwistTag.E6 k σ) ∧
      (∀ c : fixField σ,
        fixOrb σ δ (heisα0 TwistTag.E6.tag - e6F l) εγ c ∈ graphFixedRootGroup TwistTag.E6 k σ) ∧
      ∀ c d : fixField σ,
        ⁅(fixOrb σ δ (heisα0 TwistTag.E6.tag - e6F l) εγ c)⁻¹, fixOrb σ δ (e6F l) εβ d⁆ =
          pinnedX TwistTag.E6.tag k (heisα0 TwistTag.E6.tag) (m * c.1 * d.1) := by
  classical
  have hβ : e6F l ∈ heisS TwistTag.E6.tag := e6F_mem l
  have hβ_fix : permLattice TwistTag.E6.perm (e6F l) = e6F l := permLattice_e6F l
  have hγ_fix : permLattice TwistTag.E6.perm (heisα0 TwistTag.E6.tag - e6F l) =
      heisα0 TwistTag.E6.tag - e6F l := by
    rw [permLattice_sub_heisα0, hβ_fix]
  obtain ⟨εβ, hεβ, hFβ⟩ := twist_pinnedX σ (hF6.isRoot_of_mem _ hβ)
  obtain ⟨εγ, hεγ, hFγ⟩ := twist_pinnedX σ (hF6.isRoot_sub _ hβ)
  obtain ⟨η, hη, hcomm_raw⟩ := exists_comm_T_S (k := k) hβ
  let sβ : k := if εβ = 1 then 1 else δ
  let sγ : k := if εγ = 1 then 1 else δ
  let m : k := -η * sγ * sβ
  have hsβ0 : sβ ≠ 0 := by simp only [sβ]; split_ifs; exact one_ne_zero; exact hδ0
  have hsγ0 : sγ ≠ 0 := by simp only [sγ]; split_ifs; exact one_ne_zero; exact hδ0
  have hη0 : -η ≠ 0 := neg_ne_zero.2 (fun h => by rw [h, zero_mul] at hη; exact zero_ne_one hη)
  have hm0 : m ≠ 0 := mul_ne_zero (mul_ne_zero hη0 hsγ0) hsβ0
  have hcomm : ∀ c d : fixField σ,
      ⁅(fixOrb σ δ (heisα0 TwistTag.E6.tag - e6F l) εγ c)⁻¹, fixOrb σ δ (e6F l) εβ d⁆ =
        pinnedX TwistTag.E6.tag k (heisα0 TwistTag.E6.tag) (m * c.1 * d.1) := fun c d => by
    unfold fixOrb scaleSign
    rw [pinnedX_neg, hcomm_raw]
    congr 1
    simp only [m, sγ, sβ]
    ring
  have hm_fix : ε₀ * σ m = m := by
    have h1 := hcomm 1 1
    simp only [Subfield.coe_one, mul_one] at h1
    have hfix : twistHom TwistTag.E6 k σ
        ⁅(fixOrb σ δ (heisα0 TwistTag.E6.tag - e6F l) εγ 1)⁻¹, fixOrb σ δ (e6F l) εβ 1⁆ =
        ⁅(fixOrb σ δ (heisα0 TwistTag.E6.tag - e6F l) εγ 1)⁻¹, fixOrb σ δ (e6F l) εβ 1⁆ := by
      rw [map_commutatorElement, map_inv,
        twist_fixOrb_eq σ hσδ hγ_fix hεγ hFγ 1,
        twist_fixOrb_eq σ hσδ hβ_fix hεβ hFβ 1]
    rw [h1, hF₀] at hfix
    exact pinnedX_injective TwistTag.E6.tag k (heisα0 TwistTag.E6.tag) hfix
  refine ⟨εβ, εγ, m, hεβ, hεγ, hm0, hm_fix,
    fun d => fixOrb_mem σ hσδ (hF6.isRoot_of_mem _ hβ) (hF6.pos_of_mem _ hβ) hβ_fix hεβ hFβ d,
    fun c => fixOrb_mem σ hσδ (hF6.isRoot_sub _ hβ) (heis_gamma_pos (hF := hF6) hβ)
      hγ_fix hεγ hFγ c,
    hcomm⟩

private theorem div_mem_fixField {k : Type} [Field k] (σ : k →+* k) {ε₀ : k} (hε₀ : ε₀ * ε₀ = 1)
    {a₀ : k} (ha₀ : ε₀ * σ a₀ = a₀) {u : k} (hu : ε₀ * σ u = u) :
    u / a₀ ∈ fixField σ := by
  rw [mem_fixField_iff, map_div₀]
  have hε0 : ε₀ ≠ 0 := fun h => by rw [h, zero_mul] at hε₀; exact zero_ne_one hε₀
  have hσu : σ u = ε₀ * u := by linear_combination ε₀ * hu - σ u * hε₀
  have hσa : σ a₀ = ε₀ * a₀ := by linear_combination ε₀ * ha₀ - σ a₀ * hε₀
  rw [hσu, hσa, mul_div_mul_left _ _ hε0]

/-! ### Combined `Fin 3 ⊕ Fin 2` Heisenberg family for `²E₆(q)` -/

private abbrev e6Param {k : Type} [Field k] (σ : k →+* k) :
    Fin 3 ⊕ Fin 2 → Type
  | Sum.inl _ => k
  | Sum.inr _ => fixField σ

private noncomputable instance {k : Type} [Field k] (σ : k →+* k) (s : Fin 3 ⊕ Fin 2) :
    AddCommGroup (e6Param σ s) := by
  cases s <;> infer_instance

private instance {k : Type} [Field k] [Finite k] (σ : k →+* k) (s : Fin 3 ⊕ Fin 2) :
    Finite (e6Param σ s) := by
  cases s <;> infer_instance

private theorem exists_heisFam_twistedE6 {k : Type} [Field k] (σ : k →+* k)
    (hσ2 : ∀ c, σ (σ c) = c) (hne : ∃ u, σ u ≠ u) :
    ∃ H : HeisFam ↥(graphFixedRootGroup TwistTag.E6 k σ) (Fin 3 ⊕ Fin 2) (e6Param σ) (fixField σ),
      ∃ w ∈ H.Rg, H.z w ≠ 1 ∧ ((2 : k) = 0 → H.z w * H.z w = 1) := by
  classical
  obtain ⟨u₀, hu₀⟩ := hne
  let δ : k := u₀ - σ u₀
  have hδ0 : δ ≠ 0 := sub_ne_zero.2 hu₀.symm
  have hσδ : σ δ = -δ := by simp only [δ, map_sub, hσ2]; ring
  obtain ⟨ε₀, hε₀, hF₀'⟩ := twist_pinnedX σ (hF6.isRoot_α0 (τ := TwistTag.E6.tag))
  have hF₀ : ∀ w : k, twistHom TwistTag.E6 k σ
      (pinnedX TwistTag.E6.tag k (heisα0 TwistTag.E6.tag) w) =
        pinnedX TwistTag.E6.tag k (heisα0 TwistTag.E6.tag) (ε₀ * σ w) := fun w => by
    rw [hF₀' w, permLattice_heisα0]
  choose p hp1 hp2 using pair_comm σ hσ2 ⟨u₀, hu₀⟩ hε₀ hF₀
  have hp0 : ∀ j, p j ≠ 0 := fun j h => by
    have := hp1 j
    rw [h, zero_mul] at this
    exact zero_ne_one this
  choose εβ εγ m hεβ hεγ hm0 hm_fix hxa_fix hxb_fix hcomm_fix using
    fix_pair_comm σ hδ0 hσδ hε₀ hF₀
  have hρB : ∀ j, permLattice TwistTag.E6.perm (e6B j) ∈ heisS TwistTag.E6.tag := fun j => by
    rw [permLattice_e6B]; exact e6R_mem j
  have hxa_B : ∀ (j : Fin 3) (d : k), orb σ (e6B j) d ∈ graphFixedRootGroup TwistTag.E6 k σ :=
    fun j d => orb_mem σ (hF6.isRoot_of_mem _ (e6B_mem j)) (hF6.pos_of_mem _ (e6B_mem j)) hσ2
      (comm2_B j) d
  have hxb_B : ∀ (j : Fin 3) (c : k),
      orb σ (heisα0 TwistTag.E6.tag - e6B j) c ∈ graphFixedRootGroup TwistTag.E6 k σ :=
    fun j c => orb_mem σ (hF6.isRoot_sub _ (e6B_mem j)) (heis_gamma_pos (hF := hF6) (e6B_mem j))
      hσ2 (comm2_T j) c
  have hz := z_mem σ hσ2 hε₀ hF₀
  obtain ⟨w₀, hw₀⟩ : ∃ w : k, w + ε₀ * σ w ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have h1 := hcon 1
    rw [map_one, mul_one] at h1
    have h2 := hcon u₀
    have hε : ε₀ = -1 := by linear_combination h1
    rw [hε] at h2
    exact hu₀ (by linear_combination -h2)
  let a₀ : k := w₀ + ε₀ * σ w₀
  have ha₀_inv : ∀ v : k, ε₀ * σ (v + ε₀ * σ v) = v + ε₀ * σ v := fun v => by
    rw [map_add, map_mul, hσ2, map_sign σ hε₀]
    linear_combination v * hε₀
  have ha₀ : ε₀ * σ a₀ = a₀ := ha₀_inv w₀
  have hzw : ∀ w : fixField σ, (w.1 * w₀) + ε₀ * σ (w.1 * w₀) = w.1 * a₀ := fun w => by
    have hw : σ w.1 = w.1 := (mem_fixField_iff σ w.1).1 w.2
    simp only [map_mul, hw, a₀]
    ring
  let tr₀ : k → fixField σ := fun v =>
    ⟨(v + ε₀ * σ v) / a₀, div_mem_fixField σ hε₀ ha₀ (ha₀_inv v)⟩
  let qf : Fin 2 → fixField σ := fun l =>
    ⟨m l / a₀, div_mem_fixField σ hε₀ ha₀ (hm_fix l)⟩
  have hqf0 : ∀ l, qf l ≠ 0 := fun l h =>
    hm0 l (div_eq_zero_iff.1 (congrArg Subtype.val h) |>.resolve_right hw₀)
  refine ⟨{ xa := fun s => match s with
              | Sum.inl j => fun d => ⟨orb σ (e6B j) d, hxa_B j d⟩
              | Sum.inr l => fun d => ⟨fixOrb σ δ (e6F l) (εβ l) d, hxa_fix l d⟩
            xb := fun s => match s with
              | Sum.inl j => fun c => ⟨orb σ (heisα0 TwistTag.E6.tag - e6B j) c, hxb_B j c⟩
              | Sum.inr l => fun c =>
                  ⟨fixOrb σ δ (heisα0 TwistTag.E6.tag - e6F l) (εγ l) c, hxb_fix l c⟩
            z := fun w => ⟨pinnedX TwistTag.E6.tag k (heisα0 TwistTag.E6.tag)
              ((w.1 * w₀) + ε₀ * σ (w.1 * w₀)), hz (w.1 * w₀)⟩
            e := fun s => match s with
              | Sum.inl j => fun c d => tr₀ (p j * c * d)
              | Sum.inr l => fun c d => qf l * c * d
            Rg := ⊤
            z_add := fun w w' => Subtype.ext (by
              show pinnedX TwistTag.E6.tag k (heisα0 TwistTag.E6.tag) _ =
                pinnedX TwistTag.E6.tag k (heisα0 TwistTag.E6.tag) _ *
                  pinnedX TwistTag.E6.tag k (heisα0 TwistTag.E6.tag) _
              rw [← pinnedX_add, hzw (w + w'), hzw w, hzw w']
              congr 1
              simp only [Subfield.coe_add]
              ring)
            e_add_left := fun s c c' d => by
              cases s with
              | inl j =>
                refine Subtype.ext ?_
                show ((p j * (c + c') * d + ε₀ * σ (p j * (c + c') * d)) / a₀) =
                  (p j * c * d + ε₀ * σ (p j * c * d)) / a₀ +
                    (p j * c' * d + ε₀ * σ (p j * c' * d)) / a₀
                have : p j * (c + c') * d = p j * c * d + p j * c' * d := by ring
                rw [this, map_add]
                ring
              | inr l =>
                change qf l * (c + c') * d = qf l * c * d + qf l * c' * d
                ring
            e_mem := fun _ _ _ => AddSubgroup.mem_top _
            e_surj := fun s c hc w _ => by
              cases s with
              | inl j =>
                refine ⟨(w.1 * w₀) / (p j * c), Subtype.ext ?_⟩
                show (p j * c * ((w.1 * w₀) / (p j * c)) +
                  ε₀ * σ (p j * c * ((w.1 * w₀) / (p j * c)))) / a₀ = w.1
                have hpc : p j * c ≠ 0 := mul_ne_zero (hp0 j) hc
                rw [mul_div_cancel₀ _ hpc, hzw w, mul_div_cancel_right₀ _ hw₀]
              | inr l =>
                refine ⟨w / (qf l * c), ?_⟩
                change qf l * c * (w / (qf l * c)) = w
                have hqc : qf l * c ≠ 0 := mul_ne_zero (hqf0 l) hc
                exact mul_div_cancel₀ w hqc
            xa_comm := fun s t c d => Subtype.ext (by
              cases s with
              | inl j =>
                cases t with
                | inl j' => exact commute_orb_S σ (e6B_mem j) (hρB j) (e6B_mem j') (hρB j') c d
                | inr l' => exact commute_orb_pinnedX_S σ (e6B_mem j) (hρB j) (e6F_mem l') c _
              | inr l =>
                cases t with
                | inl j' =>
                  exact (commute_orb_pinnedX_S σ (e6B_mem j') (hρB j') (e6F_mem l) d _).symm
                | inr l' => exact commute_S (e6F_mem l) (e6F_mem l') _ _)
            xb_comm := fun s t c d => Subtype.ext (by
              cases s with
              | inl j =>
                cases t with
                | inl j' => exact commute_orb_T σ (e6B_mem j) (hρB j) (e6B_mem j') (hρB j') c d
                | inr l' => exact commute_orb_pinnedX_T σ (e6B_mem j) (hρB j) (e6F_mem l') c _
              | inr l =>
                cases t with
                | inl j' =>
                  exact (commute_orb_pinnedX_T σ (e6B_mem j') (hρB j') (e6F_mem l) d _).symm
                | inr l' => exact commute_T (e6F_mem l) (e6F_mem l') _ _)
            z_comm_a := fun w s d => Subtype.ext (by
              cases s with
              | inl j => exact commute_α0_orb_S σ (e6B_mem j) (hρB j) _ d
              | inr l => exact commute_α0_S (e6F_mem l) _ _)
            z_comm_b := fun w s d => Subtype.ext (by
              cases s with
              | inl j => exact commute_α0_orb_T σ (e6B_mem j) (hρB j) _ d
              | inr l => exact commute_α0_T (e6F_mem l) _ _)
            xab_comm := fun s t hst c d => Subtype.ext (by
              cases s with
              | inl j =>
                cases t with
                | inl j' =>
                  have hne' : j ≠ j' := fun h => hst (congrArg Sum.inl h)
                  obtain ⟨h11, h12, h21, h22⟩ := e6_distinct j j' hne'
                  rw [← permLattice_e6B j, ← permLattice_e6B j'] at *
                  exact commute_orb_T_S σ (e6B_mem j) (hρB j) (e6B_mem j') (hρB j')
                    h11 h12 h21 h22 c d
                | inr l' =>
                  obtain ⟨h1, h2⟩ := e6B_ne_e6F j l'
                  rw [← permLattice_e6B j] at h2
                  exact commute_orb_T_pinnedX_S σ (e6B_mem j) (hρB j) (e6F_mem l') h1 h2 c _
              | inr l =>
                cases t with
                | inl j' =>
                  obtain ⟨h1, h2⟩ := e6B_ne_e6F j' l
                  rw [← permLattice_e6B j'] at h2
                  exact commute_pinnedX_T_orb_S σ (e6F_mem l) (e6B_mem j') (hρB j')
                    h1.symm h2.symm _ d
                | inr l' =>
                  have hne' : l ≠ l' := fun h => hst (congrArg Sum.inr h)
                  exact commute_T_S (e6F_mem l) (e6F_mem l') (e6F_distinct l l' hne') _ _)
            comm_ss := fun s c d => Subtype.ext (by
              cases s with
              | inl j =>
                show ⁅(orb σ (heisα0 TwistTag.E6.tag - e6B j) c)⁻¹, orb σ (e6B j) d⁆ =
                  pinnedX TwistTag.E6.tag k (heisα0 TwistTag.E6.tag)
                    (((tr₀ (p j * c * d)).1 * w₀) + ε₀ * σ ((tr₀ (p j * c * d)).1 * w₀))
                rw [hp2 j c d, hzw (tr₀ (p j * c * d))]
                congr 1
                show _ = ((p j * c * d + ε₀ * σ (p j * c * d)) / a₀) * a₀
                exact (div_mul_cancel₀ _ hw₀).symm
              | inr l =>
                show ⁅(fixOrb σ δ (heisα0 TwistTag.E6.tag - e6F l) (εγ l) c)⁻¹,
                    fixOrb σ δ (e6F l) (εβ l) d⁆ =
                  pinnedX TwistTag.E6.tag k (heisα0 TwistTag.E6.tag)
                    (((qf l * c * d).1 * w₀) + ε₀ * σ ((qf l * c * d).1 * w₀))
                rw [hcomm_fix l c d, hzw (qf l * c * d)]
                congr 1
                show m l * c.1 * d.1 = ((m l / a₀) * c.1 * d.1) * a₀
                calc m l * c.1 * d.1 = ((m l / a₀) * a₀) * c.1 * d.1 := by
                      rw [div_mul_cancel₀ _ hw₀]
                  _ = ((m l / a₀) * c.1 * d.1) * a₀ := by ring) },
    1, AddSubgroup.mem_top _, ?_, ?_⟩
  · intro h
    have h1 := congrArg Subtype.val h
    change pinnedX TwistTag.E6.tag k (heisα0 TwistTag.E6.tag)
      ((1 : fixField σ).1 * w₀ + ε₀ * σ ((1 : fixField σ).1 * w₀)) = 1 at h1
    rw [hzw 1, Subfield.coe_one, one_mul] at h1
    exact hw₀ (pinnedX_injective TwistTag.E6.tag k (heisα0 TwistTag.E6.tag)
      (h1.trans (pinnedX_zero _ _ _).symm))
  · intro h2
    refine Subtype.ext ?_
    show pinnedX TwistTag.E6.tag k (heisα0 TwistTag.E6.tag) _ *
      pinnedX TwistTag.E6.tag k (heisα0 TwistTag.E6.tag) _ = 1
    rw [← pinnedX_add]
    have : (1 : fixField σ).1 * w₀ + ε₀ * σ ((1 : fixField σ).1 * w₀) +
        ((1 : fixField σ).1 * w₀ + ε₀ * σ ((1 : fixField σ).1 * w₀)) = 0 := by
      linear_combination ((1 : fixField σ).1 * w₀ + ε₀ * σ ((1 : fixField σ).1 * w₀)) * h2
    rw [this, pinnedX_zero]

/-! ### Subgroup index bounds and Maróti's bound for `²E₆(p^f)` -/

/-- Every proper subgroup `H` of `²E₆(p^f)` has index at least `(p ^ f) ^ 8`, and at least
`2 * (p ^ f) ^ 8` when `p = 2`. -/
theorem index_ge_of_chevalley_twistedE6 {S : Type} [Group S] [IsSimpleGroup S] {p f : ℕ}
    (h : ChevalleyExceptionalModel S .twistedE6 p f) (H : Subgroup S) (hH : H ≠ ⊤) :
    (p ^ f) ^ 8 ≤ H.index ∧ (p = 2 → 2 * (p ^ f) ^ 8 ≤ H.index) := by
  classical
  obtain ⟨⟨hp, hf, -⟩, hm⟩ := h
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ := exists_mulEquiv_graphFixedRootGroup_card .E6 hp hf hm
  obtain ⟨σ', hσ', hord, hcard_orb, -⟩ := finite_graph_field_parameter_fields .E6 hp hf K hK
  have hσσ' : σ = σ' := RingEquiv.ext fun c => by rw [hσ, hσ']
  subst hσσ'
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  have : Finite (graphFixedRootGroup TwistTag.E6 K σ.toRingHom) := Subtype.finite
  have : IsSimpleGroup ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) := e.symm.isSimpleGroup
  have hσ2 : ∀ c, σ.toRingHom (σ.toRingHom c) = c := fun c => by
    have h2 : σ ^ 2 = 1 := by
      change σ ^ TwistTag.E6.order = 1
      rw [← hord]
      exact pow_orderOf_eq_one σ
    have hc := congrArg (fun φ : K ≃+* K => φ c) h2
    simpa [sq, RingAut.mul_apply] using hc
  have hne : ∃ u, σ.toRingHom u ≠ u := by
    by_contra! hcon
    have h1 : σ = 1 := RingEquiv.ext hcon
    rw [h1, orderOf_one] at hord
    exact absurd hord (by decide)
  obtain ⟨Hfam, w, hwR, hw1, hw2⟩ := exists_heisFam_twistedE6 σ.toRingHom hσ2 hne
  have hM : H.map (e : S →* ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) ≠ ⊤ := by
    intro htop
    apply hH
    apply Subgroup.map_injective (f := (e : S →* ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)))
      e.injective
    rw [htop, Subgroup.map_top_of_surjective _ e.surjective]
  have hcard_fix : Nat.card (fixField σ.toRingHom) = p ^ f := by
    have h2 := hcard_orb ⟨2, by decide⟩
    have hc : (TwistTag.E6.orbit ⟨2, by decide⟩).card = 1 := by decide
    rwa [hc, pow_one] at h2
  have hcard : Nat.card (∀ s : Fin 3 ⊕ Fin 2, e6Param σ.toRingHom s) = (p ^ f) ^ 8 := by
    rw [Nat.card_congr (Equiv.sumPiEquivProdPi (e6Param σ.toRingHom)), Nat.card_prod]
    change Nat.card (Fin 3 → K) * Nat.card (Fin 2 → fixField σ.toRingHom) = (p ^ f) ^ 8
    rw [Nat.card_fun, Nat.card_fun, hK, hcard_fix, Nat.card_eq_fintype_card,
      Nat.card_eq_fintype_card, Fintype.card_fin, Fintype.card_fin]
    change ((p ^ f) ^ 2) ^ 3 * (p ^ f) ^ 2 = (p ^ f) ^ 8
    ring
  refine ⟨?_, fun hp2 => ?_⟩
  · have hle := HeisFam.card_le_index_of_isSimpleGroup Hfam ⟨w, hwR, hw1⟩
      (H.map (e : S →* ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom))) hM
    rwa [Subgroup.index_map_equiv, hcard] at hle
  · subst hp2
    have hK' : Nat.card K = 2 ^ (f * 2) := by
      rw [hK]
      change (2 ^ f) ^ 2 = 2 ^ (f * 2)
      exact (pow_mul 2 f 2).symm
    have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hK'
    have hle := HeisFam.two_mul_card_le_index_of_isSimpleGroup Hfam
      ⟨w, hwR, hw2 CharTwo.two_eq_zero, hw1⟩
      (H.map (e : S →* ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom))) hM
    rwa [Subgroup.index_map_equiv, hcard] at hle

/-- Any primitive almost simple group `G ≤ Perm α` with socle `²E₆(p^f)` satisfies
`|G| ≤ bound |α|`. -/
theorem card_le_bound_of_chevalley_twistedE6 {α : Type} [Finite α]
    {G : Subgroup (Equiv.Perm α)} [MulAction.IsPreprimitive G α]
    {S : Type} [Group S] {p f : ℕ} (hAS : IsAlmostSimpleWith G S)
    (h : ChevalleyExceptionalModel S .twistedE6 p f) :
    Nat.card G ≤ bound (Nat.card α) := by
  have : IsSimpleGroup S := hAS.isSimpleGroup
  have hcard : Nat.card S = ordTwistedE6 (p ^ f) := card_chevalleyExceptionalModel h
  have hout := (card_outerAut_twistedE6 h).2
  have hidx_both := fun H hH => index_ge_of_chevalley_twistedE6 h H hH
  obtain ⟨⟨hp, hf, -⟩, -⟩ := h
  have hfq : f ≤ p ^ f := (Nat.lt_pow_self hp.one_lt).le
  by_cases hq2 : p ^ f = 2
  · have hp2 : p = 2 := by
      have h1 : p ^ 1 ≤ p ^ f := Nat.pow_le_pow_right hp.pos hf
      rw [pow_one] at h1
      have h2 := hp.two_le
      omega
    have hf1 : f = 1 := by
      subst hp2
      have : 2 ^ f < 2 ^ 2 := by omega
      have : f < 2 := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).1 this
      omega
    have hidx : ∀ H : Subgroup S, H ≠ ⊤ → 512 ≤ H.index := by
      intro H hH
      have h2 := (hidx_both H hH).2 hp2
      rwa [hq2] at h2
    refine hAS.card_le_bound_of_outerAut_le hidx hout ?_
    rw [hcard, hq2, hf1]
    calc ordTwistedE6 2 * (6 * 1)
        ≤ 2 ^ 78 * 6 := Nat.mul_le_mul_right 6 (ordTwistedE6_le_pow 2)
      _ ≤ 512 ^ 9 := by decide
      _ ≤ 512 ^ Nat.log 2 512 :=
          Nat.pow_le_pow_right (by decide) (Nat.le_log_of_pow_le (by decide) (by decide))
      _ ≤ bound 512 := pow_log_le_bound (by decide)
  · have hq_ge2 : 2 ≤ p ^ f :=
      (Nat.pow_le_pow_left hp.two_le 1).trans (Nat.pow_le_pow_right hp.pos hf)
    have hq3 : 3 ≤ p ^ f := by omega
    have hidx : ∀ H : Subgroup S, H ≠ ⊤ → (p ^ f) ^ 8 ≤ H.index :=
      fun H hH => (hidx_both H hH).1
    refine hAS.card_le_bound_of_outerAut_le hidx hout ?_
    rw [hcard]
    have hL : 2 ^ 12 ≤ (p ^ f) ^ 8 :=
      (by decide : 2 ^ 12 ≤ 3 ^ 8).trans (Nat.pow_le_pow_left hq3 8)
    calc ordTwistedE6 (p ^ f) * (6 * f)
        ≤ (p ^ f) ^ 78 * (6 * (p ^ f)) :=
          Nat.mul_le_mul (ordTwistedE6_le_pow (p ^ f)) (Nat.mul_le_mul_left 6 hfq)
      _ ≤ bound ((p ^ f) ^ 8) :=
          pow_mul_six_le_bound hq_ge2 hL (by decide)

end Maroti
