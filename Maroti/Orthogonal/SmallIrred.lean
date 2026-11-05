module

public import Maroti.Orthogonal.Heisenberg

/-!
# Irreducibility of the Levi Action on the Heisenberg Quotient in Dimension 8 over `𝔽₂`

Let `(V, Q)` be an 8-dimensional quadratic space over a field `K` of cardinality 2 (`CharP K 2`)
with nondegenerate polar form, and let `P, R, P₂ : HypPair Q` be three pairwise orthogonal
hyperbolic pairs (`CFSG/ClassicalGroups/Orthogonal/Simple.lean`). Let
`W = orthHeisSubmodule P R = P.perp ⊓ R.perp` and let
`D = polarizedHeisenbergData_projElementary hQ hPR` be the polarized Heisenberg configuration in
`ProjElementary Q` from `Maroti/Orthogonal/Heisenberg.lean`.

This file proves `Maroti.heisSubgroup_le_of_levi_normal` (used for the `PΩ^±(8, 2)` cases in
Maróti, Section 2, Step 2, page 634): the Levi elements
`orthLeviS₁ P R = toProjElementary Q (eichler Q P.e R.f)`,
`orthLeviS₂ P R = toProjElementary Q (eichler Q P.f R.e)`, and
`orthLeviT P R a w = toProjElementary Q (eichler Q a.1 w.1)` for `a, w : W` normalize
`D.heisSubgroup`, centralize `orthHeisZ P R s`, and act irreducibly on
`D.heisSubgroup / D.centerSubgroup ≃ W × W`. Any subgroup `L ≤ ProjElementary Q` with
`D.centerSubgroup ≤ L ≤ D.heisSubgroup` that is normalized by `orthLeviS₁`, `orthLeviS₂`, and
`orthLeviT P R a w` and contains an element outside `D.centerSubgroup` is equal to
`D.heisSubgroup`.
-/

@[expose] public section

namespace Maroti

open CFSG.ClassicalGroups.Orthogonal QuadraticMap Subgroup

section CharTwoHelpers

variable {K V : Type*} [Field K] [CharP K 2] [AddCommGroup V] [Module K V]

omit [CharP K 2] in
theorem eq_zero_or_eq_one_of_card_two [Finite K] (hK : Nat.card K = 2) (s : K) :
    s = 0 ∨ s = 1 := by
  classical
  have := Fintype.ofFinite K
  have hcard : Fintype.card K = 2 := by rwa [← Nat.card_eq_fintype_card]
  have huniv : ({0, 1} : Finset K) = Finset.univ :=
    Finset.eq_univ_of_card _ (by rw [Finset.card_pair zero_ne_one, hcard])
  have hmem : s ∈ ({0, 1} : Finset K) := huniv ▸ Finset.mem_univ s
  simpa using hmem

theorem two_nsmul_eq_zero_of_charTwo (K : Type*) [Field K] [CharP K 2] {V : Type*}
    [AddCommGroup V] [Module K V] (v : V) : 2 • v = 0 := by
  rw [← Nat.cast_smul_eq_nsmul K, Nat.cast_two, CharTwo.two_eq_zero, zero_smul]

theorem add_self_eq_zero_of_charTwo (K : Type*) [Field K] [CharP K 2] {V : Type*}
    [AddCommGroup V] [Module K V] (v : V) : v + v = 0 := by
  rw [← two_nsmul, two_nsmul_eq_zero_of_charTwo K]

theorem two_zsmul_eq_zero_of_charTwo (K : Type*) [Field K] [CharP K 2] {V : Type*}
    [AddCommGroup V] [Module K V] (v : V) : (2 : ℤ) • v = 0 := by
  rw [two_zsmul, add_self_eq_zero_of_charTwo K]

theorem neg_eq_self_of_charTwo (K : Type*) [Field K] [CharP K 2] {V : Type*}
    [AddCommGroup V] [Module K V] (v : V) : -v = v := by
  rw [neg_eq_iff_add_eq_zero]
  exact add_self_eq_zero_of_charTwo K v

theorem sub_eq_add_of_charTwo (K : Type*) [Field K] [CharP K 2] {V : Type*}
    [AddCommGroup V] [Module K V] (u v : V) : u - v = u + v := by
  rw [sub_eq_add_neg, neg_eq_self_of_charTwo K]

variable {Q : QuadraticForm K V}

theorem eichler_mul_self_charTwo (u w : V) : eichler Q u w * eichler Q u w = 1 := by
  by_cases hw : polar Q u w = 0
  · rw [eichler_mul hw hw, add_self_eq_zero_of_charTwo K, eichler_zero_right]
  · rw [eichler_of_polar_ne_zero hw, one_mul]

theorem eichler_inv_charTwo (u w : V) : (eichler Q u w)⁻¹ = eichler Q u w :=
  inv_eq_of_mul_eq_one_right (eichler_mul_self_charTwo u w)

theorem eichler_mul_eichler_add_charTwo {x y w : V}
    (hx : Q x = 0) (hy : Q y = 0) (hxy : polar Q x y = 0)
    (hxw : polar Q x w = 0) (hyw : polar Q y w = 0) :
    eichler Q x w * eichler Q y w = eichler Q (x + y) w * eichler Q x (Q w • y) := by
  have hxy' : Q (x + y) = 0 := by
    rw [QuadraticMap.map_add Q, hx, hy, hxy]
    simp
  have hxyw : polar Q (x + y) w = 0 := by
    rw [polar_add_left, hxw, hyw, add_zero]
  have hxsy : polar Q x (Q w • y) = 0 := by
    rw [polar_smul_right, hxy, smul_zero]
  refine LinearEquiv.ext fun z => ?_
  simp only [LinearEquiv.mul_apply]
  rw [eichler_apply hx hxw, eichler_apply hy hyw,
    eichler_apply hxy' hxyw, eichler_apply hx hxsy]
  simp only [polar_add_left, polar_sub_left, polar_smul_left, polar_add_right,
    polar_smul_right, smul_eq_mul, QuadraticMap.map_smul, hy,
    polar_self_eq_zero hx, polar_self_eq_zero hy, polar_comm Q w x, polar_comm Q y x,
    polar_self, CharTwo.two_nsmul, hxy, hxw, hyw, mul_zero, zero_mul, add_zero]
  match_scalars <;> ring_nf
  all_goals simp [CharTwo.two_eq_zero]

theorem eichler_add_left_charTwo {x y w : V}
    (hx : Q x = 0) (hy : Q y = 0) (hxy : polar Q x y = 0)
    (hxw : polar Q x w = 0) (hyw : polar Q y w = 0) :
    eichler Q (x + y) w = eichler Q x w * eichler Q y w * eichler Q x (Q w • y) := by
  have h := eichler_mul_eichler_add_charTwo hx hy hxy hxw hyw
  rw [h, mul_assoc, eichler_mul_self_charTwo, mul_one]

end CharTwoHelpers

section LeviConj

variable {K V : Type*} [Field K] [CharP K 2] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

/-- First `SL₂(2)` generator `eichler Q P.e R.f` in `ProjElementary Q`. -/
noncomputable def orthLeviS₁ (P R : HypPair Q) : ProjElementary Q :=
  toProjElementary Q ⟨eichler Q P.e R.f, eichler_mem_elementaryGroup Q P.e R.f⟩

/-- Second `SL₂(2)` generator `eichler Q P.f R.e` in `ProjElementary Q`. -/
noncomputable def orthLeviS₂ (P R : HypPair Q) : ProjElementary Q :=
  toProjElementary Q ⟨eichler Q P.f R.e, eichler_mem_elementaryGroup Q P.f R.e⟩

/-- Orthogonal Levi generator `eichler Q a.1 w.1` (`a, w ∈ W`) in `ProjElementary Q`. -/
noncomputable def orthLeviT (P R : HypPair Q) (a w : orthHeisSubmodule P R) : ProjElementary Q :=
  toProjElementary Q ⟨eichler Q a.1 w.1, eichler_mem_elementaryGroup Q a.1 w.1⟩

/-- Action of `eichler Q a.1 w.1` on `orthHeisSubmodule P R`. -/
noncomputable def orthLeviAct (P R : HypPair Q) (a w u : orthHeisSubmodule P R) :
    orthHeisSubmodule P R :=
  ⟨eichler Q a.1 w.1 u.1, by
    have hg := eichler_mem_orthogonalGroup Q a.1 w.1
    obtain ⟨⟨hae, haf⟩, ⟨har, harf⟩⟩ := mem_orthHeisSubmodule.mp a.2
    obtain ⟨⟨hwe, hwf⟩, ⟨hwr, hwrf⟩⟩ := mem_orthHeisSubmodule.mp w.2
    obtain ⟨⟨hue, huf⟩, ⟨hur, hurf⟩⟩ := mem_orthHeisSubmodule.mp u.2
    have hPe : eichler Q a.1 w.1 P.e = P.e := eichler_apply_of_polar_eq_zero hae hwe
    have hPf : eichler Q a.1 w.1 P.f = P.f := eichler_apply_of_polar_eq_zero haf hwf
    have hRe : eichler Q a.1 w.1 R.e = R.e := eichler_apply_of_polar_eq_zero har hwr
    have hRf : eichler Q a.1 w.1 R.f = R.f := eichler_apply_of_polar_eq_zero harf hwrf
    refine mem_orthHeisSubmodule.mpr ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · rw [← hPe, polar_map_of_mem hg, hue]
    · rw [← hPf, polar_map_of_mem hg, huf]
    · rw [← hRe, polar_map_of_mem hg, hur]
    · rw [← hRf, polar_map_of_mem hg, hurf]⟩

theorem orthLeviS₁_inv (P R : HypPair Q) : (orthLeviS₁ P R)⁻¹ = orthLeviS₁ P R := by
  rw [orthLeviS₁, ← map_inv]
  congr 1
  exact Subtype.ext (eichler_inv_charTwo P.e R.f)

theorem orthLeviS₂_inv (P R : HypPair Q) : (orthLeviS₂ P R)⁻¹ = orthLeviS₂ P R := by
  rw [orthLeviS₂, ← map_inv]
  congr 1
  exact Subtype.ext (eichler_inv_charTwo P.f R.e)

theorem orthLeviT_inv (P R : HypPair Q) (a w : orthHeisSubmodule P R) :
    (orthLeviT P R a w)⁻¹ = orthLeviT P R a w := by
  rw [orthLeviT, ← map_inv]
  congr 1
  exact Subtype.ext (eichler_inv_charTwo a.1 w.1)

private theorem eichler_Pe_Rf_apply_Re {P R : HypPair Q} (h : P.Orth R) :
    eichler Q P.e R.f R.e = P.e + R.e := by
  rw [eichler_apply P.Q_e h.ef, polar_comm Q R.e P.e, h.ee, R.polar_ef, R.Q_f,
    zero_smul, add_zero, mul_zero, add_zero, one_smul, sub_eq_add_of_charTwo K, add_comm]

omit [CharP K 2] in
private theorem eichler_Pf_Re_apply_Pe {P R : HypPair Q} (h : P.Orth R) :
    eichler Q P.f R.e P.e = P.e + R.e := by
  rw [eichler_apply P.Q_f h.fe, P.polar_ef, h.ee, R.Q_e, one_smul, zero_mul, add_zero,
    zero_smul, sub_zero]

private theorem eichler_add_Re_charTwo {P R : HypPair Q} (h : P.Orth R) (s : K) :
    eichler Q (P.e + R.e) (s • R.e) = eichler Q P.e (s • R.e) := by
  have hQ' : Q (P.e + R.e) = 0 := by
    rw [QuadraticMap.map_add Q, P.Q_e, R.Q_e, h.ee]
    simp
  have hp1 : polar Q (P.e + R.e) (s • R.e) = 0 := by
    rw [polar_add_left, polar_smul_right_eq, polar_smul_right_eq, h.ee, R.polar_ee]
    simp
  have hp2 : polar Q P.e (s • R.e) = 0 := by
    rw [polar_smul_right_eq, h.ee, mul_zero]
  refine LinearEquiv.ext fun x => ?_
  rw [eichler_apply hQ' hp1, eichler_apply P.Q_e hp2, polar_add_right, polar_smul_right_eq,
    QuadraticMap.map_smul, R.Q_e, smul_eq_mul]
  rw [sub_eq_add_of_charTwo K, sub_eq_add_of_charTwo K]
  simp only [add_mul, mul_zero, zero_mul, add_zero, add_smul, smul_add, smul_smul,
    mul_comm s]
  abel_nf
  rw [two_zsmul_eq_zero_of_charTwo K, zero_add]

omit [CharP K 2] in
theorem conj_orthLeviS₁_X {P R : HypPair Q} (u : orthHeisSubmodule P R) :
    orthLeviS₁ P R * orthHeisX P R u * (orthLeviS₁ P R)⁻¹ = orthHeisX P R u := by
  obtain ⟨⟨hue, _⟩, ⟨_, hurf⟩⟩ := mem_orthHeisSubmodule.mp u.2
  have hu : eichler Q P.e R.f u.1 = u.1 :=
    eichler_apply_of_polar_eq_zero (by rw [polar_comm, hue]) (by rw [polar_comm, hurf])
  rw [orthLeviS₁, orthHeisX, ← map_inv, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  change eichler Q P.e R.f * eichler Q P.e u.1 * (eichler Q P.e R.f)⁻¹ = eichler Q P.e u.1
  rw [eichler_conj (eichler_mem_orthogonalGroup Q P.e R.f), eichler_apply_self, hu]

theorem conj_orthLeviS₁_Y {P R : HypPair Q} (h : P.Orth R) (v : orthHeisSubmodule P R) :
    orthLeviS₁ P R * orthHeisY P R v * (orthLeviS₁ P R)⁻¹ =
      orthHeisX P R v * orthHeisY P R v * orthHeisZ P R (Q v.1) := by
  obtain ⟨⟨hve, _⟩, ⟨hvr, hvrf⟩⟩ := mem_orthHeisSubmodule.mp v.2
  have hv : eichler Q P.e R.f v.1 = v.1 :=
    eichler_apply_of_polar_eq_zero (by rw [polar_comm, hve]) (by rw [polar_comm, hvrf])
  rw [orthLeviS₁, orthHeisY, orthHeisX, orthHeisZ, ← map_inv, ← map_mul, ← map_mul, ← map_mul,
    ← map_mul]
  congr 1
  apply Subtype.ext
  change eichler Q P.e R.f * eichler Q R.e v.1 * (eichler Q P.e R.f)⁻¹ =
    eichler Q P.e v.1 * eichler Q R.e v.1 * eichler Q P.e (Q v.1 • R.e)
  rw [eichler_conj (eichler_mem_orthogonalGroup Q P.e R.f), eichler_Pe_Rf_apply_Re h, hv,
    eichler_add_left_charTwo P.Q_e R.Q_e h.ee hve hvr]

theorem conj_orthLeviS₁_Z {P R : HypPair Q} (h : P.Orth R) (s : K) :
    orthLeviS₁ P R * orthHeisZ P R s * (orthLeviS₁ P R)⁻¹ = orthHeisZ P R s := by
  rw [orthLeviS₁, orthHeisZ, ← map_inv, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  change eichler Q P.e R.f * eichler Q P.e (s • R.e) * (eichler Q P.e R.f)⁻¹ =
    eichler Q P.e (s • R.e)
  rw [eichler_conj (eichler_mem_orthogonalGroup Q P.e R.f), eichler_apply_self, map_smul,
    eichler_Pe_Rf_apply_Re h, smul_add, add_comm (s • P.e), eichler_add_smul_self P.Q_e]

theorem conj_orthLeviS₁_normalForm (hQ : (polarBilin Q).Nondegenerate) {P R : HypPair Q}
    (h : P.Orth R) (u v : orthHeisSubmodule P R) (s : K) :
    orthLeviS₁ P R * (orthHeisX P R u * orthHeisY P R v * orthHeisZ P R s) * (orthLeviS₁ P R)⁻¹ =
      orthHeisX P R (u + v) * orthHeisY P R v * orthHeisZ P R (s + Q v.1) := by
  have D := polarizedHeisenbergData_projElementary hQ h
  have hconj : orthLeviS₁ P R * (orthHeisX P R u * orthHeisY P R v * orthHeisZ P R s) *
      (orthLeviS₁ P R)⁻¹ =
      (orthLeviS₁ P R * orthHeisX P R u * (orthLeviS₁ P R)⁻¹) *
        (orthLeviS₁ P R * orthHeisY P R v * (orthLeviS₁ P R)⁻¹) *
        (orthLeviS₁ P R * orthHeisZ P R s * (orthLeviS₁ P R)⁻¹) := by group
  rw [hconj, conj_orthLeviS₁_X, conj_orthLeviS₁_Y h, conj_orthLeviS₁_Z h]
  have h1 : orthHeisX P R u * (orthHeisX P R v * orthHeisY P R v * orthHeisZ P R (Q v.1)) *
      orthHeisZ P R s =
      (orthHeisX P R u * orthHeisX P R v) * orthHeisY P R v *
        (orthHeisZ P R s * orthHeisZ P R (Q v.1)) := by
    calc orthHeisX P R u * (orthHeisX P R v * orthHeisY P R v * orthHeisZ P R (Q v.1)) *
          orthHeisZ P R s
        = (orthHeisX P R u * orthHeisX P R v) * orthHeisY P R v *
            (orthHeisZ P R (Q v.1) * orthHeisZ P R s) := by group
      _ = (orthHeisX P R u * orthHeisX P R v) * orthHeisY P R v *
            (orthHeisZ P R s * orthHeisZ P R (Q v.1)) := by rw [(D.commute_z_z (Q v.1) s).eq]
  rw [h1, ← D.X_add, ← D.z_add]

theorem conj_orthLeviS₂_X {P R : HypPair Q} (h : P.Orth R) (u : orthHeisSubmodule P R) :
    orthLeviS₂ P R * orthHeisX P R u * (orthLeviS₂ P R)⁻¹ =
      orthHeisX P R u * orthHeisY P R u * orthHeisZ P R (Q u.1) := by
  obtain ⟨⟨hue, huf⟩, ⟨hur, _⟩⟩ := mem_orthHeisSubmodule.mp u.2
  have hu : eichler Q P.f R.e u.1 = u.1 :=
    eichler_apply_of_polar_eq_zero (by rw [polar_comm, huf]) (by rw [polar_comm, hur])
  rw [orthLeviS₂, orthHeisX, orthHeisY, orthHeisZ, ← map_inv, ← map_mul, ← map_mul, ← map_mul,
    ← map_mul]
  congr 1
  apply Subtype.ext
  change eichler Q P.f R.e * eichler Q P.e u.1 * (eichler Q P.f R.e)⁻¹ =
    eichler Q P.e u.1 * eichler Q R.e u.1 * eichler Q P.e (Q u.1 • R.e)
  rw [eichler_conj (eichler_mem_orthogonalGroup Q P.f R.e), eichler_Pf_Re_apply_Pe h, hu,
    eichler_add_left_charTwo P.Q_e R.Q_e h.ee hue hur]

omit [CharP K 2] in
theorem conj_orthLeviS₂_Y {P R : HypPair Q} (h : P.Orth R) (v : orthHeisSubmodule P R) :
    orthLeviS₂ P R * orthHeisY P R v * (orthLeviS₂ P R)⁻¹ = orthHeisY P R v := by
  obtain ⟨⟨_, hvf⟩, ⟨hvr, _⟩⟩ := mem_orthHeisSubmodule.mp v.2
  have hv : eichler Q P.f R.e v.1 = v.1 :=
    eichler_apply_of_polar_eq_zero (by rw [polar_comm, hvf]) (by rw [polar_comm, hvr])
  have hRe : eichler Q P.f R.e R.e = R.e :=
    eichler_apply_of_polar_eq_zero (by rw [polar_comm, h.fe]) R.polar_ee
  rw [orthLeviS₂, orthHeisY, ← map_inv, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  change eichler Q P.f R.e * eichler Q R.e v.1 * (eichler Q P.f R.e)⁻¹ = eichler Q R.e v.1
  rw [eichler_conj (eichler_mem_orthogonalGroup Q P.f R.e), hRe, hv]

theorem conj_orthLeviS₂_Z {P R : HypPair Q} (h : P.Orth R) (s : K) :
    orthLeviS₂ P R * orthHeisZ P R s * (orthLeviS₂ P R)⁻¹ = orthHeisZ P R s := by
  have hRe : eichler Q P.f R.e R.e = R.e :=
    eichler_apply_of_polar_eq_zero (by rw [polar_comm, h.fe]) R.polar_ee
  rw [orthLeviS₂, orthHeisZ, ← map_inv, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  change eichler Q P.f R.e * eichler Q P.e (s • R.e) * (eichler Q P.f R.e)⁻¹ =
    eichler Q P.e (s • R.e)
  rw [eichler_conj (eichler_mem_orthogonalGroup Q P.f R.e), eichler_Pf_Re_apply_Pe h,
    map_smul, hRe, eichler_add_Re_charTwo h]

theorem conj_orthLeviS₂_normalForm (hQ : (polarBilin Q).Nondegenerate) {P R : HypPair Q}
    (h : P.Orth R) (u v : orthHeisSubmodule P R) (s : K) :
    orthLeviS₂ P R * (orthHeisX P R u * orthHeisY P R v * orthHeisZ P R s) * (orthLeviS₂ P R)⁻¹ =
      orthHeisX P R u * orthHeisY P R (u + v) * orthHeisZ P R (s + Q u.1) := by
  have D := polarizedHeisenbergData_projElementary hQ h
  have hconj : orthLeviS₂ P R * (orthHeisX P R u * orthHeisY P R v * orthHeisZ P R s) *
      (orthLeviS₂ P R)⁻¹ =
      (orthLeviS₂ P R * orthHeisX P R u * (orthLeviS₂ P R)⁻¹) *
        (orthLeviS₂ P R * orthHeisY P R v * (orthLeviS₂ P R)⁻¹) *
        (orthLeviS₂ P R * orthHeisZ P R s * (orthLeviS₂ P R)⁻¹) := by group
  rw [hconj, conj_orthLeviS₂_X h, conj_orthLeviS₂_Y h, conj_orthLeviS₂_Z h]
  have hc : orthHeisZ P R (Q u.1) * orthHeisY P R v = orthHeisY P R v * orthHeisZ P R (Q u.1) :=
    (D.commute_Y_z v (Q u.1)).symm
  have h1 : (orthHeisX P R u * orthHeisY P R u * orthHeisZ P R (Q u.1)) *
      orthHeisY P R v * orthHeisZ P R s =
      orthHeisX P R u * (orthHeisY P R u * orthHeisY P R v) *
        (orthHeisZ P R s * orthHeisZ P R (Q u.1)) := by
    calc (orthHeisX P R u * orthHeisY P R u * orthHeisZ P R (Q u.1)) *
          orthHeisY P R v * orthHeisZ P R s
        = orthHeisX P R u * orthHeisY P R u * (orthHeisZ P R (Q u.1) * orthHeisY P R v) *
            orthHeisZ P R s := by group
      _ = orthHeisX P R u * (orthHeisY P R u * orthHeisY P R v) *
            (orthHeisZ P R (Q u.1) * orthHeisZ P R s) := by rw [hc]; group
      _ = orthHeisX P R u * (orthHeisY P R u * orthHeisY P R v) *
            (orthHeisZ P R s * orthHeisZ P R (Q u.1)) := by rw [(D.commute_z_z (Q u.1) s).eq]
  rw [h1, ← D.Y_add, ← D.z_add]

omit [CharP K 2] in
theorem conj_orthLeviT_X {P R : HypPair Q} (a w u : orthHeisSubmodule P R) :
    orthLeviT P R a w * orthHeisX P R u * (orthLeviT P R a w)⁻¹ =
      orthHeisX P R (orthLeviAct P R a w u) := by
  have hae := (mem_orthHeisSubmodule.mp a.2).1.1
  have hwe := (mem_orthHeisSubmodule.mp w.2).1.1
  have hPe : eichler Q a.1 w.1 P.e = P.e := eichler_apply_of_polar_eq_zero hae hwe
  rw [orthLeviT, orthHeisX, orthHeisX, ← map_inv, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  change eichler Q a.1 w.1 * eichler Q P.e u.1 * (eichler Q a.1 w.1)⁻¹ =
    eichler Q P.e (eichler Q a.1 w.1 u.1)
  rw [eichler_conj (eichler_mem_orthogonalGroup Q a.1 w.1), hPe]

omit [CharP K 2] in
theorem conj_orthLeviT_Y {P R : HypPair Q} (a w v : orthHeisSubmodule P R) :
    orthLeviT P R a w * orthHeisY P R v * (orthLeviT P R a w)⁻¹ =
      orthHeisY P R (orthLeviAct P R a w v) := by
  have har := (mem_orthHeisSubmodule.mp a.2).2.1
  have hwr := (mem_orthHeisSubmodule.mp w.2).2.1
  have hRe : eichler Q a.1 w.1 R.e = R.e := eichler_apply_of_polar_eq_zero har hwr
  rw [orthLeviT, orthHeisY, orthHeisY, ← map_inv, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  change eichler Q a.1 w.1 * eichler Q R.e v.1 * (eichler Q a.1 w.1)⁻¹ =
    eichler Q R.e (eichler Q a.1 w.1 v.1)
  rw [eichler_conj (eichler_mem_orthogonalGroup Q a.1 w.1), hRe]

omit [CharP K 2] in
theorem conj_orthLeviT_Z {P R : HypPair Q} (a w : orthHeisSubmodule P R) (s : K) :
    orthLeviT P R a w * orthHeisZ P R s * (orthLeviT P R a w)⁻¹ = orthHeisZ P R s := by
  have hae := (mem_orthHeisSubmodule.mp a.2).1.1
  have hwe := (mem_orthHeisSubmodule.mp w.2).1.1
  have har := (mem_orthHeisSubmodule.mp a.2).2.1
  have hwr := (mem_orthHeisSubmodule.mp w.2).2.1
  have hPe : eichler Q a.1 w.1 P.e = P.e := eichler_apply_of_polar_eq_zero hae hwe
  have hRe : eichler Q a.1 w.1 R.e = R.e := eichler_apply_of_polar_eq_zero har hwr
  rw [orthLeviT, orthHeisZ, ← map_inv, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  change eichler Q a.1 w.1 * eichler Q P.e (s • R.e) * (eichler Q a.1 w.1)⁻¹ =
    eichler Q P.e (s • R.e)
  rw [eichler_conj (eichler_mem_orthogonalGroup Q a.1 w.1), hPe, map_smul, hRe]

omit [CharP K 2] in
theorem conj_orthLeviT_normalForm {P R : HypPair Q} (a w u v : orthHeisSubmodule P R) (s : K) :
    orthLeviT P R a w * (orthHeisX P R u * orthHeisY P R v * orthHeisZ P R s) *
      (orthLeviT P R a w)⁻¹ =
      orthHeisX P R (orthLeviAct P R a w u) * orthHeisY P R (orthLeviAct P R a w v) *
        orthHeisZ P R s := by
  have hconj : orthLeviT P R a w * (orthHeisX P R u * orthHeisY P R v * orthHeisZ P R s) *
      (orthLeviT P R a w)⁻¹ =
      (orthLeviT P R a w * orthHeisX P R u * (orthLeviT P R a w)⁻¹) *
        (orthLeviT P R a w * orthHeisY P R v * (orthLeviT P R a w)⁻¹) *
        (orthLeviT P R a w * orthHeisZ P R s * (orthLeviT P R a w)⁻¹) := by group
  rw [hconj, conj_orthLeviT_X, conj_orthLeviT_Y, conj_orthLeviT_Z]

end LeviConj

section Irred

variable {K V : Type*} [Field K] [CharP K 2] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

private theorem orthLeviAct_add_self {P R : HypPair Q} {a w x : orthHeisSubmodule P R}
    (ha : Q a.1 = 0) (haw : polar Q a.1 w.1 = 0) :
    (orthLeviAct P R a w x + x).1 =
      polar Q x.1 a.1 • w.1 + (polar Q x.1 w.1 + Q w.1 * polar Q x.1 a.1) • a.1 := by
  change eichler Q a.1 w.1 x.1 + x.1 = _
  rw [eichler_apply ha haw, sub_eq_add_of_charTwo K]
  abel_nf
  rw [two_zsmul_eq_zero_of_charTwo K, zero_add]

private theorem mem_of_polar_eq_zero_of_polar_ne_zero {P R : HypPair Q}
    {M₀ : Submodule K (orthHeisSubmodule P R)}
    (hM₀ : ∀ a w u : orthHeisSubmodule P R, u ∈ M₀ → orthLeviAct P R a w u ∈ M₀)
    {a v y : orthHeisSubmodule P R} (ha : Q a.1 = 0) (hav : polar Q a.1 v.1 = 0)
    (hy : y ∈ M₀) (hya : polar Q y.1 a.1 = 0) (hyv : polar Q y.1 v.1 ≠ 0) :
    a ∈ M₀ := by
  have hmem : orthLeviAct P R a v y + y ∈ M₀ := M₀.add_mem (hM₀ a v y hy) hy
  have hval : orthLeviAct P R a v y + y = polar Q y.1 v.1 • a := by
    apply Subtype.ext
    rw [orthLeviAct_add_self ha hav, hya, zero_smul, zero_add, mul_zero, add_zero]
    rfl
  rw [hval] at hmem
  have h1 := M₀.smul_mem (polar Q y.1 v.1)⁻¹ hmem
  rwa [smul_smul, inv_mul_cancel₀ hyv, one_smul] at h1

/-- Any `K`-submodule `M₀` of `orthHeisSubmodule P R` that is invariant under `orthLeviAct P R a w`
for all `a, w` and contains a nonzero vector is equal to `⊤`, provided `orthHeisSubmodule P R`
contains a hyperbolic pair `P₂` with nontrivial orthogonal complement. -/
theorem eq_top_of_orthLeviAct_invariant (hQ : (polarBilin Q).Nondegenerate)
    {P R P₂ : HypPair Q} (hPR : P.Orth R) (hPP₂ : P.Orth P₂) (hRP₂ : R.Orth P₂)
    {u₀ : V} (hu₀W : u₀ ∈ orthHeisSubmodule P R) (hu₀P₂ : u₀ ∈ P₂.perp) (hu₀_ne : u₀ ≠ 0)
    {M₀ : Submodule K (orthHeisSubmodule P R)}
    (hM₀ : ∀ a w u : orthHeisSubmodule P R, u ∈ M₀ → orthLeviAct P R a w u ∈ M₀)
    {x₀ : orthHeisSubmodule P R} (hx₀ : x₀ ∈ M₀) (hx₀_ne : x₀ ≠ 0) :
    M₀ = ⊤ := by
  let e₂ : orthHeisSubmodule P R :=
    ⟨P₂.e, mem_orthHeisSubmodule.mpr ⟨⟨hPP₂.ee, hPP₂.fe⟩, ⟨hRP₂.ee, hRP₂.fe⟩⟩⟩
  let f₂ : orthHeisSubmodule P R :=
    ⟨P₂.f, mem_orthHeisSubmodule.mpr ⟨⟨hPP₂.ef, hPP₂.ff⟩, ⟨hRP₂.ef, hRP₂.ff⟩⟩⟩
  set U : Submodule K V := orthHeisSubmodule P R ⊓ P₂.perp
  have hU_nondeg : PolarNondegOn Q U :=
    (polarNondegOn_orthHeisSubmodule hQ hPR).inf_perp P₂ e₂.2 f₂.2
  have hu₀U : u₀ ∈ U := ⟨hu₀W, hu₀P₂⟩
  obtain ⟨v₁, hv₁U, hv₁_ne⟩ := hU_nondeg.exists_polar_ne_zero hu₀U hu₀_ne
  let v₀ : V := (polar Q u₀ v₁)⁻¹ • v₁
  have hv₀U : v₀ ∈ U := U.smul_mem _ hv₁U
  have hu₀v₀ : polar Q u₀ v₀ = 1 := by
    rw [polar_smul_right_eq, inv_mul_cancel₀ hv₁_ne]
  let w₀ : orthHeisSubmodule P R := ⟨u₀, hu₀W⟩
  let v₀' : orthHeisSubmodule P R := ⟨v₀, hv₀U.1⟩
  have he₂w₀ : polar Q e₂.1 w₀.1 = 0 := (HypPair.mem_perp.mp hu₀P₂).1
  have he₂v₀ : polar Q e₂.1 v₀'.1 = 0 := (HypPair.mem_perp.mp hv₀U.2).1
  have hf₂w₀ : polar Q f₂.1 w₀.1 = 0 := (HypPair.mem_perp.mp hu₀P₂).2
  have hf₂v₀ : polar Q f₂.1 v₀'.1 = 0 := (HypPair.mem_perp.mp hv₀U.2).2
  have he₂_or_f₂ : e₂ ∈ M₀ ∨ f₂ ∈ M₀ := by
    by_cases hxe : polar Q x₀.1 e₂.1 ≠ 0
    · left
      let y := orthLeviAct P R e₂ w₀ x₀ + x₀
      have hyM : y ∈ M₀ := M₀.add_mem (hM₀ e₂ w₀ x₀ hx₀) hx₀
      have hy_val : y.1 = polar Q x₀.1 e₂.1 • u₀ +
          (polar Q x₀.1 u₀ + Q u₀ * polar Q x₀.1 e₂.1) • P₂.e :=
        orthLeviAct_add_self P₂.Q_e he₂w₀
      have hye : polar Q y.1 e₂.1 = 0 := by
        change polar Q y.1 P₂.e = 0
        rw [hy_val, polar_add_left, polar_smul_left_eq, polar_smul_left_eq,
          polar_comm Q u₀ P₂.e, he₂w₀, P₂.polar_ee, mul_zero, mul_zero, add_zero]
      have hyv : polar Q y.1 v₀'.1 ≠ 0 := by
        rw [hy_val, polar_add_left, polar_smul_left_eq, polar_smul_left_eq,
          hu₀v₀, he₂v₀, mul_one, mul_zero, add_zero]
        exact hxe
      exact mem_of_polar_eq_zero_of_polar_ne_zero hM₀ P₂.Q_e he₂v₀ hyM hye hyv
    · push Not at hxe
      by_cases hxf : polar Q x₀.1 f₂.1 ≠ 0
      · right
        let y := orthLeviAct P R f₂ w₀ x₀ + x₀
        have hyM : y ∈ M₀ := M₀.add_mem (hM₀ f₂ w₀ x₀ hx₀) hx₀
        have hy_val : y.1 = polar Q x₀.1 f₂.1 • u₀ +
            (polar Q x₀.1 u₀ + Q u₀ * polar Q x₀.1 f₂.1) • P₂.f :=
          orthLeviAct_add_self P₂.Q_f hf₂w₀
        have hyf : polar Q y.1 f₂.1 = 0 := by
          change polar Q y.1 P₂.f = 0
          rw [hy_val, polar_add_left, polar_smul_left_eq, polar_smul_left_eq,
            polar_comm Q u₀ P₂.f, hf₂w₀, P₂.polar_ff, mul_zero, mul_zero, add_zero]
        have hyv : polar Q y.1 v₀'.1 ≠ 0 := by
          rw [hy_val, polar_add_left, polar_smul_left_eq, polar_smul_left_eq,
            hu₀v₀, hf₂v₀, mul_one, mul_zero, add_zero]
          exact hxf
        exact mem_of_polar_eq_zero_of_polar_ne_zero hM₀ P₂.Q_f hf₂v₀ hyM hyf hyv
      · push Not at hxf
        left
        have hxU : x₀.1 ∈ U := ⟨x₀.2, HypPair.mem_perp.mpr ⟨by rw [polar_comm, hxe],
          by rw [polar_comm, hxf]⟩⟩
        have hx0 : x₀.1 ≠ 0 := fun h => hx₀_ne (Subtype.ext h)
        obtain ⟨v, hvU, hxv⟩ := hU_nondeg.exists_polar_ne_zero hxU hx0
        let v' : orthHeisSubmodule P R := ⟨v, hvU.1⟩
        have he₂v' : polar Q e₂.1 v'.1 = 0 := (HypPair.mem_perp.mp hvU.2).1
        exact mem_of_polar_eq_zero_of_polar_ne_zero hM₀ P₂.Q_e he₂v' hx₀ hxe hxv
  have h_step_w : ∀ {a b : orthHeisSubmodule P R},
      Q b.1 = 0 → polar Q a.1 b.1 = 1 → a ∈ M₀ →
      (∀ w : orthHeisSubmodule P R, w.1 ∈ P₂.perp → polar Q b.1 w.1 = 0 ∧ polar Q a.1 w.1 = 0) →
      ∀ w : orthHeisSubmodule P R, w.1 ∈ P₂.perp → w + Q w.1 • b ∈ M₀ := by
    intro a b hb hab haM hperp w hwP₂
    obtain ⟨hbw, haw⟩ := hperp w hwP₂
    have hmem : orthLeviAct P R b w a + a ∈ M₀ := M₀.add_mem (hM₀ b w a haM) haM
    have hval : orthLeviAct P R b w a + a = w + Q w.1 • b := by
      apply Subtype.ext
      rw [orthLeviAct_add_self hb hbw, hab, haw, one_smul, zero_add, mul_one]
      rfl
    rwa [hval] at hmem
  have h_other : ∀ {a b : orthHeisSubmodule P R},
      Q b.1 = 0 → polar Q a.1 b.1 = 1 → a ∈ M₀ →
      (∀ w : orthHeisSubmodule P R, w.1 ∈ P₂.perp → polar Q b.1 w.1 = 0 ∧ polar Q a.1 w.1 = 0) →
      b ∈ M₀ := by
    intro a b hb hab haM hperp
    have h1 : w₀ + Q w₀.1 • b ∈ M₀ := h_step_w hb hab haM hperp w₀ hu₀P₂
    have h2 : v₀' + Q v₀'.1 • b ∈ M₀ := h_step_w hb hab haM hperp v₀' hv₀U.2
    have h3 : (w₀ + v₀') + Q (w₀ + v₀').1 • b ∈ M₀ :=
      h_step_w hb hab haM hperp (w₀ + v₀') (P₂.perp.add_mem hu₀P₂ hv₀U.2)
    have hsum : (w₀ + Q w₀.1 • b) + (v₀' + Q v₀'.1 • b) + ((w₀ + v₀') + Q (w₀ + v₀').1 • b) ∈ M₀ :=
      M₀.add_mem (M₀.add_mem h1 h2) h3
    have heq : (w₀ + Q w₀.1 • b) + (v₀' + Q v₀'.1 • b) + ((w₀ + v₀') + Q (w₀ + v₀').1 • b) = b := by
      have hQadd : Q (w₀ + v₀').1 = Q u₀ + Q v₀ + 1 := by
        change Q (u₀ + v₀) = Q u₀ + Q v₀ + 1
        rw [QuadraticMap.map_add Q, hu₀v₀]
      apply Subtype.ext
      change (u₀ + Q u₀ • b.1) + (v₀ + Q v₀ • b.1) + ((u₀ + v₀) + Q (w₀ + v₀').1 • b.1) = b.1
      rw [hQadd, add_smul, add_smul, one_smul]
      abel_nf
      simp [two_zsmul_eq_zero_of_charTwo K]
    rwa [heq] at hsum
  have hperp_ef : ∀ w : orthHeisSubmodule P R, w.1 ∈ P₂.perp →
      polar Q f₂.1 w.1 = 0 ∧ polar Q e₂.1 w.1 = 0 := fun w hw =>
    ⟨(HypPair.mem_perp.mp hw).2, (HypPair.mem_perp.mp hw).1⟩
  have hperp_fe : ∀ w : orthHeisSubmodule P R, w.1 ∈ P₂.perp →
      polar Q e₂.1 w.1 = 0 ∧ polar Q f₂.1 w.1 = 0 := fun w hw =>
    ⟨(HypPair.mem_perp.mp hw).1, (HypPair.mem_perp.mp hw).2⟩
  obtain ⟨he₂M, hf₂M⟩ : e₂ ∈ M₀ ∧ f₂ ∈ M₀ := by
    rcases he₂_or_f₂ with he | hf
    · exact ⟨he, h_other P₂.Q_f P₂.polar_ef he hperp_ef⟩
    · exact ⟨h_other P₂.Q_e P₂.polar_fe hf hperp_fe, hf⟩
  rw [eq_top_iff]
  intro u _
  let u_proj : orthHeisSubmodule P R :=
    ⟨P₂.proj u.1,
      (orthHeisSubmodule P R).sub_mem
        ((orthHeisSubmodule P R).sub_mem u.2 ((orthHeisSubmodule P R).smul_mem _ e₂.2))
        ((orthHeisSubmodule P R).smul_mem _ f₂.2)⟩
  have hu_proj_perp : u_proj.1 ∈ P₂.perp := P₂.proj_mem_perp u.1
  have hu_proj_add : u_proj + Q u_proj.1 • f₂ ∈ M₀ :=
    h_step_w P₂.Q_f P₂.polar_ef he₂M hperp_ef u_proj hu_proj_perp
  have hu_projM : u_proj ∈ M₀ := by
    have h := M₀.add_mem hu_proj_add (M₀.smul_mem (Q u_proj.1) hf₂M)
    rwa [add_assoc, add_self_eq_zero_of_charTwo K, add_zero] at h
  have hu_eq : u = polar Q u.1 P₂.f • e₂ + polar Q u.1 P₂.e • f₂ + u_proj := by
    apply Subtype.ext
    exact P₂.eq_add_proj u.1
  rw [hu_eq]
  exact M₀.add_mem (M₀.add_mem (M₀.smul_mem _ he₂M) (M₀.smul_mem _ hf₂M)) hu_projM

/-- Main irreducibility theorem on `D.heisSubgroup`: if `L ≤ ProjElementary Q` contains
`orthHeisZ P R s` for all `s`, is contained in `D.heisSubgroup`, is normalized by `orthLeviS₁`,
`orthLeviS₂`, and `orthLeviT P R a w`, and contains an element `g₀ ∈ L` not of the form
`orthHeisZ P R s`, then `D.heisSubgroup ≤ L`. -/
theorem heisSubgroup_le_of_levi_normal [Finite K] (hK : Nat.card K = 2)
    (hQ : (polarBilin Q).Nondegenerate)
    {P R P₂ : HypPair Q} (hPR : P.Orth R) (hPP₂ : P.Orth P₂) (hRP₂ : R.Orth P₂)
    {u₀ : V} (hu₀W : u₀ ∈ orthHeisSubmodule P R) (hu₀P₂ : u₀ ∈ P₂.perp) (hu₀_ne : u₀ ≠ 0)
    {L : Subgroup (ProjElementary Q)}
    (hZL : ∀ s : K, orthHeisZ P R s ∈ L)
    (hL_le : L ≤ (polarizedHeisenbergData_projElementary hQ hPR).heisSubgroup)
    (hS₁ : ∀ g ∈ L, orthLeviS₁ P R * g * (orthLeviS₁ P R)⁻¹ ∈ L)
    (hS₂ : ∀ g ∈ L, orthLeviS₂ P R * g * (orthLeviS₂ P R)⁻¹ ∈ L)
    (hT : ∀ a w : orthHeisSubmodule P R, ∀ g ∈ L,
      orthLeviT P R a w * g * (orthLeviT P R a w)⁻¹ ∈ L)
    {g₀ : ProjElementary Q} (hg₀L : g₀ ∈ L) (hg₀_not_Z : ∀ s : K, g₀ ≠ orthHeisZ P R s) :
    (polarizedHeisenbergData_projElementary hQ hPR).heisSubgroup ≤ L := by
  let D := polarizedHeisenbergData_projElementary hQ hPR
  have hmem_iff : ∀ u v (s : K),
      orthHeisX P R u * orthHeisY P R v * orthHeisZ P R s ∈ L ↔
        orthHeisX P R u * orthHeisY P R v * orthHeisZ P R 0 ∈ L := by
    intro u v s
    rw [D.z_zero, mul_one]
    exact ⟨fun h => by
      have h1 := L.mul_mem h (L.inv_mem (hZL s))
      rwa [mul_inv_cancel_right] at h1,
      fun h => L.mul_mem h (hZL s)⟩
  have hmul_mem : ∀ {u₁ v₁ u₂ v₂},
      orthHeisX P R u₁ * orthHeisY P R v₁ * orthHeisZ P R 0 ∈ L →
      orthHeisX P R u₂ * orthHeisY P R v₂ * orthHeisZ P R 0 ∈ L →
      orthHeisX P R (u₁ + u₂) * orthHeisY P R (v₁ + v₂) * orthHeisZ P R 0 ∈ L := by
    intro u₁ v₁ u₂ v₂ h1 h2
    have hm := L.mul_mem h1 h2
    rw [D.mul_normalForm, hmem_iff] at hm
    exact hm
  have hproj_Y : ∀ {u v},
      orthHeisX P R u * orthHeisY P R v * orthHeisZ P R 0 ∈ L →
      orthHeisX P R v * orthHeisY P R 0 * orthHeisZ P R 0 ∈ L := by
    intro u v h
    have hc := hS₁ _ h
    rw [conj_orthLeviS₁_normalForm hQ hPR, hmem_iff] at hc
    have hadd := hmul_mem hc h
    have huvu : u + v + u = v := by
      rw [add_comm u v, add_assoc, add_self_eq_zero_of_charTwo K, add_zero]
    rwa [huvu, add_self_eq_zero_of_charTwo K] at hadd
  have hproj_X : ∀ {u v},
      orthHeisX P R u * orthHeisY P R v * orthHeisZ P R 0 ∈ L →
      orthHeisX P R 0 * orthHeisY P R u * orthHeisZ P R 0 ∈ L := by
    intro u v h
    have hc := hS₂ _ h
    rw [conj_orthLeviS₂_normalForm hQ hPR, hmem_iff] at hc
    have hadd := hmul_mem hc h
    have huvu : u + v + v = u := by
      rw [add_assoc, add_self_eq_zero_of_charTwo K, add_zero]
    rwa [add_self_eq_zero_of_charTwo K, huvu] at hadd
  let M₀ : Submodule K (orthHeisSubmodule P R) :=
    { carrier := { u | orthHeisX P R u * orthHeisY P R 0 * orthHeisZ P R 0 ∈ L }
      add_mem' := fun {u₁ u₂} h1 h2 => by
        simpa [add_zero] using hmul_mem h1 h2
      zero_mem' := by
        change orthHeisX P R 0 * orthHeisY P R 0 * orthHeisZ P R 0 ∈ L
        rw [D.X_zero, D.Y_zero, D.z_zero, mul_one, mul_one]
        exact L.one_mem
      smul_mem' := fun c {u} hu => by
        rcases eq_zero_or_eq_one_of_card_two hK c with rfl | rfl
        · change orthHeisX P R (0 • u) * orthHeisY P R 0 * orthHeisZ P R 0 ∈ L
          rw [zero_smul, D.X_zero, D.Y_zero, D.z_zero, mul_one, mul_one]
          exact L.one_mem
        · rwa [one_smul] }
  have hM₀_act : ∀ a w u : orthHeisSubmodule P R, u ∈ M₀ → orthLeviAct P R a w u ∈ M₀ := by
    intro a w u hu
    change orthHeisX P R (orthLeviAct P R a w u) * orthHeisY P R 0 * orthHeisZ P R 0 ∈ L
    have h0 : orthLeviAct P R a w 0 = 0 := Subtype.ext (map_zero _)
    have hc := hT a w _ hu
    rwa [conj_orthLeviT_normalForm, h0] at hc
  obtain ⟨u₀', v₀', s₀', rfl⟩ := hL_le hg₀L
  have huv_ne : u₀' ≠ 0 ∨ v₀' ≠ 0 := by
    by_contra! h0
    rw [h0.1, h0.2, D.X_zero, D.Y_zero, one_mul, one_mul] at hg₀_not_Z
    exact hg₀_not_Z s₀' rfl
  have hg₀' : orthHeisX P R u₀' * orthHeisY P R v₀' * orthHeisZ P R 0 ∈ L :=
    (hmem_iff u₀' v₀' s₀').mp hg₀L
  have hex_M₀ : ∃ x₀ ∈ M₀, x₀ ≠ 0 := by
    rcases huv_ne with hu | hv
    · exact ⟨u₀', hproj_Y (hproj_X hg₀'), hu⟩
    · exact ⟨v₀', hproj_Y hg₀', hv⟩
  obtain ⟨x₀, hx₀M, hx₀_ne⟩ := hex_M₀
  have hM₀_top : M₀ = ⊤ :=
    eq_top_of_orthLeviAct_invariant hQ hPR hPP₂ hRP₂ hu₀W hu₀P₂ hu₀_ne hM₀_act hx₀M hx₀_ne
  rintro _ ⟨u, v, s, rfl⟩
  rw [hmem_iff]
  have huM : u ∈ M₀ := hM₀_top ▸ Submodule.mem_top
  have hvM : v ∈ M₀ := hM₀_top ▸ Submodule.mem_top
  have hvY : orthHeisX P R 0 * orthHeisY P R v * orthHeisZ P R 0 ∈ L := hproj_X hvM
  simpa [add_zero, zero_add] using hmul_mem huM hvY

end Irred

end Maroti
