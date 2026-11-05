module

public import Maroti.AlmostSimple.Basic
public import Maroti.MinDegree.PolarizedHeisenberg
public import CFSG.ClassicalGroups.Orthogonal.Simple

/-!
# Long-Root Heisenberg Subgroups in Orthogonal Groups

This file proves the subgroup index lower bounds `p * (p ^ f) ^ (2 * n - 3) ≤ H.index` for
`PΩ(2n + 1, p^f)` (`Maroti.index_ge_of_statedClassicalModel_pOmegaOdd`) and
`p * (p ^ f) ^ (2 * n - 4) ≤ H.index` for `PΩ⁺(2n, p^f)` and `PΩ⁻(2n, p^f)`
(`Maroti.index_ge_of_statedClassicalModel_pOmegaPlus`,
`Maroti.index_ge_of_statedClassicalModel_pOmegaMinus`) used in Step 2 of Maróti, Section 2,
page 634. For comparison, the exact minimal degrees are given in Kleidman and Liebeck,
*The Subgroup Structure of the Finite Classical Groups*, Table 5.2.A, page 175.

Let `(V, Q)` be a finite-dimensional quadratic space over a finite field `K` of characteristic `p`
with nondegenerate polar form, and let `P, R : HypPair Q` be two orthogonal hyperbolic pairs
(`P.Orth R`). Let `W = P.perp ⊓ R.perp` be the orthogonal complement of `span {P.e, P.f, R.e, R.f}`,
which has cardinality `|V| / |K|^4 = q^(dim V - 4)`.

The Eichler transformations `X(u) = eichler Q P.e u` for `u ∈ W`, `Y(v) = eichler Q R.e v` for
`v ∈ W`, and `z(s) = eichler Q P.e (s • R.e)` for `s ∈ K`
(`CFSG/ClassicalGroups/Orthogonal/Simple.lean`) descend to `ProjElementary Q` and satisfy
`PolarizedHeisenbergData` with respect to the pairing `B(u, v) = polar Q v u`, which is
nondegenerate on `W`.

Combining `PolarizedHeisenbergData.mul_card_le_index_of_ne_top` with simplicity of
`ProjElementary Q` (`isSimpleGroup_projElementary_quadOdd`,
`isSimpleGroup_projElementary_quadPlus`, and `isSimpleGroup_projElementary_quadMinus` in
`CFSG/ClassicalGroups/Orthogonal/Simple.lean`) shows that every proper subgroup `H` of a simple
orthogonal group `S` has index at least `p * (p ^ f) ^ (2 * n - 3)` for `PΩ(2n + 1, p^f)`
(`n ≥ 3`, `p` odd) and at least `p * (p ^ f) ^ (2 * n - 4)` for `PΩ⁺(2n, p^f)` and
`PΩ⁻(2n, p^f)` (`n ≥ 4`).
-/

@[expose] public section

namespace Maroti

open CFSG.Open CFSG.ClassicalGroups.Orthogonal CFSG.Assembly.LowTwoRank
  CFSG.LieType.Universal.Spin QuadraticMap Subgroup
open scoped commutatorElement

section General

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

/-- The orthogonal complement `P.perp ⊓ R.perp` of two hyperbolic pairs `P, R`. -/
def orthHeisSubmodule (P R : HypPair Q) : Submodule K V :=
  P.perp ⊓ R.perp

theorem mem_orthHeisSubmodule {P R : HypPair Q} {x : V} :
    x ∈ orthHeisSubmodule P R ↔
      (polar Q P.e x = 0 ∧ polar Q P.f x = 0) ∧ (polar Q R.e x = 0 ∧ polar Q R.f x = 0) := by
  rw [orthHeisSubmodule, Submodule.mem_inf, HypPair.mem_perp, HypPair.mem_perp]

theorem polarNondegOn_orthHeisSubmodule (hQ : (polarBilin Q).Nondegenerate) {P R : HypPair Q}
    (h : P.Orth R) : PolarNondegOn Q (orthHeisSubmodule P R) :=
  (P.polarNondegOn_perp hQ).inf_perp R (HypPair.mem_perp.mpr ⟨h.ee, h.fe⟩)
    (HypPair.mem_perp.mpr ⟨h.ef, h.ff⟩)

/-- Canonical quotient map `elementaryGroup Q →* ProjElementary Q`. -/
def toProjElementary (Q : QuadraticForm K V) : elementaryGroup Q →* ProjElementary Q :=
  QuotientGroup.mk' ((scalars K V).subgroupOf (elementaryGroup Q))

/-- First abelian factor `X : W → ProjElementary Q` given by `u ↦ eichler Q P.e u`. -/
noncomputable def orthHeisX (P R : HypPair Q) (u : orthHeisSubmodule P R) : ProjElementary Q :=
  toProjElementary Q ⟨eichler Q P.e u.1, eichler_mem_elementaryGroup Q P.e u.1⟩

/-- Second abelian factor `Y : W → ProjElementary Q` given by `v ↦ eichler Q R.e v`. -/
noncomputable def orthHeisY (P R : HypPair Q) (v : orthHeisSubmodule P R) : ProjElementary Q :=
  toProjElementary Q ⟨eichler Q R.e v.1, eichler_mem_elementaryGroup Q R.e v.1⟩

/-- Central root subgroup `z : K → ProjElementary Q` given by `s ↦ eichler Q P.e (s • R.e)`. -/
noncomputable def orthHeisZ (P R : HypPair Q) (s : K) : ProjElementary Q :=
  toProjElementary Q ⟨eichler Q P.e (s • R.e), eichler_mem_elementaryGroup Q P.e (s • R.e)⟩

/-- Commutator pairing `B(u, v) = polar Q v u` on `orthHeisSubmodule P R`. -/
def orthHeisB (P R : HypPair Q) (u v : orthHeisSubmodule P R) : K :=
  polar Q v.1 u.1

private theorem eichler_swap_span_pair {P R : HypPair Q} (h : P.Orth R) (c : K) :
    eichler Q R.e ((-c) • P.e) = eichler Q P.e (c • R.e) := by
  have hba : polar Q R.e P.e = 0 := by rw [polar_comm, h.ee]
  have h1 : polar Q R.e ((-c) • P.e) = 0 := by rw [polar_smul_right_eq, hba, mul_zero]
  have h2 : polar Q P.e (c • R.e) = 0 := by rw [polar_smul_right_eq, h.ee, mul_zero]
  refine LinearEquiv.ext fun x => ?_
  rw [eichler_apply R.Q_e h1, eichler_apply P.Q_e h2]
  simp only [polar_smul_right_eq, QuadraticMap.map_smul, smul_eq_mul, R.Q_e, P.Q_e, mul_zero,
    zero_mul, add_zero]
  module

private theorem eichler_comm_eichler_root {P R : HypPair Q} (h : P.Orth R)
    {w₁ w₂ : V} (hw₁e : polar Q P.e w₁ = 0) (hw₁b : polar Q R.e w₁ = 0)
    (hw₂e : polar Q P.e w₂ = 0) (hw₂b : polar Q R.e w₂ = 0) :
    ⁅eichler Q P.e w₁, eichler Q R.e w₂⁆ = eichler Q P.e ((polar Q w₂ w₁) • R.e) := by
  rw [commutatorElement_def]
  have hba : polar Q R.e P.e = 0 := by rw [polar_comm, h.ee]
  have hneg : polar Q R.e ((-polar Q w₂ w₁) • P.e) = 0 := by
    rw [polar_smul_right_eq, hba, mul_zero]
  have hgb : eichler Q P.e w₁ R.e = R.e := by
    rw [eichler_apply P.Q_e hw₁e]
    simp [hba, hw₁b]
  have hgw₂ : eichler Q P.e w₁ w₂ = w₂ - (polar Q w₂ w₁) • P.e := by
    rw [eichler_apply P.Q_e hw₁e]
    simp only [polar_comm Q w₂ P.e, hw₂e, mul_zero, add_zero, zero_smul]
  have hconj := eichler_conj (eichler_mem_orthogonalGroup Q P.e w₁) R.e w₂
  rw [hgb, hgw₂] at hconj
  have hsum : w₂ - (polar Q w₂ w₁) • P.e = w₂ + (-polar Q w₂ w₁) • P.e := by
    rw [sub_eq_add_neg, neg_smul]
  have hAB : eichler Q R.e w₂ * eichler Q R.e ((-polar Q w₂ w₁) • P.e) =
      eichler Q R.e ((-polar Q w₂ w₁) • P.e) * eichler Q R.e w₂ := by
    rw [eichler_mul hw₂b hneg, eichler_mul hneg hw₂b, add_comm]
  rw [hconj, hsum, ← eichler_mul hw₂b hneg, hAB, mul_assoc, mul_inv_cancel, mul_one]
  exact eichler_swap_span_pair h (polar Q w₂ w₁)

private theorem eq_zero_of_eichler_mem_scalars {P R : HypPair Q} (h : P.Orth R) {s : K}
    (hs : eichler Q P.e (s • R.e) ∈ scalars K V) : s = 0 := by
  obtain ⟨c, hc⟩ := mem_scalars.mp hs
  have h1 : eichler Q P.e (s • R.e) P.e = P.e := eichler_apply_self P.e (s • R.e)
  rw [hc P.e] at h1
  have hc1 : c = 1 := by
    have := congrArg (fun x => polar Q x P.f) h1
    simpa [polar_smul_left_eq, P.polar_ef] using this
  subst hc1
  have hw : polar Q P.e (s • R.e) = 0 := by rw [polar_smul_right_eq, h.ee, mul_zero]
  have h2 := hc R.f
  rw [one_smul, eichler_apply P.Q_e hw, polar_comm Q R.f P.e, h.ef, zero_smul, add_zero,
    mul_zero, add_zero, polar_smul_right_eq, R.polar_fe, mul_one] at h2
  have h3 : s • P.e = 0 := sub_eq_self.mp h2
  have h4 := congrArg (fun x => polar Q x P.f) h3
  simpa [polar_smul_left_eq, P.polar_ef] using h4

/-- The Eichler maps `(orthHeisX P R, orthHeisY P R, orthHeisZ P R, orthHeisB P R)` form a
polarized Heisenberg configuration in `ProjElementary Q`. -/
theorem polarizedHeisenbergData_projElementary (hQ : (polarBilin Q).Nondegenerate)
    {P R : HypPair Q} (h : P.Orth R) :
    PolarizedHeisenbergData (orthHeisX P R) (orthHeisY P R) (orthHeisZ P R) (orthHeisB P R) where
  X_add u₁ u₂ := by
    rw [orthHeisX, orthHeisX, orthHeisX, ← map_mul]
    congr 1
    apply Subtype.ext
    exact (eichler_mul (mem_orthHeisSubmodule.mp u₁.2).1.1 (mem_orthHeisSubmodule.mp u₂.2).1.1).symm
  Y_add v₁ v₂ := by
    rw [orthHeisY, orthHeisY, orthHeisY, ← map_mul]
    congr 1
    apply Subtype.ext
    exact (eichler_mul (mem_orthHeisSubmodule.mp v₁.2).2.1 (mem_orthHeisSubmodule.mp v₂.2).2.1).symm
  z_add s₁ s₂ := by
    have hp : ∀ s : K, polar Q P.e (s • R.e) = 0 := fun s => by
      rw [polar_smul_right_eq, h.ee, mul_zero]
    rw [orthHeisZ, orthHeisZ, orthHeisZ, ← map_mul]
    congr 1
    apply Subtype.ext
    change eichler Q P.e ((s₁ + s₂) • R.e) = eichler Q P.e (s₁ • R.e) * eichler Q P.e (s₂ • R.e)
    rw [add_smul, eichler_mul (hp s₁) (hp s₂)]
  z_eq_one s hs := by
    rw [orthHeisZ, toProjElementary, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf] at hs
    exact eq_zero_of_eichler_mem_scalars h hs
  commute_X_z u s := by
    have hu : polar Q P.e u.1 = 0 := (mem_orthHeisSubmodule.mp u.2).1.1
    have hs : polar Q P.e (s • R.e) = 0 := by rw [polar_smul_right_eq, h.ee, mul_zero]
    change orthHeisX P R u * orthHeisZ P R s = orthHeisZ P R s * orthHeisX P R u
    rw [orthHeisX, orthHeisZ, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    change eichler Q P.e u.1 * eichler Q P.e (s • R.e) =
      eichler Q P.e (s • R.e) * eichler Q P.e u.1
    rw [eichler_mul hu hs, eichler_mul hs hu, add_comm]
  commute_Y_z v s := by
    have hv : polar Q R.e v.1 = 0 := (mem_orthHeisSubmodule.mp v.2).2.1
    have hba : polar Q R.e P.e = 0 := by rw [polar_comm, h.ee]
    have hs : polar Q R.e ((-s) • P.e) = 0 := by rw [polar_smul_right_eq, hba, mul_zero]
    change orthHeisY P R v * orthHeisZ P R s = orthHeisZ P R s * orthHeisY P R v
    rw [orthHeisY, orthHeisZ, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    change eichler Q R.e v.1 * eichler Q P.e (s • R.e) =
      eichler Q P.e (s • R.e) * eichler Q R.e v.1
    rw [← eichler_swap_span_pair h s, eichler_mul hv hs, eichler_mul hs hv, add_comm]
  comm_X_Y u v := by
    have hue := (mem_orthHeisSubmodule.mp u.2).1.1
    have hub := (mem_orthHeisSubmodule.mp u.2).2.1
    have hve := (mem_orthHeisSubmodule.mp v.2).1.1
    have hvb := (mem_orthHeisSubmodule.mp v.2).2.1
    rw [orthHeisX, orthHeisY, orthHeisZ, ← map_commutatorElement]
    congr 1
    apply Subtype.ext
    exact eichler_comm_eichler_root h hue hub hve hvb
  B_add_left u₁ u₂ v := by
    change polar Q v.1 (u₁.1 + u₂.1) = polar Q v.1 u₁.1 + polar Q v.1 u₂.1
    exact polar_add_right Q v.1 u₁.1 u₂.1
  B_add_right u v₁ v₂ := by
    change polar Q (v₁.1 + v₂.1) u.1 = polar Q v₁.1 u.1 + polar Q v₂.1 u.1
    exact polar_add_left Q v₁.1 v₂.1 u.1
  B_surj_left u hu s := by
    have hW := polarNondegOn_orthHeisSubmodule hQ h
    have hu0 : u.1 ≠ 0 := fun h0 => hu (Subtype.ext h0)
    obtain ⟨y, hyW, hy⟩ := hW.exists_polar_ne_zero u.2 hu0
    have hy' : polar Q y u.1 ≠ 0 := by rwa [polar_comm]
    refine ⟨(s / polar Q y u.1) • ⟨y, hyW⟩, ?_⟩
    change polar Q ((s / polar Q y u.1) • y) u.1 = s
    rw [polar_smul_left_eq, div_mul_cancel₀ _ hy']
  B_surj_right v hv s := by
    have hW := polarNondegOn_orthHeisSubmodule hQ h
    have hv0 : v.1 ≠ 0 := fun h0 => hv (Subtype.ext h0)
    obtain ⟨x, hxW, hx⟩ := hW.exists_polar_ne_zero v.2 hv0
    refine ⟨(s / polar Q v.1 x) • ⟨x, hxW⟩, ?_⟩
    change polar Q v.1 ((s / polar Q v.1 x) • x) = s
    rw [polar_smul_right_eq, div_mul_cancel₀ _ hx]

/-- Decomposition `W ≃ (W ⊓ P.perp) × K × K` for any submodule `W` containing `P.e` and `P.f`. -/
def submoduleEquivInfPerp (W : Submodule K V) (P : HypPair Q) (he : P.e ∈ W) (hf : P.f ∈ W) :
    (W ⊓ P.perp : Submodule K V) × K × K ≃ W where
  toFun t :=
    ⟨t.1.1 + t.2.1 • P.e + t.2.2 • P.f,
      W.add_mem (W.add_mem t.1.2.1 (W.smul_mem _ he)) (W.smul_mem _ hf)⟩
  invFun x :=
    (⟨P.proj x.1,
      W.sub_mem (W.sub_mem x.2 (W.smul_mem _ he)) (W.smul_mem _ hf),
      P.proj_mem_perp x.1⟩,
     polar Q x.1 P.f,
     polar Q x.1 P.e)
  left_inv := by
    rintro ⟨⟨y, hyW, hyP⟩, a, b⟩
    obtain ⟨hye, hyf⟩ := HypPair.mem_perp.mp hyP
    have hpf : polar Q (y + a • P.e + b • P.f) P.f = a := by
      rw [polar_add_left, polar_add_left, polar_smul_left_eq, polar_smul_left_eq,
        polar_comm Q y P.f, hyf, P.polar_ef, P.polar_ff]
      ring
    have hpe : polar Q (y + a • P.e + b • P.f) P.e = b := by
      rw [polar_add_left, polar_add_left, polar_smul_left_eq, polar_smul_left_eq,
        polar_comm Q y P.e, hye, P.polar_ee, P.polar_fe]
      ring
    ext
    · change P.proj (y + a • P.e + b • P.f) = y
      rw [HypPair.proj, hpf, hpe]
      abel
    · exact hpf
    · exact hpe
  right_inv x := by
    apply Subtype.ext
    change P.proj x.1 + polar Q x.1 P.f • P.e + polar Q x.1 P.e • P.f = x.1
    have h := P.eq_add_proj x.1
    abel_nf at h ⊢
    exact h.symm

theorem card_submodule_inf_perp (W : Submodule K V) (P : HypPair Q) (he : P.e ∈ W) (hf : P.f ∈ W) :
    Nat.card W = Nat.card (W ⊓ P.perp : Submodule K V) * (Nat.card K * Nat.card K) := by
  rw [Nat.card_congr (submoduleEquivInfPerp W P he hf).symm, Nat.card_prod, Nat.card_prod]

theorem card_orthHeisSubmodule {P R : HypPair Q} (h : P.Orth R) :
    Nat.card V = Nat.card (orthHeisSubmodule P R) * Nat.card K ^ 4 := by
  have h1 := card_submodule_inf_perp (⊤ : Submodule K V) P Submodule.mem_top Submodule.mem_top
  rw [Nat.card_congr Submodule.topEquiv.toEquiv, top_inf_eq] at h1
  have h2 := card_submodule_inf_perp P.perp R (HypPair.mem_perp.mpr ⟨h.ee, h.fe⟩)
    (HypPair.mem_perp.mpr ⟨h.ef, h.ff⟩)
  rw [h1, h2]
  change Nat.card (orthHeisSubmodule P R) * (Nat.card K * Nat.card K) * (Nat.card K * Nat.card K) =
    Nat.card (orthHeisSubmodule P R) * Nat.card K ^ 4
  ring

/-- Minimum index of a proper subgroup in a simple `ProjElementary Q`. -/
theorem mul_card_orthHeisSubmodule_le_index [Finite K] [Finite V] {p : ℕ} [Fact p.Prime]
    [CharP K p] (hQ : (polarBilin Q).Nondegenerate) {P R : HypPair Q} (h : P.Orth R)
    [IsSimpleGroup (ProjElementary Q)] {H : Subgroup (ProjElementary Q)} (hH : H ≠ ⊤) :
    p * Nat.card (orthHeisSubmodule P R) ≤ H.index := by
  have : Finite (V ≃ₗ[K] V) :=
    Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V)) DFunLike.coe_injective
  have hW : ∀ u : orthHeisSubmodule P R, p • u = 0 := fun u => by
    rw [← Nat.cast_smul_eq_nsmul K, CharP.cast_eq_zero, zero_smul]
  exact (polarizedHeisenbergData_projElementary hQ h).mul_card_le_index_of_ne_top hW hH

end General

section Models

theorem card_orthHeisSubmodule_eq_pow {K V : Type} [Field K] [Finite K] [AddCommGroup V]
    [Module K V] [Finite V] {Q : QuadraticForm K V} {P R : HypPair Q} (h : P.Orth R)
    {q d : ℕ} (hq : Nat.card K = q) (hq0 : 0 < q) (hV : Nat.card V = q ^ (d + 4)) :
    Nat.card (orthHeisSubmodule P R) = q ^ d := by
  have hcard := card_orthHeisSubmodule h
  rw [hq, hV, pow_add] at hcard
  exact Nat.eq_of_mul_eq_mul_right (Nat.pow_pos hq0) hcard.symm

/-- Every proper subgroup `H` of `PΩ(2n + 1, p^f)` (`n ≥ 3`, `p` odd) has index at least
`p * (p ^ f) ^ (2 * n - 3)`, proved via the long-root polarized Heisenberg subgroup on
`orthHeisSubmodule`. -/
theorem index_ge_of_statedClassicalModel_pOmegaOdd {S : Type} [Group S] {n p f : ℕ}
    (h : StatedClassicalModel S .POmegaOdd n p f) {H : Subgroup S} (hH : H ≠ ⊤) :
    p * (p ^ f) ^ (2 * n - 3) ≤ H.index := by
  obtain ⟨⟨hp, hf, hn, hp2⟩, K, _, _, hK, ⟨eS⟩⟩ := h
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := Maroti.charP_of_card_eq hp hf hK
  have h2 : (2 : K) ≠ 0 := Maroti.two_ne_zero_of_charP p hp2
  have : IsSimpleGroup (ProjElementary (quadOdd n K)) := isSimpleGroup_projElementary_quadOdd h2 hn
  let e : S ≃* ProjElementary (quadOdd n K) :=
    eS.trans (statedProjEquiv (coe_quadOdd n K) (commutator_orthogonalGroup_quadOdd h2 hn))
  let P : HypPair (quadOdd n K) := oddPair K ⟨0, by omega⟩
  let R : HypPair (quadOdd n K) := oddPair K ⟨1, by omega⟩
  have hPR : P.Orth R := oddPair_orth (by simp [Fin.ext_iff])
  have hV : Nat.card (Fin n ⊕ Fin n ⊕ Unit → K) = (p ^ f) ^ ((2 * n - 3) + 4) := by
    rw [Nat.card_fun, hK, Nat.card_eq_fintype_card, Fintype.card_sum, Fintype.card_sum,
      Fintype.card_fin, Fintype.card_unit]
    congr 1
    omega
  have hW : Nat.card (orthHeisSubmodule P R) = (p ^ f) ^ (2 * n - 3) :=
    card_orthHeisSubmodule_eq_pow hPR hK (Nat.pow_pos hp.pos) hV
  have hH' : H.map e.toMonoidHom ≠ ⊤ := by
    intro htop
    apply hH
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [htop, Subgroup.map_top_of_surjective _ e.surjective]
  rw [← Subgroup.index_map_equiv H e, ← hW]
  exact mul_card_orthHeisSubmodule_le_index (nondegenerate_polarBilin_quadOdd n K h2) hPR hH'

/-- Every proper subgroup `H` of `PΩ⁺(2n, p^f)` (`n ≥ 4`) has index at least
`p * (p ^ f) ^ (2 * n - 4)`, proved via the long-root polarized Heisenberg subgroup on
`orthHeisSubmodule`. -/
theorem index_ge_of_statedClassicalModel_pOmegaPlus {S : Type} [Group S] {n p f : ℕ}
    (h : StatedClassicalModel S .POmegaPlus n p f) {H : Subgroup S} (hH : H ≠ ⊤) :
    p * (p ^ f) ^ (2 * n - 4) ≤ H.index := by
  obtain ⟨⟨hp, hf, hn⟩, K, _, _, hK, ⟨eS⟩⟩ := h
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := Maroti.charP_of_card_eq hp hf hK
  have hn3 : 3 ≤ n := by omega
  have : IsSimpleGroup (ProjElementary (quadPlus n K)) := isSimpleGroup_projElementary_quadPlus hn3
  let e : S ≃* ProjElementary (quadPlus n K) :=
    eS.trans (statedProjEquiv (coe_quadPlus n K) (commutator_orthogonalGroup_quadPlus hn3))
  let P : HypPair (quadPlus n K) := plusPair K ⟨0, by omega⟩
  let R : HypPair (quadPlus n K) := plusPair K ⟨1, by omega⟩
  have hPR : P.Orth R := plusPair_orth (by simp [Fin.ext_iff])
  have hV : Nat.card (Fin n ⊕ Fin n → K) = (p ^ f) ^ ((2 * n - 4) + 4) := by
    rw [Nat.card_fun, hK, Nat.card_eq_fintype_card, Fintype.card_sum, Fintype.card_fin]
    congr 1
    omega
  have hW : Nat.card (orthHeisSubmodule P R) = (p ^ f) ^ (2 * n - 4) :=
    card_orthHeisSubmodule_eq_pow hPR hK (Nat.pow_pos hp.pos) hV
  have hH' : H.map e.toMonoidHom ≠ ⊤ := by
    intro htop
    apply hH
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [htop, Subgroup.map_top_of_surjective _ e.surjective]
  rw [← Subgroup.index_map_equiv H e, ← hW]
  exact mul_card_orthHeisSubmodule_le_index (nondegenerate_polarBilin_quadPlus n K) hPR hH'

/-- Every proper subgroup `H` of `PΩ⁻(2n, p^f)` (`n ≥ 4`) has index at least
`p * (p ^ f) ^ (2 * n - 4)`, proved via the long-root polarized Heisenberg subgroup on
`orthHeisSubmodule`. -/
theorem index_ge_of_statedClassicalModel_pOmegaMinus {S : Type} [Group S] {n p f : ℕ}
    (h : StatedClassicalModel S .POmegaMinus n p f) {H : Subgroup S} (hH : H ≠ ⊤) :
    p * (p ^ f) ^ (2 * n - 4) ≤ H.index := by
  obtain ⟨⟨hp, hf, hn⟩, K, _, _, hK, b, c, hirr, ⟨eS⟩⟩ := h
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := Maroti.charP_of_card_eq hp hf hK
  have : IsSimpleGroup (ProjElementary (quadMinus n K b c)) :=
    isSimpleGroup_projElementary_quadMinus hn hirr
  let e : S ≃* ProjElementary (quadMinus n K b c) :=
    eS.trans (statedProjEquiv (coe_quadMinus n K b c)
      (commutator_orthogonalGroup_quadMinus hn hirr))
  let P : HypPair (quadMinus n K b c) := minusPair K b c ⟨0, by omega⟩
  let R : HypPair (quadMinus n K b c) := minusPair K b c ⟨1, by omega⟩
  have hPR : P.Orth R := minusPair_orth (by simp [Fin.ext_iff])
  have hV : Nat.card (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) = (p ^ f) ^ ((2 * n - 4) + 4) := by
    rw [Nat.card_fun, hK, Nat.card_eq_fintype_card, Fintype.card_sum, Fintype.card_sum,
      Fintype.card_fin, Fintype.card_fin]
    congr 1
    omega
  have hW : Nat.card (orthHeisSubmodule P R) = (p ^ f) ^ (2 * n - 4) :=
    card_orthHeisSubmodule_eq_pow hPR hK (Nat.pow_pos hp.pos) hV
  have hH' : H.map e.toMonoidHom ≠ ⊤ := by
    intro htop
    apply hH
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [htop, Subgroup.map_top_of_surjective _ e.surjective]
  rw [← Subgroup.index_map_equiv H e, ← hW]
  exact mul_card_orthHeisSubmodule_le_index
    (nondegenerate_polarBilin_quadMinus_of_finite n K hirr) hPR hH'

end Models

end Maroti
