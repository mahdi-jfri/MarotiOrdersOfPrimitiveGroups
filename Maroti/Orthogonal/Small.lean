module

public import Maroti.Orthogonal.OrderBound
public import Maroti.Orthogonal.SmallIrred

/-!
# Minimum Degree Bounds for `PΩ⁺(8, 2)` and `PΩ⁻(8, 2)` and the Even Orthogonal Maróti Theorems

This file proves the subgroup index lower bound `64 ≤ H.index` for every proper subgroup `H` of
`PΩ⁺(8, 2)` and `PΩ⁻(8, 2)`, where the general Heisenberg bound `p * q ^ (2n - 4) = 32` is below
the Maróti threshold (`n₀ = 38` for `PΩ⁺(8, 2)` and `n₀ = 33` for `PΩ⁻(8, 2)`), and assembles the
even orthogonal cases `Maroti.orthogonalPlusCase` and `Maroti.orthogonalMinusCase` of Theorem 1.1
(Maróti, Section 2, Step 2, page 634). For comparison, the exact minimal degrees are given in
Kleidman and Liebeck, *The Subgroup Structure of the Finite Classical Groups*, Table 5.2.A,
page 175.

## Method for `PΩ^±(8, 2)`
Let `(V, Q)` be an 8-dimensional quadratic space over a field `K` of cardinality 2 with
nondegenerate polar form, and let `P, R, P₂ : HypPair Q` be three pairwise orthogonal hyperbolic
pairs such that `orthHeisSubmodule P R ⊓ P₂.perp` contains a nonzero vector `u₀`. Let
`D = polarizedHeisenbergData_projElementary hQ hPR` be the polarized Heisenberg data in
`G = ProjElementary Q`, with Heisenberg subgroup `D.heisSubgroup` of order `2 ^ 9 = 512` and
central subgroup `D.centerSubgroup = {1, z₁}` (`z₁ = orthHeisZ P R 1`).

Let `M = orthHeisNormCentralizer hQ hPR ≤ G` be the intersection of the normalizer of
`D.heisSubgroup` and the centralizer of `z₁`. By `Maroti/Orthogonal/SmallIrred.lean`, `M` contains
`D.heisSubgroup` together with the Levi generators `orthLeviS₁ P R`, `orthLeviS₂ P R`, and
`orthLeviT P R a w`. For any subgroup `H' ≤ M` not containing `z₁`:
1. The relative index `H'.relIndex Q'` (`Q' = D.heisSubgroup.subgroupOf M`) is at least `32` and
   divides `512`. If `H'.relIndex Q' ≠ 32`, then `64 ≤ H'.relIndex Q' ≤ H'.index`.
2. If `H'.relIndex Q' = 32` and `2 ≤ (H' ⊔ Q').index`, then
   `64 = 32 * 2 ≤ H'.relIndex Q' * (H' ⊔ Q').index ≤ H'.index`.
3. If `H'.relIndex Q' = 32` and `(H' ⊔ Q').index = 1` (`H' ⊔ Q' = ⊤`), then `L' = (H' ⊓ Q') ⊔ ⟨z₁⟩`
   is normalized by both `H'` and `Q'`, hence normal in `M`, and has cardinality at least `16 > 2`.
   By `heisSubgroup_le_of_levi_normal`, `L' = Q'`. On the other hand `[L', L'] ≤ H' ⊓ Q'`, so
   `z₁ = ⁅orthHeisX P R P₂.e, orthHeisY P R P₂.f⁆ ∈ H'`, contradicting `z₁ ∉ H'`.

Thus every subgroup of `M` not containing `z₁` has index at least `64`, so every proper subgroup of
`G` (when `G` is simple) has index at least `64`.
-/

@[expose] public section

namespace Maroti

open CFSG.ClassicalGroups.Orthogonal CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.LieType.Universal.Spin QuadraticMap Subgroup
open scoped commutatorElement

section Helpers

private lemma le_64_of_dvd_512 {d : ℕ} (h32 : 32 ≤ d) (hdvd : d ∣ 2 ^ 9) (hne : d ≠ 32) :
    64 ≤ d := by
  obtain ⟨k, hk, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  revert h32 hne
  revert k
  decide

end Helpers

section NormCentralizer

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

/-- The subgroup of `ProjElementary Q` normalizing `D.heisSubgroup` and centralizing
`orthHeisZ P R 1`. -/
noncomputable def orthHeisNormCentralizer (hQ : (polarBilin Q).Nondegenerate) {P R : HypPair Q}
    (hPR : P.Orth R) : Subgroup (ProjElementary Q) :=
  Subgroup.normalizer
      ((polarizedHeisenbergData_projElementary hQ hPR).heisSubgroup : Set (ProjElementary Q)) ⊓
    Subgroup.centralizer {orthHeisZ P R 1}

theorem orthHeisZ_mem_heisSubgroup (hQ : (polarBilin Q).Nondegenerate) {P R : HypPair Q}
    (hPR : P.Orth R) (s : K) :
    orthHeisZ P R s ∈ (polarizedHeisenbergData_projElementary hQ hPR).heisSubgroup := by
  let D := polarizedHeisenbergData_projElementary hQ hPR
  exact ⟨0, 0, s, by rw [D.X_zero, D.Y_zero, one_mul, one_mul]⟩

theorem heisSubgroup_le_orthHeisNormCentralizer (hQ : (polarBilin Q).Nondegenerate)
    {P R : HypPair Q} (hPR : P.Orth R) :
    (polarizedHeisenbergData_projElementary hQ hPR).heisSubgroup ≤
      orthHeisNormCentralizer hQ hPR := by
  let D := polarizedHeisenbergData_projElementary hQ hPR
  intro g hg
  rw [orthHeisNormCentralizer, Subgroup.mem_inf]
  refine ⟨Subgroup.le_normalizer hg, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  rintro _ rfl
  obtain ⟨u, v, s, rfl⟩ := hg
  exact (((D.commute_X_z u 1).mul_left (D.commute_Y_z v 1)).mul_left (D.commute_z_z s 1)).symm

private theorem mem_normalizer_heisSubgroup_of_inv_eq_self (hQ : (polarBilin Q).Nondegenerate)
    {P R : HypPair Q} (hPR : P.Orth R) {g : ProjElementary Q} (hinv : g⁻¹ = g)
    (hconj : ∀ x ∈ (polarizedHeisenbergData_projElementary hQ hPR).heisSubgroup,
      g * x * g⁻¹ ∈ (polarizedHeisenbergData_projElementary hQ hPR).heisSubgroup) :
    g ∈ Subgroup.normalizer
      ((polarizedHeisenbergData_projElementary hQ hPR).heisSubgroup : Set (ProjElementary Q)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact hconj x
  · intro hgx
    have h1 := hconj (g * x * g⁻¹) hgx
    have h2 : g * (g * x * g⁻¹) * g⁻¹ = x := by
      calc g * (g * x * g⁻¹) * g⁻¹ = g⁻¹ * (g * x * g⁻¹) * g := by rw [hinv]
        _ = x := by group
    rwa [h2] at h1

variable [CharP K 2]

theorem orthLeviS₁_mem_orthHeisNormCentralizer (hQ : (polarBilin Q).Nondegenerate)
    {P R : HypPair Q} (hPR : P.Orth R) :
    orthLeviS₁ P R ∈ orthHeisNormCentralizer hQ hPR := by
  rw [orthHeisNormCentralizer, Subgroup.mem_inf]
  refine ⟨mem_normalizer_heisSubgroup_of_inv_eq_self hQ hPR (orthLeviS₁_inv P R) ?_, ?_⟩
  · rintro _ ⟨u, v, s, rfl⟩
    rw [conj_orthLeviS₁_normalForm hQ hPR]
    exact ⟨u + v, v, s + Q v.1, rfl⟩
  · rw [Subgroup.mem_centralizer_iff]
    rintro _ rfl
    exact (mul_inv_eq_iff_eq_mul.mp (conj_orthLeviS₁_Z hPR 1)).symm

theorem orthLeviS₂_mem_orthHeisNormCentralizer (hQ : (polarBilin Q).Nondegenerate)
    {P R : HypPair Q} (hPR : P.Orth R) :
    orthLeviS₂ P R ∈ orthHeisNormCentralizer hQ hPR := by
  rw [orthHeisNormCentralizer, Subgroup.mem_inf]
  refine ⟨mem_normalizer_heisSubgroup_of_inv_eq_self hQ hPR (orthLeviS₂_inv P R) ?_, ?_⟩
  · rintro _ ⟨u, v, s, rfl⟩
    rw [conj_orthLeviS₂_normalForm hQ hPR]
    exact ⟨u, u + v, s + Q u.1, rfl⟩
  · rw [Subgroup.mem_centralizer_iff]
    rintro _ rfl
    exact (mul_inv_eq_iff_eq_mul.mp (conj_orthLeviS₂_Z hPR 1)).symm

theorem orthLeviT_mem_orthHeisNormCentralizer (hQ : (polarBilin Q).Nondegenerate)
    {P R : HypPair Q} (hPR : P.Orth R) (a w : orthHeisSubmodule P R) :
    orthLeviT P R a w ∈ orthHeisNormCentralizer hQ hPR := by
  rw [orthHeisNormCentralizer, Subgroup.mem_inf]
  refine ⟨mem_normalizer_heisSubgroup_of_inv_eq_self hQ hPR (orthLeviT_inv P R a w) ?_, ?_⟩
  · rintro _ ⟨u, v, s, rfl⟩
    rw [conj_orthLeviT_normalForm]
    exact ⟨orthLeviAct P R a w u, orthLeviAct P R a w v, s, rfl⟩
  · rw [Subgroup.mem_centralizer_iff]
    rintro _ rfl
    exact (mul_inv_eq_iff_eq_mul.mp (conj_orthLeviT_Z a w 1)).symm

end NormCentralizer

section SmallIndexBound

variable {K V : Type*} [Field K] [CharP K 2] [Finite K] [AddCommGroup V] [Module K V] [Finite V]
  {Q : QuadraticForm K V}

/-- Every subgroup `H'` of `M = orthHeisNormCentralizer hQ hPR` not containing `orthHeisZ P R 1`
has index at least `64` when `Nat.card K = 2` and `Nat.card (orthHeisSubmodule P R) = 16`. -/
theorem index_ge_64_of_not_zpowers_le (hK : Nat.card K = 2)
    (hQ : (polarBilin Q).Nondegenerate)
    {P R P₂ : HypPair Q} (hPR : P.Orth R) (hPP₂ : P.Orth P₂) (hRP₂ : R.Orth P₂)
    {u₀ : V} (hu₀W : u₀ ∈ orthHeisSubmodule P R) (hu₀P₂ : u₀ ∈ P₂.perp) (hu₀_ne : u₀ ≠ 0)
    (hW : Nat.card (orthHeisSubmodule P R) = 16)
    {H' : Subgroup (orthHeisNormCentralizer hQ hPR)}
    (hzH' : ¬ Subgroup.zpowers
      (⟨orthHeisZ P R 1, heisSubgroup_le_orthHeisNormCentralizer hQ hPR
        (orthHeisZ_mem_heisSubgroup hQ hPR 1)⟩ : orthHeisNormCentralizer hQ hPR) ≤ H') :
    64 ≤ H'.index := by
  have : Finite (V ≃ₗ[K] V) :=
    Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V)) DFunLike.coe_injective
  let D := polarizedHeisenbergData_projElementary hQ hPR
  let M := orthHeisNormCentralizer hQ hPR
  have hQM : D.heisSubgroup ≤ M := heisSubgroup_le_orthHeisNormCentralizer hQ hPR
  let Q' : Subgroup M := D.heisSubgroup.subgroupOf M
  let zM : M := ⟨orthHeisZ P R 1, hQM (orthHeisZ_mem_heisSubgroup hQ hPR 1)⟩
  have hzM_Q' : zM ∈ Q' := orthHeisZ_mem_heisSubgroup hQ hPR 1
  have hz_not_mem : zM ∉ H' := fun h => hzH' (Subgroup.zpowers_le.mpr h)
  have hQ'_norm : Q'.Normal := by
    refine ⟨fun q hq m => ?_⟩
    exact ((Subgroup.mem_normalizer_iff.mp m.2.1) q.1).mp hq
  let eQ : D.heisSubgroup ≃* Q' :=
    { toFun := fun q => ⟨⟨q.1, hQM q.2⟩, q.2⟩
      invFun := fun q => ⟨q.1.1, q.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcardQ : Nat.card D.heisSubgroup = 2 ^ 9 := by
    rw [← Nat.card_congr D.heisEquiv, Nat.card_prod, Nat.card_prod, hW, hK]
    norm_num
  have hcardQ' : Nat.card Q' = 2 ^ 9 := (Nat.card_congr eQ.symm.toEquiv).trans hcardQ
  let K₀ : Subgroup D.heisSubgroup := (H'.subgroupOf Q').comap eQ.toMonoidHom
  have hK₀_idx : K₀.index = H'.relIndex Q' :=
    Subgroup.index_comap_of_surjective (H'.subgroupOf Q') eQ.surjective
  have hnot_Z_le_K₀ : ¬ D.centerSubgroup ≤ K₀ := by
    intro hle
    have hz1_center : (⟨orthHeisZ P R 1, orthHeisZ_mem_heisSubgroup hQ hPR 1⟩ : D.heisSubgroup) ∈
        D.centerSubgroup :=
      ⟨1, by rw [D.X_zero, D.Y_zero, one_mul, one_mul]⟩
    exact hz_not_mem (hle hz1_center)
  have h32 : 32 ≤ H'.relIndex Q' := by
    rw [← hK₀_idx]
    have hm : 16 ^ 2 ≤ D.centerSubgroup.index := by
      rw [D.index_centerSubgroup, hW]
    exact mul_le_index_of_not_le (p := 2)
      D.centerSubgroup_le_center
      D.commutator_mem_centerSubgroup
      (fun _ hq => D.pow_p_eq_one_of_mem_centerSubgroup hq)
      (D.pow_p_mem_centerSubgroup (two_nsmul_eq_zero_of_charTwo K))
      (fun _ hq _ hz => D.exists_commutator_eq_of_not_mem hq hz)
      hnot_Z_le_K₀ hm
  have hdvd512 : H'.relIndex Q' ∣ 2 ^ 9 := by
    rw [← hcardQ, ← hK₀_idx]
    exact Subgroup.index_dvd_card K₀
  have hH'_mul : H'.relIndex Q' * (H' ⊔ Q').index ≤ H'.index := by
    rw [← Subgroup.relIndex_mul_index (le_sup_left : H' ≤ H' ⊔ Q')]
    exact Nat.mul_le_mul_right _ (relIndex_le_relIndex_of_le H' Q' (H' ⊔ Q') le_sup_right)
  by_cases hrel32 : H'.relIndex Q' ≠ 32
  · have h64 : 64 ≤ H'.relIndex Q' := le_64_of_dvd_512 h32 hdvd512 hrel32
    have hpos : 1 ≤ (H' ⊔ Q').index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    exact (Nat.mul_le_mul h64 hpos).trans hH'_mul
  · push Not at hrel32
    by_cases hsup2 : 2 ≤ (H' ⊔ Q').index
    · calc 64 = 32 * 2 := by norm_num
        _ = H'.relIndex Q' * 2 := by rw [hrel32]
        _ ≤ H'.relIndex Q' * (H' ⊔ Q').index := Nat.mul_le_mul_left _ hsup2
        _ ≤ H'.index := hH'_mul
    · push Not at hsup2
      exfalso
      have hpos : 0 < (H' ⊔ Q').index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
      have hsup1 : (H' ⊔ Q').index = 1 := by omega
      have hsup_top : H' ⊔ Q' = ⊤ := Subgroup.index_eq_one.mp hsup1
      set Z' : Subgroup M := Subgroup.zpowers zM
      set K' : Subgroup M := H' ⊓ Q'
      set L' : Subgroup M := K' ⊔ Z'
      have hZ'_le_Q' : Z' ≤ Q' := Subgroup.zpowers_le.mpr hzM_Q'
      have hL'Q' : L' ≤ Q' := sup_le inf_le_right hZ'_le_Q'
      have hzM_zz : zM * zM = 1 := by
        apply Subtype.ext
        change orthHeisZ P R 1 * orthHeisZ P R 1 = 1
        rw [← D.z_add, add_self_eq_zero_of_charTwo K, D.z_zero]
      have hZ_comm : ∀ c : M, c * zM = zM * c := fun c =>
        Subtype.ext (Subgroup.mem_centralizer_iff.mp c.2.2 (orthHeisZ P R 1) rfl).symm
      have hL'_cases : ∀ x ∈ L', x ∈ K' ∨ x * zM ∈ K' := by
        let S_L : Subgroup M :=
          { carrier := {x : M | x ∈ K' ∨ x * zM ∈ K'}
            one_mem' := Or.inl K'.one_mem
            mul_mem' := fun {a b} ha hb => by
              rcases ha with ha | ha <;> rcases hb with hb | hb
              · exact Or.inl (K'.mul_mem ha hb)
              · right
                rw [mul_assoc]
                exact K'.mul_mem ha hb
              · right
                have habz : a * b * zM = a * zM * b := by rw [mul_assoc, hZ_comm b, ← mul_assoc]
                rw [habz]
                exact K'.mul_mem ha hb
              · left
                have hbz : zM * (b * zM) = b * (zM * zM) := by
                  calc zM * (b * zM) = (zM * b) * zM := (mul_assoc zM b zM).symm
                    _ = (b * zM) * zM := by rw [hZ_comm b]
                    _ = b * (zM * zM) := mul_assoc b zM zM
                have hab : a * b = (a * zM) * (b * zM) := by
                  calc a * b = a * (b * (zM * zM)) := by rw [hzM_zz, mul_one]
                    _ = a * (zM * (b * zM)) := by rw [← hbz]
                    _ = (a * zM) * (b * zM) := (mul_assoc a zM (b * zM)).symm
                rw [hab]
                exact K'.mul_mem ha hb
            inv_mem' := fun {a} ha => by
              rcases ha with ha | ha
              · exact Or.inl (K'.inv_mem ha)
              · right
                have haz : a⁻¹ * zM = (a * zM)⁻¹ := by
                  apply mul_left_cancel (a := a * zM)
                  rw [mul_inv_cancel]
                  calc (a * zM) * (a⁻¹ * zM) = a * (zM * a⁻¹) * zM := by group
                    _ = a * (a⁻¹ * zM) * zM := by rw [hZ_comm a⁻¹]
                    _ = zM * zM := by group
                    _ = 1 := hzM_zz
                rw [haz]
                exact K'.inv_mem ha }
        have hL_le : L' ≤ S_L := by
          refine sup_le (fun k hk => Or.inl hk) ?_
          rw [Subgroup.zpowers_le]
          change zM ∈ K' ∨ zM * zM ∈ K'
          right
          rw [hzM_zz]
          exact K'.one_mem
        exact fun x hx => hL_le hx
      have hQ'_comm : ∀ q ∈ Q', ∀ r ∈ Q', ⁅q, r⁆ = 1 ∨ ⁅q, r⁆ = zM := by
        intro q hq r hr
        obtain ⟨u₁, v₁, s₁, hq₁⟩ := hq
        obtain ⟨u₂, v₂, s₂, hr₁⟩ := hr
        have hcomm : (⁅q, r⁆ : M).1 =
            orthHeisZ P R (orthHeisB P R u₁ v₂ - orthHeisB P R u₂ v₁) := by
          change ⁅M.subtype q, M.subtype r⁆ = _
          rw [← hq₁, ← hr₁, D.comm_normalForm, D.X_zero, D.Y_zero, one_mul, one_mul]
        rcases eq_zero_or_eq_one_of_card_two hK
            (orthHeisB P R u₁ v₂ - orthHeisB P R u₂ v₁) with hs0 | hs1
        · left
          apply Subtype.ext
          rw [hcomm, hs0, D.z_zero]
          rfl
        · right
          apply Subtype.ext
          rw [hcomm, hs1]
      have hL'_ne_Q' : L' ≠ Q' := by
        intro hLQ_eq
        let e₂ : orthHeisSubmodule P R :=
          ⟨P₂.e, mem_orthHeisSubmodule.mpr ⟨⟨hPP₂.ee, hPP₂.fe⟩, ⟨hRP₂.ee, hRP₂.fe⟩⟩⟩
        let f₂ : orthHeisSubmodule P R :=
          ⟨P₂.f, mem_orthHeisSubmodule.mpr ⟨⟨hPP₂.ef, hPP₂.ff⟩, ⟨hRP₂.ef, hRP₂.ff⟩⟩⟩
        have hq₁_D : orthHeisX P R e₂ ∈ D.heisSubgroup :=
          ⟨e₂, 0, 0, by rw [D.Y_zero, D.z_zero, mul_one, mul_one]⟩
        have hq₂_D : orthHeisY P R f₂ ∈ D.heisSubgroup :=
          ⟨0, f₂, 0, by rw [D.X_zero, D.z_zero, one_mul, mul_one]⟩
        let q₁ : M := ⟨orthHeisX P R e₂, hQM hq₁_D⟩
        let q₂ : M := ⟨orthHeisY P R f₂, hQM hq₂_D⟩
        have hq₁L : q₁ ∈ L' := hLQ_eq.symm ▸ hq₁_D
        have hq₂L : q₂ ∈ L' := hLQ_eq.symm ▸ hq₂_D
        have hz_inv : zM⁻¹ = zM := inv_eq_of_mul_eq_one_right hzM_zz
        have hcomm_z_right : ∀ x y : M, ⁅x, y * zM⁆ = ⁅x, y⁆ := fun x y => by
          simp only [commutatorElement_def, mul_inv_rev, hz_inv]
          calc x * (y * zM) * x⁻¹ * (zM * y⁻¹)
              = x * y * (zM * x⁻¹) * zM * y⁻¹ := by group
            _ = x * y * (x⁻¹ * zM) * zM * y⁻¹ := by rw [hZ_comm x⁻¹]
            _ = x * y * x⁻¹ * (zM * zM) * y⁻¹ := by group
            _ = x * y * x⁻¹ * y⁻¹ := by rw [hzM_zz, mul_one]
        have hcomm_z_left : ∀ x y : M, ⁅x * zM, y⁆ = ⁅x, y⁆ := fun x y => by
          simp only [commutatorElement_def, mul_inv_rev, hz_inv]
          calc x * zM * y * (zM * x⁻¹) * y⁻¹
              = x * (zM * y) * zM * x⁻¹ * y⁻¹ := by group
            _ = x * (y * zM) * zM * x⁻¹ * y⁻¹ := by rw [hZ_comm y]
            _ = x * y * (zM * zM) * x⁻¹ * y⁻¹ := by group
            _ = x * y * x⁻¹ * y⁻¹ := by rw [hzM_zz, mul_one]
        have hcomm_mem : ∀ {x y : M}, x ∈ K' → y ∈ K' → ⁅x, y⁆ ∈ K' := fun hx hy => by
          rw [commutatorElement_def]
          exact K'.mul_mem (K'.mul_mem (K'.mul_mem hx hy) (K'.inv_mem hx)) (K'.inv_mem hy)
        have hcomm_K' : ∀ a b : M,
            (a ∈ K' ∨ a * zM ∈ K') → (b ∈ K' ∨ b * zM ∈ K') → ⁅a, b⁆ ∈ K' := by
          intro a b ha hb
          rcases ha with ha | ha <;> rcases hb with hb | hb
          · exact hcomm_mem ha hb
          · rw [← hcomm_z_right a b]
            exact hcomm_mem ha hb
          · rw [← hcomm_z_left a b]
            exact hcomm_mem ha hb
          · rw [← hcomm_z_left a b, ← hcomm_z_right (a * zM) b]
            exact hcomm_mem ha hb
        have hq_comm_K' : ⁅q₁, q₂⁆ ∈ K' :=
          hcomm_K' q₁ q₂ (hL'_cases q₁ hq₁L) (hL'_cases q₂ hq₂L)
        have hq_comm_eq : ⁅q₁, q₂⁆ = zM := by
          apply Subtype.ext
          change ⁅orthHeisX P R e₂, orthHeisY P R f₂⁆ = orthHeisZ P R 1
          rw [D.comm_X_Y]
          change orthHeisZ P R (polar Q P₂.f P₂.e) = orthHeisZ P R 1
          rw [P₂.polar_fe]
        exact hz_not_mem (hq_comm_eq ▸ hq_comm_K'.1)
      set N : Subgroup M := Subgroup.normalizer (L' : Set M)
      have hZ_le_comap : ∀ c : M, Z' ≤ L'.comap (MulAut.conj c).toMonoidHom := by
        intro c
        rw [Subgroup.zpowers_le]
        change c * zM * c⁻¹ ∈ L'
        have hc : c * zM * c⁻¹ = zM := by rw [hZ_comm c, mul_inv_cancel_right]
        rw [hc]
        exact (le_sup_right : Z' ≤ L') (Subgroup.mem_zpowers zM)
      have hH'_le_N : H' ≤ N := by
        refine le_normalizer_of_conj_mem fun h hh => sup_le ?_ (hZ_le_comap h)
        intro k hk
        change h * k * h⁻¹ ∈ L'
        exact (le_sup_left : K' ≤ L')
          ⟨H'.mul_mem (H'.mul_mem hh hk.1) (H'.inv_mem hh), hQ'_norm.conj_mem k hk.2 h⟩
      have hQ'_le_N : Q' ≤ N := by
        refine le_normalizer_of_conj_mem fun q hq => sup_le ?_ (hZ_le_comap q)
        intro k hk
        change q * k * q⁻¹ ∈ L'
        have heq : q * k * q⁻¹ = ⁅q, k⁆ * k := by simp [commutatorElement_def]
        rw [heq]
        have hcomm_L' : ⁅q, k⁆ ∈ L' := by
          rcases hQ'_comm q hq k hk.2 with h1 | hz
          · rw [h1]
            exact L'.one_mem
          · rw [hz]
            exact (le_sup_right : Z' ≤ L') (Subgroup.mem_zpowers zM)
        exact L'.mul_mem hcomm_L' ((le_sup_left : K' ≤ L') hk)
      have hN_top : N = ⊤ := top_unique (hsup_top ▸ sup_le hH'_le_N hQ'_le_N)
      have hL'_conj : ∀ m : M, ∀ x ∈ L', m * x * m⁻¹ ∈ L' := by
        intro m x hx
        have hmN : m ∈ N := hN_top ▸ Subgroup.mem_top m
        exact ((Subgroup.mem_normalizer_iff.mp hmN) x).mp hx
      let L : Subgroup (ProjElementary Q) := L'.map M.subtype
      have hZL : ∀ s : K, orthHeisZ P R s ∈ L := by
        intro s
        rcases eq_zero_or_eq_one_of_card_two hK s with rfl | rfl
        · rw [D.z_zero]
          exact L.one_mem
        · exact ⟨zM, (le_sup_right : Z' ≤ L') (Subgroup.mem_zpowers zM), rfl⟩
      have hL_le : L ≤ D.heisSubgroup := by
        rintro _ ⟨x, hx, rfl⟩
        exact hL'Q' hx
      have hconj_L : ∀ {g : ProjElementary Q} (hg : g ∈ M), ∀ x ∈ L, g * x * g⁻¹ ∈ L := by
        rintro g hg _ ⟨x, hx, rfl⟩
        exact ⟨⟨g, hg⟩ * x * ⟨g, hg⟩⁻¹, hL'_conj ⟨g, hg⟩ x hx, rfl⟩
      have hcardHQ' : Nat.card (H'.subgroupOf Q') = 16 := by
        have hmul := Subgroup.card_mul_index (H'.subgroupOf Q')
        change Nat.card (H'.subgroupOf Q') * H'.relIndex Q' = Nat.card Q' at hmul
        rw [hrel32, hcardQ'] at hmul
        omega
      have hcardL : 16 ≤ Nat.card L := by
        rw [← hcardHQ']
        let iHL : H'.subgroupOf Q' → L := fun k =>
          ⟨k.1.1.1, k.1.1, (le_sup_left : K' ≤ L') ⟨k.2, k.1.2⟩, rfl⟩
        have hiHL : Function.Injective iHL := by
          intro a b h
          have hval : (iHL a).1 = (iHL b).1 := congrArg Subtype.val h
          exact Subtype.ext (Subtype.ext (Subtype.ext hval))
        exact Nat.card_le_card_of_injective iHL hiHL
      have hex_not_Z : ∃ g₀ ∈ L, ∀ s : K, g₀ ≠ orthHeisZ P R s := by
        by_contra! hall
        have hle2 : Nat.card L ≤ Nat.card K := by
          let f : L → K := fun g => Classical.choose (hall g.1 g.2)
          have hf : Function.Injective f := by
            intro g₁ g₂ h
            apply Subtype.ext
            rw [Classical.choose_spec (hall g₁.1 g₁.2), Classical.choose_spec (hall g₂.1 g₂.2)]
            exact congrArg (orthHeisZ P R) h
          exact Nat.card_le_card_of_injective f hf
        rw [hK] at hle2
        omega
      obtain ⟨g₀, hg₀L, hg₀_not_Z⟩ := hex_not_Z
      have hQ_le_L : D.heisSubgroup ≤ L :=
        heisSubgroup_le_of_levi_normal hK hQ hPR hPP₂ hRP₂ hu₀W hu₀P₂ hu₀_ne hZL hL_le
          (hconj_L (orthLeviS₁_mem_orthHeisNormCentralizer hQ hPR))
          (hconj_L (orthLeviS₂_mem_orthHeisNormCentralizer hQ hPR))
          (fun a w => hconj_L (orthLeviT_mem_orthHeisNormCentralizer hQ hPR a w))
          hg₀L hg₀_not_Z
      have hQ'_le_L' : Q' ≤ L' := by
        intro q hq
        obtain ⟨x, hx, hqx⟩ := hQ_le_L hq
        have hxeq : x = q := M.subtype_injective hqx
        rwa [← hxeq]
      exact hL'_ne_Q' (le_antisymm hL'Q' hQ'_le_L')

/-- Every proper subgroup `H ≠ ⊤` of `ProjElementary Q` (when `ProjElementary Q` is simple) has
index at least `64` when `Nat.card K = 2` and `Nat.card (orthHeisSubmodule P R) = 16`. -/
theorem index_ge_64_of_card_two_eight [IsSimpleGroup (ProjElementary Q)]
    (hK : Nat.card K = 2) (hQ : (polarBilin Q).Nondegenerate)
    {P R P₂ : HypPair Q} (hPR : P.Orth R) (hPP₂ : P.Orth P₂) (hRP₂ : R.Orth P₂)
    {u₀ : V} (hu₀W : u₀ ∈ orthHeisSubmodule P R) (hu₀P₂ : u₀ ∈ P₂.perp) (hu₀_ne : u₀ ≠ 0)
    (hW : Nat.card (orthHeisSubmodule P R) = 16)
    {H : Subgroup (ProjElementary Q)} (hH : H ≠ ⊤) :
    64 ≤ H.index := by
  have : Finite (V ≃ₗ[K] V) :=
    Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V)) DFunLike.coe_injective
  let D := polarizedHeisenbergData_projElementary hQ hPR
  let M := orthHeisNormCentralizer hQ hPR
  let zM : M := ⟨orthHeisZ P R 1, heisSubgroup_le_orthHeisNormCentralizer hQ hPR
    (orthHeisZ_mem_heisSubgroup hQ hPR 1)⟩
  have hzM_ne : Subgroup.zpowers zM ≠ ⊥ := by
    rw [ne_eq, Subgroup.zpowers_eq_bot]
    intro hz1
    have h1 : orthHeisZ P R 1 = 1 := congrArg Subtype.val hz1
    exact one_ne_zero (D.z_eq_one 1 h1)
  exact le_index_of_injective_of_forall_not_le_index hH M.subtype M.subtype_injective hzM_ne
    fun H' hzH' =>
      index_ge_64_of_not_zpowers_le hK hQ hPR hPP₂ hRP₂ hu₀W hu₀P₂ hu₀_ne hW hzH'

end SmallIndexBound

section ModelsAndCases

/-- Every proper subgroup `H` of `PΩ⁺(8, 2)` has index at least `64`. -/
theorem index_ge_64_of_statedClassicalModel_pOmegaPlus_four_two {S : Type} [Group S]
    (h : StatedClassicalModel S .POmegaPlus 4 2 1) {H : Subgroup S} (hH : H ≠ ⊤) :
    64 ≤ H.index := by
  obtain ⟨⟨hp, hf, hn⟩, K, _, _, hK, ⟨eS⟩⟩ := h
  have : Fact (Nat.Prime 2) := ⟨hp⟩
  have : CharP K 2 := Maroti.charP_of_card_eq hp hf hK
  have hK2 : Nat.card K = 2 := by simpa using hK
  have hn3 : 3 ≤ (4 : ℕ) := by decide
  have : IsSimpleGroup (ProjElementary (quadPlus 4 K)) := isSimpleGroup_projElementary_quadPlus hn3
  let e : S ≃* ProjElementary (quadPlus 4 K) :=
    eS.trans (statedProjEquiv (coe_quadPlus 4 K) (commutator_orthogonalGroup_quadPlus hn3))
  let P : HypPair (quadPlus 4 K) := plusPair K 0
  let R : HypPair (quadPlus 4 K) := plusPair K 1
  let P₂ : HypPair (quadPlus 4 K) := plusPair K 2
  let P₃ : HypPair (quadPlus 4 K) := plusPair K 3
  have hPR : P.Orth R := plusPair_orth (by decide)
  have hPP₂ : P.Orth P₂ := plusPair_orth (by decide)
  have hRP₂ : R.Orth P₂ := plusPair_orth (by decide)
  have hPP₃ : P.Orth P₃ := plusPair_orth (by decide)
  have hRP₃ : R.Orth P₃ := plusPair_orth (by decide)
  have hP₂P₃ : P₂.Orth P₃ := plusPair_orth (by decide)
  have hu₀W : P₃.e ∈ orthHeisSubmodule P R :=
    mem_orthHeisSubmodule.mpr ⟨⟨hPP₃.ee, hPP₃.fe⟩, ⟨hRP₃.ee, hRP₃.fe⟩⟩
  have hu₀P₂ : P₃.e ∈ P₂.perp := HypPair.mem_perp.mpr ⟨hP₂P₃.ee, hP₂P₃.fe⟩
  have hu₀_ne : P₃.e ≠ 0 := by
    intro h0
    have h1 := P₃.polar_ef
    rw [h0, polar_zero_left] at h1
    exact zero_ne_one h1
  have hV : Nat.card (Fin 4 ⊕ Fin 4 → K) = 2 ^ (4 + 4) := by
    rw [Nat.card_fun, hK2, Nat.card_eq_fintype_card, Fintype.card_sum, Fintype.card_fin]
  have hW : Nat.card (orthHeisSubmodule P R) = 16 :=
    card_orthHeisSubmodule_eq_pow hPR hK2 (by norm_num) hV
  have hH' : H.map e.toMonoidHom ≠ ⊤ := by
    intro htop
    apply hH
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [htop, Subgroup.map_top_of_surjective _ e.surjective]
  rw [← Subgroup.index_map_equiv H e]
  exact index_ge_64_of_card_two_eight hK2 (nondegenerate_polarBilin_quadPlus 4 K)
    hPR hPP₂ hRP₂ hu₀W hu₀P₂ hu₀_ne hW hH'

/-- Every proper subgroup `H` of `PΩ⁻(8, 2)` has index at least `64`. -/
theorem index_ge_64_of_statedClassicalModel_pOmegaMinus_four_two {S : Type} [Group S]
    (h : StatedClassicalModel S .POmegaMinus 4 2 1) {H : Subgroup S} (hH : H ≠ ⊤) :
    64 ≤ H.index := by
  obtain ⟨⟨hp, hf, hn⟩, K, _, _, hK, b, c, hirr, ⟨eS⟩⟩ := h
  have : Fact (Nat.Prime 2) := ⟨hp⟩
  have : CharP K 2 := Maroti.charP_of_card_eq hp hf hK
  have hK2 : Nat.card K = 2 := by simpa using hK
  have : IsSimpleGroup (ProjElementary (quadMinus 4 K b c)) :=
    isSimpleGroup_projElementary_quadMinus hn hirr
  let e : S ≃* ProjElementary (quadMinus 4 K b c) :=
    eS.trans (statedProjEquiv (coe_quadMinus 4 K b c)
      (commutator_orthogonalGroup_quadMinus hn hirr))
  let P : HypPair (quadMinus 4 K b c) := minusPair K b c ⟨0, by decide⟩
  let R : HypPair (quadMinus 4 K b c) := minusPair K b c ⟨1, by decide⟩
  let P₂ : HypPair (quadMinus 4 K b c) := minusPair K b c ⟨2, by decide⟩
  have hPR : P.Orth R := minusPair_orth (by decide)
  have hPP₂ : P.Orth P₂ := minusPair_orth (by decide)
  have hRP₂ : R.Orth P₂ := minusPair_orth (by decide)
  let u₀ : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → K := Pi.single (Sum.inr (Sum.inr 0)) 1
  have hu₀_perp : ∀ i : Fin (4 - 1), u₀ ∈ (minusPair (n := 4) K b c i).perp := fun i => by
    rw [HypPair.mem_perp, minusPair_e, minusPair_f,
      polar_single_inl_quadMinus, polar_single_inr_quadMinus]
    simp [u₀]
  have hu₀W : u₀ ∈ orthHeisSubmodule P R := ⟨hu₀_perp ⟨0, by decide⟩, hu₀_perp ⟨1, by decide⟩⟩
  have hu₀P₂ : u₀ ∈ P₂.perp := hu₀_perp ⟨2, by decide⟩
  have hu₀_ne : u₀ ≠ 0 := by
    intro h0
    have h1 : u₀ (Sum.inr (Sum.inr 0)) = 0 := congrFun h0 (Sum.inr (Sum.inr 0))
    simp [u₀] at h1
  have hV : Nat.card (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → K) = 2 ^ (4 + 4) := by
    rw [Nat.card_fun, hK2, Nat.card_eq_fintype_card, Fintype.card_sum, Fintype.card_sum,
      Fintype.card_fin, Fintype.card_fin]
  have hW : Nat.card (orthHeisSubmodule P R) = 16 :=
    card_orthHeisSubmodule_eq_pow hPR hK2 (by norm_num) hV
  have hH' : H.map e.toMonoidHom ≠ ⊤ := by
    intro htop
    apply hH
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [htop, Subgroup.map_top_of_surjective _ e.surjective]
  rw [← Subgroup.index_map_equiv H e]
  exact index_ge_64_of_card_two_eight hK2
    (nondegenerate_polarBilin_quadMinus_of_finite 4 K hirr)
    hPR hPP₂ hRP₂ hu₀W hu₀P₂ hu₀_ne hW hH'

private theorem three_mul_two_pow_29_le_bound_64 :
    3 * (2 ^ 1) ^ (4 * (2 * 4 - 1) + 1) ≤ bound 64 := by
  have h1 : 3 * (2 ^ 1) ^ (4 * (2 * 4 - 1) + 1) ≤ 64 ^ Nat.log 2 64 := by decide
  exact h1.trans (pow_log_le_bound (by norm_num))

/-- Theorem 1.1 of Maróti (2002) for almost simple primitive groups with socle `PΩ⁺(2n, p^f)`
(`n ≥ 4`). -/
theorem orthogonalPlusCase : AlmostSimpleCase (ClassicalSocle .POmegaPlus) := by
  intro α _ G S _ _ hAS ⟨n, p, f, hModel⟩
  right; right
  have hf : 0 < f := hModel.1.2.1
  have hc_pos : 0 < Nat.gcd 4 ((p ^ f) ^ n - 1) * f * (if n = 4 then 6 else 2) := by
    refine Nat.mul_pos (Nat.mul_pos ?_ hf) ?_
    · exact Nat.gcd_pos_of_pos_left _ (by norm_num)
    · split <;> norm_num
  by_cases h421 : n = 4 ∧ p = 2 ∧ f = 1
  · rcases h421 with ⟨rfl, rfl, rfl⟩
    exact hAS.card_le_bound_of_outerAut_dvd hc_pos
      (fun H hH => index_ge_64_of_statedClassicalModel_pOmegaPlus_four_two hModel hH)
      (card_outerAut_pOmegaPlus_dvd hModel)
      ((card_mul_outer_le_pow_pOmegaPlus hModel).trans three_mul_two_pow_29_le_bound_64)
  · exact hAS.card_le_bound_of_outerAut_dvd hc_pos
      (fun H hH => index_ge_of_statedClassicalModel_pOmegaPlus hModel hH)
      (card_outerAut_pOmegaPlus_dvd hModel)
      (card_mul_outer_le_bound_pOmegaPlus hModel h421)

/-- Theorem 1.1 of Maróti (2002) for almost simple primitive groups with socle `PΩ⁻(2n, p^f)`
(`n ≥ 4`). -/
theorem orthogonalMinusCase : AlmostSimpleCase (ClassicalSocle .POmegaMinus) := by
  intro α _ G S _ _ hAS ⟨n, p, f, hModel⟩
  right; right
  have hf : 0 < f := hModel.1.2.1
  have hc_pos : 0 < Nat.gcd 4 ((p ^ f) ^ n + 1) * f * 2 :=
    Nat.mul_pos (Nat.mul_pos (Nat.gcd_pos_of_pos_left _ (by norm_num)) hf) (by norm_num)
  by_cases h421 : n = 4 ∧ p = 2 ∧ f = 1
  · rcases h421 with ⟨rfl, rfl, rfl⟩
    exact hAS.card_le_bound_of_outerAut_dvd hc_pos
      (fun H hH => index_ge_64_of_statedClassicalModel_pOmegaMinus_four_two hModel hH)
      (card_outerAut_pOmegaMinus_dvd hModel)
      ((card_mul_outer_le_pow_pOmegaMinus hModel).trans three_mul_two_pow_29_le_bound_64)
  · exact hAS.card_le_bound_of_outerAut_dvd hc_pos
      (fun H hH => index_ge_of_statedClassicalModel_pOmegaMinus hModel hH)
      (card_outerAut_pOmegaMinus_dvd hModel)
      (card_mul_outer_le_bound_pOmegaMinus hModel h421)

end ModelsAndCases

end Maroti
