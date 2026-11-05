module

public import Maroti.Linear.DegreeBoundHigher

/-!
# Degree lower bound `36 ≤ n` for `PSL(4, 3)` and Heisenberg intersection structure

This file proves the refined degree lower bound `36 ≤ H.index` (hence `32 ≤ H.index`) for every
proper subgroup `H < projectiveSL 4 K` when `Nat.card K = 3`, together with the middle-transvection
invariance and isotropy structure of `eAddSubgroup ht H₀` when `H₀.index < 2 * p ^ (t - 1)` over a
prime field `K` of order `p` (`t ≥ 4`):

* The theorem `Maroti.transvection_mid_conj_qMat` computes conjugation of `qMat ht u v z` by a
  middle transvection `SpecialLinearGroup.transvection hm c` (`m₁ ≠ m₂` in `Mid t`).
* The theorem `Maroti.eAddSubgroup_mid_invariance` shows that if `Nat.card K = p`,
  `¬ (zSubgroup ht K ≤ H₀)`, and `H₀.index < 2 * p ^ (t - 1)`, then `eAddSubgroup ht H₀` has order
  `p ^ (t - 2)` and satisfies
  `(-(u m₁ * c) • Pi.single m₂ 1, (c * v m₂) • Pi.single m₁ 1) ∈ eAddSubgroup ht H₀` for all
  `(u, v) ∈ eAddSubgroup ht H₀` and `m₁ ≠ m₂` in `Mid t`.
* The theorem `Maroti.eAddSubgroup_dichotomy` shows that for `t ≥ 4`, under the above hypotheses,
  if `5 ≤ t ∨ p ≠ 2`, then `eAddSubgroup ht H₀` is either `⊤ × ⊥` or `⊥ × ⊤`.
* The theorem `Maroti.pow_pred_add_pow_sub_two_le_index` shows that when `eAddSubgroup ht H₀` is
  `⊤ × ⊥` or `⊥ × ⊤`, `p ^ (t - 1) + p ^ (t - 2) ≤ H₀.index`.
* The theorems `Maroti.thirty_six_le_index_of_four_three` and
  `Maroti.thirty_two_le_card_of_four_three` show that for `t = 4` and `Nat.card K = 3`, every
  proper subgroup `H < projectiveSL 4 K` has `36 ≤ H.index` (so `32 ≤ Nat.card α`).
-/

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace Maroti

open Subgroup Equiv Matrix
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

/-- For `m₁, m₂ : Mid t`,
`single m₁.1 m₂.1 c * qNil u v z = qNil 0 ((c * v m₂) • Pi.single m₁ 1) 0`. -/
theorem single_mid_mul_qNil {t : ℕ} [NeZero t] {K : Type*} [Field K]
    (m₁ m₂ : Mid t) (c : K) (u v : Mid t → K) (z : K) :
    single m₁.1 m₂.1 c * qNil u v z = qNil 0 ((c * v m₂) • Pi.single m₁ 1) 0 := by
  ext i j
  by_cases hi : i = m₁.1
  · subst hi
    rw [single_mul_apply_same, qNil_apply_mid_left, qNil_apply, ite_eq_right m₁.2.1,
      dite_eq_left m₁.2]
    by_cases hj : j = lastIdx t
    · subst hj
      simp [Pi.single_eq_same]
    · simp [hj]
  · rw [single_mul_apply_of_ne _ _ _ _ _ hi, qNil_apply]
    split_ifs with h1 h2 h3 h4 h5
    · rfl
    · rfl
    · rfl
    · rw [Pi.smul_apply, Pi.single_eq_of_ne (fun h => hi (congrArg Subtype.val h)), smul_zero]
    · rfl
    · rfl

/-- For `m₁, m₂ : Mid t`,
`qNil u v z * single m₁.1 m₂.1 c = qNil ((u m₁ * c) • Pi.single m₂ 1) 0 0`. -/
theorem qNil_mul_single_mid {t : ℕ} [NeZero t] {K : Type*} [Field K]
    (m₁ m₂ : Mid t) (c : K) (u v : Mid t → K) (z : K) :
    qNil u v z * single m₁.1 m₂.1 c = qNil ((u m₁ * c) • Pi.single m₂ 1) 0 0 := by
  ext i j
  by_cases hj : j = m₂.1
  · subst hj
    rw [mul_single_apply_same, qNil_apply_mid_right, qNil_apply, ite_eq_right m₂.2.2,
      dite_eq_left m₂.2]
    by_cases hi : i = firstIdx t
    · subst hi
      simp [Pi.single_eq_same]
    · simp [hi]
  · rw [mul_single_apply_of_ne _ _ _ _ _ hj, qNil_apply]
    split_ifs with h1 h2 h3 h4 h5
    · rfl
    · rw [Pi.smul_apply, Pi.single_eq_of_ne (fun h => hj (congrArg Subtype.val h)), smul_zero]
    · rfl
    · rfl
    · rfl
    · rfl

/-- Conjugation of `qMat ht u v z` by a middle transvection
`SpecialLinearGroup.transvection hm c`. -/
theorem transvection_mid_conj_qMat {t : ℕ} [NeZero t] {K : Type*} [Field K] (ht : 2 ≤ t)
    {m₁ m₂ : Mid t} (hm : m₁ ≠ m₂) (c : K) (u v : Mid t → K) (z : K) :
    let hm' : m₁.1 ≠ m₂.1 := Subtype.val_injective.ne hm
    SpecialLinearGroup.transvection hm' c * qMat ht u v z *
        (SpecialLinearGroup.transvection hm' c)⁻¹ =
      qMat ht (u - (u m₁ * c) • Pi.single m₂ 1) (v + (c * v m₂) • Pi.single m₁ 1) z := by
  intro hm'
  rw [SpecialLinearGroup.transvection_inv]
  apply Subtype.ext
  change (1 + single m₁.1 m₂.1 c) * (1 + qNil u v z) * (1 + single m₁.1 m₂.1 (-c)) =
    1 + qNil (u - (u m₁ * c) • Pi.single m₂ 1) (v + (c * v m₂) • Pi.single m₁ 1) z
  have hss : single m₁.1 m₂.1 c * single m₁.1 m₂.1 (-c) = 0 :=
    single_mul_single_of_ne c m₁.1 m₂.1 m₁.1 hm'.symm (-c)
  have hsn : single m₁.1 m₂.1 c * qNil u v z = qNil 0 ((c * v m₂) • Pi.single m₁ 1) 0 :=
    single_mid_mul_qNil m₁ m₂ c u v z
  have hns : qNil u v z * single m₁.1 m₂.1 (-c) = qNil (-(u m₁ * c) • Pi.single m₂ 1) 0 0 := by
    rw [qNil_mul_single_mid]
    congr 2
    ring
  have hsns : single m₁.1 m₂.1 c * qNil u v z * single m₁.1 m₂.1 (-c) = 0 := by
    rw [hsn, qNil_mul_single_mid]
    simp
  calc (1 + single m₁.1 m₂.1 c) * (1 + qNil u v z) * (1 + single m₁.1 m₂.1 (-c))
    _ = 1 + (single m₁.1 m₂.1 c + single m₁.1 m₂.1 (-c) +
          single m₁.1 m₂.1 c * single m₁.1 m₂.1 (-c)) +
        (qNil u v z + single m₁.1 m₂.1 c * qNil u v z + qNil u v z * single m₁.1 m₂.1 (-c) +
          single m₁.1 m₂.1 c * qNil u v z * single m₁.1 m₂.1 (-c)) := by
        noncomm_ring
    _ = 1 + (qNil u v z + qNil 0 ((c * v m₂) • Pi.single m₁ 1) 0 +
          qNil (-(u m₁ * c) • Pi.single m₂ 1) 0 0) := by
        rw [← single_add, add_neg_cancel, single_zero, hss, hsns, hsn, hns]
        simp
    _ = 1 + qNil (u - (u m₁ * c) • Pi.single m₂ 1) (v + (c * v m₂) • Pi.single m₁ 1) z := by
        rw [qNil_add, qNil_add]
        congr 1
        funext m
        simp [sub_eq_add_neg]

/-- A middle transvection `SpecialLinearGroup.transvection hm c` commutes with `qMat ht 0 0 z`. -/
theorem transvection_mid_comm_qMat_zero {t : ℕ} [NeZero t] {K : Type*} [Field K] (ht : 2 ≤ t)
    {m₁ m₂ : Mid t} (hm : m₁ ≠ m₂) (c z : K) :
    let hm' : m₁.1 ≠ m₂.1 := Subtype.val_injective.ne hm
    SpecialLinearGroup.transvection hm' c * qMat ht 0 0 z =
      qMat ht 0 0 z * SpecialLinearGroup.transvection hm' c := by
  intro hm'
  rw [← mul_inv_eq_iff_eq_mul, transvection_mid_conj_qMat ht hm c 0 0 z]
  simp

/-- Over a prime field `K` of order `p`, `zSubgroup ht K ≤ H ↔ qMat ht 0 0 1 ∈ H`. -/
theorem zSubgroup_le_iff_qMat_one_mem {t : ℕ} [NeZero t] (ht : 2 ≤ t) {K : Type*} [Field K]
    [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p] (hK : Nat.card K = p)
    (H : Subgroup (SpecialLinearGroup (Fin t) K)) :
    zSubgroup ht K ≤ H ↔ qMat ht 0 0 1 ∈ H := by
  constructor
  · intro hle
    exact hle ⟨1, rfl⟩
  · intro h1
    by_contra hZ
    have hbot := (prime_field_qSubgroup_bounds ht hK hZ).1
    have hmem : (1 : K) ∈ zAddSubgroup ht H := h1
    rw [hbot, AddSubgroup.mem_bot] at hmem
    exact one_ne_zero hmem

/-- For any subgroups `H P : Subgroup G` and `g : G`, the `P`-orbit of `QuotientGroup.mk g` in
`G ⧸ H` has cardinality `(H.map (MulAut.conj g)).relIndex P`. -/
theorem card_orbit_quotient_eq_relIndex {G : Type*} [Group G] (H P : Subgroup G) (g : G) :
    Nat.card (MulAction.orbit P (QuotientGroup.mk g : G ⧸ H)) =
      (H.map (MulAut.conj g : G →* G)).relIndex P := by
  rw [Nat.card_congr (MulAction.orbitEquivQuotientStabilizer P (QuotientGroup.mk g : G ⧸ H)),
    Subgroup.relIndex, Subgroup.index]
  congr 2
  ext ⟨s, hs⟩
  simp only [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_map]
  change QuotientGroup.mk (s * g) = (QuotientGroup.mk g : G ⧸ H) ↔
    ∃ h ∈ H, g * h * g⁻¹ = s
  rw [QuotientGroup.eq]
  constructor
  · intro hmem
    refine ⟨g⁻¹ * s * g, ?_, by group⟩
    have heq : g⁻¹ * s * g = ((s * g)⁻¹ * g)⁻¹ := by group
    rw [heq]
    exact H.inv_mem hmem
  · rintro ⟨h, hh, rfl⟩
    have heq : (g * h * g⁻¹ * g)⁻¹ * g = h⁻¹ := by group
    rw [heq]
    exact H.inv_mem hh

/-- For `g = 1`, `Nat.card (MulAction.orbit P (QuotientGroup.mk 1 : G ⧸ H)) = H.relIndex P`. -/
theorem card_orbit_quotient_one_eq_relIndex {G : Type*} [Group G] (H P : Subgroup G) :
    Nat.card (MulAction.orbit P (QuotientGroup.mk 1 : G ⧸ H)) = H.relIndex P := by
  rw [card_orbit_quotient_eq_relIndex]
  congr 1
  ext x
  simp

/-- If `Nat.card K = p`, `¬ (zSubgroup ht K ≤ H₀)`, and `H₀.index < 2 * p ^ (t - 1)`, then
`H₀.relIndex (qSubgroup ht K) = p ^ (t - 1)`, `Nat.card (eAddSubgroup ht H₀) = p ^ (t - 2)`,
and for every `T : SpecialLinearGroup (Fin t) K` commuting with `qMat ht 0 0 1`, there exists
`q ∈ qSubgroup ht K` such that `q⁻¹ * T ∈ H₀`. -/
theorem exists_qSubgroup_mul_mem_of_comm_zMat {t : ℕ} [NeZero t] (ht : 2 ≤ t)
    {K : Type*} [Field K] [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (hK : Nat.card K = p) {H₀ : Subgroup (SpecialLinearGroup (Fin t) K)}
    (hZ : ¬ (zSubgroup ht K ≤ H₀)) (hidx : H₀.index < 2 * p ^ (t - 1)) :
    H₀.relIndex (qSubgroup ht K) = p ^ (t - 1) ∧
      Nat.card (eAddSubgroup ht H₀) = p ^ (t - 2) ∧
      ∀ T : SpecialLinearGroup (Fin t) K,
        T * qMat ht 0 0 1 = qMat ht 0 0 1 * T →
        ∃ q ∈ qSubgroup ht K, q⁻¹ * T ∈ H₀ := by
  have hp : p.Prime := Fact.out
  obtain ⟨_, hinf_card, _, hrel_ge, hdvd⟩ := prime_field_qSubgroup_bounds ht hK hZ
  have hrel_lt : H₀.relIndex (qSubgroup ht K) < 2 * p ^ (t - 1) :=
    lt_of_le_of_lt (relIndex_le_index H₀ (qSubgroup ht K)) hidx
  have hrel_eq : H₀.relIndex (qSubgroup ht K) = p ^ (t - 1) := by
    obtain ⟨k, hk, hk_eq⟩ := (Nat.dvd_prime_pow hp).mp hdvd
    rw [hk_eq] at hrel_ge hrel_lt ⊢
    have h1 : t - 1 ≤ k := (Nat.pow_le_pow_iff_right hp.one_lt).mp hrel_ge
    have h2 : ¬ (t ≤ k) := by
      intro htk
      have hle : 2 * p ^ (t - 1) ≤ p ^ k := calc
        2 * p ^ (t - 1) ≤ p * p ^ (t - 1) := Nat.mul_le_mul_right _ hp.two_le
        _ = p ^ t := by rw [← pow_succ']; congr 1; omega
        _ ≤ p ^ k := Nat.pow_le_pow_right hp.pos htk
      omega
    have hk_t : k = t - 1 := by omega
    rw [hk_t]
  have hE_eq : Nat.card (eAddSubgroup ht H₀) = p ^ (t - 2) := by
    have hmul : Nat.card (eAddSubgroup ht H₀) * p ^ (t - 1) = p ^ (t - 2) * p ^ (t - 1) := by
      calc Nat.card (eAddSubgroup ht H₀) * p ^ (t - 1)
        _ = Nat.card ↥(H₀ ⊓ qSubgroup ht K) * H₀.relIndex (qSubgroup ht K) := by
            rw [hinf_card, hrel_eq]
        _ = Nat.card (qSubgroup ht K) := by
            rw [← card_subgroupOf, Subgroup.relIndex, Subgroup.card_mul_index]
        _ = p ^ (2 * t - 3) := by rw [card_qSubgroup, hK]
        _ = p ^ ((t - 2) + (t - 1)) := by congr 1; omega
        _ = p ^ (t - 2) * p ^ (t - 1) := pow_add p _ _
    exact Nat.eq_of_mul_eq_mul_right (pow_pos hp.pos _) hmul
  refine ⟨hrel_eq, hE_eq, fun T hcomm => ?_⟩
  let Q := qSubgroup ht K
  let X := SpecialLinearGroup (Fin t) K ⧸ H₀
  let x₀ : X := QuotientGroup.mk 1
  let xT : X := QuotientGroup.mk T
  have horb : xT ∈ MulAction.orbit Q x₀ := by
    by_contra hnot
    let H_T := H₀.map (MulAut.conj T : SpecialLinearGroup (Fin t) K →* SpecialLinearGroup (Fin t) K)
    have hZ_T : ¬ (zSubgroup ht K ≤ H_T) := by
      rw [zSubgroup_le_iff_qMat_one_mem ht hK] at hZ ⊢
      rintro ⟨h, hh, hTh⟩
      apply hZ
      change T * h * T⁻¹ = qMat ht 0 0 1 at hTh
      have heq : h = qMat ht 0 0 1 := by
        calc h = T⁻¹ * (T * h * T⁻¹) * T := by group
          _ = T⁻¹ * (qMat ht 0 0 1 * T) := by rw [hTh, mul_assoc]
          _ = T⁻¹ * (T * qMat ht 0 0 1) := by rw [hcomm]
          _ = qMat ht 0 0 1 := by group
      exact heq ▸ hh
    have hrel_T : p ^ (t - 1) ≤ H_T.relIndex Q :=
      (prime_field_qSubgroup_bounds ht hK hZ_T).2.2.2.1
    let f : MulAction.orbit Q x₀ ⊕ MulAction.orbit Q xT → X :=
      Sum.elim Subtype.val Subtype.val
    have hf_inj : Function.Injective f := by
      rintro (⟨y₁, hy₁⟩ | ⟨y₁, hy₁⟩) (⟨y₂, hy₂⟩ | ⟨y₂, hy₂⟩) h
      · exact congrArg Sum.inl (Subtype.ext h)
      · exfalso
        change y₁ = y₂ at h
        subst h
        have horb1 := MulAction.orbit_eq_iff.mpr hy₁
        have horb2 := MulAction.orbit_eq_iff.mpr hy₂
        apply hnot
        rw [← horb1, horb2]
        exact MulAction.mem_orbit_self xT
      · exfalso
        change y₁ = y₂ at h
        subst h
        have horb1 := MulAction.orbit_eq_iff.mpr hy₂
        have horb2 := MulAction.orbit_eq_iff.mpr hy₁
        apply hnot
        rw [← horb1, horb2]
        exact MulAction.mem_orbit_self xT
      · exact congrArg Sum.inr (Subtype.ext h)
    have hcard_sum : Nat.card (MulAction.orbit Q x₀) + Nat.card (MulAction.orbit Q xT) ≤
        H₀.index := by
      rw [← Nat.card_sum, Subgroup.index]
      exact Nat.card_le_card_of_injective f hf_inj
    rw [card_orbit_quotient_one_eq_relIndex, card_orbit_quotient_eq_relIndex, hrel_eq] at hcard_sum
    change p ^ (t - 1) + H_T.relIndex Q ≤ H₀.index at hcard_sum
    omega
  obtain ⟨⟨q, hqQ⟩, hqx⟩ := horb
  refine ⟨q, hqQ, ?_⟩
  have hqx' : QuotientGroup.mk (q * 1) = (QuotientGroup.mk T : X) := hqx
  rw [mul_one, QuotientGroup.eq] at hqx'
  exact hqx'

/-- Middle-transvection invariance of `eAddSubgroup ht H₀` when `H₀.index < 2 * p ^ (t - 1)`. -/
theorem eAddSubgroup_mid_invariance {t : ℕ} [NeZero t] (ht : 2 ≤ t)
    {K : Type*} [Field K] [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (hK : Nat.card K = p) {H₀ : Subgroup (SpecialLinearGroup (Fin t) K)}
    (hZ : ¬ (zSubgroup ht K ≤ H₀)) (hidx : H₀.index < 2 * p ^ (t - 1))
    {u v : Mid t → K} (huv : (u, v) ∈ eAddSubgroup ht H₀)
    {m₁ m₂ : Mid t} (hm : m₁ ≠ m₂) (c : K) :
    (-(u m₁ * c) • Pi.single m₂ 1, (c * v m₂) • Pi.single m₁ 1) ∈ eAddSubgroup ht H₀ := by
  have hm' : m₁.1 ≠ m₂.1 := Subtype.val_injective.ne hm
  let T := SpecialLinearGroup.transvection hm' c
  have hcomm : T * qMat ht 0 0 1 = qMat ht 0 0 1 * T :=
    transvection_mid_comm_qMat_zero ht hm c 1
  obtain ⟨-, -, hex⟩ := exists_qSubgroup_mul_mem_of_comm_zMat ht hK hZ hidx
  obtain ⟨q, ⟨u_q, v_q, z_q, rfl⟩, hqT⟩ := hex T hcomm
  obtain ⟨z, hz⟩ := huv
  have hconj : qMat ht (-u_q) (-v_q) (-z_q + u_q ⬝ᵥ v_q) *
      (T * qMat ht u v z * T⁻¹) *
      (qMat ht (-u_q) (-v_q) (-z_q + u_q ⬝ᵥ v_q))⁻¹ ∈ H₀ := by
    have hq_inv := qMat_inv ht u_q v_q z_q
    rw [← hq_inv]
    have h1 : (qMat ht u_q v_q z_q)⁻¹ * T * qMat ht u v z *
        ((qMat ht u_q v_q z_q)⁻¹ * T)⁻¹ ∈ H₀ :=
      H₀.mul_mem (H₀.mul_mem hqT hz) (H₀.inv_mem hqT)
    convert h1 using 1
    group
  rw [transvection_mid_conj_qMat ht hm c u v z, qMat_conj] at hconj
  have hmem : (u - (u m₁ * c) • Pi.single m₂ 1, v + (c * v m₂) • Pi.single m₁ 1) ∈
      eAddSubgroup ht H₀ := ⟨_, hconj⟩
  have hsub := (eAddSubgroup ht H₀).sub_mem hmem ⟨z, hz⟩
  convert hsub using 1
  ext <;> simp [sub_eq_add_neg]

/-- If `4 ≤ t` and `∃ u ≠ 0, (u, 0) ∈ eAddSubgroup ht H₀`, then
`∀ u, (u, 0) ∈ eAddSubgroup ht H₀` and `∀ u v, (u, v) ∈ eAddSubgroup ht H₀ → v = 0`. -/
theorem eAddSubgroup_eq_fst_of_exists_ne_zero {t : ℕ} [NeZero t] (ht4 : 4 ≤ t)
    {K : Type*} [Field K] [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (hK : Nat.card K = p) {H₀ : Subgroup (SpecialLinearGroup (Fin t) K)}
    (hZ : ¬ (zSubgroup (by omega : 2 ≤ t) K ≤ H₀))
    (hidx : H₀.index < 2 * p ^ (t - 1))
    {u₀ : Mid t → K} (hu₀_ne : u₀ ≠ 0)
    (hu₀_mem : (u₀, 0) ∈ eAddSubgroup (by omega : 2 ≤ t) H₀) :
    (∀ u : Mid t → K, (u, 0) ∈ eAddSubgroup (by omega : 2 ≤ t) H₀) ∧
      (∀ u v : Mid t → K, (u, v) ∈ eAddSubgroup (by omega : 2 ≤ t) H₀ → v = 0) := by
  have ht2 : 2 ≤ t := by omega
  have _ : Fintype K := Fintype.ofFinite K
  have hex_m₁ : ∃ m₁ : Mid t, u₀ m₁ ≠ 0 := by
    by_contra! hall
    exact hu₀_ne (funext hall)
  obtain ⟨m₁, hm₁⟩ := hex_m₁
  have hsingle_other : ∀ (m₂ : Mid t), m₁ ≠ m₂ → ∀ a : K,
      (Pi.single m₂ a, (0 : Mid t → K)) ∈ eAddSubgroup ht2 H₀ := by
    intro m₂ hm a
    have hinv := eAddSubgroup_mid_invariance ht2 hK hZ hidx hu₀_mem hm (-(u₀ m₁)⁻¹ * a)
    convert hinv using 1
    ext m
    · simp only [Pi.smul_apply, Pi.single_apply, smul_eq_mul]
      split_ifs with h
      · calc a = (u₀ m₁ * (u₀ m₁)⁻¹) * a := by rw [mul_inv_cancel₀ hm₁, one_mul]
          _ = -(u₀ m₁ * (-(u₀ m₁)⁻¹ * a)) * 1 := by ring
      · ring
    · simp
  let m_a : Mid t := midEquiv ht2 ⟨0, by omega⟩
  let m_b : Mid t := midEquiv ht2 ⟨1, by omega⟩
  have hm_ab : m_a ≠ m_b := fun h => by
    have := (midEquiv ht2).injective h
    simp at this
  obtain ⟨m₂, hm₁₂⟩ : ∃ m₂ : Mid t, m₁ ≠ m₂ := by
    by_cases h : m₁ = m_a
    · exact ⟨m_b, h ▸ hm_ab⟩
    · exact ⟨m_a, h⟩
  have hm₂_mem : (Pi.single m₂ 1, (0 : Mid t → K)) ∈ eAddSubgroup ht2 H₀ :=
    hsingle_other m₂ hm₁₂ 1
  have hsingle_m₁ : ∀ a : K, (Pi.single m₁ a, (0 : Mid t → K)) ∈ eAddSubgroup ht2 H₀ := by
    intro a
    have hinv := eAddSubgroup_mid_invariance ht2 hK hZ hidx hm₂_mem hm₁₂.symm (-a)
    convert hinv using 1
    ext m
    · simp only [Pi.single_eq_same, one_mul, neg_neg, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
      split_ifs <;> ring
    · simp
  have hsingle_all : ∀ (m : Mid t) (a : K),
      (Pi.single m a, (0 : Mid t → K)) ∈ eAddSubgroup ht2 H₀ := by
    intro m a
    by_cases hm : m₁ = m
    · exact hm ▸ hsingle_m₁ a
    · exact hsingle_other m hm a
  have hall_u : ∀ u : Mid t → K, (u, 0) ∈ eAddSubgroup ht2 H₀ := by
    intro u
    have heq : (u, (0 : Mid t → K)) = ∑ m : Mid t, (Pi.single m (u m), (0 : Mid t → K)) := by
      apply Prod.ext
      · rw [Prod.fst_sum]
        ext m
        simp
      · rw [Prod.snd_sum]
        simp
    rw [heq]
    exact AddSubgroup.sum_mem _ fun m _ => hsingle_all m (u m)
  refine ⟨hall_u, fun u v huv => ?_⟩
  have hE_card := (exists_qSubgroup_mul_mem_of_comm_zMat ht2 hK hZ hidx).2.1
  let ι : (Mid t → K) → eAddSubgroup ht2 H₀ := fun u' => ⟨(u', 0), hall_u u'⟩
  have hι_inj : Function.Injective ι := fun u₁ u₂ h =>
    congrArg Prod.fst (congrArg Subtype.val h)
  have _ : Fintype (eAddSubgroup ht2 H₀) := Fintype.ofFinite _
  have hcard_eq : Fintype.card (Mid t → K) = Fintype.card (eAddSubgroup ht2 H₀) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, card_mid_fun ht2 K, hK, hE_card]
  have hι_surj : Function.Surjective ι :=
    ((Fintype.bijective_iff_injective_and_card ι).mpr ⟨hι_inj, hcard_eq⟩).2
  obtain ⟨u', hu'⟩ := hι_surj ⟨(u, v), huv⟩
  exact (congrArg Prod.snd (congrArg Subtype.val hu')).symm

/-- Symmetric version: if `4 ≤ t` and `∃ v ≠ 0, (0, v) ∈ eAddSubgroup ht H₀`, then
`∀ v, (0, v) ∈ eAddSubgroup ht H₀` and `∀ u v, (u, v) ∈ eAddSubgroup ht H₀ → u = 0`. -/
theorem eAddSubgroup_eq_snd_of_exists_ne_zero {t : ℕ} [NeZero t] (ht4 : 4 ≤ t)
    {K : Type*} [Field K] [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (hK : Nat.card K = p) {H₀ : Subgroup (SpecialLinearGroup (Fin t) K)}
    (hZ : ¬ (zSubgroup (by omega : 2 ≤ t) K ≤ H₀))
    (hidx : H₀.index < 2 * p ^ (t - 1))
    {v₀ : Mid t → K} (hv₀_ne : v₀ ≠ 0)
    (hv₀_mem : (0, v₀) ∈ eAddSubgroup (by omega : 2 ≤ t) H₀) :
    (∀ v : Mid t → K, (0, v) ∈ eAddSubgroup (by omega : 2 ≤ t) H₀) ∧
      (∀ u v : Mid t → K, (u, v) ∈ eAddSubgroup (by omega : 2 ≤ t) H₀ → u = 0) := by
  have ht2 : 2 ≤ t := by omega
  have _ : Fintype K := Fintype.ofFinite K
  have hex_m₂ : ∃ m₂ : Mid t, v₀ m₂ ≠ 0 := by
    by_contra! hall
    exact hv₀_ne (funext hall)
  obtain ⟨m₂, hm₂⟩ := hex_m₂
  have hsingle_other : ∀ (m₁ : Mid t), m₁ ≠ m₂ → ∀ a : K,
      ((0 : Mid t → K), Pi.single m₁ a) ∈ eAddSubgroup ht2 H₀ := by
    intro m₁ hm a
    have hinv := eAddSubgroup_mid_invariance ht2 hK hZ hidx hv₀_mem hm (a * (v₀ m₂)⁻¹)
    convert hinv using 1
    ext m
    · simp
    · simp only [Pi.smul_apply, Pi.single_apply, smul_eq_mul]
      split_ifs with h
      · rw [mul_one, mul_assoc, inv_mul_cancel₀ hm₂, mul_one]
      · ring
  let m_a : Mid t := midEquiv ht2 ⟨0, by omega⟩
  let m_b : Mid t := midEquiv ht2 ⟨1, by omega⟩
  have hm_ab : m_a ≠ m_b := fun h => by
    have := (midEquiv ht2).injective h
    simp at this
  obtain ⟨m₁, hm₁₂⟩ : ∃ m₁ : Mid t, m₁ ≠ m₂ := by
    by_cases h : m_a = m₂
    · exact ⟨m_b, h ▸ hm_ab.symm⟩
    · exact ⟨m_a, h⟩
  have hm₁_mem : ((0 : Mid t → K), Pi.single m₁ 1) ∈ eAddSubgroup ht2 H₀ :=
    hsingle_other m₁ hm₁₂ 1
  have hsingle_m₂ : ∀ a : K, ((0 : Mid t → K), Pi.single m₂ a) ∈ eAddSubgroup ht2 H₀ := by
    intro a
    have hinv := eAddSubgroup_mid_invariance ht2 hK hZ hidx hm₁_mem hm₁₂.symm a
    convert hinv using 1
    ext m
    · simp
    · simp only [Pi.single_eq_same, mul_one, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
      split_ifs <;> ring
  have hsingle_all : ∀ (m : Mid t) (a : K),
      ((0 : Mid t → K), Pi.single m a) ∈ eAddSubgroup ht2 H₀ := by
    intro m a
    by_cases hm : m = m₂
    · exact hm ▸ hsingle_m₂ a
    · exact hsingle_other m hm a
  have hall_v : ∀ v : Mid t → K, (0, v) ∈ eAddSubgroup ht2 H₀ := by
    intro v
    have heq : ((0 : Mid t → K), v) = ∑ m : Mid t, ((0 : Mid t → K), Pi.single m (v m)) := by
      apply Prod.ext
      · rw [Prod.fst_sum]
        simp
      · rw [Prod.snd_sum]
        ext m
        simp
    rw [heq]
    exact AddSubgroup.sum_mem _ fun m _ => hsingle_all m (v m)
  refine ⟨hall_v, fun u v huv => ?_⟩
  have hE_card := (exists_qSubgroup_mul_mem_of_comm_zMat ht2 hK hZ hidx).2.1
  let ι : (Mid t → K) → eAddSubgroup ht2 H₀ := fun v' => ⟨(0, v'), hall_v v'⟩
  have hι_inj : Function.Injective ι := fun v₁ v₂ h =>
    congrArg Prod.snd (congrArg Subtype.val h)
  have _ : Fintype (eAddSubgroup ht2 H₀) := Fintype.ofFinite _
  have hcard_eq : Fintype.card (Mid t → K) = Fintype.card (eAddSubgroup ht2 H₀) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, card_mid_fun ht2 K, hK, hE_card]
  have hι_surj : Function.Surjective ι :=
    ((Fintype.bijective_iff_injective_and_card ι).mpr ⟨hι_inj, hcard_eq⟩).2
  obtain ⟨v', hv'⟩ := hι_surj ⟨(u, v), huv⟩
  exact (congrArg Prod.fst (congrArg Subtype.val hv')).symm

/-- For `t ≥ 4`, if `5 ≤ t ∨ p ≠ 2`, `¬ (zSubgroup ht K ≤ H₀)`, and `H₀.index < 2 * p ^ (t - 1)`,
then `eAddSubgroup ht H₀` is either `⊤ × ⊥` or `⊥ × ⊤`. -/
theorem eAddSubgroup_dichotomy {t : ℕ} [NeZero t] (ht4 : 4 ≤ t)
    {K : Type*} [Field K] [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (hK : Nat.card K = p) (htp : 5 ≤ t ∨ p ≠ 2)
    {H₀ : Subgroup (SpecialLinearGroup (Fin t) K)}
    (hZ : ¬ (zSubgroup (by omega : 2 ≤ t) K ≤ H₀))
    (hidx : H₀.index < 2 * p ^ (t - 1)) :
    ((∀ u : Mid t → K, (u, 0) ∈ eAddSubgroup (by omega : 2 ≤ t) H₀) ∧
        (∀ u v : Mid t → K, (u, v) ∈ eAddSubgroup (by omega : 2 ≤ t) H₀ → v = 0)) ∨
      ((∀ v : Mid t → K, (0, v) ∈ eAddSubgroup (by omega : 2 ≤ t) H₀) ∧
        (∀ u v : Mid t → K, (u, v) ∈ eAddSubgroup (by omega : 2 ≤ t) H₀ → u = 0)) := by
  have ht2 : 2 ≤ t := by omega
  have _ : Fintype K := Fintype.ofFinite K
  by_cases hu : ∃ u₀ : Mid t → K, u₀ ≠ 0 ∧ (u₀, 0) ∈ eAddSubgroup ht2 H₀
  · obtain ⟨u₀, hu₀_ne, hu₀_mem⟩ := hu
    exact Or.inl (eAddSubgroup_eq_fst_of_exists_ne_zero ht4 hK hZ hidx hu₀_ne hu₀_mem)
  · by_cases hv : ∃ v₀ : Mid t → K, v₀ ≠ 0 ∧ (0, v₀) ∈ eAddSubgroup ht2 H₀
    · obtain ⟨v₀, hv₀_ne, hv₀_mem⟩ := hv
      exact Or.inr (eAddSubgroup_eq_snd_of_exists_ne_zero ht4 hK hZ hidx hv₀_ne hv₀_mem)
    · exfalso
      have hu' : ∀ u₀ : Mid t → K, (u₀, 0) ∈ eAddSubgroup ht2 H₀ → u₀ = 0 :=
        fun u₀ h => by_contra fun hne => hu ⟨u₀, hne, h⟩
      have hv' : ∀ v₀ : Mid t → K, (0, v₀) ∈ eAddSubgroup ht2 H₀ → v₀ = 0 :=
        fun v₀ h => by_contra fun hne => hv ⟨v₀, hne, h⟩
      have hE_card := (exists_qSubgroup_mul_mem_of_comm_zMat ht2 hK hZ hidx).2.1
      let π₁ : eAddSubgroup ht2 H₀ → (Mid t → K) := fun x => x.1.1
      have hπ₁_inj : Function.Injective π₁ := by
        intro x y hxy
        have hdiff_mem : (x.1.1 - y.1.1, x.1.2 - y.1.2) ∈ eAddSubgroup ht2 H₀ :=
          (eAddSubgroup ht2 H₀).sub_mem x.2 y.2
        have h1 : x.1.1 - y.1.1 = 0 := sub_eq_zero.mpr hxy
        rw [h1] at hdiff_mem
        have h2 : x.1.2 - y.1.2 = 0 := hv' _ hdiff_mem
        exact Subtype.ext (Prod.ext hxy (sub_eq_zero.mp h2))
      have _ : Fintype (eAddSubgroup ht2 H₀) := Fintype.ofFinite _
      have hcard_eq : Fintype.card (eAddSubgroup ht2 H₀) = Fintype.card (Mid t → K) := by
        rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, card_mid_fun ht2 K, hK, hE_card]
      have hπ₁_surj : Function.Surjective π₁ :=
        ((Fintype.bijective_iff_injective_and_card π₁).mpr ⟨hπ₁_inj, hcard_eq⟩).2
      let m₀ : Mid t := midEquiv ht2 ⟨0, by omega⟩
      let m₁ : Mid t := midEquiv ht2 ⟨1, by omega⟩
      have hm₀₁ : m₀ ≠ m₁ := fun h => by
        have := (midEquiv ht2).injective h
        simp at this
      obtain ⟨⟨⟨u₀, v₀⟩, hx₀⟩, hu₀_eq⟩ := hπ₁_surj (Pi.single m₀ 1)
      change u₀ = Pi.single m₀ 1 at hu₀_eq
      subst hu₀_eq
      have hy_mem : (Pi.single m₁ 1, (-v₀ m₁) • Pi.single m₀ 1) ∈ eAddSubgroup ht2 H₀ := by
        have hinv := eAddSubgroup_mid_invariance ht2 hK hZ hidx hx₀ hm₀₁ (-1)
        convert hinv using 1
        ext m
        · simp [Pi.single_eq_same]
        · simp
      set b : K := -v₀ m₁
      have hb_ne : b ≠ 0 := by
        intro hb0
        have hmem0 : (Pi.single m₁ (1 : K), (0 : Mid t → K)) ∈ eAddSubgroup ht2 H₀ := by
          convert hy_mem using 1
          rw [hb0, zero_smul]
        have hsingle0 := hu' (Pi.single m₁ 1) hmem0
        have := congrFun hsingle0 m₁
        simp at this
      rcases htp with ht5 | hp2
      · let m₂ : Mid t := midEquiv ht2 ⟨2, by omega⟩
        have hm₂₁ : m₂ ≠ m₁ := fun h => by
          have := (midEquiv ht2).injective h
          simp at this
        have hm₀₂ : m₀ ≠ m₂ := fun h => by
          have := (midEquiv ht2).injective h
          simp at this
        obtain ⟨⟨⟨u₂, v₂⟩, hx₂⟩, hu₂_eq⟩ := hπ₁_surj (Pi.single m₂ 1)
        change u₂ = Pi.single m₂ 1 at hu₂_eq
        subst hu₂_eq
        have hy'_mem : (Pi.single m₁ 1, (-v₂ m₁) • Pi.single m₂ 1) ∈ eAddSubgroup ht2 H₀ := by
          have hinv := eAddSubgroup_mid_invariance ht2 hK hZ hidx hx₂ hm₂₁ (-1)
          convert hinv using 1
          ext m
          · simp [Pi.single_eq_same]
          · simp
        have hsub := (eAddSubgroup ht2 H₀).sub_mem hy_mem hy'_mem
        have hsub' : ((0 : Mid t → K), b • Pi.single m₀ 1 - (-v₂ m₁) • Pi.single m₂ 1) ∈
            eAddSubgroup ht2 H₀ := by
          convert hsub using 1
          ext <;> simp
        have hv_eq := hv' _ hsub'
        have eval_m₀ := congrFun hv_eq m₀
        simp only [Pi.sub_apply, Pi.smul_apply, Pi.single_eq_same,
          Pi.single_eq_of_ne hm₀₂, smul_eq_mul, mul_one, mul_zero, sub_zero,
          Pi.zero_apply] at eval_m₀
        exact hb_ne eval_m₀
      · have hx'_mem : (Pi.single m₀ 1, (-b) • Pi.single m₁ 1) ∈ eAddSubgroup ht2 H₀ := by
          have hinv := eAddSubgroup_mid_invariance ht2 hK hZ hidx hy_mem hm₀₁.symm (-1)
          convert hinv using 1
          ext m
          · simp [Pi.single_eq_same]
          · simp [Pi.single_eq_same]
        have hiso := isotropic_eAddSubgroup ht2 H₀ hx'_mem hy_mem
        have hW₀_bot := (prime_field_qSubgroup_bounds ht2 hK hZ).1
        rw [hW₀_bot, AddSubgroup.mem_bot] at hiso
        simp only [single_dotProduct, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul,
          one_mul] at hiso
        have h2b : (2 : K) * b = 0 := by linear_combination hiso
        have h20 : ((2 : ℕ) : K) = 0 := by
          rcases mul_eq_zero.mp h2b with h2 | hb
          · exact_mod_cast h2
          · exact absurd hb hb_ne
        have hp_dvd : p ∣ 2 := (CharP.cast_eq_zero_iff K p 2).mp h20
        have hp : p.Prime := Fact.out
        have hp_le : p ≤ 2 := Nat.le_of_dvd (by decide) hp_dvd
        have hp_ge : 2 ≤ p := hp.two_le
        omega

/-- Every `qMat ht (Pi.single m₀ 1) 0 z₁` is conjugate in `SL(t, K)` to `qMat ht 0 0 1`. -/
theorem exists_conj_qMat_single_left {t : ℕ} [NeZero t] {K : Type*} [Field K] (ht : 2 ≤ t)
    (m₀ : Mid t) (z₁ : K) :
    ∃ s : SpecialLinearGroup (Fin t) K,
      s * qMat ht (Pi.single m₀ 1) 0 z₁ * s⁻¹ = qMat ht 0 0 1 := by
  let q₀ := qMat ht 0 (Pi.single m₀ (z₁ - 1)) 0
  have hq₀ : q₀ * qMat ht (Pi.single m₀ 1) 0 z₁ * q₀⁻¹ = qMat ht (Pi.single m₀ 1) 0 1 := by
    rw [qMat_conj]
    congr 1
    simp only [zero_dotProduct, single_dotProduct, Pi.single_eq_same, one_mul]
    ring
  have hm_ne : lastIdx t ≠ m₀.1 := m₀.2.2.symm
  let T₀ := SpecialLinearGroup.transvection hm_ne (1 : K)
  have hT₀ : T₀ * qMat ht (Pi.single m₀ 1) 0 1 * T₀⁻¹ = qMat ht 0 0 1 := by
    rw [SpecialLinearGroup.transvection_inv]
    apply Subtype.ext
    change (1 + single (lastIdx t) m₀.1 (1 : K)) * (1 + qNil (Pi.single m₀ 1) 0 1) *
        (1 + single (lastIdx t) m₀.1 (-1 : K)) = 1 + qNil 0 0 1
    have hsn : single (lastIdx t) m₀.1 (1 : K) * qNil (Pi.single m₀ 1) 0 1 = 0 := by
      ext i j
      by_cases hi : i = lastIdx t
      · subst hi
        rw [single_mul_apply_same, qNil_apply_mid_left]
        simp
      · exact single_mul_apply_of_ne _ _ _ _ _ hi _
    have hns : qNil (Pi.single m₀ (1 : K)) 0 1 * single (lastIdx t) m₀.1 (-1 : K) =
        qNil (Pi.single m₀ (-1 : K)) 0 0 := by
      ext i j
      by_cases hj : j = m₀.1
      · subst hj
        rw [mul_single_apply_same, qNil_apply, qNil_apply, ite_eq_right m₀.2.2,
          dite_eq_left m₀.2]
        by_cases hi : i = firstIdx t
        · subst hi
          simp [Pi.single_eq_same]
        · simp [hi]
      · rw [mul_single_apply_of_ne _ _ _ _ _ hj, qNil_apply]
        split_ifs with h1 h2 h3
        · rfl
        · rw [Pi.single_eq_of_ne (fun h => hj (congrArg Subtype.val h))]
        · rfl
        · rfl
        · rfl
        · rfl
    have hss : single (lastIdx t) m₀.1 (1 : K) * single (lastIdx t) m₀.1 (-1 : K) = 0 :=
      single_mul_single_of_ne (1 : K) (lastIdx t) m₀.1 (lastIdx t) hm_ne.symm (-1 : K)
    have hsns : single (lastIdx t) m₀.1 (1 : K) * qNil (Pi.single m₀ 1) 0 1 *
        single (lastIdx t) m₀.1 (-1 : K) = 0 := by
      rw [hsn, zero_mul]
    calc (1 + single (lastIdx t) m₀.1 (1 : K)) * (1 + qNil (Pi.single m₀ 1) 0 1) *
          (1 + single (lastIdx t) m₀.1 (-1 : K))
      _ = 1 + (single (lastIdx t) m₀.1 (1 : K) + single (lastIdx t) m₀.1 (-1 : K) +
            single (lastIdx t) m₀.1 (1 : K) * single (lastIdx t) m₀.1 (-1 : K)) +
          (qNil (Pi.single m₀ 1) 0 1 +
            single (lastIdx t) m₀.1 (1 : K) * qNil (Pi.single m₀ 1) 0 1 +
            qNil (Pi.single m₀ 1) 0 1 * single (lastIdx t) m₀.1 (-1 : K) +
            single (lastIdx t) m₀.1 (1 : K) * qNil (Pi.single m₀ 1) 0 1 *
              single (lastIdx t) m₀.1 (-1 : K)) := by
          noncomm_ring
      _ = 1 + (qNil (Pi.single m₀ 1) 0 1 + qNil (Pi.single m₀ (-1 : K)) 0 0) := by
          rw [← single_add, add_neg_cancel, single_zero, hss, hsns, hsn, hns]
          simp
      _ = 1 + qNil 0 0 1 := by
          rw [qNil_add, ← Pi.single_add, add_neg_cancel, Pi.single_zero, add_zero, add_zero]
  refine ⟨T₀ * q₀, ?_⟩
  calc (T₀ * q₀) * qMat ht (Pi.single m₀ 1) 0 z₁ * (T₀ * q₀)⁻¹
    _ = T₀ * (q₀ * qMat ht (Pi.single m₀ 1) 0 z₁ * q₀⁻¹) * T₀⁻¹ := by group
    _ = qMat ht 0 0 1 := by rw [hq₀, hT₀]

/-- Every `qMat ht 0 (Pi.single m₀ 1) z₁` is conjugate in `SL(t, K)` to `qMat ht 0 0 1`. -/
theorem exists_conj_qMat_single_right {t : ℕ} [NeZero t] {K : Type*} [Field K] (ht : 2 ≤ t)
    (m₀ : Mid t) (z₁ : K) :
    ∃ s : SpecialLinearGroup (Fin t) K,
      s * qMat ht 0 (Pi.single m₀ 1) z₁ * s⁻¹ = qMat ht 0 0 1 := by
  let q₀ := qMat ht (Pi.single m₀ (1 - z₁)) 0 0
  have hq₀ : q₀ * qMat ht 0 (Pi.single m₀ 1) z₁ * q₀⁻¹ = qMat ht 0 (Pi.single m₀ 1) 1 := by
    rw [qMat_conj]
    congr 1
    simp only [dotProduct_zero, single_dotProduct, Pi.single_eq_same, mul_one]
    ring
  have hm_ne : m₀.1 ≠ firstIdx t := m₀.2.1
  let T₁ := SpecialLinearGroup.transvection hm_ne (-1 : K)
  have hT₁ : T₁ * qMat ht 0 (Pi.single m₀ 1) 1 * T₁⁻¹ = qMat ht 0 0 1 := by
    rw [SpecialLinearGroup.transvection_inv, neg_neg]
    apply Subtype.ext
    change (1 + single m₀.1 (firstIdx t) (-1 : K)) * (1 + qNil 0 (Pi.single m₀ 1) 1) *
        (1 + single m₀.1 (firstIdx t) (1 : K)) = 1 + qNil 0 0 1
    have hns : qNil 0 (Pi.single m₀ (1 : K)) 1 * single m₀.1 (firstIdx t) (1 : K) = 0 := by
      ext i j
      by_cases hj : j = firstIdx t
      · subst hj
        rw [mul_single_apply_same, qNil_apply_mid_right]
        simp
      · exact mul_single_apply_of_ne _ _ _ _ _ hj _
    have hsn : single m₀.1 (firstIdx t) (-1 : K) * qNil 0 (Pi.single m₀ (1 : K)) 1 =
        qNil 0 (Pi.single m₀ (-1 : K)) 0 := by
      ext i j
      by_cases hi : i = m₀.1
      · subst hi
        rw [single_mul_apply_same, qNil_apply, qNil_apply, ite_eq_right m₀.2.1,
          dite_eq_left m₀.2]
        by_cases hj : j = lastIdx t
        · subst hj
          simp [Pi.single_eq_same]
        · simp [hj]
      · rw [single_mul_apply_of_ne _ _ _ _ _ hi, qNil_apply]
        split_ifs with h1 h2 h3 h4 h5
        · rfl
        · rfl
        · rfl
        · rw [Pi.single_eq_of_ne (fun h => hi (congrArg Subtype.val h))]
        · rfl
        · rfl
    have hss : single m₀.1 (firstIdx t) (-1 : K) * single m₀.1 (firstIdx t) (1 : K) = 0 :=
      single_mul_single_of_ne (-1 : K) m₀.1 (firstIdx t) m₀.1 hm_ne.symm (1 : K)
    have hsns : single m₀.1 (firstIdx t) (-1 : K) * qNil 0 (Pi.single m₀ 1) 1 *
        single m₀.1 (firstIdx t) (1 : K) = 0 := by
      rw [mul_assoc, hns, mul_zero]
    calc (1 + single m₀.1 (firstIdx t) (-1 : K)) * (1 + qNil 0 (Pi.single m₀ 1) 1) *
          (1 + single m₀.1 (firstIdx t) (1 : K))
      _ = 1 + (single m₀.1 (firstIdx t) (-1 : K) + single m₀.1 (firstIdx t) (1 : K) +
            single m₀.1 (firstIdx t) (-1 : K) * single m₀.1 (firstIdx t) (1 : K)) +
          (qNil 0 (Pi.single m₀ 1) 1 +
            single m₀.1 (firstIdx t) (-1 : K) * qNil 0 (Pi.single m₀ 1) 1 +
            qNil 0 (Pi.single m₀ 1) 1 * single m₀.1 (firstIdx t) (1 : K) +
            single m₀.1 (firstIdx t) (-1 : K) * qNil 0 (Pi.single m₀ 1) 1 *
              single m₀.1 (firstIdx t) (1 : K)) := by
          noncomm_ring
      _ = 1 + (qNil 0 (Pi.single m₀ 1) 1 + qNil 0 (Pi.single m₀ (-1 : K)) 0) := by
          rw [← single_add, neg_add_cancel, single_zero, hss, hsns, hsn, hns]
          simp
      _ = 1 + qNil 0 0 1 := by
          rw [qNil_add, ← Pi.single_add, add_neg_cancel, Pi.single_zero, add_zero, add_zero]
  refine ⟨T₁ * q₀, ?_⟩
  calc (T₁ * q₀) * qMat ht 0 (Pi.single m₀ 1) z₁ * (T₁ * q₀)⁻¹
    _ = T₁ * (q₀ * qMat ht 0 (Pi.single m₀ 1) z₁ * q₀⁻¹) * T₁⁻¹ := by group
    _ = qMat ht 0 0 1 := by rw [hq₀, hT₁]

/-- Disjoint orbit sum bound: if `qMat ht 0 0 1 ∉ H₀`, `g ∈ H₀`, `s * g * s⁻¹ = qMat ht 0 0 1`,
and `C ≤ SL(t, K)` centralizes `g`, then
`H₀.relIndex (qSubgroup ht K) + H₀.relIndex C ≤ H₀.index`. -/
theorem relIndex_add_relIndex_le_index_of_conj_zMat {t : ℕ} [NeZero t] {K : Type*} [Field K]
    [Finite K] (ht : 2 ≤ t) {H₀ C : Subgroup (SpecialLinearGroup (Fin t) K)}
    (hz₀ : qMat ht 0 0 1 ∉ H₀) {g s : SpecialLinearGroup (Fin t) K} (hg : g ∈ H₀)
    (hs : s * g * s⁻¹ = qMat ht 0 0 1) (hC : ∀ c ∈ C, c * g = g * c) :
    H₀.relIndex (qSubgroup ht K) + H₀.relIndex C ≤ H₀.index := by
  let Q := qSubgroup ht K
  let X := SpecialLinearGroup (Fin t) K ⧸ H₀
  let x₀ : X := QuotientGroup.mk 1
  let z₀ : SpecialLinearGroup (Fin t) K := qMat ht 0 0 1
  let f : MulAction.orbit Q x₀ ⊕ MulAction.orbit C x₀ → X :=
    Sum.elim (fun y => s⁻¹ • y.1) (fun w => w.1)
  have hmove : ∀ y : MulAction.orbit Q x₀, g • (s⁻¹ • y.1) ≠ s⁻¹ • y.1 := by
    rintro ⟨_, ⟨q, ⟨u, v, z, rfl⟩⟩, rfl⟩ hfix
    apply hz₀
    have hcomm_q : z₀ * qMat ht u v z = qMat ht u v z * z₀ := by
      change qMat ht 0 0 1 * qMat ht u v z = qMat ht u v z * qMat ht 0 0 1
      rw [← mul_inv_eq_iff_eq_mul, qMat_conj]
      simp
    have hgs : g * s⁻¹ = s⁻¹ * z₀ := by
      change g * s⁻¹ = s⁻¹ * qMat ht 0 0 1
      rw [← hs]
      group
    have h1 : s⁻¹ • (z₀ • (qMat ht u v z • x₀)) = s⁻¹ • (qMat ht u v z • x₀) := by
      calc s⁻¹ • (z₀ • (qMat ht u v z • x₀))
        _ = (s⁻¹ * z₀) • (qMat ht u v z • x₀) := (mul_smul _ _ _).symm
        _ = (g * s⁻¹) • (qMat ht u v z • x₀) := by rw [hgs]
        _ = g • (s⁻¹ • (qMat ht u v z • x₀)) := mul_smul _ _ _
        _ = s⁻¹ • (qMat ht u v z • x₀) := hfix
    have h2 : z₀ • (qMat ht u v z • x₀) = qMat ht u v z • x₀ := by
      have := congrArg (s • ·) h1
      rwa [smul_inv_smul, smul_inv_smul] at this
    have h3 : qMat ht u v z • (z₀ • x₀) = qMat ht u v z • x₀ := by
      rw [← mul_smul, ← hcomm_q, mul_smul]
      exact h2
    have h4 : z₀ • x₀ = x₀ := by
      have := congrArg ((qMat ht u v z)⁻¹ • ·) h3
      rwa [inv_smul_smul, inv_smul_smul] at this
    have h5 : QuotientGroup.mk (z₀ * 1) = (QuotientGroup.mk 1 : X) := h4
    rw [mul_one, QuotientGroup.eq, mul_one, inv_mem_iff] at h5
    exact h5
  have hfixC : ∀ w : MulAction.orbit C x₀, g • w.1 = w.1 := by
    rintro ⟨_, ⟨c, hcC⟩, rfl⟩
    have hg0 : g • x₀ = x₀ := by
      change QuotientGroup.mk (g * 1) = QuotientGroup.mk 1
      rw [mul_one, QuotientGroup.eq, mul_one, inv_mem_iff]
      exact hg
    change g • (c • x₀) = c • x₀
    rw [← mul_smul, ← hC c hcC, mul_smul, hg0]
  have hf_inj : Function.Injective f := by
    rintro (y₁ | w₁) (y₂ | w₂) h
    · refine congrArg Sum.inl (Subtype.ext ?_)
      have := congrArg (s • ·) h
      simpa [f] using this
    · exfalso
      change s⁻¹ • y₁.1 = w₂.1 at h
      have hm := hmove y₁
      rw [h] at hm
      exact hm (hfixC w₂)
    · exfalso
      change w₁.1 = s⁻¹ • y₂.1 at h
      have hm := hmove y₂
      rw [← h] at hm
      exact hm (hfixC w₁)
    · exact congrArg Sum.inr (Subtype.ext h)
  rw [← card_orbit_quotient_one_eq_relIndex H₀ Q, ← card_orbit_quotient_one_eq_relIndex H₀ C,
    ← Nat.card_sum, Subgroup.index]
  exact Nat.card_le_card_of_injective f hf_inj

/-- Subgroup of `qSubgroup ht K` where `v m₀ = 0`. -/
@[expose]
def qSubgroupVMidZero {t : ℕ} [NeZero t] (ht : 2 ≤ t) (K : Type*) [Field K] (m₀ : Mid t) :
    Subgroup (SpecialLinearGroup (Fin t) K) where
  carrier := {g | ∃ (u v : Mid t → K) (z : K), v m₀ = 0 ∧ g = qMat ht u v z}
  one_mem' := ⟨0, 0, 0, rfl, (qMat_zero ht).symm⟩
  mul_mem' := by
    rintro _ _ ⟨u₁, v₁, z₁, hv₁, rfl⟩ ⟨u₂, v₂, z₂, hv₂, rfl⟩
    refine ⟨u₁ + u₂, v₁ + v₂, z₁ + z₂ + u₁ ⬝ᵥ v₂, ?_, qMat_mul ht u₁ v₁ u₂ v₂ z₁ z₂⟩
    simp [hv₁, hv₂]
  inv_mem' := by
    rintro _ ⟨u, v, z, hv, rfl⟩
    refine ⟨-u, -v, -z + u ⬝ᵥ v, ?_, qMat_inv ht u v z⟩
    simp [hv]

/-- Subgroup of `qSubgroup ht K` where `u m₀ = 0`. -/
@[expose]
def qSubgroupUMidZero {t : ℕ} [NeZero t] (ht : 2 ≤ t) (K : Type*) [Field K] (m₀ : Mid t) :
    Subgroup (SpecialLinearGroup (Fin t) K) where
  carrier := {g | ∃ (u v : Mid t → K) (z : K), u m₀ = 0 ∧ g = qMat ht u v z}
  one_mem' := ⟨0, 0, 0, rfl, (qMat_zero ht).symm⟩
  mul_mem' := by
    rintro _ _ ⟨u₁, v₁, z₁, hu₁, rfl⟩ ⟨u₂, v₂, z₂, hu₂, rfl⟩
    refine ⟨u₁ + u₂, v₁ + v₂, z₁ + z₂ + u₁ ⬝ᵥ v₂, ?_, qMat_mul ht u₁ v₁ u₂ v₂ z₁ z₂⟩
    simp [hu₁, hu₂]
  inv_mem' := by
    rintro _ ⟨u, v, z, hu, rfl⟩
    refine ⟨-u, -v, -z + u ⬝ᵥ v, ?_, qMat_inv ht u v z⟩
    simp [hu]

theorem card_qSubgroupVMidZero_mul_card {t : ℕ} [NeZero t] (ht : 2 ≤ t) (K : Type*) [Field K]
    [Finite K] (m₀ : Mid t) :
    Nat.card (qSubgroupVMidZero ht K m₀) * Nat.card K = Nat.card (qSubgroup ht K) := by
  let φ : qSubgroup ht K →* Multiplicative K :=
    { toFun := fun g => Multiplicative.ofAdd ((g.1 : Matrix (Fin t) (Fin t) K) m₀.1 (lastIdx t))
      map_one' := by
        change Multiplicative.ofAdd ((1 : Matrix (Fin t) (Fin t) K) m₀.1 (lastIdx t)) = 1
        rw [Matrix.one_apply_ne m₀.2.2, ofAdd_zero]
      map_mul' := by
        rintro ⟨_, u₁, v₁, z₁, rfl⟩ ⟨_, u₂, v₂, z₂, rfl⟩
        change Multiplicative.ofAdd ((qMat ht u₁ v₁ z₁ * qMat ht u₂ v₂ z₂ :
            SpecialLinearGroup (Fin t) K).1 m₀.1 (lastIdx t)) =
          Multiplicative.ofAdd ((qMat ht u₁ v₁ z₁).1 m₀.1 (lastIdx t)) *
          Multiplicative.ofAdd ((qMat ht u₂ v₂ z₂).1 m₀.1 (lastIdx t))
        rw [qMat_mul, qMat_apply_mid_lastIdx, qMat_apply_mid_lastIdx, qMat_apply_mid_lastIdx,
          Pi.add_apply, ofAdd_add] }
  have hφ_surj : Function.Surjective φ := by
    intro a
    refine ⟨⟨qMat ht 0 (Pi.single m₀ (Multiplicative.toAdd a)) 0, 0, _, 0, rfl⟩, ?_⟩
    change Multiplicative.ofAdd ((qMat ht 0 (Pi.single m₀ (Multiplicative.toAdd a)) 0).1
      m₀.1 (lastIdx t)) = a
    rw [qMat_apply_mid_lastIdx, Pi.single_eq_same, ofAdd_toAdd]
  have eKer : φ.ker ≃ qSubgroupVMidZero ht K m₀ :=
    { toFun := fun k => ⟨k.1.1, by
        rcases k with ⟨⟨_, u, v, z, rfl⟩, hk⟩
        have hv : v m₀ = 0 := by
          have hk' := Multiplicative.ofAdd.injective hk
          rwa [qMat_apply_mid_lastIdx] at hk'
        exact ⟨u, v, z, hv, rfl⟩⟩
      invFun := fun g => ⟨⟨g.1, by
        obtain ⟨_, u, v, z, -, rfl⟩ := g
        exact ⟨u, v, z, rfl⟩⟩, by
        obtain ⟨_, u, v, z, hv, rfl⟩ := g
        rw [MonoidHom.mem_ker]
        change Multiplicative.ofAdd ((qMat ht u v z).1 m₀.1 (lastIdx t)) = 1
        rw [qMat_apply_mid_lastIdx, hv, ofAdd_zero]⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
  have h2 : Nat.card (qSubgroup ht K ⧸ φ.ker) = Nat.card (Multiplicative K) :=
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφ_surj).toEquiv
  rw [h1, h2, Nat.card_congr Multiplicative.toAdd, Nat.card_congr eKer, mul_comm]

theorem card_qSubgroupUMidZero_mul_card {t : ℕ} [NeZero t] (ht : 2 ≤ t) (K : Type*) [Field K]
    [Finite K] (m₀ : Mid t) :
    Nat.card (qSubgroupUMidZero ht K m₀) * Nat.card K = Nat.card (qSubgroup ht K) := by
  let φ : qSubgroup ht K →* Multiplicative K :=
    { toFun := fun g => Multiplicative.ofAdd ((g.1 : Matrix (Fin t) (Fin t) K) (firstIdx t) m₀.1)
      map_one' := by
        change Multiplicative.ofAdd ((1 : Matrix (Fin t) (Fin t) K) (firstIdx t) m₀.1) = 1
        rw [Matrix.one_apply_ne m₀.2.1.symm, ofAdd_zero]
      map_mul' := by
        rintro ⟨_, u₁, v₁, z₁, rfl⟩ ⟨_, u₂, v₂, z₂, rfl⟩
        change Multiplicative.ofAdd ((qMat ht u₁ v₁ z₁ * qMat ht u₂ v₂ z₂ :
            SpecialLinearGroup (Fin t) K).1 (firstIdx t) m₀.1) =
          Multiplicative.ofAdd ((qMat ht u₁ v₁ z₁).1 (firstIdx t) m₀.1) *
          Multiplicative.ofAdd ((qMat ht u₂ v₂ z₂).1 (firstIdx t) m₀.1)
        rw [qMat_mul, qMat_apply_firstIdx_mid, qMat_apply_firstIdx_mid, qMat_apply_firstIdx_mid,
          Pi.add_apply, ofAdd_add] }
  have hφ_surj : Function.Surjective φ := by
    intro a
    refine ⟨⟨qMat ht (Pi.single m₀ (Multiplicative.toAdd a)) 0 0, _, 0, 0, rfl⟩, ?_⟩
    change Multiplicative.ofAdd ((qMat ht (Pi.single m₀ (Multiplicative.toAdd a)) 0 0).1
      (firstIdx t) m₀.1) = a
    rw [qMat_apply_firstIdx_mid, Pi.single_eq_same, ofAdd_toAdd]
  have eKer : φ.ker ≃ qSubgroupUMidZero ht K m₀ :=
    { toFun := fun k => ⟨k.1.1, by
        rcases k with ⟨⟨_, u, v, z, rfl⟩, hk⟩
        have hu : u m₀ = 0 := by
          have hk' := Multiplicative.ofAdd.injective hk
          rwa [qMat_apply_firstIdx_mid] at hk'
        exact ⟨u, v, z, hu, rfl⟩⟩
      invFun := fun g => ⟨⟨g.1, by
        obtain ⟨_, u, v, z, -, rfl⟩ := g
        exact ⟨u, v, z, rfl⟩⟩, by
        obtain ⟨_, u, v, z, hu, rfl⟩ := g
        rw [MonoidHom.mem_ker]
        change Multiplicative.ofAdd ((qMat ht u v z).1 (firstIdx t) m₀.1) = 1
        rw [qMat_apply_firstIdx_mid, hu, ofAdd_zero]⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
  have h2 : Nat.card (qSubgroup ht K ⧸ φ.ker) = Nat.card (Multiplicative K) :=
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφ_surj).toEquiv
  rw [h1, h2, Nat.card_congr Multiplicative.toAdd, Nat.card_congr eKer, mul_comm]

/-- For `t ≥ 4` and a prime field `K` of order `p` with `5 ≤ t ∨ p ≠ 2`, if
`¬ (zSubgroup ht K ≤ H₀)`, then `p ^ (t - 1) + p ^ (t - 2) ≤ H₀.index`. -/
theorem pow_pred_add_pow_sub_two_le_index {t : ℕ} [NeZero t] (ht4 : 4 ≤ t)
    {K : Type*} [Field K] [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (hK : Nat.card K = p) (htp : 5 ≤ t ∨ p ≠ 2)
    {H₀ : Subgroup (SpecialLinearGroup (Fin t) K)}
    (hZ : ¬ (zSubgroup (by omega : 2 ≤ t) K ≤ H₀)) :
    p ^ (t - 1) + p ^ (t - 2) ≤ H₀.index := by
  have hp : p.Prime := Fact.out
  have ht2 : 2 ≤ t := by omega
  by_cases hidx_ge : 2 * p ^ (t - 1) ≤ H₀.index
  · have hle : p ^ (t - 2) ≤ p ^ (t - 1) := Nat.pow_le_pow_right hp.pos (by omega)
    omega
  have hidx : H₀.index < 2 * p ^ (t - 1) := Nat.lt_of_not_le hidx_ge
  have hz₀ : qMat ht2 0 0 1 ∉ H₀ :=
    fun h => hZ ((zSubgroup_le_iff_qMat_one_mem ht2 hK H₀).mpr h)
  obtain ⟨hrel_Q, hE_card, -⟩ := exists_qSubgroup_mul_mem_of_comm_zMat ht2 hK hZ hidx
  have hinf_Q : Nat.card ↥(H₀ ⊓ qSubgroup ht2 K) = p ^ (t - 2) := by
    rw [(prime_field_qSubgroup_bounds ht2 hK hZ).2.1, hE_card]
  let m₀ : Mid t := midEquiv ht2 ⟨0, by omega⟩
  rcases eAddSubgroup_dichotomy ht4 hK htp hZ hidx with ⟨hu_all, hv_zero⟩ | ⟨hv_all, hu_zero⟩
  · obtain ⟨z₁, hg⟩ := hu_all (Pi.single m₀ 1)
    obtain ⟨s, hs⟩ := exists_conj_qMat_single_left ht2 m₀ z₁
    let C := qSubgroupVMidZero ht2 K m₀
    have hC_comm : ∀ c ∈ C, c * qMat ht2 (Pi.single m₀ 1) 0 z₁ =
        qMat ht2 (Pi.single m₀ 1) 0 z₁ * c := by
      rintro _ ⟨u, v, z, hv, rfl⟩
      rw [← mul_inv_eq_iff_eq_mul, qMat_conj]
      simp [hv]
    have hinf_eq : H₀ ⊓ C = H₀ ⊓ qSubgroup ht2 K := by
      ext x
      simp only [Subgroup.mem_inf]
      constructor
      · rintro ⟨hxH, u, v, z, -, rfl⟩
        exact ⟨hxH, u, v, z, rfl⟩
      · rintro ⟨hxH, u, v, z, rfl⟩
        have hv0 : v = 0 := hv_zero u v ⟨z, hxH⟩
        exact ⟨hxH, u, v, z, by simp [hv0], rfl⟩
    have hrel_C : H₀.relIndex C = p ^ (t - 2) := by
      have hmul : (p ^ (t - 2) * p) * H₀.relIndex C = (p ^ (t - 2) * p) * p ^ (t - 2) := by
        calc (p ^ (t - 2) * p) * H₀.relIndex C
          _ = (Nat.card ↥(H₀ ⊓ C) * H₀.relIndex C) * Nat.card K := by
              rw [hinf_eq, hinf_Q, hK]
              ring
          _ = Nat.card C * Nat.card K := by
              rw [← card_subgroupOf, Subgroup.relIndex, Subgroup.card_mul_index]
          _ = Nat.card (qSubgroup ht2 K) := card_qSubgroupVMidZero_mul_card ht2 K m₀
          _ = p ^ (2 * t - 3) := by rw [card_qSubgroup, hK]
          _ = p ^ ((t - 2) + 1 + (t - 2)) := by congr 1; omega
          _ = (p ^ (t - 2) * p) * p ^ (t - 2) := by rw [pow_add, pow_add, pow_one]
      exact Nat.eq_of_mul_eq_mul_left (Nat.mul_pos (pow_pos hp.pos _) hp.pos) hmul
    have hbound := relIndex_add_relIndex_le_index_of_conj_zMat ht2 hz₀ hg hs hC_comm
    rwa [hrel_Q, hrel_C] at hbound
  · obtain ⟨z₁, hg⟩ := hv_all (Pi.single m₀ 1)
    obtain ⟨s, hs⟩ := exists_conj_qMat_single_right ht2 m₀ z₁
    let C := qSubgroupUMidZero ht2 K m₀
    have hC_comm : ∀ c ∈ C, c * qMat ht2 0 (Pi.single m₀ 1) z₁ =
        qMat ht2 0 (Pi.single m₀ 1) z₁ * c := by
      rintro _ ⟨u, v, z, hu, rfl⟩
      rw [← mul_inv_eq_iff_eq_mul, qMat_conj]
      simp [hu]
    have hinf_eq : H₀ ⊓ C = H₀ ⊓ qSubgroup ht2 K := by
      ext x
      simp only [Subgroup.mem_inf]
      constructor
      · rintro ⟨hxH, u, v, z, -, rfl⟩
        exact ⟨hxH, u, v, z, rfl⟩
      · rintro ⟨hxH, u, v, z, rfl⟩
        have hu0 : u = 0 := hu_zero u v ⟨z, hxH⟩
        exact ⟨hxH, u, v, z, by simp [hu0], rfl⟩
    have hrel_C : H₀.relIndex C = p ^ (t - 2) := by
      have hmul : (p ^ (t - 2) * p) * H₀.relIndex C = (p ^ (t - 2) * p) * p ^ (t - 2) := by
        calc (p ^ (t - 2) * p) * H₀.relIndex C
          _ = (Nat.card ↥(H₀ ⊓ C) * H₀.relIndex C) * Nat.card K := by
              rw [hinf_eq, hinf_Q, hK]
              ring
          _ = Nat.card C * Nat.card K := by
              rw [← card_subgroupOf, Subgroup.relIndex, Subgroup.card_mul_index]
          _ = Nat.card (qSubgroup ht2 K) := card_qSubgroupUMidZero_mul_card ht2 K m₀
          _ = p ^ (2 * t - 3) := by rw [card_qSubgroup, hK]
          _ = p ^ ((t - 2) + 1 + (t - 2)) := by congr 1; omega
          _ = (p ^ (t - 2) * p) * p ^ (t - 2) := by rw [pow_add, pow_add, pow_one]
      exact Nat.eq_of_mul_eq_mul_left (Nat.mul_pos (pow_pos hp.pos _) hp.pos) hmul
    have hbound := relIndex_add_relIndex_le_index_of_conj_zMat ht2 hz₀ hg hs hC_comm
    rwa [hrel_Q, hrel_C] at hbound

/-- For `t = 4` and `Nat.card K = 3`, every proper subgroup `H < projectiveSL 4 K` has
`36 ≤ H.index`. -/
theorem thirty_six_le_index_of_four_three {K : Type*} [Field K] [Finite K]
    (hK : Nat.card K = 3) {H : Subgroup (projectiveSL 4 K)} (hH : H ≠ ⊤) :
    36 ≤ H.index := by
  have _ : Fintype K := Fintype.ofFinite K
  obtain ⟨p, hchar⟩ := CharP.exists K
  have hp : p.Prime := CharP.char_is_prime K p
  have _ : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, -, hcard⟩ := FiniteField.card K p
  rw [← Nat.card_eq_fintype_card, hK] at hcard
  have hp3 : p = 3 := by
    have hdvd : p ∣ 3 := ⟨p ^ ((n : ℕ) - 1), by
      rw [← pow_succ', Nat.sub_add_cancel n.pos, hcard]⟩
    rcases Nat.Prime.eq_one_or_self_of_dvd (by decide : Nat.Prime 3) p hdvd with rfl | rfl
    · exact absurd hp Nat.not_prime_one
    · rfl
  subst hp3
  obtain ⟨g, hidx, hZ⟩ := exists_comap_not_le_zSubgroup (by decide : 3 ≤ 4) hH
  rw [← hidx]
  have hbound := pow_pred_add_pow_sub_two_le_index (by decide : 4 ≤ 4) hK
    (Or.inr (by decide : 3 ≠ 2)) hZ
  norm_num at hbound
  exact hbound

/-- For `t = 4` and `Nat.card K = 3`, every primitive action with socle `T ≃* projectiveSL 4 K`
has `32 ≤ Nat.card α`. -/
theorem thirty_two_le_card_of_four_three {α : Type*} {K : Type} [Finite α] [Field K] [Finite K]
    {T : Subgroup (Perm α)} [MulAction.IsPretransitive T α]
    (e : T ≃* projectiveSL 4 K) (hK : Nat.card K = 3) :
    32 ≤ Nat.card α := by
  obtain ⟨x, hx⟩ := exists_not_le_ptStab_of_ne_bot e
    (map_proj_zSubgroup_ne_bot (by decide : 2 ≤ 4) K)
  rw [← index_ptStab_eq_card e x]
  have hne : ptStab e x ≠ ⊤ := fun htop => hx (htop ▸ le_top)
  exact le_trans (by decide : 32 ≤ 36) (thirty_six_le_index_of_four_three hK hne)

end Maroti
