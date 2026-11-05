module

public import Maroti.Linear.DegreeBoundFourThree

/-!
# Extremal parabolics and unipotent radicals over `GF(2)`

This file establishes the parabolic subgroup machinery over a field `K` with `Nat.card K = 2`
needed for the inductive degree lower bound `2 ^ t - 1 ≤ H.index` (`t ≥ 3`):

* The theorems `Maroti.charP_two_of_card_two` and `Maroti.eq_one_of_ne_zero_of_card_two` show that
  over a field `K` of order `2`, `CharP K 2` holds and every nonzero element is `1`.
* The theorems `Maroti.upperTriangular_eq_unitriangular_of_card_two` and
  `Maroti.projUpperTriangular_eq_projUnitriangular_of_card_two` show that over `GF(2)`, the Borel
  subgroup equals the unitriangular Sylow `2`-subgroup.
* The theorems `Maroti.two_pow_sub_one_le_index_of_not_two_dvd` and
  `Maroti.mem_extremalParabolics_of_index_eq_two_pow_sub_one` show that every proper subgroup `H`
  of `projectiveSL t K` (`t ≥ 3`, `Nat.card K = 2`) of odd index has `2 ^ t - 1 ≤ H.index`, with
  equality only when `H ∈ extremalParabolics (projectiveSL t K) 2`.
* The theorems `Maroti.thirty_one_le_index_of_five_two` and
  `Maroti.thirty_one_le_index_sl_five_two` show that every proper subgroup of `PSL(5, 2)` or
  `SL(5, 2)` has index at least `31`.
* The definitions `Maroti.vZeroSubgroup`, `Maroti.vOneSubgroup`, `Maroti.parabolicFirstProj`, and
  `Maroti.parabolicLastProj` construct the unipotent radicals `V₀` and `V₁` inside `qSubgroup` and
  the surjective Levi projections from `stabilizer (flagSpace (m + 1) K 1)` and
  `stabilizer (flagSpace (m + 1) K m)` onto `SpecialLinearGroup (Fin m) K` with kernels `V₀`
  and `V₁`.
-/

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace Maroti

open Subgroup Equiv Matrix Module
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

/-- In a field `K` with `Nat.card K = 2`, every nonzero element is `1`. -/
theorem eq_one_of_ne_zero_of_card_two {K : Type*} [Field K] [Finite K] (hK : Nat.card K = 2)
    {x : K} (hx : x ≠ 0) : x = 1 := by
  let u : Kˣ := Units.mk0 x hx
  have hcard : Nat.card Kˣ = 1 := by rw [Nat.card_units, hK]
  have hu : u = 1 := by
    have := pow_card_eq_one' (x := u)
    rwa [hcard, pow_one] at this
  exact congrArg Units.val hu

/-- In a field `K` with `Nat.card K = 2`, every element is `0` or `1`. -/
theorem field_eq_zero_or_eq_one_of_card_two {K : Type*} [Field K] [Finite K] (hK : Nat.card K = 2)
    (x : K) : x = 0 ∨ x = 1 := by
  by_cases hx : x = 0
  · exact Or.inl hx
  · exact Or.inr (eq_one_of_ne_zero_of_card_two hK hx)

/-- When `Nat.card K = 2`, `upperTriangular t K = unitriangular t K`. -/
theorem upperTriangular_eq_unitriangular_of_card_two (t : ℕ) {K : Type*} [Field K] [Finite K]
    (hK : Nat.card K = 2) :
    upperTriangular t K = unitriangular t K := by
  apply le_antisymm
  · intro b hb
    exact ⟨hb, fun i => eq_one_of_ne_zero_of_card_two hK (upperTriangular_apply_self_ne_zero hb i)⟩
  · exact unitriangular_le_upperTriangular t K

/-- When `Nat.card K = 2`, `projUpperTriangular t K = projUnitriangular t K`. -/
theorem projUpperTriangular_eq_projUnitriangular_of_card_two (t : ℕ) {K : Type*} [Field K]
    [Finite K] (hK : Nat.card K = 2) :
    projUpperTriangular t K = projUnitriangular t K := by
  rw [projUpperTriangular, projUnitriangular, upperTriangular_eq_unitriangular_of_card_two t hK]

/-- When `Nat.card K = 2`, `proj t K : SpecialLinearGroup (Fin t) K →* projectiveSL t K` is an
isomorphism. -/
noncomputable def slEquivProjectiveSLOfCardTwo (t : ℕ) {K : Type*} [Field K] [Finite K]
    (hK : Nat.card K = 2) :
    SpecialLinearGroup (Fin t) K ≃* projectiveSL t K := by
  have hker : (proj t K).ker = ⊥ := by
    rw [ker_proj, scalars_eq_bot_of_card_two t hK]
  exact MulEquiv.ofBijective (proj t K)
    ⟨(MonoidHom.ker_eq_bot_iff (proj t K)).mp hker, proj_surjective t K⟩

/-- Over a field `K` of order `2`, any maximal subgroup `M` of `projectiveSL t K` (`1 ≤ t`) of odd
index lies in `maximalParabolics (projectiveSL t K) 2`. -/
theorem mem_maximalParabolics_of_isCoatom_and_not_two_dvd {t : ℕ} (ht : 1 ≤ t)
    {K : Type*} [Field K] [Finite K] [Fact (Nat.Prime 2)] [CharP K 2] (hK : Nat.card K = 2)
    {M : Subgroup (projectiveSL t K)} (hM : IsCoatom M) (hodd : ¬ 2 ∣ M.index) :
    M ∈ maximalParabolics (projectiveSL t K) 2 := by
  have _ : Finite (projectiveSL t K) := by unfold projectiveSL; infer_instance
  let Q₀ : Sylow 2 M := Sylow.nonempty.some
  let Q : Subgroup (projectiveSL t K) := Q₀.1.map M.subtype
  have hpQ : IsPGroup 2 Q := Q₀.2.map M.subtype
  have hQ_idx : ¬ 2 ∣ Q.index := by
    rw [Subgroup.index_map_subtype Q₀.1]
    exact Nat.Prime.not_dvd_mul Nat.prime_two Q₀.not_dvd_index hodd
  let P : Sylow 2 (projectiveSL t K) := hpQ.toSylow hQ_idx
  have hP_coe : (P : Subgroup (projectiveSL t K)) = Q := IsPGroup.toSylow_coe hpQ hQ_idx
  have hPM : (P : Subgroup (projectiveSL t K)) ≤ M := by
    rw [hP_coe]
    exact Subgroup.map_subtype_le Q₀.1
  obtain ⟨SU, hSU⟩ := exists_sylow_projUnitriangular (K := K) 2 (n := t) ht
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq (projectiveSL t K) SU P
  have hP_eq : (P : Subgroup (projectiveSL t K)) =
      (projUpperTriangular t K).map (MulAut.conj x : projectiveSL t K →* projectiveSL t K) := by
    rw [← hx, coe_sylow_smul, hSU, projUpperTriangular_eq_projUnitriangular_of_card_two t hK]
  refine ⟨hM, (P : Subgroup (projectiveSL t K)), ?_, hPM⟩
  rw [sylowNormalizers_eq (K := K) 2 ht]
  exact ⟨x, hP_eq⟩

/-- When `3 ≤ t` and `Nat.card K = 2`, every `M ∈ extremalParabolics (projectiveSL t K) 2` has
`M.index = 2 ^ t - 1`. -/
theorem index_eq_two_pow_sub_one_of_mem_extremalParabolics {t : ℕ} (ht : 3 ≤ t)
    {K : Type*} [Field K] [Finite K] [Fact (Nat.Prime 2)] [CharP K 2] (hK : Nat.card K = 2)
    {M : Subgroup (projectiveSL t K)} (hM : M ∈ extremalParabolics (projectiveSL t K) 2) :
    M.index = 2 ^ t - 1 := by
  have hidx := (intrinsic_extremal_parabolics (K := K) 2 ht).2.2.1 M hM
  rw [hK] at hidx
  have h1 : (1 : ℕ) ≤ 2 ^ t := Nat.one_le_two_pow
  have hidx' : (M.index : ℚ) = ((2 ^ t - 1 : ℕ) : ℚ) := by
    rw [hidx, Nat.cast_sub h1, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
    ring
  exact_mod_cast hidx'

/-- When `3 ≤ t` and `Nat.card K = 2`, every `M ∈ maximalParabolics (projectiveSL t K) 2` has
`2 ^ t - 1 ≤ M.index`. -/
theorem two_pow_sub_one_le_index_of_mem_maximalParabolics {t : ℕ} (ht : 3 ≤ t)
    {K : Type*} [Field K] [Finite K] [Fact (Nat.Prime 2)] [CharP K 2] (hK : Nat.card K = 2)
    {M : Subgroup (projectiveSL t K)} (hM : M ∈ maximalParabolics (projectiveSL t K) 2) :
    2 ^ t - 1 ≤ M.index := by
  obtain ⟨M₀, hM₀⟩ := (intrinsic_extremal_parabolics (K := K) 2 ht).2.2.2.2
  rw [← index_eq_two_pow_sub_one_of_mem_extremalParabolics ht hK hM₀]
  exact hM₀.2 M hM

/-- When `3 ≤ t` and `Nat.card K = 2`, every proper subgroup `H < projectiveSL t K` of odd index
satisfies `2 ^ t - 1 ≤ H.index`. -/
theorem two_pow_sub_one_le_index_of_not_two_dvd {t : ℕ} (ht : 3 ≤ t)
    {K : Type*} [Field K] [Finite K] (hK : Nat.card K = 2)
    {H : Subgroup (projectiveSL t K)} (hH : H ≠ ⊤) (hodd : ¬ 2 ∣ H.index) :
    2 ^ t - 1 ≤ H.index := by
  have _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have _ : CharP K 2 := charP_two_of_card_two hK
  have _ : Finite (projectiveSL t K) := by unfold projectiveSL; infer_instance
  obtain ⟨M, hM_coatom, hHM⟩ := (IsCoatomic.eq_top_or_exists_le_coatom H).resolve_left hH
  have hM_dvd : M.index ∣ H.index := Subgroup.index_dvd_of_le hHM
  have hM_odd : ¬ 2 ∣ M.index := fun h => hodd (h.trans hM_dvd)
  have hM_par : M ∈ maximalParabolics (projectiveSL t K) 2 :=
    mem_maximalParabolics_of_isCoatom_and_not_two_dvd (by omega) hK hM_coatom hM_odd
  exact le_trans (two_pow_sub_one_le_index_of_mem_maximalParabolics ht hK hM_par)
    (Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) hM_dvd)

/-- When `3 ≤ t` and `Nat.card K = 2`, any subgroup `H : Subgroup (projectiveSL t K)` of index
`2 ^ t - 1` lies in `extremalParabolics (projectiveSL t K) 2`. -/
theorem mem_extremalParabolics_of_index_eq_two_pow_sub_one {t : ℕ} (ht : 3 ≤ t)
    {K : Type*} [Field K] [Finite K] [Fact (Nat.Prime 2)] [CharP K 2] (hK : Nat.card K = 2)
    {H : Subgroup (projectiveSL t K)} (hidx : H.index = 2 ^ t - 1) :
    H ∈ extremalParabolics (projectiveSL t K) 2 := by
  have _ : Finite (projectiveSL t K) := by unfold projectiveSL; infer_instance
  have h8 : 8 ≤ 2 ^ t := by
    calc 8 = 2 ^ 3 := by decide
      _ ≤ 2 ^ t := Nat.pow_le_pow_right (by decide) ht
  have hH_ne : H ≠ ⊤ := by
    intro htop
    rw [htop, Subgroup.index_top] at hidx
    omega
  have hodd : ¬ 2 ∣ H.index := by
    rw [hidx]
    intro hdvd
    have h2t : 2 ∣ 2 ^ t := dvd_pow_self 2 (by omega : t ≠ 0)
    have h1 : 2 ∣ 2 ^ t - (2 ^ t - 1) := Nat.dvd_sub h2t hdvd
    rw [Nat.sub_sub_self (by omega)] at h1
    exact absurd (Nat.le_of_dvd zero_lt_one h1) (by decide)
  obtain ⟨M, hM_coatom, hHM⟩ := (IsCoatomic.eq_top_or_exists_le_coatom H).resolve_left hH_ne
  have hM_dvd : M.index ∣ H.index := Subgroup.index_dvd_of_le hHM
  have hM_odd : ¬ 2 ∣ M.index := fun h => hodd (h.trans hM_dvd)
  have hM_par : M ∈ maximalParabolics (projectiveSL t K) 2 :=
    mem_maximalParabolics_of_isCoatom_and_not_two_dvd (by omega) hK hM_coatom hM_odd
  have hM_ge : 2 ^ t - 1 ≤ M.index :=
    two_pow_sub_one_le_index_of_mem_maximalParabolics ht hK hM_par
  have hM_le : M.index ≤ 2 ^ t - 1 :=
    hidx ▸ Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) hM_dvd
  have hM_eq : M.index = 2 ^ t - 1 := le_antisymm hM_le hM_ge
  have hrel_mul := Subgroup.relIndex_mul_index hHM
  rw [hM_eq, hidx] at hrel_mul
  have hrel_one : H.relIndex M = 1 := by
    have hpos : 0 < 2 ^ t - 1 := by omega
    exact Nat.eq_of_mul_eq_mul_right hpos (hrel_mul.trans (one_mul _).symm)
  have hHM_eq : H = M :=
    le_antisymm hHM (Subgroup.subgroupOf_eq_top.mp (Subgroup.index_eq_one.mp hrel_one))
  subst hHM_eq
  refine ⟨hM_par, fun M' hM' => ?_⟩
  rw [hM_eq]
  exact two_pow_sub_one_le_index_of_mem_maximalParabolics ht hK hM'

/-- For `3 ≤ t` and `Nat.card K = 2`, `(stabilizer (flagSpace t K 1)).index = 2 ^ t - 1`. -/
theorem index_stabilizer_flagSpace_one_of_card_two {t : ℕ} (ht : 3 ≤ t)
    {K : Type*} [Field K] [Finite K] (hK : Nat.card K = 2) :
    (stabilizer (flagSpace t K 1)).index = 2 ^ t - 1 := by
  have _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have _ : CharP K 2 := charP_two_of_card_two hK
  rw [← comap_projStabilizer, Subgroup.index_comap_of_surjective _ (proj_surjective t K)]
  apply index_eq_two_pow_sub_one_of_mem_extremalParabolics ht hK
  rw [(intrinsic_extremal_parabolics (K := K) 2 ht).1]
  exact Or.inl ⟨flagSpace t K 1, finrank_flagSpace (by omega), rfl⟩

/-- For `3 ≤ t` and `Nat.card K = 2`, `(stabilizer (flagSpace t K (t - 1))).index = 2 ^ t - 1`. -/
theorem index_stabilizer_flagSpace_pred_of_card_two {t : ℕ} (ht : 3 ≤ t)
    {K : Type*} [Field K] [Finite K] (hK : Nat.card K = 2) :
    (stabilizer (flagSpace t K (t - 1))).index = 2 ^ t - 1 := by
  have _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have _ : CharP K 2 := charP_two_of_card_two hK
  rw [← comap_projStabilizer, Subgroup.index_comap_of_surjective _ (proj_surjective t K)]
  apply index_eq_two_pow_sub_one_of_mem_extremalParabolics ht hK
  rw [(intrinsic_extremal_parabolics (K := K) 2 ht).1]
  exact Or.inr ⟨flagSpace t K (t - 1), finrank_flagSpace (by omega), rfl⟩

/-- Order of `projectiveSL 5 K` when `Nat.card K = 2` is `9999360`. -/
theorem card_projectiveSL_five_two {K : Type*} [Field K] [Finite K] (hK : Nat.card K = 2) :
    Nat.card (projectiveSL 5 K) = 9999360 := by
  have h1 := (scalars 5 K).card_eq_card_quotient_mul_card_subgroup
  have hSL : Nat.card (SpecialLinearGroup (Fin 5) K) = 9999360 := by
    rw [card_SL_eq (by omega : 1 ≤ 5), hK]
    decide
  have hsc : Nat.card (scalars 5 K) = 1 := by
    rw [scalars_eq_bot_of_card_two 5 hK, Subgroup.card_bot]
  rw [hSL, hsc, mul_one] at h1
  exact h1.symm

/-- For `t = 5` and `Nat.card K = 2`, every proper subgroup `H < projectiveSL 5 K` has
`31 ≤ H.index`. -/
theorem thirty_one_le_index_of_five_two {K : Type*} [Field K] [Finite K] (hK : Nat.card K = 2)
    {H : Subgroup (projectiveSL 5 K)} (hH : H ≠ ⊤) :
    31 ≤ H.index := by
  have _ : IsSimpleGroup (projectiveSL 5 K) := isSimpleGroup_projectiveSL (by decide) K
  have hdvd := card_dvd_index_factorial_of_ne_top hH
  rw [card_projectiveSL_five_two hK] at hdvd
  have h31 : 31 ∣ (H.index).factorial := dvd_trans (by decide : 31 ∣ 9999360) hdvd
  exact (by decide : Nat.Prime 31).dvd_factorial.mp h31

/-- For `t = 5` and `Nat.card K = 2`, every proper subgroup `H < SL(5, K)` has `31 ≤ H.index`. -/
theorem thirty_one_le_index_sl_five_two {K : Type*} [Field K] [Finite K] (hK : Nat.card K = 2)
    {H : Subgroup (SpecialLinearGroup (Fin 5) K)} (hH : H ≠ ⊤) :
    31 ≤ H.index := by
  let e := slEquivProjectiveSLOfCardTwo 5 hK
  have hmap_ne : H.map e.toMonoidHom ≠ ⊤ := by
    intro htop
    apply hH
    rw [eq_top_iff]
    intro g _
    have hg : e g ∈ H.map e.toMonoidHom := htop ▸ Subgroup.mem_top (e g)
    obtain ⟨h, hhH, hhe⟩ := hg
    exact e.injective hhe ▸ hhH
  rw [← Subgroup.index_map_equiv H e]
  exact thirty_one_le_index_of_five_two hK hmap_ne

/-- Matrix entry characterization of `g ∈ stabilizer (flagSpace n K i)`. -/
theorem mem_stabilizer_flagSpace_iff {n i : ℕ} {K : Type*} [Field K]
    {g : SpecialLinearGroup (Fin n) K} :
    g ∈ stabilizer (flagSpace n K i) ↔
      ∀ r c : Fin n, (c : ℕ) < i → i ≤ (r : ℕ) →
        (g : Matrix (Fin n) (Fin n) K) r c = 0 := by
  constructor
  · intro hg r c hc hr
    have hmem : (g : Matrix (Fin n) (Fin n) K) *ᵥ Pi.single c 1 ∈ flagSpace n K i := by
      rw [← mem_stabilizer.mp hg]
      exact ⟨Pi.single c 1, Submodule.subset_span ⟨c, hc, rfl⟩, rfl⟩
    have h0 := mem_flagSpace.mp hmem r hr
    rwa [mulVec_single_one, col_apply] at h0
  · intro h
    refine mem_stabilizer_of_map_le ?_
    conv_lhs => rw [flagSpace]
    rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨c, hc, rfl⟩, rfl⟩
    rw [SetLike.mem_coe, mem_flagSpace]
    intro r hr
    rw [mulVecLin_apply, mulVec_single_one, col_apply]
    exact h r c hc hr

/-- Characterization of `g ∈ stabilizer (flagSpace (m + 1) K 1)` by vanishing of the first column
below row `0`. -/
theorem mem_stabilizer_flagSpace_one_iff {m : ℕ} {K : Type*} [Field K]
    {g : SpecialLinearGroup (Fin (m + 1)) K} :
    g ∈ stabilizer (flagSpace (m + 1) K 1) ↔
      ∀ r : Fin m, (g : Matrix (Fin (m + 1)) (Fin (m + 1)) K) r.succ 0 = 0 := by
  rw [mem_stabilizer_flagSpace_iff]
  constructor
  · intro h r
    exact h r.succ 0 (by simp) (by simp)
  · intro h r c hc hr
    have hc0 : c = 0 := Fin.ext (by rw [Fin.val_zero]; omega)
    subst hc0
    rcases Fin.eq_zero_or_eq_succ r with rfl | ⟨r', rfl⟩
    · simp at hr
    · exact h r'

/-- Characterization of `g ∈ stabilizer (flagSpace (m + 1) K m)` by vanishing of the last row
before column `m`. -/
theorem mem_stabilizer_flagSpace_last_iff {m : ℕ} {K : Type*} [Field K]
    {g : SpecialLinearGroup (Fin (m + 1)) K} :
    g ∈ stabilizer (flagSpace (m + 1) K m) ↔
      ∀ c : Fin m, (g : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (Fin.last m) c.castSucc = 0 := by
  rw [mem_stabilizer_flagSpace_iff]
  constructor
  · intro h c
    exact h (Fin.last m) c.castSucc c.isLt le_rfl
  · intro h r c hc hr
    have hr_last : r = Fin.last m := Fin.ext (by rw [Fin.val_last]; have := r.isLt; omega)
    subst hr_last
    exact h ⟨c.1, hc⟩

/-- Determinant of a `(m + 1) × (m + 1)` matrix whose first column vanishes below `(0, 0)`. -/
theorem det_of_succ_col_zero {m : ℕ} {K : Type*} [CommRing K]
    {A : Matrix (Fin (m + 1)) (Fin (m + 1)) K} (h : ∀ r : Fin m, A r.succ 0 = 0) :
    A.det = A 0 0 * (A.submatrix Fin.succ Fin.succ).det := by
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  simp [h]

/-- Determinant of a `(m + 1) × (m + 1)` matrix whose last row vanishes before `(m, m)`. -/
theorem det_of_last_row_zero {m : ℕ} {K : Type*} [CommRing K]
    {A : Matrix (Fin (m + 1)) (Fin (m + 1)) K}
    (h : ∀ c : Fin m, A (Fin.last m) c.castSucc = 0) :
    A.det = A (Fin.last m) (Fin.last m) * (A.submatrix Fin.castSucc Fin.castSucc).det := by
  rw [Matrix.det_succ_row A (Fin.last m), Fin.sum_univ_castSucc]
  have hsum : ∑ c : Fin m,
      (-1 : K) ^ ((Fin.last m : ℕ) + (c.castSucc : ℕ)) * A (Fin.last m) c.castSucc *
        (A.submatrix (Fin.last m).succAbove c.castSucc.succAbove).det = 0 :=
    Finset.sum_eq_zero fun c _ => by rw [h c, mul_zero, zero_mul]
  have hsign : (-1 : K) ^ ((Fin.last m : ℕ) + (Fin.last m : ℕ)) = 1 :=
    Even.neg_one_pow ⟨m, by simp [Fin.val_last]⟩
  rw [hsum, zero_add, hsign, one_mul, Fin.succAbove_last]

/-- Over a field `K` of order `2`, any `g ∈ stabilizer (flagSpace (m + 1) K 1)` has `g 0 0 = 1`
and `(g.submatrix Fin.succ Fin.succ).det = 1`. -/
theorem apply_zero_and_det_submatrix_succ_of_mem_stabilizer_one {m : ℕ} {K : Type*} [Field K]
    [Finite K] (hK : Nat.card K = 2) {g : SpecialLinearGroup (Fin (m + 1)) K}
    (hg : g ∈ stabilizer (flagSpace (m + 1) K 1)) :
    (g : Matrix (Fin (m + 1)) (Fin (m + 1)) K) 0 0 = 1 ∧
      ((g : Matrix (Fin (m + 1)) (Fin (m + 1)) K).submatrix Fin.succ Fin.succ).det = 1 := by
  have hdet := det_of_succ_col_zero (mem_stabilizer_flagSpace_one_iff.mp hg)
  rw [g.2] at hdet
  have h1 : (g : Matrix (Fin (m + 1)) (Fin (m + 1)) K) 0 0 ≠ 0 :=
    fun h0 => zero_ne_one (by rw [h0, zero_mul] at hdet; exact hdet.symm)
  have h2 : ((g : Matrix (Fin (m + 1)) (Fin (m + 1)) K).submatrix Fin.succ Fin.succ).det ≠ 0 :=
    fun h0 => zero_ne_one (by rw [h0, mul_zero] at hdet; exact hdet.symm)
  exact ⟨eq_one_of_ne_zero_of_card_two hK h1, eq_one_of_ne_zero_of_card_two hK h2⟩

/-- Over a field `K` of order `2`, any `g ∈ stabilizer (flagSpace (m + 1) K m)` has
`g (Fin.last m) (Fin.last m) = 1` and `(g.submatrix Fin.castSucc Fin.castSucc).det = 1`. -/
theorem apply_last_and_det_submatrix_castSucc_of_mem_stabilizer_last {m : ℕ} {K : Type*} [Field K]
    [Finite K] (hK : Nat.card K = 2) {g : SpecialLinearGroup (Fin (m + 1)) K}
    (hg : g ∈ stabilizer (flagSpace (m + 1) K m)) :
    (g : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (Fin.last m) (Fin.last m) = 1 ∧
      ((g : Matrix (Fin (m + 1)) (Fin (m + 1)) K).submatrix Fin.castSucc Fin.castSucc).det = 1 := by
  have hdet := det_of_last_row_zero (mem_stabilizer_flagSpace_last_iff.mp hg)
  rw [g.2] at hdet
  have h1 : (g : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (Fin.last m) (Fin.last m) ≠ 0 :=
    fun h0 => zero_ne_one (by rw [h0, zero_mul] at hdet; exact hdet.symm)
  have h2 : ((g : Matrix (Fin (m + 1)) (Fin (m + 1)) K).submatrix
      Fin.castSucc Fin.castSucc).det ≠ 0 :=
    fun h0 => zero_ne_one (by rw [h0, mul_zero] at hdet; exact hdet.symm)
  exact ⟨eq_one_of_ne_zero_of_card_two hK h1, eq_one_of_ne_zero_of_card_two hK h2⟩

/-- Homomorphism `stabilizer (flagSpace (m + 1) K 1) →* SpecialLinearGroup (Fin m) K` taking the
lower-right `m × m` block (`Nat.card K = 2`). -/
@[expose]
def parabolicFirstProj {m : ℕ} {K : Type*} [Field K] [Finite K] (hK : Nat.card K = 2) :
    stabilizer (flagSpace (m + 1) K 1) →* SpecialLinearGroup (Fin m) K where
  toFun g := ⟨(g.1 : Matrix (Fin (m + 1)) (Fin (m + 1)) K).submatrix Fin.succ Fin.succ,
    (apply_zero_and_det_submatrix_succ_of_mem_stabilizer_one hK g.2).2⟩
  map_one' := by
    apply Subtype.ext
    ext r c
    simp [Matrix.one_apply]
  map_mul' g₁ g₂ := by
    have hg₁ := mem_stabilizer_flagSpace_one_iff.mp g₁.2
    apply Subtype.ext
    ext r c
    change ((g₁.1 : Matrix (Fin (m + 1)) (Fin (m + 1)) K) *
        (g₂.1 : Matrix (Fin (m + 1)) (Fin (m + 1)) K)).submatrix Fin.succ Fin.succ r c =
      ((g₁.1 : Matrix (Fin (m + 1)) (Fin (m + 1)) K).submatrix Fin.succ Fin.succ *
        (g₂.1 : Matrix (Fin (m + 1)) (Fin (m + 1)) K).submatrix Fin.succ Fin.succ) r c
    simp only [submatrix_apply, mul_apply]
    rw [Fin.sum_univ_succ, hg₁ r, zero_mul, zero_add]

/-- Homomorphism `stabilizer (flagSpace (m + 1) K m) →* SpecialLinearGroup (Fin m) K` taking the
upper-left `m × m` block (`Nat.card K = 2`). -/
@[expose]
def parabolicLastProj {m : ℕ} {K : Type*} [Field K] [Finite K] (hK : Nat.card K = 2) :
    stabilizer (flagSpace (m + 1) K m) →* SpecialLinearGroup (Fin m) K where
  toFun g := ⟨(g.1 : Matrix (Fin (m + 1)) (Fin (m + 1)) K).submatrix Fin.castSucc Fin.castSucc,
    (apply_last_and_det_submatrix_castSucc_of_mem_stabilizer_last hK g.2).2⟩
  map_one' := by
    apply Subtype.ext
    ext r c
    simp [Matrix.one_apply]
  map_mul' g₁ g₂ := by
    have hg₂ := mem_stabilizer_flagSpace_last_iff.mp g₂.2
    apply Subtype.ext
    ext r c
    change ((g₁.1 : Matrix (Fin (m + 1)) (Fin (m + 1)) K) *
        (g₂.1 : Matrix (Fin (m + 1)) (Fin (m + 1)) K)).submatrix Fin.castSucc Fin.castSucc r c =
      ((g₁.1 : Matrix (Fin (m + 1)) (Fin (m + 1)) K).submatrix Fin.castSucc Fin.castSucc *
        (g₂.1 : Matrix (Fin (m + 1)) (Fin (m + 1)) K).submatrix Fin.castSucc Fin.castSucc) r c
    simp only [submatrix_apply, mul_apply]
    rw [Fin.sum_univ_castSucc, hg₂ c, mul_zero, add_zero]

/-- Surjectivity of `parabolicFirstProj hK`. -/
theorem parabolicFirstProj_surjective {m : ℕ} {K : Type*} [Field K] [Finite K]
    (hK : Nat.card K = 2) :
    Function.Surjective (parabolicFirstProj (m := m) hK) := by
  intro A
  let M : Matrix (Fin (m + 1)) (Fin (m + 1)) K :=
    Matrix.of (Fin.cases (Fin.cases 1 (fun _ => 0)) (fun i => Fin.cases 0 (fun j => A.1 i j)))
  have hcol : ∀ r : Fin m, M r.succ 0 = 0 := fun _ => rfl
  have hsub : M.submatrix Fin.succ Fin.succ = A.1 := by
    ext i j
    rfl
  have hdet : M.det = 1 := by
    rw [det_of_succ_col_zero hcol, hsub, A.2]
    exact mul_one 1
  refine ⟨⟨⟨M, hdet⟩, mem_stabilizer_flagSpace_one_iff.mpr hcol⟩, ?_⟩
  apply Subtype.ext
  exact hsub

/-- Surjectivity of `parabolicLastProj hK`. -/
theorem parabolicLastProj_surjective {m : ℕ} {K : Type*} [Field K] [Finite K]
    (hK : Nat.card K = 2) :
    Function.Surjective (parabolicLastProj (m := m) hK) := by
  intro A
  let M : Matrix (Fin (m + 1)) (Fin (m + 1)) K :=
    Matrix.of (Fin.lastCases (Fin.lastCases 1 (fun _ => 0))
      (fun i => Fin.lastCases 0 (fun j => A.1 i j)))
  have hrow : ∀ c : Fin m, M (Fin.last m) c.castSucc = 0 := fun c => by
    simp [M]
  have hsub : M.submatrix Fin.castSucc Fin.castSucc = A.1 := by
    ext i j
    simp [M]
  have h0 : M (Fin.last m) (Fin.last m) = 1 := by
    simp [M]
  have hdet : M.det = 1 := by
    rw [det_of_last_row_zero hrow, h0, hsub, A.2, one_mul]
  refine ⟨⟨⟨M, hdet⟩, mem_stabilizer_flagSpace_last_iff.mpr hrow⟩, ?_⟩
  apply Subtype.ext
  exact hsub

/-- The top-row unipotent subgroup `V₀ = {qMat ht u 0 z | u, z}` inside `SL(t, K)`. -/
@[expose]
def vZeroSubgroup {t : ℕ} [NeZero t] (ht : 2 ≤ t) (K : Type*) [Field K] :
    Subgroup (SpecialLinearGroup (Fin t) K) where
  carrier := {g | ∃ (u : Mid t → K) (z : K), g = qMat ht u 0 z}
  one_mem' := ⟨0, 0, (qMat_zero ht).symm⟩
  mul_mem' := by
    rintro _ _ ⟨u₁, z₁, rfl⟩ ⟨u₂, z₂, rfl⟩
    refine ⟨u₁ + u₂, z₁ + z₂, ?_⟩
    rw [qMat_mul, add_zero, dotProduct_zero, add_zero]
  inv_mem' := by
    rintro _ ⟨u, z, rfl⟩
    refine ⟨-u, -z, ?_⟩
    rw [qMat_inv, neg_zero, dotProduct_zero, add_zero]

/-- The right-column unipotent subgroup `V₁ = {qMat ht 0 v z | v, z}` inside `SL(t, K)`. -/
@[expose]
def vOneSubgroup {t : ℕ} [NeZero t] (ht : 2 ≤ t) (K : Type*) [Field K] :
    Subgroup (SpecialLinearGroup (Fin t) K) where
  carrier := {g | ∃ (v : Mid t → K) (z : K), g = qMat ht 0 v z}
  one_mem' := ⟨0, 0, (qMat_zero ht).symm⟩
  mul_mem' := by
    rintro _ _ ⟨v₁, z₁, rfl⟩ ⟨v₂, z₂, rfl⟩
    refine ⟨v₁ + v₂, z₁ + z₂, ?_⟩
    rw [qMat_mul, add_zero, zero_dotProduct, add_zero]
  inv_mem' := by
    rintro _ ⟨v, z, rfl⟩
    refine ⟨-v, -z, ?_⟩
    rw [qMat_inv, neg_zero, zero_dotProduct, add_zero]

theorem vZeroSubgroup_le_qSubgroup {t : ℕ} [NeZero t] (ht : 2 ≤ t) (K : Type*) [Field K] :
    vZeroSubgroup ht K ≤ qSubgroup ht K := by
  rintro _ ⟨u, z, rfl⟩
  exact ⟨u, 0, z, rfl⟩

theorem vOneSubgroup_le_qSubgroup {t : ℕ} [NeZero t] (ht : 2 ≤ t) (K : Type*) [Field K] :
    vOneSubgroup ht K ≤ qSubgroup ht K := by
  rintro _ ⟨v, z, rfl⟩
  exact ⟨0, v, z, rfl⟩

/-- The subgroup `vZeroSubgroup` is commutative. -/
theorem vZeroSubgroup_mul_comm {t : ℕ} [NeZero t] (ht : 2 ≤ t) {K : Type*} [Field K]
    {a b : SpecialLinearGroup (Fin t) K} (ha : a ∈ vZeroSubgroup ht K)
    (hb : b ∈ vZeroSubgroup ht K) :
    a * b = b * a := by
  obtain ⟨u₁, z₁, rfl⟩ := ha
  obtain ⟨u₂, z₂, rfl⟩ := hb
  rw [qMat_mul, qMat_mul, add_comm u₁ u₂, dotProduct_zero, dotProduct_zero, add_comm z₁ z₂]

/-- The subgroup `vOneSubgroup` is commutative. -/
theorem vOneSubgroup_mul_comm {t : ℕ} [NeZero t] (ht : 2 ≤ t) {K : Type*} [Field K]
    {a b : SpecialLinearGroup (Fin t) K} (ha : a ∈ vOneSubgroup ht K)
    (hb : b ∈ vOneSubgroup ht K) :
    a * b = b * a := by
  obtain ⟨v₁, z₁, rfl⟩ := ha
  obtain ⟨v₂, z₂, rfl⟩ := hb
  rw [qMat_mul, qMat_mul, add_comm v₁ v₂, zero_dotProduct, zero_dotProduct, add_comm z₁ z₂]

/-- The subgroup `vZeroSubgroup` is contained in `stabilizer (flagSpace t K 1)`. -/
theorem vZeroSubgroup_le_stabilizer_flagSpace_one {t : ℕ} [NeZero t] (ht : 2 ≤ t)
    (K : Type*) [Field K] :
    vZeroSubgroup ht K ≤ stabilizer (flagSpace t K 1) := by
  rintro _ ⟨u, z, rfl⟩
  exact upperTriangular_le_stabilizer_flagSpace 1
    (unitriangular_le_upperTriangular t K (qMat_mem_unitriangular ht u 0 z))

/-- The subgroup `vOneSubgroup` is contained in `stabilizer (flagSpace t K (t - 1))`. -/
theorem vOneSubgroup_le_stabilizer_flagSpace_pred {t : ℕ} [NeZero t] (ht : 2 ≤ t)
    (K : Type*) [Field K] :
    vOneSubgroup ht K ≤ stabilizer (flagSpace t K (t - 1)) := by
  rintro _ ⟨v, z, rfl⟩
  exact upperTriangular_le_stabilizer_flagSpace (t - 1)
    (unitriangular_le_upperTriangular t K (qMat_mem_unitriangular ht 0 v z))

/-- The kernel of `parabolicFirstProj hK` is `(vZeroSubgroup ht K).subgroupOf _`. -/
theorem ker_parabolicFirstProj {m : ℕ} (hm : 1 ≤ m) {K : Type*} [Field K] [Finite K]
    (hK : Nat.card K = 2) :
    (parabolicFirstProj (m := m) hK).ker =
      (vZeroSubgroup (by omega : 2 ≤ m + 1) K).subgroupOf
        (stabilizer (flagSpace (m + 1) K 1)) := by
  have ht : 2 ≤ m + 1 := by omega
  ext ⟨g, hg⟩
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro hker
    have hsub : (g : Matrix (Fin (m + 1)) (Fin (m + 1)) K).submatrix Fin.succ Fin.succ =
        (1 : Matrix (Fin m) (Fin m) K) :=
      congrArg Subtype.val hker
    have hg00 := (apply_zero_and_det_submatrix_succ_of_mem_stabilizer_one hK hg).1
    have hg_col := mem_stabilizer_flagSpace_one_iff.mp hg
    let u : Mid (m + 1) → K := fun k =>
      (g : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (firstIdx (m + 1)) k.1
    let z : K := (g : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (firstIdx (m + 1)) (lastIdx (m + 1))
    refine ⟨u, z, Subtype.ext (Matrix.ext fun i j => ?_)⟩
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨r, rfl⟩
    · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨c, rfl⟩
      · rw [hg00]
        exact (qMat_apply_diag ht u 0 z 0).symm
      · by_cases hlast : c.succ = lastIdx (m + 1)
        · rw [hlast]
          exact (qMat_apply_firstIdx_lastIdx ht u 0 z).symm
        · let k : Mid (m + 1) := ⟨c.succ, Fin.succ_ne_zero c, hlast⟩
          exact (qMat_apply_firstIdx_mid ht u 0 z k).symm
    · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨c, rfl⟩
      · rw [hg_col r, coe_qMat, Matrix.add_apply, Matrix.one_apply_ne (Fin.succ_ne_zero r),
          qNil_apply_of_le ht u 0 z (Fin.zero_le r.succ), add_zero]
      · have hrc : (g : Matrix (Fin (m + 1)) (Fin (m + 1)) K) r.succ c.succ =
            (1 : Matrix (Fin m) (Fin m) K) r c :=
          congrFun (congrFun hsub r) c
        have hr0 : r.succ ≠ firstIdx (m + 1) := Fin.succ_ne_zero r
        rw [hrc, coe_qMat, Matrix.add_apply, qNil_apply, ite_eq_right hr0]
        split_ifs <;> simp [Matrix.one_apply]
  · rintro ⟨u, z, rfl⟩
    apply Subtype.ext
    ext r c
    change ((qMat ht u 0 z : Matrix (Fin (m + 1)) (Fin (m + 1)) K).submatrix
        Fin.succ Fin.succ) r c =
      (1 : Matrix (Fin m) (Fin m) K) r c
    have hr0 : r.succ ≠ firstIdx (m + 1) := Fin.succ_ne_zero r
    rw [submatrix_apply, coe_qMat, Matrix.add_apply, qNil_apply, ite_eq_right hr0]
    split_ifs <;> simp [Matrix.one_apply]

/-- The kernel of `parabolicLastProj hK` is `(vOneSubgroup ht K).subgroupOf _`. -/
theorem ker_parabolicLastProj {m : ℕ} (hm : 1 ≤ m) {K : Type*} [Field K] [Finite K]
    (hK : Nat.card K = 2) :
    (parabolicLastProj (m := m) hK).ker =
      (vOneSubgroup (by omega : 2 ≤ m + 1) K).subgroupOf
        (stabilizer (flagSpace (m + 1) K m)) := by
  have ht : 2 ≤ m + 1 := by omega
  ext ⟨g, hg⟩
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro hker
    have hsub : (g : Matrix (Fin (m + 1)) (Fin (m + 1)) K).submatrix
        Fin.castSucc Fin.castSucc = (1 : Matrix (Fin m) (Fin m) K) :=
      congrArg Subtype.val hker
    have hg_last := (apply_last_and_det_submatrix_castSucc_of_mem_stabilizer_last hK hg).1
    have hg_row := mem_stabilizer_flagSpace_last_iff.mp hg
    let v : Mid (m + 1) → K := fun k =>
      (g : Matrix (Fin (m + 1)) (Fin (m + 1)) K) k.1 (lastIdx (m + 1))
    let z : K := (g : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (firstIdx (m + 1)) (lastIdx (m + 1))
    refine ⟨v, z, Subtype.ext (Matrix.ext fun i j => ?_)⟩
    rcases Fin.eq_castSucc_or_eq_last j with ⟨c, rfl⟩ | rfl
    · rcases Fin.eq_castSucc_or_eq_last i with ⟨r, rfl⟩ | rfl
      · have hrc : (g : Matrix (Fin (m + 1)) (Fin (m + 1)) K) r.castSucc c.castSucc =
            (1 : Matrix (Fin m) (Fin m) K) r c :=
          congrFun (congrFun hsub r) c
        have hc_ne : c.castSucc ≠ lastIdx (m + 1) := Fin.castSucc_ne_last c
        rw [hrc, coe_qMat, Matrix.add_apply, qNil_apply]
        split_ifs <;> simp [Matrix.one_apply]
      · have hlast_eq : (Fin.last m : Fin (m + 1)) = lastIdx (m + 1) := rfl
        rw [hg_row c, coe_qMat, Matrix.add_apply,
          Matrix.one_apply_ne (Fin.castSucc_ne_last c).symm,
          hlast_eq, qNil_apply_lastIdx_left ht 0 v z c.castSucc, add_zero]
    · have hlast_eq : (Fin.last m : Fin (m + 1)) = lastIdx (m + 1) := rfl
      rcases Fin.eq_castSucc_or_eq_last i with ⟨r, rfl⟩ | rfl
      · by_cases hfirst : r.castSucc = firstIdx (m + 1)
        · rw [hfirst, hlast_eq]
          exact (qMat_apply_firstIdx_lastIdx ht 0 v z).symm
        · let k : Mid (m + 1) := ⟨r.castSucc, hfirst, Fin.castSucc_ne_last r⟩
          rw [hlast_eq]
          exact (qMat_apply_mid_lastIdx ht 0 v z k).symm
      · rw [hg_last]
        exact (qMat_apply_diag ht 0 v z (Fin.last m)).symm
  · rintro ⟨v, z, rfl⟩
    apply Subtype.ext
    ext r c
    change ((qMat ht 0 v z : Matrix (Fin (m + 1)) (Fin (m + 1)) K).submatrix
        Fin.castSucc Fin.castSucc) r c =
      (1 : Matrix (Fin m) (Fin m) K) r c
    have hc_ne : c.castSucc ≠ lastIdx (m + 1) := Fin.castSucc_ne_last c
    rw [submatrix_apply, coe_qMat, Matrix.add_apply, qNil_apply]
    split_ifs <;> simp [Matrix.one_apply]

/-- Normalizer property: for any `p ∈ stabilizer (flagSpace (m + 1) K 1)` and
`v ∈ vZeroSubgroup ht K`, `p * v * p⁻¹ ∈ vZeroSubgroup ht K` (`Nat.card K = 2`). -/
theorem conj_mem_vZeroSubgroup_of_mem_stabilizer_one {m : ℕ} (hm : 1 ≤ m) {K : Type*} [Field K]
    [Finite K] (hK : Nat.card K = 2) {p v : SpecialLinearGroup (Fin (m + 1)) K}
    (hp : p ∈ stabilizer (flagSpace (m + 1) K 1))
    (hv : v ∈ vZeroSubgroup (by omega : 2 ≤ m + 1) K) :
    p * v * p⁻¹ ∈ vZeroSubgroup (by omega : 2 ≤ m + 1) K := by
  have ht : 2 ≤ m + 1 := by omega
  let P₁ := stabilizer (flagSpace (m + 1) K 1)
  have hvP : v ∈ P₁ := vZeroSubgroup_le_stabilizer_flagSpace_one ht K hv
  have hv_ker : (⟨v, hvP⟩ : P₁) ∈ (parabolicFirstProj hK).ker := by
    rw [ker_parabolicFirstProj hm hK]
    exact hv
  have hconj_ker : (⟨p, hp⟩ : P₁) * ⟨v, hvP⟩ * (⟨p, hp⟩ : P₁)⁻¹ ∈ (parabolicFirstProj hK).ker :=
    Subgroup.Normal.conj_mem inferInstance _ hv_ker ⟨p, hp⟩
  rw [ker_parabolicFirstProj hm hK] at hconj_ker
  exact hconj_ker

/-- Normalizer property: for any `p ∈ stabilizer (flagSpace (m + 1) K m)` and
`v ∈ vOneSubgroup ht K`, `p * v * p⁻¹ ∈ vOneSubgroup ht K` (`Nat.card K = 2`). -/
theorem conj_mem_vOneSubgroup_of_mem_stabilizer_last {m : ℕ} (hm : 1 ≤ m) {K : Type*} [Field K]
    [Finite K] (hK : Nat.card K = 2) {p v : SpecialLinearGroup (Fin (m + 1)) K}
    (hp : p ∈ stabilizer (flagSpace (m + 1) K m))
    (hv : v ∈ vOneSubgroup (by omega : 2 ≤ m + 1) K) :
    p * v * p⁻¹ ∈ vOneSubgroup (by omega : 2 ≤ m + 1) K := by
  have ht : 2 ≤ m + 1 := by omega
  let P₂ := stabilizer (flagSpace (m + 1) K m)
  have hvP : v ∈ P₂ := vOneSubgroup_le_stabilizer_flagSpace_pred ht K hv
  have hv_ker : (⟨v, hvP⟩ : P₂) ∈ (parabolicLastProj hK).ker := by
    rw [ker_parabolicLastProj hm hK]
    exact hv
  have hconj_ker : (⟨p, hp⟩ : P₂) * ⟨v, hvP⟩ * (⟨p, hp⟩ : P₂)⁻¹ ∈ (parabolicLastProj hK).ker :=
    Subgroup.Normal.conj_mem inferInstance _ hv_ker ⟨p, hp⟩
  rw [ker_parabolicLastProj hm hK] at hconj_ker
  exact hconj_ker

end Maroti
