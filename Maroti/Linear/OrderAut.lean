module

public import Maroti.AlmostSimple.Basic
public import CFSG.Adapters.StatedClassicalOrders
public import CFSG.LocalAnalysis.ComponentInitial.LinearTwoOuterOrder
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherLinearOuterOrder
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel

/-!
# Orders and automorphisms of projective special linear groups

This file establishes the order formula and automorphism group bounds for projective special linear
groups `PSL(n, p^f)` (`Maroti.LinearSocle`), deduced from the CFSG order and outer automorphism
theorems `statedClassicalModel_psl_card`, `outer_projectiveSL_two_card_dvd`, and
`UnitaryHigher.card_outer_projectiveSL_dvd`:

* The theorem `Maroti.autBound_linear` shows `|Aut(S)| ≤ |S|²` for every group `S` with
  `LinearSocle S` (Maróti, Section 2, Step 1, page 634).
* The theorem `Maroti.card_mulAut_le_of_statedClassicalModel_psl` shows
  `|Aut(S)| ≤ (if n = 2 then 1 else 2) * f * gcd(n, p^f - 1) * |S|`.
* The theorem `Maroti.mem_inner_of_map_extremalParabolic_conj_of_card_two` shows that when `n ≥ 3`
  and `q = 2`, any automorphism of `PSL(n, 2)` mapping an extremal parabolic subgroup to a
  conjugate in `PSL(n, 2)` is inner.
-/

@[expose] public section

namespace Maroti

open Subgroup Equiv Matrix
open CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner equivalence)
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

/-- The outer automorphism multiplier `(if n = 2 then 1 else 2) * f * gcd(n, p^f - 1)` for
`PSL(n, p^f)`. -/
def pslOuterBound (n p f : ℕ) : ℕ :=
  (if n = 2 then 1 else 2) * f * n.gcd (p ^ f - 1)

theorem pslOuterBound_le_two_mul (n p f : ℕ) :
    pslOuterBound n p f ≤ 2 * f * n.gcd (p ^ f - 1) := by
  unfold pslOuterBound
  refine Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ ?_)
  split_ifs <;> omega

/-- Every group with `StatedClassicalModel S .PSL n p f` is finite and has positive cardinality. -/
theorem finite_and_card_pos_of_statedClassicalModel_psl {S : Type} [Group S] {n p f : ℕ}
    (h : StatedClassicalModel S .PSL n p f) : Finite S ∧ 0 < Nat.card S := by
  obtain ⟨⟨hp, hf, hn2, -⟩, K, _, _, hK, ⟨e⟩⟩ := h
  have hK_pos : 0 < Nat.card K := by
    rw [hK]
    exact pow_pos hp.pos f
  have : Finite K := Nat.finite_of_card_ne_zero hK_pos.ne'
  have e' : S ≃* projectiveSL n K :=
    (e.trans (projectiveSpecialLinearGroupEquivStatedProj n K).symm).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL n K)
  have : Finite (projectiveSL n K) := by
    unfold projectiveSL
    infer_instance
  have : Finite S := Finite.of_equiv _ e'.symm.toEquiv
  exact ⟨‹Finite S›, Nat.card_pos⟩

/-- Outer automorphism order divisibility for `StatedClassicalModel S .PSL n p f`. -/
theorem card_outer_dvd_pslOuterBound {S : Type} [Group S] {n p f : ℕ}
    (h : StatedClassicalModel S .PSL n p f) :
    Nat.card (Outer S) ∣ pslOuterBound n p f := by
  obtain ⟨⟨hp, hf, hn2, -⟩, K, _, _, hK, ⟨e⟩⟩ := h
  unfold pslOuterBound
  split_ifs with hn
  · subst hn
    rw [one_mul]
    have e2 : S ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) K :=
      e.trans (projectiveSpecialLinearGroupEquivStatedProj 2 K).symm
    exact (linear_two_outer_order_divisor hp K hK).2 S ⟨e2⟩
  · have hn3 : 3 ≤ n := by omega
    have e' : S ≃* projectiveSL n K :=
      (e.trans (projectiveSpecialLinearGroupEquivStatedProj n K).symm).trans
        (LinearCover.projectiveSpecialLinearEquivProjectiveSL n K)
    rw [Nat.card_congr (equivalence e').toEquiv]
    exact UnitaryHigher.higher_linear_outer_order_divides_field_gcd_bound hp hf hn3 hK

theorem pslOuterBound_pos {n p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (hn : 2 ≤ n) :
    0 < pslOuterBound n p f := by
  unfold pslOuterBound
  have hq : 2 ≤ p ^ f := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
  have hgcd : 0 < n.gcd (p ^ f - 1) := Nat.gcd_pos_of_pos_left _ (by omega)
  split_ifs <;> positivity

/-- Bound on `|Aut(S)|` in terms of `pslOuterBound n p f` and `|S|`. -/
theorem card_mulAut_le_of_statedClassicalModel_psl {S : Type} [Group S] {n p f : ℕ}
    (h : StatedClassicalModel S .PSL n p f) :
    Nat.card (MulAut S) ≤ pslOuterBound n p f * Nat.card S := by
  obtain ⟨hfin, hpos⟩ := finite_and_card_pos_of_statedClassicalModel_psl h
  have : Finite S := hfin
  have : Finite (MulAut S) :=
    Finite.of_injective (fun φ : MulAut S => (φ : S → S)) fun a b hab =>
      MulEquiv.ext (congrFun hab)
  have h' := h
  obtain ⟨⟨hp, hf, hn2, -⟩, -⟩ := h'
  have hdvd := card_outer_dvd_pslOuterBound h
  have hout_le : Nat.card (Outer S) ≤ pslOuterBound n p f :=
    Nat.le_of_dvd (pslOuterBound_pos hp hf hn2) hdvd
  have hinner_le : Nat.card (inner S) ≤ Nat.card S := by
    refine Nat.le_of_dvd hpos ?_
    exact Subgroup.card_dvd_of_surjective
      (f := (MulAut.conj : S →* MulAut S).rangeRestrict)
      (MonoidHom.rangeRestrict_surjective _)
  have hlag : Nat.card (MulAut S) = Nat.card (Outer S) * Nat.card (inner S) := by
    rw [Outer, Subgroup.card_eq_card_quotient_mul_card_subgroup (inner S)]
  rw [hlag]
  exact Nat.mul_le_mul hout_le hinner_le

/-- For `n ≥ 2` and `q ≥ 2`, `∏ i ∈ Finset.Icc 2 n, (q ^ i - 1) ≥ q ^ 2 - 1`. -/
theorem sq_sub_one_le_prod_Icc {n q : ℕ} (hn : 2 ≤ n) (hq : 2 ≤ q) :
    q ^ 2 - 1 ≤ ∏ i ∈ Finset.Icc 2 n, (q ^ i - 1) := by
  have hmem : 2 ∈ Finset.Icc 2 n := Finset.mem_Icc.mpr ⟨le_rfl, hn⟩
  rw [← Finset.mul_prod_erase (Finset.Icc 2 n) (fun i => q ^ i - 1) hmem]
  refine Nat.le_mul_of_pos_right _ (Finset.prod_pos fun i hi => ?_)
  have hi2 : 2 ≤ i := (Finset.mem_Icc.mp (Finset.mem_of_mem_erase hi)).1
  have hqi : 4 ≤ q ^ i := calc
    4 = 2 ^ 2 := rfl
    _ ≤ q ^ 2 := Nat.pow_le_pow_left hq 2
    _ ≤ q ^ i := Nat.pow_le_pow_right (by omega) hi2
  omega

/-- Every `PSL(n, p^f)` model has `pslOuterBound n p f ≤ Nat.card S`. -/
theorem pslOuterBound_le_card {S : Type} [Group S] {n p f : ℕ}
    (h : StatedClassicalModel S .PSL n p f) :
    pslOuterBound n p f ≤ Nat.card S := by
  have h' := h
  obtain ⟨⟨hp, hf, hn2, h22, h23⟩, -⟩ := h'
  have hcard := StatedAPI.card_of_statedClassicalModel_psl (by omega : 0 < n) h
  set q := p ^ f with hq_def
  have hq2 : 2 ≤ q := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
  have hfl : f ≤ q := by
    calc f ≤ 2 ^ f := Nat.le_of_lt (Nat.lt_two_pow_self)
      _ ≤ p ^ f := Nat.pow_le_pow_left hp.two_le f
  have hgcd_le : n.gcd (q - 1) ≤ q - 1 := Nat.gcd_le_right n (by omega)
  have hgcd_pos : 0 < n.gcd (q - 1) := Nat.gcd_pos_of_pos_right n (by omega)
  rw [hcard]
  rcases eq_or_lt_of_le hn2 with rfl | hn3
  · have hq4 : 4 ≤ q := by
      by_contra hlt
      interval_cases hq_val : q
      · exact h22 rfl
      · exact h23 rfl
    have hprod : ∏ i ∈ Finset.Icc 2 2, (q ^ i - 1) = q ^ 2 - 1 := by simp
    have hpow : 2 * (2 - 1) / 2 = 1 := rfl
    rw [hpow, pow_one, hprod]
    unfold pslOuterBound
    simp only [↓reduceIte, one_mul, ← hq_def]
    have hg2 : Nat.gcd 2 (q - 1) ≤ 2 := Nat.gcd_le_left (q - 1) (by omega)
    rw [Nat.le_div_iff_mul_le hgcd_pos]
    have h1 : f * Nat.gcd 2 (q - 1) * Nat.gcd 2 (q - 1) ≤ q * 2 * 2 :=
      Nat.mul_le_mul (Nat.mul_le_mul hfl hg2) hg2
    have h2 : q * 2 * 2 ≤ q * (q ^ 2 - 1) := by
      rw [mul_assoc]
      refine Nat.mul_le_mul_left q ?_
      have : 16 ≤ q ^ 2 := Nat.pow_le_pow_left hq4 2
      omega
    exact le_trans h1 h2
  · have hpow_ge : q ^ 3 ≤ q ^ (n * (n - 1) / 2) := by
      refine Nat.pow_le_pow_right (by omega) ?_
      have : 3 * 2 ≤ n * (n - 1) := Nat.mul_le_mul hn3 (by omega)
      omega
    have hprod_ge : q ^ 2 - 1 ≤ ∏ i ∈ Finset.Icc 2 n, (q ^ i - 1) :=
      sq_sub_one_le_prod_Icc (by omega) hq2
    have hnum_ge : q ^ 3 * (q ^ 2 - 1) ≤
        q ^ (n * (n - 1) / 2) * ∏ i ∈ Finset.Icc 2 n, (q ^ i - 1) :=
      Nat.mul_le_mul hpow_ge hprod_ge
    unfold pslOuterBound
    have hn_ne : n ≠ 2 := by omega
    simp only [hn_ne, ↓reduceIte, ← hq_def]
    rw [Nat.le_div_iff_mul_le hgcd_pos]
    have h2f : 2 * f ≤ q ^ 2 := calc
      2 * f ≤ q * q := Nat.mul_le_mul hq2 hfl
      _ = q ^ 2 := (sq q).symm
    have hgcd_q : n.gcd (q - 1) ≤ q := by omega
    have hgcd_sq : n.gcd (q - 1) ≤ q ^ 2 - 1 := by
      have : q ≤ q ^ 2 := Nat.le_self_pow (by omega) q
      omega
    have h1 : (2 * f * n.gcd (q - 1)) * n.gcd (q - 1) ≤ q ^ 3 * (q ^ 2 - 1) := calc
      (2 * f * n.gcd (q - 1)) * n.gcd (q - 1)
        ≤ (q ^ 2 * q) * (q ^ 2 - 1) := Nat.mul_le_mul (Nat.mul_le_mul h2f hgcd_q) hgcd_sq
      _ = q ^ 3 * (q ^ 2 - 1) := by ring
    exact le_trans h1 hnum_ge

/-- Every group `S` with `LinearSocle S` has `|Aut(S)| ≤ |S|²`
(Maróti, Section 2, Step 1, page 634). -/
theorem autBound_linear : AutBound LinearSocle := by
  intro S _ _ ⟨n, p, f, h⟩
  rw [sq]
  exact le_trans (card_mulAut_le_of_statedClassicalModel_psl h)
    (Nat.mul_le_mul_right _ (pslOuterBound_le_card h))

/-- Over a field `K` of cardinality `2`, every semilinear automorphism of `projectiveSL n K` is
inner. -/
theorem semilinearAutGroup_eq_inner_of_card_two {K : Type} [Field K] [Finite K] {n : ℕ}
    (hn : 3 ≤ n) (hK : Nat.card K = 2) :
    semilinearAutGroup n K = inner (projectiveSL n K) := by
  have h1 := UnitaryHigher.relIndex_inner_linearAutGroup_dvd (k := K) (n := n) (by omega)
  rw [hK, show 2 - 1 = 1 from rfl, Nat.gcd_one_right, Nat.dvd_one] at h1
  obtain ⟨hID, -⟩ := standard_outer_quotients (n := n) (K := K)
  have hIL : inner (projectiveSL n K) = linearAutGroup n K :=
    hID.antisymm (Subgroup.relIndex_eq_one.mp h1)
  have hE : semilinearAutGroup n K = linearAutGroup n K ⊔ (fieldAut n K).range := by
    rw [semilinearAutGroup, Subgroup.closure_union, Subgroup.closure_eq, ← MonoidHom.coe_range,
      Subgroup.closure_eq]
  obtain ⟨-, -, -, -, hcard, -⟩ :=
    finite_field_automorphism_fixed_field_cardinality (F := K)
      Nat.prime_two le_rfl (by rw [hK, pow_one])
  have : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hcard]; omega)
  have : Subsingleton (K ≃+* K) := Finite.card_le_one_iff_subsingleton.mp (by rw [hcard])
  have hrange : (fieldAut n K).range = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨σ, rfl⟩
    rw [Subsingleton.elim σ 1, map_one]
    exact Subgroup.one_mem ⊥
  rw [hE, hrange, sup_bot_eq, hIL]

/-- When `n ≥ 3` and `Nat.card K = 2`, any automorphism `φ` of `projectiveSL n K` that maps an
extremal parabolic `M` to a `projectiveSL n K`-conjugate of `M` is an inner automorphism. -/
theorem mem_inner_of_map_extremalParabolic_conj_of_card_two {K : Type} [Field K] [Finite K]
    {n : ℕ} (hn : 3 ≤ n) (hK : Nat.card K = 2) (φ : MulAut (projectiveSL n K))
    {M : Subgroup (projectiveSL n K)} (hM : M ∈ extremalParabolics (projectiveSL n K) 2)
    {s : projectiveSL n K}
    (hφM : M.map (φ : projectiveSL n K →* projectiveSL n K) =
      M.map (MulAut.conj s : projectiveSL n K →* projectiveSL n K)) :
    φ ∈ inner (projectiveSL n K) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : Fintype K := Fintype.ofFinite K
  have : CharP K 2 :=
    charP_of_card_eq_prime_pow (f := 1) (by rw [← Nat.card_eq_fintype_card, hK, pow_one])
  obtain ⟨-, hbip, -, -, -, -, haut⟩ := incidence_graph (K := K) 2 hn
  obtain ⟨hE, hdisjE, -, -, -⟩ := intrinsic_extremal_parabolics (K := K) 2 hn
  obtain ⟨Φ, hΦ, hpres⟩ := haut φ
  have hpt_pres : ∀ N, N ∈ pointVertices n K 2 → Φ N ∈ pointVertices n K 2 := by
    rcases hpres with ⟨h1, -⟩ | ⟨h1, h2⟩
    · exact h1
    · exfalso
      obtain ⟨g, rfl⟩ := proj_surjective n K s
      let M' : extremalParabolics (projectiveSL n K) 2 := ⟨M, hM⟩
      have hΦM' : (Φ M' : Subgroup (projectiveSL n K)) =
          M.map (MulAut.conj (proj n K g) : projectiveSL n K →* projectiveSL n K) := by
        rw [hΦ M', hφM]
      have hM_cases : M ∈ extremalParabolics (projectiveSL n K) 2 := hM
      rw [hE] at hM_cases
      rcases hM_cases with ⟨L, hL, hML⟩ | ⟨H, hH, hMH⟩
      · have hM'pt : M' ∈ pointVertices n K 2 := ⟨L, hL, hML.symm⟩
        have hΦhyp : Φ M' ∈ hyperplaneVertices n K 2 := h1 M' hM'pt
        obtain ⟨H', hH', hΦH'⟩ := hΦhyp
        have hconj : (Φ M' : Subgroup (projectiveSL n K)) =
            projStabilizer (L.map (mulVecLin (g : Matrix (Fin n) (Fin n) K))) := by
          rw [hΦM', ← hML, projStabilizer_map_conj]
        have hfin : Module.finrank K (L.map (mulVecLin (g : Matrix (Fin n) (Fin n) K))) = 1 :=
          (LinearEquiv.finrank_map_eq (Matrix.SpecialLinearGroup.toLin' g) L).trans hL
        have hmem_both : (Φ M' : Subgroup (projectiveSL n K)) ∈
            (projStabilizer '' {W : Submodule K (Fin n → K) | Module.finrank K W = 1}) ∩
            (projStabilizer '' {W : Submodule K (Fin n → K) | Module.finrank K W = n - 1}) :=
          ⟨⟨_, hfin, hconj.symm⟩, ⟨H', hH', hΦH'.symm⟩⟩
        exact Set.disjoint_iff.mp hdisjE hmem_both
      · have hM'hyp : M' ∈ hyperplaneVertices n K 2 := ⟨H, hH, hMH.symm⟩
        have hΦpt : Φ M' ∈ pointVertices n K 2 := h2 M' hM'hyp
        obtain ⟨L', hL', hΦL'⟩ := hΦpt
        have hconj : (Φ M' : Subgroup (projectiveSL n K)) =
            projStabilizer (H.map (mulVecLin (g : Matrix (Fin n) (Fin n) K))) := by
          rw [hΦM', ← hMH, projStabilizer_map_conj]
        have hfin : Module.finrank K (H.map (mulVecLin (g : Matrix (Fin n) (Fin n) K))) = n - 1 :=
          (LinearEquiv.finrank_map_eq (Matrix.SpecialLinearGroup.toLin' g) H).trans hH
        have hmem_both : (Φ M' : Subgroup (projectiveSL n K)) ∈
            (projStabilizer '' {W : Submodule K (Fin n → K) | Module.finrank K W = 1}) ∩
            (projStabilizer '' {W : Submodule K (Fin n → K) | Module.finrank K W = n - 1}) :=
          ⟨⟨L', hL', hΦL'.symm⟩, ⟨_, hfin, hconj.symm⟩⟩
        exact Set.disjoint_iff.mp hdisjE hmem_both
  have htype : ∀ L : Submodule K (Fin n → K), Module.finrank K L = 1 →
      ∃ L' : Submodule K (Fin n → K), Module.finrank K L' = 1 ∧
        (projStabilizer L).map (φ : projectiveSL n K →* projectiveSL n K) = projStabilizer L' := by
    intro L hL
    have hmem : projStabilizer L ∈ extremalParabolics (projectiveSL n K) 2 := by
      rw [hE]
      exact Or.inl ⟨L, hL, rfl⟩
    obtain ⟨L', hL', hΦL'⟩ := hpt_pres ⟨projStabilizer L, hmem⟩ ⟨L, hL, rfl⟩
    exact ⟨L', hL', (hΦ ⟨projStabilizer L, hmem⟩).symm.trans hΦL'⟩
  obtain ⟨A, σ, hφ_eq⟩ := type_preserving_automorphisms hn φ htype
  rw [← semilinearAutGroup_eq_inner_of_card_two hn hK, hφ_eq]
  exact Subgroup.mul_mem _ (linearAutGroup_le_semilinearAutGroup
    (Subgroup.subset_closure (Set.mem_range_self A)))
    (Subgroup.subset_closure (Or.inr (Set.mem_range_self σ)))

end Maroti
