module

public import Maroti.MinDegree.Heisenberg
public import Maroti.Unitary.HeisenbergGroup
public import Maroti.Unitary.OrderBound
public import CFSG.ClassicalGroups.Unitary.Simple

/-!
# Minimum Degree and Maróti's Theorem for Unitary Groups

This file completes the proof of Theorem 1.1 of Maróti (2002), Section 2, Step 2, page 634 for
almost simple groups with projective special unitary socle `PSU(n, p^f)` (`n ≥ 3`,
`(n, p^f) ≠ (3, 2)`).

Using the Heisenberg subgroup `heisSubgroup hσ.invol m ≤ SU σ (m + 2)` constructed in
`Maroti/Unitary/HeisenbergGroup.lean` together with the normalizer actions of hyperbolic diagonal
torus elements `hypTorus` and middle transvections `midRoot`, and simplicity of `PSU(n, p^f)`
(`CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU` in
`CFSG/ClassicalGroups/Unitary/Simple.lean`), we apply
`Maroti.two_mul_le_index_of_map_ne_bot_of_ne_top` to show that every proper subgroup of
`PSU(n, p^f)` has index at least `2 * p * (p ^ f) ^ (n - 2)`
(`Maroti.index_ge_of_statedClassicalModel_psu`). For comparison, the exact minimal degree is given
in Kleidman and Liebeck, *The Subgroup Structure of the Finite Classical Groups*, Table 5.2.A,
page 175. Combining this subgroup index bound with `Maroti.card_mul_outer_le_bound_psu` and
`Maroti.card_outerAut_psu_eq` proves `Maroti.unitaryCase`.
-/

@[expose] public section

namespace Maroti

open Matrix CFSG.Open CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary
open CFSG.ClassicalGroups.Unitary
open scoped commutatorElement

namespace Unitary

variable {K : Type} [Field K] {σ : K ≃+* K}

/-! ### Diagonal hyperbolic torus elements in `SU σ (m + 2)` -/

section Torus

variable {m : ℕ}

/-- Pointwise multiplication vector equal to `a` at `i₀` and `1` elsewhere. -/
noncomputable def singleMul (i₀ : Fin (m + 2)) (a : K) : Fin (m + 2) → K :=
  Function.update 1 i₀ a

@[simp] theorem singleMul_same (i₀ : Fin (m + 2)) (a : K) :
    singleMul i₀ a i₀ = a := by
  simp [singleMul]

theorem singleMul_of_ne {i₀ i : Fin (m + 2)} (h : i ≠ i₀) (a : K) :
    singleMul i₀ a i = 1 := by
  simp [singleMul, h]

@[simp] theorem singleMul_one (i₀ : Fin (m + 2)) (i : Fin (m + 2)) :
    singleMul i₀ (1 : K) i = 1 := by
  simp [singleMul]

theorem map_singleMul (σ : K ≃+* K) (i₀ : Fin (m + 2)) (a : K) (i : Fin (m + 2)) :
    σ (singleMul i₀ a i) = singleMul i₀ (σ a) i := by
  by_cases h : i = i₀
  · subst h; simp
  · rw [singleMul_of_ne h, singleMul_of_ne h, map_one]

theorem singleMul_rev (i₀ : Fin (m + 2)) (a : K) (i : Fin (m + 2)) :
    singleMul i₀ a (Fin.rev i) = singleMul (Fin.rev i₀) a i := by
  by_cases h : i = Fin.rev i₀
  · subst h; simp
  · have h' : Fin.rev i ≠ i₀ := fun heq => h (by rw [← heq, Fin.rev_rev])
    rw [singleMul_of_ne h', singleMul_of_ne h]

theorem singleMul_mul_singleMul (i₀ : Fin (m + 2)) (a b : K) (i : Fin (m + 2)) :
    singleMul i₀ a i * singleMul i₀ b i = singleMul i₀ (a * b) i := by
  by_cases h : i = i₀
  · subst h; simp
  · rw [singleMul_of_ne h, singleMul_of_ne h, singleMul_of_ne h, mul_one]

theorem prod_singleMul (i₀ : Fin (m + 2)) (a : K) :
    ∏ i, singleMul i₀ a i = a := by
  rw [Finset.prod_eq_single i₀ (fun i _ hi => singleMul_of_ne hi a) (by simp), singleMul_same]

/-- Unitary pair vector at `(i₀, Fin.rev i₀)` with parameter `a`. -/
noncomputable def pairVec (σ : K ≃+* K) (i₀ : Fin (m + 2)) (a : K) : Fin (m + 2) → K :=
  singleMul i₀ a * singleMul (Fin.rev i₀) (σ a)⁻¹

theorem prod_pairVec (σ : K ≃+* K) (i₀ : Fin (m + 2)) (a : K) :
    ∏ i, pairVec σ i₀ a i = a * (σ a)⁻¹ := by
  simp only [pairVec, Pi.mul_apply, Finset.prod_mul_distrib, prod_singleMul]

theorem pairVec_conj_mul_rev (hσ : ∀ x, σ (σ x) = x) (i₀ : Fin (m + 2)) {a : K} (ha : a ≠ 0)
    (i : Fin (m + 2)) :
    σ (pairVec σ i₀ a i) * pairVec σ i₀ a (Fin.rev i) = 1 := by
  have hσa : σ a ≠ 0 := (map_ne_zero_iff σ σ.injective).mpr ha
  simp only [pairVec, Pi.mul_apply, map_mul, map_singleMul, singleMul_rev, Fin.rev_rev,
    map_inv₀, hσ]
  calc singleMul i₀ (σ a) i * singleMul (Fin.rev i₀) a⁻¹ i *
        (singleMul (Fin.rev i₀) a i * singleMul i₀ (σ a)⁻¹ i)
      = (singleMul i₀ (σ a) i * singleMul i₀ (σ a)⁻¹ i) *
        (singleMul (Fin.rev i₀) a⁻¹ i * singleMul (Fin.rev i₀) a i) := by ring
    _ = singleMul i₀ (σ a * (σ a)⁻¹) i * singleMul (Fin.rev i₀) (a⁻¹ * a) i := by
        rw [singleMul_mul_singleMul, singleMul_mul_singleMul]
    _ = 1 := by
        rw [mul_inv_cancel₀ hσa, inv_mul_cancel₀ ha, singleMul_one, singleMul_one, mul_one]

/-- Diagonal vector for the hyperbolic torus element coupling `(0, Fin.rev 0)` and
`(mid j, mid (Fin.rev j))`. -/
noncomputable def hypTorusVec (σ : K ≃+* K) (j : Fin m) (κ : K) : Fin (m + 2) → K :=
  pairVec σ 0 κ * pairVec σ (mid j) κ⁻¹

theorem prod_hypTorusVec (σ : K ≃+* K) (j : Fin m) {κ : K} (hκ : κ ≠ 0) :
    ∏ i, hypTorusVec σ j κ i = 1 := by
  have hσκ : σ κ ≠ 0 := (map_ne_zero_iff σ σ.injective).mpr hκ
  simp only [hypTorusVec, Pi.mul_apply, Finset.prod_mul_distrib, prod_pairVec, map_inv₀, inv_inv]
  calc κ * (σ κ)⁻¹ * (κ⁻¹ * σ κ)
      = (κ * κ⁻¹) * ((σ κ)⁻¹ * σ κ) := by ring
    _ = 1 := by rw [mul_inv_cancel₀ hκ, inv_mul_cancel₀ hσκ, mul_one]

theorem hypTorusVec_conj_mul_rev (hσ : ∀ x, σ (σ x) = x) (j : Fin m) {κ : K} (hκ : κ ≠ 0)
    (i : Fin (m + 2)) :
    σ (hypTorusVec σ j κ i) * hypTorusVec σ j κ (Fin.rev i) = 1 := by
  simp only [hypTorusVec, Pi.mul_apply, map_mul]
  calc σ (pairVec σ 0 κ i) * σ (pairVec σ (mid j) κ⁻¹ i) *
        (pairVec σ 0 κ (Fin.rev i) * pairVec σ (mid j) κ⁻¹ (Fin.rev i))
      = (σ (pairVec σ 0 κ i) * pairVec σ 0 κ (Fin.rev i)) *
        (σ (pairVec σ (mid j) κ⁻¹ i) * pairVec σ (mid j) κ⁻¹ (Fin.rev i)) := by ring
    _ = 1 := by
        rw [pairVec_conj_mul_rev hσ 0 hκ, pairVec_conj_mul_rev hσ (mid j) (inv_ne_zero hκ), mul_one]

@[simp] theorem hypTorusVec_zero (σ : K ≃+* K) (j : Fin m) (κ : K) :
    hypTorusVec σ j κ 0 = κ := by
  have h1 : (0 : Fin (m + 2)) ≠ Fin.rev 0 := zero_ne_rev_zero
  have h2 : (0 : Fin (m + 2)) ≠ mid j := (mid_ne_zero j).symm
  have h3 : (0 : Fin (m + 2)) ≠ Fin.rev (mid j) := by
    rw [rev_mid]; exact (mid_ne_zero (Fin.rev j)).symm
  simp only [hypTorusVec, pairVec, Pi.mul_apply, singleMul_same, singleMul_of_ne h1,
    singleMul_of_ne h2, singleMul_of_ne h3, mul_one]

theorem hypTorusVec_mid (σ : K ≃+* K) (j k : Fin m) (κ : K) :
    hypTorusVec σ j κ (mid k) =
      singleMul (mid j) κ⁻¹ (mid k) * singleMul (mid (Fin.rev j)) (σ κ) (mid k) := by
  have h1 : mid k ≠ (0 : Fin (m + 2)) := mid_ne_zero k
  have h2 : mid k ≠ Fin.rev (0 : Fin (m + 2)) := mid_ne_rev_zero k
  simp only [hypTorusVec, pairVec, Pi.mul_apply, singleMul_of_ne h1, singleMul_of_ne h2,
    rev_mid, map_inv₀, inv_inv, mul_one, one_mul]

theorem hypTorusVec_mid_of_ne (σ : K ≃+* K) {j k : Fin m} (hkj : k ≠ j) (hkr : k ≠ Fin.rev j)
    (κ : K) :
    hypTorusVec σ j κ (mid k) = 1 := by
  rw [hypTorusVec_mid, singleMul_of_ne (fun h => hkj (mid_injective h)),
    singleMul_of_ne (fun h => hkr (mid_injective h)), mul_one]

theorem hypTorusVec_mid_rev_of_ne (σ : K ≃+* K) {j : Fin m} (hj : Fin.rev j ≠ j) (κ : K) :
    hypTorusVec σ j κ (mid (Fin.rev j)) = σ κ := by
  rw [hypTorusVec_mid, singleMul_of_ne (fun h => hj (mid_injective h)), singleMul_same, one_mul]

theorem hypTorusVec_mid_self_of_eq (σ : K ≃+* K) {j : Fin m} (hj : Fin.rev j = j) (κ : K) :
    hypTorusVec σ j κ (mid j) = κ⁻¹ * σ κ := by
  rw [hypTorusVec_mid, hj, singleMul_same, singleMul_same]

/-- The diagonal hyperbolic torus element in `SU σ (m + 2)` associated to `j : Fin m` and
`κ ≠ 0`. -/
noncomputable def hypTorus (hσ : ∀ x, σ (σ x) = x) (j : Fin m) {κ : K} (hκ : κ ≠ 0) :
    SU σ (m + 2) :=
  diagSU (hypTorusVec σ j κ) (prod_hypTorusVec σ j hκ) (hypTorusVec_conj_mul_rev hσ j hκ)

theorem hypTorus_mem_normalizer (hσ : ∀ x, σ (σ x) = x) (j : Fin m) {κ : K} (hκ : κ ≠ 0) :
    hypTorus hσ j hκ ∈ Subgroup.normalizer (heisSubgroup hσ m : Set (SU σ (m + 2))) :=
  diagSU_mem_normalizer_heisSubgroup hσ (hypTorusVec σ j κ) (prod_hypTorusVec σ j hκ)
    (hypTorusVec_conj_mul_rev hσ j hκ)

end Torus

/-! ### Normalizer subgroup `heisNorm` and Heisenberg subgroup `heisQ` -/

section NormalizerAction

variable (hσ : IsUnitaryInvolution σ) (m : ℕ)

/-- The normalizer `N_{SU}(Q)` of `heisSubgroup hσ.invol m` in `SU σ (m + 2)`. -/
noncomputable def heisNorm : Subgroup (SU σ (m + 2)) :=
  Subgroup.normalizer (heisSubgroup hσ.invol m : Set (SU σ (m + 2)))

/-- The Heisenberg subgroup viewed as a normal subgroup of `heisNorm hσ m`. -/
noncomputable def heisQ : Subgroup (heisNorm hσ m) :=
  (heisSubgroup hσ.invol m).subgroupOf (heisNorm hσ m)

theorem heisQ_normal : (heisQ hσ m).Normal :=
  Subgroup.normal_in_normalizer

/-- Canonical isomorphism `heisQ hσ m ≃* heisSubgroup hσ.invol m`. -/
noncomputable def heisQEquiv : heisQ hσ m ≃* heisSubgroup hσ.invol m :=
  Subgroup.subgroupOfEquivOfLe Subgroup.le_normalizer

@[simp] theorem coe_heisQEquiv (x : heisQ hσ m) :
    ((heisQEquiv hσ m x : heisSubgroup hσ.invol m) : SU σ (m + 2)) = x.1.1 :=
  rfl

@[simp] theorem coe_heisQEquiv_symm (x : heisSubgroup hσ.invol m) :
    (((heisQEquiv hσ m).symm x : heisQ hσ m) : SU σ (m + 2)) = x.1 :=
  rfl

/-- The center `Z(Q)` viewed as a subgroup of `heisQ hσ m`. -/
noncomputable def heisZ : Subgroup (heisQ hσ m) :=
  (heisCenter hσ.invol m).comap (heisQEquiv hσ m).toMonoidHom

theorem mem_heisZ_iff {x : heisQ hσ m} :
    x ∈ heisZ hσ m ↔ (heisProj hσ.invol m (heisQEquiv hσ m x)).toAdd = 0 :=
  mem_heisCenter_iff hσ.invol

theorem eq_mkHeisZ_of_mem_heisZ {z : heisQ hσ m} (hz : z ∈ heisZ hσ m) :
    ∃ (c : K) (hc : c + σ c = 0), heisQEquiv hσ m z = mkHeisZ hσ.invol c hc :=
  eq_mkHeisZ_of_mem_heisCenter hσ.invol hz

theorem heisQEquiv_conjQ (g : heisNorm hσ m) (x : heisQ hσ m) :
    ((heisQEquiv hσ m (conjQ (heisQ_normal hσ m) g x) : heisSubgroup hσ.invol m) :
      SU σ (m + 2)) = g.1 * (heisQEquiv hσ m x : SU σ (m + 2)) * g.1⁻¹ :=
  rfl

theorem heisZ_le_center : heisZ hσ m ≤ Subgroup.center (heisQ hσ m) := by
  intro z hz
  rw [Subgroup.mem_center_iff]
  intro y
  apply (heisQEquiv hσ m).injective
  rw [map_mul, map_mul]
  exact Subgroup.mem_center_iff.mp (heisCenter_le_center hσ.invol hz) (heisQEquiv hσ m y)

theorem commutator_mem_heisZ (x y : heisQ hσ m) : ⁅x, y⁆ ∈ heisZ hσ m := by
  change (heisQEquiv hσ m) ⁅x, y⁆ ∈ heisCenter hσ.invol m
  rw [map_commutatorElement]
  exact commutator_mem_heisCenter hσ.invol (heisQEquiv hσ m x) (heisQEquiv hσ m y)

theorem pow_char_eq_one_of_mem_heisZ (p : ℕ) [CharP K p] (z : heisQ hσ m) (hz : z ∈ heisZ hσ m) :
    z ^ p = 1 := by
  apply (heisQEquiv hσ m).injective
  rw [map_pow, map_one]
  obtain ⟨c, hc, hzv⟩ := eq_mkHeisZ_of_mem_heisZ hσ m hz
  have hpow : ∀ k : ℕ, (mkHeisZ (m := m) hσ.invol c hc) ^ k =
      mkHeisZ hσ.invol (k • c) (by
        rw [nsmul_eq_mul, map_mul, map_natCast]
        linear_combination (k : K) * hc) := by
    intro k
    induction k with
    | zero =>
      simp only [pow_zero, zero_smul]
      exact Subtype.ext (heis_zero_zero hσ.invol).symm
    | succ k ih =>
      rw [pow_succ, ih, mkHeisZ, mkHeisZ, mkHeisZ, mkHeis_mul, mkHeis_ext_iff]
      refine ⟨by abel, ?_⟩
      rw [hermJ_zero_left, sub_zero, add_nsmul, one_nsmul]
  rw [hzv, hpow p, mkHeisZ]
  have hp0 : (p • c : K) = 0 := by rw [nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]
  apply Subtype.ext
  rw [coe_mkHeis]
  simp only [hp0]
  exact heis_zero_zero hσ.invol

theorem pow_char_mem_heisZ (p : ℕ) [CharP K p] (x : heisQ hσ m) :
    x ^ p ∈ heisZ hσ m := by
  change (heisQEquiv hσ m) (x ^ p) ∈ heisCenter hσ.invol m
  rw [map_pow]
  exact pow_char_mem_heisCenter hσ.invol p (heisQEquiv hσ m x)

theorem exists_commutator_eq_of_not_mem_heisZ (x : heisQ hσ m) (hx : x ∉ heisZ hσ m)
    (z : heisQ hσ m) (hz : z ∈ heisZ hσ m) :
    ∃ y : heisQ hσ m, ⁅x, y⁆ = z := by
  obtain ⟨v, c, hc, hxv⟩ := (heisQEquiv hσ m x).2
  have hx_eq : heisQEquiv hσ m x = mkHeis hσ.invol v c hc := Subtype.ext hxv
  obtain ⟨cz, hcz, hz_eq⟩ := eq_mkHeisZ_of_mem_heisZ hσ m hz
  have hv0 : v ≠ 0 := by
    intro h0
    apply hx
    rw [mem_heisZ_iff, hx_eq, toAdd_heisProj_mkHeis, h0]
  obtain ⟨j₀, hj₀⟩ : ∃ j₀ : Fin m, v j₀ ≠ 0 := Function.ne_iff.mp hv0
  obtain ⟨r, hr⟩ := hσ.exists_sub_eq hcz
  have hσv : σ (v j₀) ≠ 0 := (map_ne_zero_iff σ σ.injective).mpr hj₀
  let w : Fin m → K := Pi.single (Fin.rev j₀) ((σ (v j₀))⁻¹ * r)
  obtain ⟨cw, hcw⟩ := hσ.trace_surj (-hermJ σ w w) (by rw [map_neg, hermJ_self_fixed σ hσ.invol])
  let y' : heisSubgroup hσ.invol m := mkHeis hσ.invol w cw hcw
  refine ⟨(heisQEquiv hσ m).symm y', ?_⟩
  apply (heisQEquiv hσ m).injective
  rw [map_commutatorElement, MulEquiv.apply_symm_apply, hx_eq, hz_eq, mkHeis_commutator]
  have hvw : hermJ σ v w = r := by
    dsimp [w]
    rw [hermJ_single_right, Fin.rev_rev, mul_inv_cancel_left₀ hσv]
  have hwv : hermJ σ w v = σ r := by
    rw [hermJ_conj σ hσ.invol, hvw]
  rw [mkHeisZ, mkHeisZ, mkHeis_ext_iff]
  exact ⟨rfl, by rw [hwv, hvw, hr]⟩

theorem index_heisZ [Finite K] :
    (heisZ hσ m).index = Nat.card K ^ m := by
  rw [heisZ, Subgroup.index_comap_of_surjective _ (heisQEquiv hσ m).surjective,
    index_heisCenter hσ]

/-- Transitivity of `heisNorm hσ m` on `heisZ hσ m \ {1}` for `0 < m`. -/
theorem heisZ_transitive (hm : 0 < m) :
    ∀ z₁ ∈ heisZ hσ m, z₁ ≠ 1 → ∀ z₂ ∈ heisZ hσ m, z₂ ≠ 1 →
      ∃ g : heisNorm hσ m, conjQ (heisQ_normal hσ m) g z₁ = z₂ := by
  intro z₁ hz₁ hz₁1 z₂ hz₂ hz₂1
  obtain ⟨c₁, hc₁, hz₁v⟩ := eq_mkHeisZ_of_mem_heisZ hσ m hz₁
  obtain ⟨c₂, hc₂, hz₂v⟩ := eq_mkHeisZ_of_mem_heisZ hσ m hz₂
  have hc₁0 : c₁ ≠ 0 := by
    rintro rfl
    apply hz₁1
    apply (heisQEquiv hσ m).injective
    rw [hz₁v, map_one]
    exact Subtype.ext (heis_zero_zero hσ.invol)
  have hc₂0 : c₂ ≠ 0 := by
    rintro rfl
    apply hz₂1
    apply (heisQEquiv hσ m).injective
    rw [hz₂v, map_one]
    exact Subtype.ext (heis_zero_zero hσ.invol)
  have hσc₁ : σ c₁ = -c₁ := eq_neg_of_add_eq_zero_right hc₁
  have hσc₂ : σ c₂ = -c₂ := eq_neg_of_add_eq_zero_right hc₂
  have hd_fix : σ (c₂ * c₁⁻¹) = c₂ * c₁⁻¹ := by
    rw [map_mul, map_inv₀, hσc₁, hσc₂, inv_neg, neg_mul_neg]
  have hd0 : c₂ * c₁⁻¹ ≠ 0 := mul_ne_zero hc₂0 (inv_ne_zero hc₁0)
  obtain ⟨κ, hκ⟩ := hσ.norm_surj (c₂ * c₁⁻¹) hd_fix hd0
  have hκ0 : κ ≠ 0 := fun h0 => hd0 (by rw [← hκ, h0, mul_zero])
  let j₀ : Fin m := ⟨0, hm⟩
  let g : heisNorm hσ m := ⟨hypTorus hσ.invol j₀ hκ0, hypTorus_mem_normalizer hσ.invol j₀ hκ0⟩
  refine ⟨g, ?_⟩
  apply (heisQEquiv hσ m).injective
  apply Subtype.ext
  rw [heisQEquiv_conjQ, hz₁v, hz₂v, mkHeisZ, mkHeisZ, coe_mkHeis, coe_mkHeis]
  change hypTorus hσ.invol j₀ hκ0 * _ * (hypTorus hσ.invol j₀ hκ0)⁻¹ = _
  rw [hypTorus, conj_diagSU_heis, heis_ext_iff]
  refine ⟨?_, ?_⟩
  · funext k; simp
  · rw [hypTorusVec_zero, hκ, inv_mul_cancel_right₀ hc₁0]

/-! ### No normalizer-invariant abelian subgroup strictly contains `heisZ` -/

variable {hσ m}

theorem toAdd_heisProj_of_coe_eq {hσ' : ∀ x, σ (σ x) = x} {q : heisSubgroup hσ' m}
    {v : Fin m → K} {c : K} {hc : c + σ c = -hermJ σ v v}
    (hq : (q : SU σ (m + 2)) = heis hσ' v c hc) :
    (heisProj hσ' m q).toAdd = v := by
  rw [show q = mkHeis hσ' v c hc from Subtype.ext hq, toAdd_heisProj_mkHeis]

/-- Predicate stating that `v : Fin m → K` appears as the vector projection of an element of
`K_sub ≤ heisQ hσ m`. -/
def HasVec (K_sub : Subgroup (heisQ hσ m)) (v : Fin m → K) : Prop :=
  ∃ k ∈ K_sub, (heisProj hσ.invol m (heisQEquiv hσ m k)).toAdd = v

theorem hasVec_sub {K_sub : Subgroup (heisQ hσ m)} {v w : Fin m → K}
    (hv : HasVec K_sub v) (hw : HasVec K_sub w) :
    HasVec K_sub (v - w) := by
  obtain ⟨k₁, hk₁, rfl⟩ := hv
  obtain ⟨k₂, hk₂, rfl⟩ := hw
  refine ⟨k₁ * k₂⁻¹, K_sub.mul_mem hk₁ (K_sub.inv_mem hk₂), ?_⟩
  rw [map_mul, map_inv, map_mul, map_inv, toAdd_mul, toAdd_inv, sub_eq_add_neg]

theorem hermJ_eq_of_hasVec_of_abel {K_sub : Subgroup (heisQ hσ m)}
    (hK_abel : ∀ k₁ ∈ K_sub, ∀ k₂ ∈ K_sub, ⁅k₁, k₂⁆ = 1) {v w : Fin m → K}
    (hv : HasVec K_sub v) (hw : HasVec K_sub w) :
    hermJ σ w v = hermJ σ v w := by
  obtain ⟨k₁, hk₁, hv₁⟩ := hv
  obtain ⟨k₂, hk₂, hw₂⟩ := hw
  obtain ⟨v₁, c₁, hc₁, h₁⟩ := (heisQEquiv hσ m k₁).2
  obtain ⟨v₂, c₂, hc₂, h₂⟩ := (heisQEquiv hσ m k₂).2
  have hk₁_eq : heisQEquiv hσ m k₁ = mkHeis hσ.invol v₁ c₁ hc₁ := Subtype.ext h₁
  have hk₂_eq : heisQEquiv hσ m k₂ = mkHeis hσ.invol v₂ c₂ hc₂ := Subtype.ext h₂
  rw [hk₁_eq, toAdd_heisProj_mkHeis] at hv₁
  rw [hk₂_eq, toAdd_heisProj_mkHeis] at hw₂
  subst v₁ v₂
  have hcomm : heisQEquiv hσ m ⁅k₁, k₂⁆ = 1 := by rw [hK_abel k₁ hk₁ k₂ hk₂, map_one]
  rw [map_commutatorElement, hk₁_eq, hk₂_eq, mkHeis_commutator] at hcomm
  have h1 : (1 : heisSubgroup hσ.invol m) = mkHeis hσ.invol 0 0 (by simp) :=
    Subtype.ext (heis_zero_zero hσ.invol).symm
  rw [h1, mkHeisZ, mkHeis_ext_iff] at hcomm
  exact sub_eq_zero.mp hcomm.2

theorem hasVec_single_of_ne_rev {K_sub : Subgroup (heisQ hσ m)}
    (hK_inv : ∀ g : heisNorm hσ m, ∀ k ∈ K_sub, conjQ (heisQ_normal hσ m) g k ∈ K_sub)
    {v : Fin m → K} (hv : HasVec K_sub v) {j : Fin m} (hj : Fin.rev j ≠ j)
    {τ : K} (hτ : τ + σ τ = 0) :
    HasVec K_sub (Pi.single j (τ * v (Fin.rev j))) := by
  obtain ⟨k, hk, hkv⟩ := hv
  obtain ⟨v', c, hc, hk'⟩ := (heisQEquiv hσ m k).2
  have hk_eq : heisQEquiv hσ m k = mkHeis hσ.invol v' c hc := Subtype.ext hk'
  rw [hk_eq, toAdd_heisProj_mkHeis] at hkv
  subst v'
  let g : heisNorm hσ m :=
    ⟨midRoot hσ.invol hj τ hτ, midRoot_mem_normalizer_heisSubgroup hσ.invol hj τ hτ⟩
  have hk_conj : HasVec K_sub (v + Pi.single j (τ * v (Fin.rev j))) := by
    refine ⟨conjQ (heisQ_normal hσ m) g k, hK_inv g k hk, ?_⟩
    exact toAdd_heisProj_of_coe_eq ((heisQEquiv_conjQ hσ m g k).trans
      (by rw [hk']; exact conj_midRoot_heis hσ.invol hj τ hτ v c hc))
  have hsub := hasVec_sub hk_conj ⟨k, hk, by rw [hk_eq, toAdd_heisProj_mkHeis]⟩
  rwa [add_sub_cancel_left] at hsub

theorem hasVec_hypTorus {K_sub : Subgroup (heisQ hσ m)}
    (hK_inv : ∀ g : heisNorm hσ m, ∀ k ∈ K_sub, conjQ (heisQ_normal hσ m) g k ∈ K_sub)
    {v : Fin m → K} (hv : HasVec K_sub v) (j : Fin m) {κ : K} (hκ : κ ≠ 0) :
    HasVec K_sub (fun i => σ κ * hypTorusVec σ j κ (mid i) * v i) := by
  obtain ⟨k, hk, hkv⟩ := hv
  obtain ⟨v', c, hc, hk'⟩ := (heisQEquiv hσ m k).2
  have hk_eq : heisQEquiv hσ m k = mkHeis hσ.invol v' c hc := Subtype.ext hk'
  rw [hk_eq, toAdd_heisProj_mkHeis] at hkv
  subst v'
  let g : heisNorm hσ m := ⟨hypTorus hσ.invol j hκ, hypTorus_mem_normalizer hσ.invol j hκ⟩
  refine ⟨conjQ (heisQ_normal hσ m) g k, hK_inv g k hk, ?_⟩
  have heq := conj_diagSU_heis hσ.invol (hypTorusVec σ j κ) (prod_hypTorusVec σ j hκ)
    (hypTorusVec_conj_mul_rev hσ.invol j hκ) v c hc
  have hproj := toAdd_heisProj_of_coe_eq ((heisQEquiv_conjQ hσ m g k).trans (hk'.symm ▸ heq))
  rw [hproj]
  funext i
  rw [hypTorusVec_zero]

theorem hasVec_single_hypTorus {K_sub : Subgroup (heisQ hσ m)}
    (hK_inv : ∀ g : heisNorm hσ m, ∀ k ∈ K_sub, conjQ (heisQ_normal hσ m) g k ∈ K_sub)
    {i₀ : Fin m} {a : K} (hv : HasVec K_sub (Pi.single i₀ a)) (j : Fin m) {κ : K} (hκ : κ ≠ 0) :
    HasVec K_sub (Pi.single i₀ (σ κ * hypTorusVec σ j κ (mid i₀) * a)) := by
  have h := hasVec_hypTorus hK_inv hv j hκ
  convert h using 1
  funext i
  by_cases hi : i = i₀
  · subst hi; simp
  · rw [Pi.single_eq_of_ne hi, Pi.single_eq_of_ne hi, mul_zero]

private theorem exists_sq_add_map_sq_ne_zero (hσ : IsUnitaryInvolution σ) :
    ∃ κ : K, κ ≠ 0 ∧ κ ^ 2 + (σ κ) ^ 2 ≠ 0 := by
  by_cases h2 : (1 : K) + 1 ≠ 0
  · refine ⟨1, one_ne_zero, ?_⟩
    simpa using h2
  · push Not at h2
    obtain ⟨κ, hκ⟩ := hσ.exists_ne
    have hκ0 : κ ≠ 0 := by
      rintro rfl
      exact hκ (map_zero σ)
    have hsum : κ + σ κ ≠ 0 := by
      intro h0
      apply hκ
      have h1 : κ + κ = 0 := by linear_combination κ * h2
      linear_combination h0 - h1
    refine ⟨κ, hκ0, ?_⟩
    have hsq : κ ^ 2 + (σ κ) ^ 2 = (κ + σ κ) ^ 2 := by
      linear_combination -(κ * σ κ) * h2
    rw [hsq]
    exact pow_ne_zero 2 hsum

theorem apply_eq_zero_of_ne_rev {K_sub : Subgroup (heisQ hσ m)}
    (hK_inv : ∀ g : heisNorm hσ m, ∀ k ∈ K_sub, conjQ (heisQ_normal hσ m) g k ∈ K_sub)
    (hK_abel : ∀ k₁ ∈ K_sub, ∀ k₂ ∈ K_sub, ⁅k₁, k₂⁆ = 1)
    {v : Fin m → K} (hv : HasVec K_sub v) {j : Fin m} (hj : Fin.rev j ≠ j) :
    v (Fin.rev j) = 0 := by
  by_contra hne
  obtain ⟨τ, hτ0, hτ⟩ := hσ.exists_traceZero
  have hστ : σ τ = -τ := eq_neg_of_add_eq_zero_right hτ
  obtain ⟨a₁, ha₁_def⟩ : ∃ a₁ : K, a₁ = τ * v (Fin.rev j) := ⟨_, rfl⟩
  have ha₁0 : a₁ ≠ 0 := ha₁_def ▸ mul_ne_zero hτ0 hne
  have hw₁ : HasVec K_sub (Pi.single j a₁) :=
    ha₁_def ▸ hasVec_single_of_ne_rev hK_inv hv hj hτ
  have hj' : Fin.rev (Fin.rev j) ≠ Fin.rev j := by rw [Fin.rev_rev]; exact hj.symm
  have hw₂ : HasVec K_sub (Pi.single (Fin.rev j) (τ * a₁)) := by
    have h := hasVec_single_of_ne_rev hK_inv hw₁ hj' hτ
    rwa [Fin.rev_rev, Pi.single_eq_same] at h
  obtain ⟨κ, hκ0, hκ2⟩ := exists_sq_add_map_sq_ne_zero hσ
  have hw₃ : HasVec K_sub (Pi.single (Fin.rev j) ((σ κ) ^ 2 * (τ * a₁))) := by
    have h := hasVec_single_hypTorus hK_inv hw₂ j hκ0
    rwa [hypTorusVec_mid_rev_of_ne σ hj, ← sq] at h
  have h_orth := hermJ_eq_of_hasVec_of_abel hK_abel hw₁ hw₃
  rw [hermJ_single_left, hermJ_single_left, Fin.rev_rev, Pi.single_eq_same, Pi.single_eq_same,
    map_mul, map_mul, map_pow, hσ.invol, hστ] at h_orth
  have hzero : (κ ^ 2 + (σ κ) ^ 2) * τ * a₁ * σ a₁ = 0 := by
    linear_combination -h_orth
  have hσa₁ : σ a₁ ≠ 0 := (map_ne_zero_iff σ σ.injective).mpr ha₁0
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero hκ2 hτ0) ha₁0) hσa₁ hzero

theorem eq_zero_of_hasVec (h3 : m = 1 → ∃ κ : K, κ ≠ 0 ∧ (σ κ) ^ 3 ≠ κ ^ 3)
    {K_sub : Subgroup (heisQ hσ m)}
    (hK_inv : ∀ g : heisNorm hσ m, ∀ k ∈ K_sub, conjQ (heisQ_normal hσ m) g k ∈ K_sub)
    (hK_abel : ∀ k₁ ∈ K_sub, ∀ k₂ ∈ K_sub, ⁅k₁, k₂⁆ = 1)
    {v : Fin m → K} (hv : HasVec K_sub v) :
    v = 0 := by
  have hall_ne : ∀ j : Fin m, Fin.rev j ≠ j → v j = 0 := by
    intro j hj
    have hj' : Fin.rev (Fin.rev j) ≠ Fin.rev j := by rw [Fin.rev_rev]; exact hj.symm
    have h := apply_eq_zero_of_ne_rev hK_inv hK_abel hv hj'
    rwa [Fin.rev_rev] at h
  funext j₀
  by_cases hj₀ : Fin.rev j₀ ≠ j₀
  · exact hall_ne j₀ hj₀
  push Not at hj₀
  by_contra hvj₀
  have hv_single : v = Pi.single j₀ (v j₀) := by
    funext k
    by_cases hk : k = j₀
    · subst hk; simp
    · rw [Pi.single_eq_of_ne hk]
      apply hall_ne k
      intro hrev
      apply hk
      have h1 := congrArg Fin.val hj₀
      have h2 := congrArg Fin.val hrev
      simp only [Fin.val_rev] at h1 h2
      ext
      omega
  have hw₁ : HasVec K_sub (Pi.single j₀ (v j₀)) := hv_single ▸ hv
  have hσv : σ (v j₀) ≠ 0 := (map_ne_zero_iff σ σ.injective).mpr hvj₀
  by_cases hm2 : 2 ≤ m
  · let j₁ : Fin m := ⟨0, by omega⟩
    have hj₀_ne_j₁ : j₀ ≠ j₁ := by
      intro heq
      have h1 := congrArg Fin.val hj₀
      have h2 := congrArg Fin.val heq
      simp only [Fin.val_rev, j₁] at h1 h2
      omega
    have hj₀_ne_rev : j₀ ≠ Fin.rev j₁ := by
      intro heq
      have h1 := congrArg Fin.val hj₀
      have h2 := congrArg Fin.val heq
      simp only [Fin.val_rev, j₁] at h1 h2
      omega
    obtain ⟨κ, hκ⟩ := hσ.exists_ne
    have hκ0 : κ ≠ 0 := by rintro rfl; exact hκ (map_zero σ)
    have hw₂ : HasVec K_sub (Pi.single j₀ (σ κ * v j₀)) := by
      have h := hasVec_single_hypTorus hK_inv hw₁ j₁ hκ0
      rwa [hypTorusVec_mid_of_ne σ hj₀_ne_j₁ hj₀_ne_rev, mul_one] at h
    have h_orth := hermJ_eq_of_hasVec_of_abel hK_abel hw₁ hw₂
    rw [hermJ_single_left, hermJ_single_left, hj₀, Pi.single_eq_same, Pi.single_eq_same,
      map_mul, hσ.invol] at h_orth
    have hzero : (κ - σ κ) * σ (v j₀) * v j₀ = 0 := by linear_combination h_orth
    exact mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hκ.symm) hσv) hvj₀ hzero
  · have hm1 : m = 1 := by have := j₀.isLt; omega
    obtain ⟨κ, hκ0, hκ3⟩ := h3 hm1
    have hσκ0 : σ κ ≠ 0 := (map_ne_zero_iff σ σ.injective).mpr hκ0
    set μ := σ κ * (κ⁻¹ * σ κ)
    have hw₂ : HasVec K_sub (Pi.single j₀ (μ * v j₀)) := by
      have h := hasVec_single_hypTorus hK_inv hw₁ j₀ hκ0
      rwa [hypTorusVec_mid_self_of_eq σ hj₀] at h
    have h_orth := hermJ_eq_of_hasVec_of_abel hK_abel hw₁ hw₂
    rw [hermJ_single_left, hermJ_single_left, hj₀, Pi.single_eq_same, Pi.single_eq_same,
      map_mul] at h_orth
    have hμ_ne : σ μ ≠ μ := by
      intro hμ
      apply hκ3
      have hμ' : κ * ((σ κ)⁻¹ * κ) = σ κ * (κ⁻¹ * σ κ) := by
        simpa [μ, map_mul, map_inv₀, hσ.invol] using hμ
      calc (σ κ) ^ 3 = (σ κ) ^ 3 * (κ⁻¹ * κ) := by rw [inv_mul_cancel₀ hκ0, mul_one]
        _ = (σ κ * (κ⁻¹ * σ κ)) * (κ * σ κ) := by ring
        _ = (κ * ((σ κ)⁻¹ * κ)) * (κ * σ κ) := by rw [← hμ']
        _ = κ ^ 2 * ((σ κ)⁻¹ * σ κ) * κ := by ring
        _ = κ ^ 3 := by rw [inv_mul_cancel₀ hσκ0, mul_one]; ring
    have hzero : (σ μ - μ) * σ (v j₀) * v j₀ = 0 := by linear_combination h_orth
    exact mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hμ_ne) hσv) hvj₀ hzero

theorem eq_heisZ_of_normalizer_invariant_of_abel
    (h3 : m = 1 → ∃ κ : K, κ ≠ 0 ∧ (σ κ) ^ 3 ≠ κ ^ 3)
    (K_sub : Subgroup (heisQ hσ m)) (hZK : heisZ hσ m ≤ K_sub)
    (hK_inv : ∀ g : heisNorm hσ m, ∀ k ∈ K_sub, conjQ (heisQ_normal hσ m) g k ∈ K_sub)
    (hK_abel : ∀ k₁ ∈ K_sub, ∀ k₂ ∈ K_sub, ⁅k₁, k₂⁆ = 1) :
    K_sub = heisZ hσ m := by
  refine le_antisymm (fun k hk => ?_) hZK
  rw [mem_heisZ_iff]
  exact eq_zero_of_hasVec h3 hK_inv hK_abel ⟨k, hk, rfl⟩

end NormalizerAction

/-! ### Minimum degree of `StatedProj (SU σ (m + 2))` and `PSU(n, p^f)` -/

section MinDegree

variable {K : Type} [Field K] {σ : K ≃+* K}

/-- Canonical homomorphism from `heisNorm hσ m` to `StatedProj (SU σ (m + 2))`. -/
noncomputable def heisNormToProj (hσ : IsUnitaryInvolution σ) (m : ℕ) :
    heisNorm hσ m →* StatedProj (SU σ (m + 2)) :=
  (QuotientGroup.mk' ((StatedScalars (Fin (m + 2)) K).subgroupOf (SU σ (m + 2)))).comp
    (heisNorm hσ m).subtype

theorem map_heisZ_heisNormToProj_ne_bot (hσ : IsUnitaryInvolution σ) (m : ℕ) :
    (((heisZ hσ m).map (heisQ hσ m).subtype).map (heisNormToProj hσ m)) ≠ ⊥ := by
  obtain ⟨τ, hτ0, hτ⟩ := hσ.exists_traceZero
  have hc0 : τ + σ τ = -hermJ σ (0 : Fin m → K) 0 := by rw [hermJ_zero_left, neg_zero]; exact hτ
  let z₀ : heisQ hσ m := (heisQEquiv hσ m).symm (mkHeisZ hσ.invol τ hτ)
  have hz₀ : z₀ ∈ heisZ hσ m := by
    rw [mem_heisZ_iff, MulEquiv.apply_symm_apply]
    exact toAdd_heisProj_mkHeis hσ.invol 0 τ hc0
  intro hbot
  have hmem : heisNormToProj hσ m ((heisQ hσ m).subtype z₀) ∈
      (((heisZ hσ m).map (heisQ hσ m).subtype).map (heisNormToProj hσ m)) :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem _ hz₀)
  rw [hbot, Subgroup.mem_bot] at hmem
  change (QuotientGroup.mk (heis hσ.invol 0 τ hc0) : StatedProj (SU σ (m + 2))) = 1 at hmem
  rw [QuotientGroup.eq_one_iff] at hmem
  obtain ⟨d, hd⟩ := hmem
  have h1 : (heis hσ.invol 0 τ hc0 • hypF K m) 0 = τ := by
    rw [heis_smul_hypF, embMid_zero_vec, add_zero, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      hypF, Pi.single_eq_of_ne zero_ne_rev_zero, zero_add, hypE, Pi.single_eq_same, mul_one]
  have h2 : (heis hσ.invol 0 τ hc0 • hypF K m) 0 = 0 := by
    have hd' : ((heis hσ.invol 0 τ hc0 : SU σ (m + 2)) : GL (Fin (m + 2)) K) =
        GeneralLinearGroup.scalar (Fin (m + 2)) d := hd.symm
    change ((((heis hσ.invol 0 τ hc0 : SU σ (m + 2)) : GL (Fin (m + 2)) K) :
      Matrix (Fin (m + 2)) (Fin (m + 2)) K) *ᵥ hypF K m) 0 = 0
    rw [hd', GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, hypF, diagonal_mulVec_single,
      Pi.single_eq_of_ne zero_ne_rev_zero]
  exact hτ0 (h1.symm.trans h2)

/-- Minimum index bound for `StatedProj (SU σ (m + 2))`. -/
theorem two_mul_pow_le_index_statedProj_SU [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (hσ : IsUnitaryInvolution σ) {m : ℕ} (hm : 1 ≤ m)
    (h3 : m = 1 → ∃ κ : K, κ ≠ 0 ∧ (σ κ) ^ 3 ≠ κ ^ 3)
    {q : ℕ} (hq : 2 ≤ q) (hK : Nat.card K = q ^ 2)
    [IsSimpleGroup (StatedProj (SU σ (m + 2)))]
    {H : Subgroup (StatedProj (SU σ (m + 2)))} (hH : H ≠ ⊤) :
    2 * p * q ^ m ≤ H.index := by
  have hqm2 : 2 ≤ q ^ m := by
    calc 2 = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
      _ ≤ q ^ m := Nat.pow_le_pow_left hq m
  have hidx : (q ^ m) ^ 2 ≤ (heisZ hσ m).index := by
    rw [index_heisZ, hK, ← pow_mul, ← pow_mul, mul_comm 2 m]
  exact two_mul_le_index_of_map_ne_bot_of_ne_top
    (heisZ_le_center hσ m)
    (commutator_mem_heisZ hσ m)
    (pow_char_eq_one_of_mem_heisZ hσ m p)
    (pow_char_mem_heisZ hσ m p)
    (exists_commutator_eq_of_not_mem_heisZ hσ m)
    (heisQ_normal hσ m)
    hH
    (heisNormToProj hσ m)
    (map_heisZ_heisNormToProj_ne_bot hσ m)
    hqm2
    hidx
    (heisZ_transitive hσ m (by omega))
    (eq_heisZ_of_normalizer_invariant_of_abel h3)

/-- Existence of `κ ∈ Kˣ` with `(σ κ) ^ 3 ≠ κ ^ 3` when `Nat.card K = (p ^ f) ^ 2` and
`p ^ f ≠ 2`. -/
theorem exists_cube_map_ne_cube [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]
    (hK : Nat.card K = (p ^ f) ^ 2) (hq2 : p ^ f ≠ 2) :
    ∃ κ : K, κ ≠ 0 ∧ (unitaryInvolution K p f κ) ^ 3 ≠ κ ^ 3 := by
  have hq1 := one_lt_pow_of_card hK
  have hq3 : 3 ≤ p ^ f := by omega
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hord : orderOf g = (p ^ f) ^ 2 - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, card_units_of_card hK]
  refine ⟨(g : K), g.ne_zero, fun h => ?_⟩
  rw [unitaryInvolution_apply, ← pow_mul] at h
  have h1 : g ^ (p ^ f * 3 - 3) = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    have hmul : (g : K) ^ (p ^ f * 3 - 3) * (g : K) ^ 3 = 1 * (g : K) ^ 3 := by
      rw [← pow_add, Nat.sub_add_cancel (by omega), one_mul, h]
    exact mul_right_cancel₀ (pow_ne_zero 3 g.ne_zero) hmul
  have hdvd := orderOf_dvd_of_pow_eq_one h1
  rw [hord] at hdvd
  have hle := Nat.le_of_dvd (by omega) hdvd
  have hlt : p ^ f * 3 ≤ (p ^ f) ^ 2 := by nlinarith
  omega

/-- Isomorphism `StatedProj H ≃* StatedProj H'` from subgroup equality `H = H'`. -/
noncomputable def statedProjEqEquiv {n : ℕ} {H H' : Subgroup (GL (Fin n) K)} (h : H = H') :
    StatedProj H ≃* StatedProj H' := by
  cases h
  exact MulEquiv.refl _

/-- Isomorphism `StatedProj (SU σ n) ≃* StatedProj (SUid σ n)` induced by `conjEquiv P hP`. -/
noncomputable def statedProjConjEquiv {n : ℕ} (P : GL (Fin n) K)
    (hP : conjTr σ (P : Matrix (Fin n) (Fin n) K) * (P : Matrix (Fin n) (Fin n) K) = antidiag n) :
    StatedProj (SU σ n) ≃* StatedProj (SUid σ n) :=
  QuotientGroup.congr ((StatedScalars (Fin n) K).subgroupOf (SU σ n))
    ((StatedScalars (Fin n) K).subgroupOf (SUid σ n)) (conjEquiv P hP) (by
      have hcent : ∀ (Q : GL (Fin n) K) (c : Kˣ),
          Q * GeneralLinearGroup.scalar (Fin n) c * Q⁻¹ =
            GeneralLinearGroup.scalar (Fin n) c := by
        intro Q c
        have hc : GeneralLinearGroup.scalar (Fin n) c ∈ Subgroup.center (GL (Fin n) K) := by
          rw [GeneralLinearGroup.center_eq_range_scalar]
          exact ⟨c, rfl⟩
        rw [Subgroup.mem_center_iff.mp hc Q, mul_inv_cancel_right]
      ext B
      simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range]
      constructor
      · rintro ⟨A, ⟨c, hc⟩, rfl⟩
        refine ⟨c, ?_⟩
        change GeneralLinearGroup.scalar (Fin n) c = ((conjEquiv P hP A : SUid σ n) : GL (Fin n) K)
        rw [coe_conjEquiv, ← hc, hcent]
      · rintro ⟨c, hc⟩
        refine ⟨(conjEquiv P hP).symm B, ⟨c, ?_⟩, (conjEquiv P hP).apply_symm_apply B⟩
        change GeneralLinearGroup.scalar (Fin n) c = P⁻¹ * (B : GL (Fin n) K) * P
        rw [← hc]
        simpa using (hcent P⁻¹ c).symm)

end MinDegree

end Unitary

/-- Every proper subgroup `H` of `PSU(n, p^f)` (`n ≥ 3`, `(n, p^f) ≠ (3, 2)`) has index at least
`2 * p * (p ^ f) ^ (n - 2)`, proved via the Heisenberg subgroup `heisSubgroup` and its normalizer
action. -/
theorem index_ge_of_statedClassicalModel_psu {S : Type} [Group S] {n p f : ℕ}
    (h : StatedClassicalModel S .PSU n p f) {H : Subgroup S} (hH : H ≠ ⊤) :
    2 * p * (p ^ f) ^ (n - 2) ≤ H.index := by
  obtain ⟨⟨hp, hf, hn, hnq⟩, K, _, _, hK, ⟨eS⟩⟩ := h
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := charP_of_card_sq hK
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hm : 1 ≤ m := by omega
  have hq : 2 ≤ p ^ f := le_trans hp.two_le (by
    calc p = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ f := Nat.pow_le_pow_right hp.pos hf)
  let σ := unitaryInvolution K p f
  have hσ : IsUnitaryInvolution σ := isUnitaryInvolution_unitaryInvolution hK
  obtain ⟨P, hP⟩ := exists_wittMatrix hK (m + 2)
  have : IsSimpleGroup (StatedProj (StatedSU (m + 2) (p ^ f) K)) :=
    isSimpleGroup_statedProj_statedSU K p f hK (m + 2) (by omega) hnq
  have : IsSimpleGroup S := eS.isSimpleGroup
  let e1 : StatedProj (StatedSU (m + 2) (p ^ f) K) ≃* StatedProj (SUid σ (m + 2)) :=
    Unitary.statedProjEqEquiv (SUid_eq_statedSU hK (m + 2)).symm
  let e : S ≃* StatedProj (SU σ (m + 2)) :=
    (eS.trans e1).trans (Unitary.statedProjConjEquiv P hP).symm
  have : IsSimpleGroup (StatedProj (SU σ (m + 2))) := e.symm.isSimpleGroup
  have hH' : H.map e.toMonoidHom ≠ ⊤ := by
    intro htop
    apply hH
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [htop, Subgroup.map_top_of_surjective _ e.surjective]
  rw [Nat.add_sub_cancel, ← Subgroup.index_map_equiv H e]
  exact Unitary.two_mul_pow_le_index_statedProj_SU hσ hm
    (fun hm1 => Unitary.exists_cube_map_ne_cube hK (fun hq2 => hnq (by rw [hm1, hq2])))
    hq hK hH'

/-- Theorem 1.1 of Maróti (2002) for almost simple groups with socle `PSU(n, p^f)` (`n ≥ 3`,
`(n, p^f) ≠ (3, 2)`). -/
theorem unitaryCase : AlmostSimpleCase (ClassicalSocle .PSU) := by
  intro α _ G S _ _ hAS ⟨n, p, f, hModel⟩
  right; right
  have hp : p.Prime := hModel.1.1
  have hf : 1 ≤ f := hModel.1.2.1
  have hn : 3 ≤ n := hModel.1.2.2.1
  have h0 : 0 < 2 * f * Nat.gcd n (p ^ f + 1) :=
    Nat.mul_pos (Nat.mul_pos (by norm_num) hf) (Nat.gcd_pos_of_pos_left _ (by omega))
  exact hAS.card_le_bound_of_outerAut_dvd h0
    (fun H hH => index_ge_of_statedClassicalModel_psu hModel hH)
    (by rw [card_outerAut_psu_eq hModel])
    (card_mul_outer_le_bound_psu hModel)

end Maroti
