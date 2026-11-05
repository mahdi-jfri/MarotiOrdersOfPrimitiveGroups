module

public import Maroti.MinDegree.Heisenberg
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Minimum index from rank-4 extraspecial subgroups with two normalizing operators

Suppose a finite group `G` contains a `p`-subgroup `Q ≤ G` of order `p ^ 5` and exponent `p` whose
center `Z(Q)` has order `p` and contains `[Q, Q]`, together with a coordinate map
`ψ : Q → (Fin 4 → ZMod p)` with kernel `Z(Q)` and two elements `g₁, g₂ ∈ G` normalizing `Q` and
acting on `ψ` via `4 × 4` matrices `A₁, A₂` over `ZMod p` that have no proper nonzero invariant
additive subgroup. Then every subgroup `K ≤ G` not containing `Z(Q)` has index
`2 * p ^ 3 ≤ K.index`, and every proper subgroup of a simple group `S ≃* G` has index at least
`2 * p ^ 3`.
-/

@[expose] public section

namespace Maroti.ExtraspecialCoord

open Subgroup
open scoped commutatorElement Matrix

/-- Explicit expansion of the `4 × 4` determinant with rows `w₀, w₁, w₂, w₃`. -/
def det4 {R : Type*} [CommRing R] (w₀ w₁ w₂ w₃ : Fin 4 → R) : R :=
  w₀ 0 * (w₁ 1 * (w₂ 2 * w₃ 3 - w₂ 3 * w₃ 2) - w₁ 2 * (w₂ 1 * w₃ 3 - w₂ 3 * w₃ 1) +
    w₁ 3 * (w₂ 1 * w₃ 2 - w₂ 2 * w₃ 1)) -
  w₀ 1 * (w₁ 0 * (w₂ 2 * w₃ 3 - w₂ 3 * w₃ 2) - w₁ 2 * (w₂ 0 * w₃ 3 - w₂ 3 * w₃ 0) +
    w₁ 3 * (w₂ 0 * w₃ 2 - w₂ 2 * w₃ 0)) +
  w₀ 2 * (w₁ 0 * (w₂ 1 * w₃ 3 - w₂ 3 * w₃ 1) - w₁ 1 * (w₂ 0 * w₃ 3 - w₂ 3 * w₃ 0) +
    w₁ 3 * (w₂ 0 * w₃ 1 - w₂ 1 * w₃ 0)) -
  w₀ 3 * (w₁ 0 * (w₂ 1 * w₃ 2 - w₂ 2 * w₃ 1) - w₁ 1 * (w₂ 0 * w₃ 2 - w₂ 2 * w₃ 0) +
    w₁ 2 * (w₂ 0 * w₃ 1 - w₂ 1 * w₃ 0))

theorem det_of_eq_det4 {R : Type*} [CommRing R] (w₀ w₁ w₂ w₃ : Fin 4 → R) :
    (Matrix.of ![w₀, w₁, w₂, w₃]).det = det4 w₀ w₁ w₂ w₃ := by
  have h12 : (Fin.succAbove 1 2 : Fin 4) = 3 := rfl
  have h22 : (Fin.succAbove 2 2 : Fin 4) = 3 := rfl
  have h32 : (Fin.succAbove 3 2 : Fin 4) = 2 := rfl
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_fin_three, Matrix.submatrix, h12, h22, h32, det4]
  ring

/-- Four vectors `w₀, w₁, w₂, w₃` in an additive subgroup `U` of `Fin 4 → ZMod p` with
`det4 w₀ w₁ w₂ w₃ ≠ 0` span all of `Fin 4 → ZMod p`. -/
theorem mem_of_det4_ne_zero {p : ℕ} [Fact (Nat.Prime p)]
    {U : AddSubgroup (Fin 4 → ZMod p)} {w₀ w₁ w₂ w₃ : Fin 4 → ZMod p}
    (h₀ : w₀ ∈ U) (h₁ : w₁ ∈ U) (h₂ : w₂ ∈ U) (h₃ : w₃ ∈ U)
    (hdet : det4 w₀ w₁ w₂ w₃ ≠ 0) (y : Fin 4 → ZMod p) :
    y ∈ U := by
  have hsmul : ∀ (c : ZMod p) {u : Fin 4 → ZMod p}, u ∈ U → c • u ∈ U := by
    intro c u hu
    rw [← ZMod.natCast_zmod_val c, Nat.cast_smul_eq_nsmul]
    exact U.nsmul_mem hu c.val
  set M : Matrix (Fin 4) (Fin 4) (ZMod p) := Matrix.of ![w₀, w₁, w₂, w₃]
  have hMdet : M.det ≠ 0 := by
    rw [det_of_eq_det4]
    exact hdet
  have hunit : IsUnit M.det := isUnit_iff_ne_zero.mpr hMdet
  set c : Fin 4 → ZMod p := y ᵥ* M⁻¹
  have hy : c ᵥ* M = y := by
    change (y ᵥ* M⁻¹) ᵥ* M = y
    rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hunit, Matrix.vecMul_one]
  have hsum : c ᵥ* M = c 0 • w₀ + c 1 • w₁ + c 2 • w₂ + c 3 • w₃ := by
    ext j
    simp only [Matrix.vecMul, dotProduct, Fin.sum_univ_four, M, Matrix.of_apply,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rfl
  rw [← hy, hsum]
  exact U.add_mem (U.add_mem (U.add_mem (hsmul (c 0) h₀) (hsmul (c 1) h₁)) (hsmul (c 2) h₂))
    (hsmul (c 3) h₃)

/-- Decidable irreducibility criterion for a pair of `4 × 4` matrices `A₁, A₂` over `ZMod p`. -/
def IrreduciblePair {p : ℕ} (A₁ A₂ : Matrix (Fin 4) (Fin 4) (ZMod p)) : Prop :=
  ∀ v : Fin 4 → ZMod p, v ≠ 0 →
    det4 v (A₁ *ᵥ v) (A₂ *ᵥ v) (A₂ *ᵥ (A₁ *ᵥ v)) ≠ 0 ∨
    det4 v (A₂ *ᵥ v) (A₁ *ᵥ (A₂ *ᵥ v)) (A₂ *ᵥ (A₁ *ᵥ (A₂ *ᵥ v))) ≠ 0 ∨
    det4 v (A₁ *ᵥ v) (A₂ *ᵥ v) (A₂ *ᵥ (A₁ *ᵥ (A₁ *ᵥ v))) ≠ 0 ∨
    det4 v (A₁ *ᵥ (A₁ *ᵥ v)) (A₁ *ᵥ (A₁ *ᵥ (A₁ *ᵥ v))) (A₂ *ᵥ (A₁ *ᵥ (A₂ *ᵥ v))) ≠ 0

instance {p : ℕ} [NeZero p] (A₁ A₂ : Matrix (Fin 4) (Fin 4) (ZMod p)) :
    Decidable (IrreduciblePair A₁ A₂) := by
  unfold IrreduciblePair
  infer_instance

theorem mem_of_irreduciblePair {p : ℕ} [Fact (Nat.Prime p)]
    {A₁ A₂ : Matrix (Fin 4) (Fin 4) (ZMod p)} (hirr : IrreduciblePair A₁ A₂)
    {U : AddSubgroup (Fin 4 → ZMod p)}
    (hA₁ : ∀ u ∈ U, A₁ *ᵥ u ∈ U) (hA₂ : ∀ u ∈ U, A₂ *ᵥ u ∈ U)
    {v : Fin 4 → ZMod p} (hvU : v ∈ U) (hv0 : v ≠ 0) (y : Fin 4 → ZMod p) :
    y ∈ U := by
  have h1 : A₁ *ᵥ v ∈ U := hA₁ v hvU
  have h2 : A₂ *ᵥ v ∈ U := hA₂ v hvU
  have h11 : A₁ *ᵥ (A₁ *ᵥ v) ∈ U := hA₁ _ h1
  have h12 : A₁ *ᵥ (A₂ *ᵥ v) ∈ U := hA₁ _ h2
  have h21 : A₂ *ᵥ (A₁ *ᵥ v) ∈ U := hA₂ _ h1
  have h111 : A₁ *ᵥ (A₁ *ᵥ (A₁ *ᵥ v)) ∈ U := hA₁ _ h11
  have h211 : A₂ *ᵥ (A₁ *ᵥ (A₁ *ᵥ v)) ∈ U := hA₂ _ h11
  have h212 : A₂ *ᵥ (A₁ *ᵥ (A₂ *ᵥ v)) ∈ U := hA₂ _ h12
  rcases hirr v hv0 with hd1 | hd2 | hd3 | hd4
  · exact mem_of_det4_ne_zero hvU h1 h2 h21 hd1 y
  · exact mem_of_det4_ne_zero hvU h2 h12 h212 hd2 y
  · exact mem_of_det4_ne_zero hvU h1 h2 h211 hd3 y
  · exact mem_of_det4_ne_zero hvU h11 h111 h212 hd4 y

section GroupBound

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [hp : Fact (Nat.Prime p)]
variable {Q : Subgroup G}

/-- The additive subgroup of `Fin 4 → ZMod p` formed by the image of `W ≤ Q` under an additive map
`ψ : Q → (Fin 4 → ZMod p)`. -/
def imageAddSubgroup (ψ : Q → (Fin 4 → ZMod p)) (hψ_one : ψ 1 = 0)
    (hψ_mul : ∀ a b : Q, ψ (a * b) = ψ a + ψ b) (W : Subgroup Q) :
    AddSubgroup (Fin 4 → ZMod p) where
  carrier := {v | ∃ w ∈ W, ψ w = v}
  zero_mem' := ⟨1, W.one_mem, hψ_one⟩
  add_mem' := by
    rintro _ _ ⟨w₁, hw₁, rfl⟩ ⟨w₂, hw₂, rfl⟩
    exact ⟨w₁ * w₂, W.mul_mem hw₁ hw₂, hψ_mul w₁ w₂⟩
  neg_mem' := by
    rintro _ ⟨w, hw, rfl⟩
    refine ⟨w⁻¹, W.inv_mem hw, ?_⟩
    apply add_left_cancel (a := ψ w)
    rw [← hψ_mul w w⁻¹, mul_inv_cancel, hψ_one, add_neg_cancel]

omit [Finite G] in
theorem psi_conj_eq (ψ : Q → (Fin 4 → ZMod p))
    (hψ_mul : ∀ a b : Q, ψ (a * b) = ψ a + ψ b) (q u : Q) :
    ψ (q * u * q⁻¹) = ψ u := by
  apply add_right_cancel (b := ψ q)
  rw [← hψ_mul (q * u * q⁻¹) q, inv_mul_cancel_right, hψ_mul, add_comm (ψ q)]

theorem subgroupOf_index_le_index (K : Subgroup G) :
    (K.subgroupOf Q).index ≤ K.index := by
  set W : Subgroup Q := K.subgroupOf Q
  let f : Q ⧸ W → G ⧸ K := fun qa =>
    Quotient.liftOn qa (fun q : Q => ((q : G) : G ⧸ K)) fun a b hab => by
      have hab' : (QuotientGroup.mk a : Q ⧸ W) = QuotientGroup.mk b := Quotient.sound hab
      rw [QuotientGroup.eq, mem_subgroupOf] at hab'
      exact QuotientGroup.eq.mpr hab'
  have hf : Function.Injective f := by
    intro qa qb heq
    induction qa using QuotientGroup.induction_on with | H a =>
    induction qb using QuotientGroup.induction_on with | H b =>
    have hK : (a : G)⁻¹ * (b : G) ∈ K := QuotientGroup.eq.mp heq
    exact QuotientGroup.eq.mpr hK
  exact Nat.card_le_card_of_injective f hf

/-- If `K ≤ G`, `W = K.subgroupOf Q`, `g ∈ G` normalizes `Q`, and no element of `Q * g` lies in `K`,
then `2 * W.index ≤ K.index`. -/
theorem two_mul_index_le_of_forall_mul_not_mem {K : Subgroup G} {g : G}
    (hg : ∀ q ∈ Q, g * q * g⁻¹ ∈ Q)
    (hnot : ∀ q : Q, (q : G) * g ∉ K) :
    2 * (K.subgroupOf Q).index ≤ K.index := by
  set W : Subgroup Q := K.subgroupOf Q
  let Φ : Fin 2 × (Q ⧸ W) → G ⧸ K := fun s =>
    Quotient.liftOn s.2 (fun q : Q => ((g ^ (s.1 : ℕ) * (q : G) : G) : G ⧸ K)) fun q₁ q₂ hq => by
      have hq' : (QuotientGroup.mk q₁ : Q ⧸ W) = QuotientGroup.mk q₂ := Quotient.sound hq
      rw [QuotientGroup.eq, mem_subgroupOf] at hq'
      apply QuotientGroup.eq.mpr
      have h1 : (g ^ (s.1 : ℕ) * (q₁ : G))⁻¹ * (g ^ (s.1 : ℕ) * (q₂ : G)) =
          (q₁ : G)⁻¹ * (q₂ : G) := by group
      rw [h1]
      exact hq'
  have hstep_lt : ∀ (s₁ s₂ : Fin 2) (q₁ q₂ : Q),
      s₁ < s₂ → Φ (s₁, QuotientGroup.mk q₁) = Φ (s₂, QuotientGroup.mk q₂) → False := by
    intro s₁ s₂ q₁ q₂ hlt heq
    have hk : (g ^ (s₁ : ℕ) * (q₁ : G))⁻¹ * (g ^ (s₂ : ℕ) * (q₂ : G)) ∈ K :=
      QuotientGroup.eq.mp heq
    have hs₁ : (s₁ : ℕ) = 0 := by omega
    have hs₂ : (s₂ : ℕ) = 1 := by omega
    let q₀ : Q := q₁⁻¹ * ⟨g * (q₂ : G) * g⁻¹, hg q₂.1 q₂.2⟩
    have hq₀g : (q₀ : G) * g =
        (g ^ (s₁ : ℕ) * (q₁ : G))⁻¹ * (g ^ (s₂ : ℕ) * (q₂ : G)) := by
      simp only [q₀, Subgroup.coe_mul, Subgroup.coe_inv, hs₁, hs₂, pow_zero, pow_one]
      group
    exact hnot q₀ (hq₀g.symm ▸ hk)
  have hΦ : Function.Injective Φ := by
    rintro ⟨s₁, a₁⟩ ⟨s₂, a₂⟩ heq
    induction a₁ using QuotientGroup.induction_on with | H q₁ =>
    induction a₂ using QuotientGroup.induction_on with | H q₂ =>
    rcases lt_trichotomy s₁ s₂ with hlt | rfl | hgt
    · exact False.elim (hstep_lt s₁ s₂ q₁ q₂ hlt heq)
    · refine Prod.ext rfl ?_
      rw [QuotientGroup.eq, mem_subgroupOf]
      have hk : (g ^ (s₁ : ℕ) * (q₁ : G))⁻¹ * (g ^ (s₁ : ℕ) * (q₂ : G)) ∈ K :=
        QuotientGroup.eq.mp heq
      have h1 : (g ^ (s₁ : ℕ) * (q₁ : G))⁻¹ * (g ^ (s₁ : ℕ) * (q₂ : G)) =
          (q₁ : G)⁻¹ * (q₂ : G) := by group
      rwa [h1] at hk
    · exact False.elim (hstep_lt s₂ s₁ q₂ q₁ hgt heq.symm)
  have hle := Nat.card_le_card_of_injective Φ hΦ
  simpa only [Nat.card_prod, Nat.card_fin, Subgroup.index] using hle

include hp in
/-- Main local index bound: if `Q ≤ G` has order `p ^ 5`, exponent `p`, center of order `p`
containing `[Q, Q]`, coordinate map `ψ : Q → (Fin 4 → ZMod p)` with kernel `Z(Q)`, and two
normalizing elements `g₁, g₂ ∈ G` acting on `ψ` via an `IrreduciblePair A₁ A₂`, then every
subgroup `K ≤ G` with `¬ center Q ≤ K.subgroupOf Q` satisfies `2 * p ^ 3 ≤ K.index`. -/
theorem two_mul_cube_le_index_of_not_le (hp3 : 3 ≤ p)
    (hcard : Nat.card Q = p ^ 5) (hcenter : Nat.card (center Q) = p)
    (hcomm : commutator Q ≤ center Q) (hexp : ∀ q : Q, q ^ p = 1)
    (ψ : Q → (Fin 4 → ZMod p)) (hψ_one : ψ 1 = 0)
    (hψ_mul : ∀ a b : Q, ψ (a * b) = ψ a + ψ b)
    (hψ_ker : ∀ q : Q, ψ q = 0 ↔ q ∈ center Q)
    {g₁ g₂ : G} (hg₁ : ∀ q ∈ Q, g₁ * q * g₁⁻¹ ∈ Q) (hg₂ : ∀ q ∈ Q, g₂ * q * g₂⁻¹ ∈ Q)
    {A₁ A₂ : Matrix (Fin 4) (Fin 4) (ZMod p)}
    (hA₁ : ∀ q : Q, ψ ⟨g₁ * (q : G) * g₁⁻¹, hg₁ q.1 q.2⟩ = A₁ *ᵥ ψ q)
    (hA₂ : ∀ q : Q, ψ ⟨g₂ * (q : G) * g₂⁻¹, hg₂ q.1 q.2⟩ = A₂ *ᵥ ψ q)
    (hirr : IrreduciblePair A₁ A₂)
    {K : Subgroup G} (hZK : ¬ center Q ≤ K.subgroupOf Q) :
    2 * p ^ 3 ≤ K.index := by
  have hp_pos : 0 < p := hp.out.pos
  have hcomm_mem : ∀ x y : Q, ⁅x, y⁆ ∈ center Q := fun x y => by
    apply hcomm
    rw [_root_.commutator_def]
    exact Subgroup.commutator_mem_commutator (mem_top x) (mem_top y)
  have hpow_Z : ∀ z ∈ center Q, z ^ p = 1 := fun z _ => hexp z
  have hpow_mem : ∀ x : Q, x ^ p ∈ center Q := fun x => by
    rw [hexp x]
    exact one_mem _
  have hexists_comm : ∀ x : Q, x ∉ center Q → ∀ z ∈ center Q, ∃ y : Q, ⁅x, y⁆ = z := by
    intro x hx z hz
    let φ : Q →* center Q :=
      { toFun := fun y => ⟨⁅x, y⁆, hcomm_mem x y⟩
        map_one' := Subtype.ext (commutatorElement_one_right x)
        map_mul' := fun y₁ y₂ =>
          Subtype.ext (commutatorElement_mul_right_of_le_center le_rfl hcomm_mem x y₁ y₂) }
    have hnot : ∃ y₀ : Q, φ y₀ ≠ 1 := by
      by_contra! hall
      apply hx
      rw [mem_center_iff]
      intro y
      have hy := congrArg Subtype.val (hall y)
      exact (commutatorElement_eq_one_iff_mul_comm.mp hy).symm
    obtain ⟨y₀, hy₀⟩ := hnot
    have hdvd : Nat.card φ.range ∣ p := by
      rw [← hcenter]
      exact Subgroup.card_subgroup_dvd_card φ.range
    rcases hp.out.eq_one_or_self_of_dvd _ hdvd with h1 | hp'
    · exfalso
      have hsub : Subsingleton φ.range := Finite.card_le_one_iff_subsingleton.mp h1.le
      exact hy₀ (congrArg Subtype.val (Subsingleton.elim (⟨φ y₀, ⟨y₀, rfl⟩⟩ : φ.range) 1))
    · have htop : φ.range = ⊤ := Subgroup.eq_top_of_card_eq _ (hp'.trans hcenter.symm)
      have hmem : (⟨z, hz⟩ : center Q) ∈ φ.range := htop ▸ mem_top _
      obtain ⟨y, hy⟩ := hmem
      exact ⟨y, congrArg Subtype.val hy⟩
  have hidx_Z : (center Q).index = (p ^ 2) ^ 2 := by
    have hmul := (center Q).index_mul_card
    rw [hcenter, hcard, show p ^ 5 = (p ^ 2) ^ 2 * p by ring] at hmul
    exact Nat.eq_of_mul_eq_mul_right hp_pos hmul
  set W : Subgroup Q := K.subgroupOf Q
  have hcube : p ^ 3 ≤ W.index := by
    rw [show p ^ 3 = p * p ^ 2 by ring]
    exact mul_le_index_of_not_le le_rfl hcomm_mem hpow_Z hpow_mem hexists_comm hZK hidx_Z.symm.le
  by_cases h1 : ∀ q : Q, (q : G) * g₁ ∉ K
  · exact le_trans (Nat.mul_le_mul_left 2 hcube)
      (two_mul_index_le_of_forall_mul_not_mem hg₁ h1)
  · push Not at h1
    obtain ⟨q₁, hq₁K⟩ := h1
    by_cases h2 : ∀ q : Q, (q : G) * g₂ ∉ K
    · exact le_trans (Nat.mul_le_mul_left 2 hcube)
        (two_mul_index_le_of_forall_mul_not_mem hg₂ h2)
    · push Not at h2
      obtain ⟨q₂, hq₂K⟩ := h2
      by_cases hW_idx : 2 * p ^ 3 ≤ W.index
      · exact le_trans hW_idx (subgroupOf_index_le_index K)
      · push Not at hW_idx
        exfalso
        have hW_mul : W.index * Nat.card W = p ^ 5 := by
          rw [W.index_mul_card, hcard]
        have hW_ne1 : Nat.card W ≠ 1 := by
          intro h1
          rw [h1, mul_one] at hW_mul
          have h2p : 2 * p ^ 3 < p ^ 5 := by
            calc
              2 * p ^ 3 < p ^ 2 * p ^ 3 := by
                refine Nat.mul_lt_mul_of_pos_right ?_ (pow_pos hp_pos 3)
                nlinarith
              _ = p ^ 5 := by ring
          omega
        have hW_ne_bot : W ≠ ⊥ := fun hbot => hW_ne1 (by rw [hbot, Subgroup.card_bot])
        obtain ⟨u₀, hu₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hW_ne_bot
        set w₀ : Q := u₀.1
        have hw₀W : w₀ ∈ W := u₀.2
        have hw₀1 : w₀ ≠ 1 := fun h => hu₀1 (Subtype.ext h)
        have hWZ_bot : W ⊓ center Q = ⊥ := by
          let Z' : Subgroup (center Q) := W.subgroupOf (center Q)
          have hdvd : Nat.card Z' ∣ p := by
            rw [← hcenter]
            exact Subgroup.card_subgroup_dvd_card Z'
          rcases hp.out.eq_one_or_self_of_dvd _ hdvd with h1 | hp'
          · rw [eq_bot_iff]
            intro x hx
            have hxZ' : (⟨x, hx.2⟩ : center Q) ∈ Z' := hx.1
            have hbot : Z' = ⊥ := Subgroup.card_eq_one.mp h1
            rw [hbot, Subgroup.mem_bot] at hxZ'
            exact congrArg Subtype.val hxZ'
          · exfalso
            apply hZK
            have htop : Z' = ⊤ := Subgroup.eq_top_of_card_eq Z' (hp'.trans hcenter.symm)
            intro z hz
            have hz' : (⟨z, hz⟩ : center Q) ∈ Z' := htop ▸ mem_top _
            exact hz'
        have hw₀_psi : ψ w₀ ≠ 0 := by
          intro h0
          have hw₀Z : w₀ ∈ W ⊓ center Q := ⟨hw₀W, (hψ_ker w₀).mp h0⟩
          rw [hWZ_bot, Subgroup.mem_bot] at hw₀Z
          exact hw₀1 hw₀Z
        set U := imageAddSubgroup ψ hψ_one hψ_mul W
        have hU₁ : ∀ u ∈ U, A₁ *ᵥ u ∈ U := by
          rintro _ ⟨w, hwW, rfl⟩
          set u₁ : Q := ⟨g₁ * (w : G) * g₁⁻¹, hg₁ w.1 w.2⟩
          refine ⟨q₁ * u₁ * q₁⁻¹, ?_, ?_⟩
          · rw [mem_subgroupOf]
            have heq : ((q₁ * u₁ * q₁⁻¹ : Q) : G) =
                ((q₁ : G) * g₁) * (w : G) * ((q₁ : G) * g₁)⁻¹ := by
              simp only [u₁, Subgroup.coe_mul, Subgroup.coe_inv]
              group
            rw [heq]
            exact K.mul_mem (K.mul_mem hq₁K hwW) (K.inv_mem hq₁K)
          · rw [psi_conj_eq ψ hψ_mul q₁ u₁, hA₁ w]
        have hU₂ : ∀ u ∈ U, A₂ *ᵥ u ∈ U := by
          rintro _ ⟨w, hwW, rfl⟩
          set u₂ : Q := ⟨g₂ * (w : G) * g₂⁻¹, hg₂ w.1 w.2⟩
          refine ⟨q₂ * u₂ * q₂⁻¹, ?_, ?_⟩
          · rw [mem_subgroupOf]
            have heq : ((q₂ * u₂ * q₂⁻¹ : Q) : G) =
                ((q₂ : G) * g₂) * (w : G) * ((q₂ : G) * g₂)⁻¹ := by
              simp only [u₂, Subgroup.coe_mul, Subgroup.coe_inv]
              group
            rw [heq]
            exact K.mul_mem (K.mul_mem hq₂K hwW) (K.inv_mem hq₂K)
          · rw [psi_conj_eq ψ hψ_mul q₂ u₂, hA₂ w]
        have hsurj : Function.Surjective (fun w : W => ψ w.1) := by
          intro y
          have hyU : y ∈ U :=
            mem_of_irreduciblePair hirr hU₁ hU₂ ⟨w₀, hw₀W, rfl⟩ hw₀_psi y
          obtain ⟨w, hwW, rfl⟩ := hyU
          exact ⟨⟨w, hwW⟩, rfl⟩
        have hcard_le : p ^ 4 ≤ Nat.card W := by
          have hle := Nat.card_le_card_of_surjective (fun w : W => ψ w.1) hsurj
          simpa only [Nat.card_eq_fintype_card (α := Fin 4 → ZMod p), Fintype.card_fun,
            ZMod.card, Fintype.card_fin] using hle
        have hmul_ge : p ^ 7 ≤ W.index * Nat.card W := by
          calc
            p ^ 7 = p ^ 3 * p ^ 4 := by ring
            _ ≤ W.index * Nat.card W := Nat.mul_le_mul hcube hcard_le
        have hlt_pow : p ^ 5 < p ^ 7 :=
          Nat.pow_lt_pow_right (by omega : 1 < p) (by norm_num)
        omega

include hp in
/-- Simple group index bound: if `S ≃* G` is simple and `Q ≤ G` satisfies the hypotheses of
`two_mul_cube_le_index_of_not_le`, then every proper subgroup `H ≠ ⊤` of `S` has index
`2 * p ^ 3 ≤ H.index`. -/
theorem two_mul_cube_le_index_of_ne_top (hp3 : 3 ≤ p)
    (hcard : Nat.card Q = p ^ 5) (hcenter : Nat.card (center Q) = p)
    (hcomm : commutator Q ≤ center Q) (hexp : ∀ q : Q, q ^ p = 1)
    (ψ : Q → (Fin 4 → ZMod p)) (hψ_one : ψ 1 = 0)
    (hψ_mul : ∀ a b : Q, ψ (a * b) = ψ a + ψ b)
    (hψ_ker : ∀ q : Q, ψ q = 0 ↔ q ∈ center Q)
    {g₁ g₂ : G} (hg₁ : ∀ q ∈ Q, g₁ * q * g₁⁻¹ ∈ Q) (hg₂ : ∀ q ∈ Q, g₂ * q * g₂⁻¹ ∈ Q)
    {A₁ A₂ : Matrix (Fin 4) (Fin 4) (ZMod p)}
    (hA₁ : ∀ q : Q, ψ ⟨g₁ * (q : G) * g₁⁻¹, hg₁ q.1 q.2⟩ = A₁ *ᵥ ψ q)
    (hA₂ : ∀ q : Q, ψ ⟨g₂ * (q : G) * g₂⁻¹, hg₂ q.1 q.2⟩ = A₂ *ᵥ ψ q)
    (hirr : IrreduciblePair A₁ A₂)
    {S : Type*} [Group S] [Finite S] [IsSimpleGroup S] (e : S ≃* G)
    {H : Subgroup S} (hH : H ≠ ⊤) :
    2 * p ^ 3 ≤ H.index := by
  have hZne : (center Q).map Q.subtype ≠ ⊥ := by
    intro hbot
    have hc : Nat.card ((center Q).map Q.subtype) = p := by
      rw [Subgroup.card_map_of_injective Q.subtype_injective, hcenter]
    rw [hbot, Subgroup.card_bot] at hc
    exact hp.out.ne_one hc.symm
  exact le_index_of_injective_of_forall_not_le_index hH e.symm.toMonoidHom e.symm.injective hZne
    fun K hZK =>
      two_mul_cube_le_index_of_not_le hp3 hcard hcenter hcomm hexp ψ hψ_one hψ_mul hψ_ker
        hg₁ hg₂ hA₁ hA₂ hirr fun hle =>
          hZK (by rintro _ ⟨z, hz, rfl⟩; exact hle hz)

end GroupBound

end Maroti.ExtraspecialCoord
