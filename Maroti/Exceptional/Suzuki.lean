module

public import Maroti.Exceptional.AutBound
public import Maroti.Exceptional.TorusHeis
import Mathlib.Data.Finite.Perm
import CFSG.LieType.Ree.SuzukiSimple
import CFSG.LieType.Ree.SuzukiOrder
import CFSG.LieType.Ree.SuzukiFrobeniusExponents
import CFSG.LieType.Ree.SuzukiSplitTorusCentralizers

/-!
# The Suzuki Groups `²B₂(q)`

This file proves the subgroup index lower bounds and Maróti's bound for primitive almost simple
groups with socle `²B₂(q)` (`q = 2^(2a+1)`, `a ≥ 1`, Maróti, Section 2, Step 2, pages 634–635):
- For every `a ≥ 1`, using the center `suzukiZ0 a K` of the Sylow 2-subgroup `suzukiU a K` and the
  normalizing torus `suzukiT a K` (`CFSG/LieType/Ree/SuzukiBorelStructure`), every proper subgroup
  `H` of `²B₂(q)` has index at least `q`.
- For `a = 1` (`²B₂(8)`, order `29120`), we further rule out proper subgroups of index `< 16`
  using the doubly transitive action on the Suzuki ovoid `suzukiOmegaSub` of degree `65`, showing
  that every proper subgroup of `²B₂(8)` has index at least `16`.
-/

@[expose] public section

namespace Maroti

open CFSG.Open CFSG.Blueprint CFSG.LieType.Ree

/-! ### General torus-root index bound `q ≤ H.index` for `²B₂(q)` -/

private noncomputable def suzukiZHom (a : ℕ) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) : Multiplicative K →* suzukiGroup a K where
  toFun v := suzukiSElt a K 0 (Multiplicative.toAdd v)
  map_one' := suzukiSElt_zero_zero hK
  map_mul' v w := by
    have hθ0 : 2 ^ (a + 1) ≠ 0 := pow_ne_zero _ two_ne_zero
    rw [toAdd_mul, suzukiSElt_mul hK]
    simp [zero_pow hθ0]

@[simp]
private theorem suzukiZHom_apply {a : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (v : Multiplicative K) :
    suzukiZHom a hK v = suzukiSElt a K 0 (Multiplicative.toAdd v) := rfl

private noncomputable def suzukiTHom (a : ℕ) (K : Type) [Field K] :
    Kˣ →* suzukiGroup a K where
  toFun := suzukiDElt a K
  map_one' := suzukiDElt_one
  map_mul' l m := (suzukiDElt_mul l m).symm

@[simp]
private theorem suzukiTHom_apply (a : ℕ) (K : Type) [Field K] (s : Kˣ) :
    suzukiTHom a K s = suzukiDElt a K s := rfl

private def suzukiChi (a : ℕ) (K : Type) [Field K] : Kˣ →* Kˣ where
  toFun l := (l⁻¹) ^ (2 ^ (a + 1) + 1)
  map_one' := by simp
  map_mul' l m := by rw [mul_inv_rev, mul_pow, mul_comm]

@[simp]
private theorem suzukiChi_apply (a : ℕ) (K : Type) [Field K] (s : Kˣ) :
    suzukiChi a K s = (s⁻¹) ^ (2 ^ (a + 1) + 1) := rfl

private theorem index_ge_card_of_suzukiGroup {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (M : Subgroup (suzukiGroup a K)) (hM : M ≠ ⊤) :
    Nat.card K ≤ M.index := by
  classical
  have : Finite (suzukiGroup a K) := (suzuki_simple ha hK).1
  have : IsSimpleGroup (suzukiGroup a K) := (suzuki_simple ha hK).2.2
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hbij, -, -⟩ := suzuki_frobenius_exponents a K hK
  have hz_inj : ∀ c : K, suzukiZHom a hK (Multiplicative.ofAdd c) = 1 → c = 0 := by
    intro c h
    rw [suzukiZHom_apply, toAdd_ofAdd, ← suzukiSElt_zero_zero hK] at h
    exact (suzukiSElt_inj.1 h).2
  have htz : ∀ (s : Kˣ) (c : K),
      suzukiTHom a K s * suzukiZHom a hK (Multiplicative.ofAdd c) * (suzukiTHom a K s)⁻¹ =
        suzukiZHom a hK (Multiplicative.ofAdd ((suzukiChi a K s : K) * c)) := by
    intro s c
    simp only [suzukiTHom_apply, suzukiZHom_apply, suzukiChi_apply, toAdd_ofAdd]
    rw [suzukiDElt_conj' hK, mul_zero, Units.val_pow_eq_pow_val]
  have hχ : Nat.card (suzukiChi a K).range = Nat.card K - 1 := by
    have hinj : Function.Injective (suzukiChi a K) := by
      intro l m h
      have h' : (l⁻¹ : Kˣ) ^ ((2 : ℤ) ^ (a + 1) + 1) = (m⁻¹ : Kˣ) ^ ((2 : ℤ) ^ (a + 1) + 1) := by
        rw [show ((2 : ℤ) ^ (a + 1) + 1) = ((2 ^ (a + 1) + 1 : ℕ) : ℤ) by push_cast; rfl,
          zpow_natCast, zpow_natCast]
        exact h
      exact inv_injective (hbij.1 h')
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_units]
  have hle := card_range_add_one_le_index_of_torus_root
    (suzukiZHom a hK) hz_inj (suzukiTHom a K) (suzukiChi a K) htz M hM
  have hpos : 1 ≤ Nat.card K := by
    rw [hK]
    exact Nat.one_le_two_pow
  omega

/-! ### Small case `²B₂(8)` (`a = 1`): ruling out index `< 16` -/

private theorem card_subtype_ne {α : Type*} [Finite α] [DecidableEq α] (a : α) :
    Nat.card {x : α // x ≠ a} + 1 = Nat.card α := by
  have e : {x : α // x ≠ a} ⊕ {x : α // ¬ x ≠ a} ≃ α := Equiv.sumCompl (· ≠ a)
  have : Unique {x : α // ¬ x ≠ a} :=
    { default := ⟨a, not_not.mpr rfl⟩
      uniq := fun ⟨x, hx⟩ => Subtype.ext (not_not.mp hx) }
  have h1 : Nat.card {x : α // ¬ x ≠ a} = 1 := Nat.card_unique
  rw [← Nat.card_congr e, Nat.card_sum, h1]

private theorem card_sigma_const {ι : Type*} [Finite ι] {β : ι → Type*} [∀ x, Finite (β x)]
    {c : ℕ} (hc : ∀ x, Nat.card (β x) = c) :
    Nat.card (Σ x, β x) = Nat.card ι * c := by
  have h : ∀ x, Nonempty (β x ≃ Fin c) := fun x => by
    have := Fintype.ofFinite (β x)
    exact ⟨Fintype.equivFinOfCardEq (by rw [← Nat.card_eq_fintype_card, hc x])⟩
  have e : (Σ x, β x) ≃ ι × Fin c :=
    (Equiv.sigmaCongrRight fun x => Classical.choice (h x)).trans (Equiv.sigmaEquivProd ι (Fin c))
  rw [Nat.card_congr e, Nat.card_prod, Nat.card_fin]

private theorem pow_factorization_mul_of_not_dvd {p k m : ℕ} (hp : p.Prime) (hm0 : m ≠ 0)
    (hndvd : ¬ p ∣ m) : p ^ (p ^ k * m).factorization p = p ^ k := by
  have hpk0 : p ^ k ≠ 0 := pow_ne_zero k hp.ne_zero
  rw [Nat.factorization_mul hpk0 hm0, Finsupp.add_apply, hp.factorization_pow,
    Finsupp.single_eq_same, Nat.factorization_eq_zero_of_not_dvd hndvd, add_zero]

private theorem card_subgroupOf_dvd_card {G : Type*} [Group G] [Finite G]
    (H K : Subgroup G) : Nat.card ↥(K.subgroupOf H) ∣ Nat.card K := by
  let φ : ↥(K.subgroupOf H) →* K :=
    { toFun := fun x => ⟨x.1.1, x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hφ : Function.Injective φ := fun x y h =>
    Subtype.ext (Subtype.ext (congrArg (Subtype.val : K → G) h))
  exact Subgroup.card_dvd_of_injective φ hφ

private theorem card_suzukiOmegaSub {a : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Nat.card (suzukiOmegaSub hK) = (2 ^ (2 * a + 1)) ^ 2 + 1 := by
  change Nat.card (suzukiOmega a K) = (2 ^ (2 * a + 1)) ^ 2 + 1
  rw [Nat.card_coe_set_eq, (suzuki_ovoid_unipotent_action hK).2.2.2.2.2.2]

private theorem card_stabilizer_suzukiOmegaSub {a : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (x : suzukiOmegaSub hK) :
    Nat.card (MulAction.stabilizer (suzukiGroup a K) x) =
      (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) := by
  obtain ⟨g, hg⟩ := exists_smul_eq_suzukiInfty hK x.2
  let x₀ : suzukiOmegaSub hK := ⟨suzukiInfty K, suzukiInfty_mem_suzukiOmega a K⟩
  have hgx : g • x = x₀ := Subtype.ext hg
  have hconj : MulAction.stabilizer (suzukiGroup a K) x₀ =
      (MulAction.stabilizer (suzukiGroup a K) x).map (MulAut.conj g).toMonoidHom := by
    rw [← hgx]
    ext h
    simp only [MulAction.mem_stabilizer_iff, Subgroup.mem_map, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    constructor
    · intro hh
      refine ⟨g⁻¹ * h * g, ?_, by group⟩
      rw [mul_smul, mul_smul, hh, inv_smul_smul]
    · rintro ⟨k, hk, rfl⟩
      rw [mul_smul, mul_smul, inv_smul_smul, hk]
  have hinj : Function.Injective (MulAut.conj g).toMonoidHom := (MulAut.conj g).injective
  rw [← Subgroup.card_map_of_injective hinj, ← hconj,
    (suzuki_ovoid_stabilizer hK).2, (suzuki_borel_structure hK).2.2.2.2.2.2.2]

private theorem card_inf_stabilizer_suzukiOmegaSub_dvd {a : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {x y : suzukiOmegaSub hK} (hxy : x ≠ y) :
    Nat.card ↥(MulAction.stabilizer (suzukiGroup a K) x ⊓
      MulAction.stabilizer (suzukiGroup a K) y) ∣ 2 ^ (2 * a + 1) - 1 := by
  have hxy' : x.1 ≠ y.1 := fun h => hxy (Subtype.ext h)
  obtain ⟨g, hgx, hgy⟩ := exists_smul_eq_pair hK x.2 y.2 hxy'
  have hle : (MulAction.stabilizer (suzukiGroup a K) x ⊓
      MulAction.stabilizer (suzukiGroup a K) y).map (MulAut.conj g).toMonoidHom ≤ suzukiT a K := by
    rintro _ ⟨h, ⟨hx, hy⟩, rfl⟩
    have hx' : h • x.1 = x.1 := congrArg Subtype.val (MulAction.mem_stabilizer_iff.1 hx)
    have hy' : h • y.1 = y.1 := congrArg Subtype.val (MulAction.mem_stabilizer_iff.1 hy)
    refine mem_suzukiT_of_smul_eq hK ?_ ?_
    · change (g * h * g⁻¹) • suzukiInfty K = suzukiInfty K
      rw [← hgx, mul_smul, mul_smul, inv_smul_smul, hx']
    · change (g * h * g⁻¹) • suzukiLine a K 0 0 = suzukiLine a K 0 0
      rw [← hgy, mul_smul, mul_smul, inv_smul_smul, hy']
  have hinj : Function.Injective (MulAut.conj g).toMonoidHom := (MulAut.conj g).injective
  rw [← (suzuki_borel_structure hK).2.2.1, ← Subgroup.card_map_of_injective hinj]
  exact Subgroup.card_dvd_of_le hle

private theorem card_ne_2240_of_suzukiGroup_one {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (2 * 1 + 1)) (M : Subgroup (suzukiGroup 1 K)) :
    Nat.card M ≠ 2240 := by
  intro hMcard
  have : Finite (suzukiGroup 1 K) := (suzuki_simple (by decide) hK).1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hGcard : Nat.card (suzukiGroup 1 K) = 29120 := by
    rw [suzuki_order hK]
    decide
  obtain ⟨P⟩ : Nonempty (Sylow 2 M) := inferInstance
  have hPcard : Nat.card P = 64 := by
    rw [Sylow.card_eq_multiplicity, hMcard, show (2240 : ℕ) = 2 ^ 6 * 35 by decide,
      pow_factorization_mul_of_not_dvd Nat.prime_two (by decide) (by decide)]
    decide
  let P₁ : Subgroup (suzukiGroup 1 K) := (P : Subgroup M).map M.subtype
  have hP₁le : P₁ ≤ M := Subgroup.map_subtype_le (P : Subgroup M)
  have hP₁card : Nat.card P₁ = 64 := by
    rw [Subgroup.card_map_of_injective M.subtype_injective]
    exact hPcard
  have hfact2 : 2 ^ (Nat.card (suzukiGroup 1 K)).factorization 2 = 64 := by
    rw [hGcard, show (29120 : ℕ) = 2 ^ 6 * 455 by decide,
      pow_factorization_mul_of_not_dvd Nat.prime_two (by decide) (by decide)]
    decide
  have hUcard : Nat.card (suzukiU 1 K) = 64 := by
    rw [(suzuki_unipotent_structure hK).2.1]
    decide
  let S₁ : Sylow 2 (suzukiGroup 1 K) := Sylow.ofCard P₁ (hP₁card.trans hfact2.symm)
  let S₂ : Sylow 2 (suzukiGroup 1 K) := Sylow.ofCard (suzukiU 1 K) (hUcard.trans hfact2.symm)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (suzukiGroup 1 K) S₂ S₁
  let x₀ : suzukiOmegaSub hK := ⟨suzukiInfty K, suzukiInfty_mem_suzukiOmega 1 K⟩
  let x₁ : suzukiOmegaSub hK := g • x₀
  have hP₁stab : P₁ ≤ MulAction.stabilizer (suzukiGroup 1 K) x₁ := by
    intro p hp
    have hp' : p ∈ (S₁ : Subgroup (suzukiGroup 1 K)) := hp
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      MulAut.smul_def, MulAut.conj_inv_apply] at hp'
    have hfix0 : (g⁻¹ * p * g) • x₀ = x₀ :=
      MulAction.mem_stabilizer_iff.1
        ((suzuki_ovoid_stabilizer hK).2.symm ▸ suzukiU_le_suzukiB 1 K hp')
    rw [MulAction.mem_stabilizer_iff]
    change p • (g • x₀) = g • x₀
    have := congrArg (g • ·) hfix0
    simpa [mul_smul] using this
  have hnotle : ¬ (M ≤ MulAction.stabilizer (suzukiGroup 1 K) x₁) := by
    intro hle
    have h1 := Subgroup.card_le_of_le hle
    have h2 : Nat.card (MulAction.stabilizer (suzukiGroup 1 K) x₁) = 448 := by
      rw [card_stabilizer_suzukiOmegaSub hK x₁]
      decide
    omega
  obtain ⟨h, hhM, hhstab⟩ : ∃ h ∈ M, h ∉ MulAction.stabilizer (suzukiGroup 1 K) x₁ := by
    by_contra hall
    push Not at hall
    exact hnotle hall
  have hx₂ : h • x₁ ≠ x₁ := hhstab
  let P₂ : Subgroup (suzukiGroup 1 K) := P₁.map (MulAut.conj h).toMonoidHom
  have hP₂le : P₂ ≤ M := by
    rintro _ ⟨p, hp, rfl⟩
    exact M.mul_mem (M.mul_mem hhM (hP₁le hp)) (M.inv_mem hhM)
  have hP₂card : Nat.card P₂ = 64 := by
    have hinj : Function.Injective (MulAut.conj h).toMonoidHom := (MulAut.conj h).injective
    rw [Subgroup.card_map_of_injective hinj, hP₁card]
  have hP₂stab : P₂ ≤ MulAction.stabilizer (suzukiGroup 1 K) (h • x₁) := by
    rintro _ ⟨p, hp, rfl⟩
    rw [MulAction.mem_stabilizer_iff]
    change (h * p * h⁻¹) • (h • x₁) = h • x₁
    rw [mul_smul, mul_smul, inv_smul_smul, MulAction.mem_stabilizer_iff.1 (hP₁stab hp)]
  have hinf : P₁ ⊓ P₂ = ⊥ := by
    have hdvd1 : Nat.card ↥(P₁ ⊓ P₂) ∣ 64 := by
      rw [← hP₁card]
      exact Subgroup.card_dvd_of_le inf_le_left
    have hdvd2 : Nat.card ↥(P₁ ⊓ P₂) ∣ 7 := by
      have hdvd2' := card_inf_stabilizer_suzukiOmegaSub_dvd hK hx₂.symm
      change _ ∣ 7 at hdvd2'
      exact (Subgroup.card_dvd_of_le (inf_le_inf hP₁stab hP₂stab)).trans hdvd2'
    have hdvd : Nat.card ↥(P₁ ⊓ P₂) ∣ Nat.gcd 64 7 := Nat.dvd_gcd hdvd1 hdvd2
    exact Subgroup.eq_bot_of_card_eq _ (Nat.eq_one_of_dvd_one hdvd)
  have hinj : Function.Injective (fun p : P₁ × P₂ =>
      (⟨p.1.1 * p.2.1, M.mul_mem (hP₁le p.1.2) (hP₂le p.2.2)⟩ : M)) := by
    rintro ⟨⟨a₁, ha₁⟩, ⟨b₁, hb₁⟩⟩ ⟨⟨a₂, ha₂⟩, ⟨b₂, hb₂⟩⟩ heq
    have hmul : a₁ * b₁ = a₂ * b₂ := congrArg Subtype.val heq
    have hmem : a₂⁻¹ * a₁ ∈ P₁ ⊓ P₂ := by
      refine ⟨P₁.mul_mem (P₁.inv_mem ha₂) ha₁, ?_⟩
      have : a₂⁻¹ * a₁ = b₂ * b₁⁻¹ := by
        calc a₂⁻¹ * a₁ = a₂⁻¹ * (a₁ * b₁) * b₁⁻¹ := by group
          _ = a₂⁻¹ * (a₂ * b₂) * b₁⁻¹ := by rw [hmul]
          _ = b₂ * b₁⁻¹ := by group
      rw [this]
      exact P₂.mul_mem hb₂ (P₂.inv_mem hb₁)
    rw [hinf, Subgroup.mem_bot, inv_mul_eq_one] at hmem
    subst hmem
    have hb : b₁ = b₂ := mul_left_cancel hmul
    subst hb
    rfl
  have hcard_le := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_prod, hP₁card, hP₂card, hMcard] at hcard_le
  omega

private theorem card_ne_2080_of_suzukiGroup_one {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (2 * 1 + 1)) (M : Subgroup (suzukiGroup 1 K)) :
    Nat.card M ≠ 2080 := by
  classical
  intro hMcard
  have : Finite (suzukiGroup 1 K) := (suzuki_simple (by decide) hK).1
  have : Fact (Nat.Prime 13) := ⟨by decide⟩
  let Ω := suzukiOmegaSub hK
  have hΩcard : Nat.card Ω = 65 := by
    rw [card_suzukiOmegaSub hK]
    decide
  have : Finite Ω := Nat.finite_of_card_ne_zero (by omega)
  let S : Ω → Subgroup M := fun x => MulAction.stabilizer M x
  have hS_eq : ∀ x : Ω, S x = (MulAction.stabilizer (suzukiGroup 1 K) x).subgroupOf M :=
    fun _ => rfl
  have hScard : ∀ x : Ω, Nat.card (S x) = 32 := by
    intro x
    have hdvdM : Nat.card (S x) ∣ 2080 := by
      rw [← hMcard]
      exact Subgroup.card_subgroup_dvd_card (S x)
    have hdvdB : Nat.card (S x) ∣ 448 := by
      have hB : Nat.card (MulAction.stabilizer (suzukiGroup 1 K) x) = 448 := by
        rw [card_stabilizer_suzukiOmegaSub hK x]
        decide
      rw [← hB, hS_eq]
      exact card_subgroupOf_dvd_card M _
    have hdvd32 : Nat.card (S x) ∣ Nat.gcd 2080 448 := Nat.dvd_gcd hdvdM hdvdB
    change Nat.card (S x) ∣ 32 at hdvd32
    have hle32 : Nat.card (S x) ≤ 32 := Nat.le_of_dvd (by decide) hdvd32
    have : Fintype M := Fintype.ofFinite M
    have : Fintype (MulAction.orbit M x) := Fintype.ofFinite _
    have : Fintype (S x) := Fintype.ofFinite _
    have horb := MulAction.card_orbit_mul_card_stabilizer_eq_card_group M x
    change Fintype.card (MulAction.orbit M x) * Fintype.card (S x) = Fintype.card M at horb
    simp only [← Nat.card_eq_fintype_card] at horb
    have horb_le : Nat.card (MulAction.orbit M x) ≤ 65 := by
      rw [← hΩcard]
      exact Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
    have hprod : Nat.card (MulAction.orbit M x) * Nat.card (S x) ≤ 65 * Nat.card (S x) :=
      Nat.mul_le_mul_right _ horb_le
    rw [horb, hMcard] at hprod
    omega
  have hSord : ∀ (x : Ω) (g : S x), orderOf g.1 ∣ 32 := by
    intro x g
    have h1 : orderOf g.1 = orderOf g := Subgroup.orderOf_coe g
    rw [h1, ← hScard x]
    exact orderOf_dvd_natCard g
  have hSinf : ∀ {x y : Ω}, x ≠ y → S x ⊓ S y = ⊥ := by
    intro x y hxy
    have hdvd1 : Nat.card ↥(S x ⊓ S y) ∣ 32 := by
      rw [← hScard x]
      exact Subgroup.card_dvd_of_le inf_le_left
    have hdvd2 : Nat.card ↥(S x ⊓ S y) ∣ 7 := by
      have hle : (S x ⊓ S y).map M.subtype ≤
          MulAction.stabilizer (suzukiGroup 1 K) x ⊓
            MulAction.stabilizer (suzukiGroup 1 K) y := by
        rintro _ ⟨m, ⟨hx, hy⟩, rfl⟩
        exact ⟨hx, hy⟩
      rw [← Subgroup.card_map_of_injective M.subtype_injective]
      have hdvd2' := card_inf_stabilizer_suzukiOmegaSub_dvd hK hxy
      change _ ∣ 7 at hdvd2'
      exact (Subgroup.card_dvd_of_le hle).trans hdvd2'
    have hdvd : Nat.card ↥(S x ⊓ S y) ∣ Nat.gcd 32 7 := Nat.dvd_gcd hdvd1 hdvd2
    exact Subgroup.eq_bot_of_card_eq _ (Nat.eq_one_of_dvd_one hdvd)
  have hPcard : ∀ P : Sylow 13 M, Nat.card ↥(P : Subgroup M) = 13 := by
    intro P
    rw [Sylow.card_eq_multiplicity, hMcard, show (2080 : ℕ) = 13 ^ 1 * 160 by decide,
      pow_factorization_mul_of_not_dvd (by decide) (by decide) (by decide), pow_one]
  have hPord : ∀ (P : Sylow 13 M) (g : P), orderOf g.1 ∣ 13 := by
    intro P g
    have h1 : orderOf g.1 = orderOf g := Subgroup.orderOf_coe g
    rw [h1]
    exact (orderOf_dvd_natCard g).trans (dvd_of_eq (hPcard P))
  let Φ : (Σ x : Ω, {g : S x // g ≠ 1}) ⊕ (Σ P : Sylow 13 M, {g : P // g ≠ 1}) → M :=
    Sum.elim (fun p => p.2.1.1) (fun p => p.2.1.1)
  have hΦinj : Function.Injective Φ := by
    rintro (⟨x, ⟨g₁, hg₁⟩⟩ | ⟨P₁, ⟨g₁, hg₁⟩⟩) (⟨y, ⟨g₂, hg₂⟩⟩ | ⟨P₂, ⟨g₂, hg₂⟩⟩) h <;>
      simp only [Φ, Sum.elim_inl, Sum.elim_inr] at h
    · by_cases hxy : x = y
      · subst hxy
        have hg : g₁ = g₂ := Subtype.ext h
        subst hg
        rfl
      · exfalso
        have hmem : g₁.1 ∈ S x ⊓ S y := ⟨g₁.2, h ▸ g₂.2⟩
        rw [hSinf hxy, Subgroup.mem_bot] at hmem
        exact hg₁ (Subtype.ext hmem)
    · exfalso
      have h1 : orderOf g₁.1 ∣ 32 := hSord x g₁
      have h2 : orderOf g₁.1 ∣ 13 := h ▸ hPord P₂ g₂
      have h3 : orderOf g₁.1 ∣ Nat.gcd 32 13 := Nat.dvd_gcd h1 h2
      have h4 : g₁.1 = 1 := orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_one h3)
      exact hg₁ (Subtype.ext h4)
    · exfalso
      have h1 : orderOf g₂.1 ∣ 32 := hSord y g₂
      have h2 : orderOf g₂.1 ∣ 13 := h ▸ hPord P₁ g₁
      have h3 : orderOf g₂.1 ∣ Nat.gcd 32 13 := Nat.dvd_gcd h1 h2
      have h4 : g₂.1 = 1 := orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_one h3)
      exact hg₂ (Subtype.ext h4)
    · have hPeq : P₁ = P₂ := by
        have hord : orderOf g₁.1 = 13 := by
          rcases (Nat.dvd_prime (by decide : Nat.Prime 13)).1 (hPord P₁ g₁) with h1 | h13
          · exact absurd (Subtype.ext (orderOf_eq_one_iff.1 h1)) hg₁
          · exact h13
        have hzcard : Nat.card (Subgroup.zpowers g₁.1) = 13 := by
          rw [Nat.card_zpowers, hord]
        have hz₁ : Subgroup.zpowers g₁.1 = (P₁ : Subgroup M) :=
          Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 g₁.2)
            (by rw [hzcard, hPcard P₁])
        have hz₂ : Subgroup.zpowers g₁.1 = (P₂ : Subgroup M) :=
          Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 (h ▸ g₂.2))
            (by rw [hzcard, hPcard P₂])
        exact Sylow.ext (hz₁.symm.trans hz₂)
      subst hPeq
      have hg : g₁ = g₂ := Subtype.ext h
      subst hg
      rfl
  have hSsub : ∀ x : Ω, Nat.card {g : S x // g ≠ 1} = 31 := by
    intro x
    have h1 := card_subtype_ne (1 : S x)
    have h2 := hScard x
    omega
  have hPsub : ∀ P : Sylow 13 M, Nat.card {g : P // g ≠ 1} = 12 := by
    intro P
    have h1 : Nat.card {g : P // g ≠ 1} + 1 = Nat.card ↥(P : Subgroup M) :=
      card_subtype_ne (1 : P)
    have h2 := hPcard P
    omega
  have hsum := Nat.card_le_card_of_injective Φ hΦinj
  rw [Nat.card_sum, card_sigma_const hSsub, card_sigma_const hPsub, hΩcard, hMcard] at hsum
  have hmod := card_sylow_modEq_one (p := 13) (G := M)
  have hpos : 0 < Nat.card (Sylow 13 M) := Nat.card_pos
  unfold Nat.ModEq at hmod
  have hcount : Nat.card (Sylow 13 M) = 1 := by omega
  have : Subsingleton (Sylow 13 M) := (Nat.card_eq_one_iff_unique.1 hcount).1
  obtain ⟨P⟩ : Nonempty (Sylow 13 M) := inferInstance
  have hPnorm : (P : Subgroup M).Normal := Sylow.normal_of_subsingleton P
  have hPcard' : Nat.card P = 13 := hPcard P
  have : Nontrivial P := Finite.one_lt_card_iff_nontrivial.1 (by rw [hPcard']; decide)
  obtain ⟨y, hy1⟩ := exists_ne (1 : P)
  let x₀ : Ω := ⟨suzukiInfty K, suzukiInfty_mem_suzukiOmega 1 K⟩
  let conjY : S x₀ → P := fun s => ⟨s.1 * y.1 * s.1⁻¹, hPnorm.conj_mem y.1 y.2 s.1⟩
  have hlt : Nat.card P < Nat.card (S x₀) := by
    rw [hPcard', hScard x₀]
    decide
  have hnotinj : ¬ Function.Injective conjY := fun hinj =>
    not_le_of_gt hlt (Nat.card_le_card_of_injective conjY hinj)
  unfold Function.Injective at hnotinj
  push Not at hnotinj
  obtain ⟨s₁, s₂, hseq, hsne⟩ := hnotinj
  let u : S x₀ := s₁⁻¹ * s₂
  have hu1 : u ≠ 1 := inv_mul_eq_one.not.mpr hsne
  have hcomm : u.1 * y.1 = y.1 * u.1 := by
    have h1 : s₁.1 * y.1 * s₁.1⁻¹ = s₂.1 * y.1 * s₂.1⁻¹ := congrArg Subtype.val hseq
    calc s₁.1⁻¹ * s₂.1 * y.1
        = s₁.1⁻¹ * (s₂.1 * y.1 * s₂.1⁻¹) * s₂.1 := by group
      _ = s₁.1⁻¹ * (s₁.1 * y.1 * s₁.1⁻¹) * s₂.1 := by rw [← h1]
      _ = y.1 * (s₁.1⁻¹ * s₂.1) := by group
  have hu_yx₀ : u.1 ∈ S (y.1 • x₀) := by
    rw [MulAction.mem_stabilizer_iff]
    change u.1 • (y.1 • x₀) = y.1 • x₀
    rw [← mul_smul, hcomm, mul_smul, MulAction.mem_stabilizer_iff.1 u.2]
  have hyx₀ : y.1 • x₀ = x₀ := by
    by_contra hne
    have hmem : u.1 ∈ S x₀ ⊓ S (y.1 • x₀) := ⟨u.2, hu_yx₀⟩
    rw [hSinf (Ne.symm hne), Subgroup.mem_bot] at hmem
    exact hu1 (Subtype.ext hmem)
  have hyS : y.1 ∈ S x₀ := hyx₀
  have hord1 : orderOf y.1 ∣ 32 := hSord x₀ ⟨y.1, hyS⟩
  have hord2 : orderOf y.1 ∣ 13 := hPord P y
  have hord3 : orderOf y.1 ∣ Nat.gcd 32 13 := Nat.dvd_gcd hord1 hord2
  exact hy1 (Subtype.ext (orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_one hord3)))

private theorem index_ge_16_of_suzukiGroup_one {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (2 * 1 + 1)) (M : Subgroup (suzukiGroup 1 K)) (hM : M ≠ ⊤) :
    16 ≤ M.index := by
  classical
  have : Finite (suzukiGroup 1 K) := (suzuki_simple (by decide) hK).1
  have : IsSimpleGroup (suzukiGroup 1 K) := (suzuki_simple (by decide) hK).2.2
  have hGcard : Nat.card (suzukiGroup 1 K) = 29120 := by
    rw [suzuki_order hK]
    decide
  let π := MulAction.toPermHom (suzukiGroup 1 K) (suzukiGroup 1 K ⧸ M)
  have hker_le : π.ker ≤ M := by
    intro g hg
    have h1 := congrArg (fun σ : Equiv.Perm (suzukiGroup 1 K ⧸ M) =>
      σ (QuotientGroup.mk (1 : suzukiGroup 1 K))) hg
    simp only [π, MulAction.toPermHom_apply, MulAction.toPerm_apply,
      Equiv.Perm.coe_one, id_eq] at h1
    simpa using QuotientGroup.leftRel_apply.mp (Quotient.exact h1)
  have hker : π.ker = ⊥ :=
    (π.normal_ker.eq_bot_or_eq_top).resolve_right (fun htop => hM (top_unique (htop ▸ hker_le)))
  have hinj : Function.Injective π := (MonoidHom.ker_eq_bot_iff π).1 hker
  have hcard_perm : Nat.card (Equiv.Perm (suzukiGroup 1 K ⧸ M)) = M.index.factorial := by
    rw [Nat.card_perm, ← Subgroup.index_eq_card]
  have hdvd_fact : 29120 ∣ M.index.factorial := by
    rw [← hGcard, ← hcard_perm]
    exact Subgroup.card_dvd_of_injective π hinj
  have h13 : 13 ≤ M.index :=
    (Nat.Prime.dvd_factorial (by decide : Nat.Prime 13)).1
      (dvd_trans (by decide : 13 ∣ 29120) hdvd_fact)
  have hprod := M.card_mul_index
  rw [hGcard] at hprod
  have hne2240 := card_ne_2240_of_suzukiGroup_one hK M
  have hne2080 := card_ne_2080_of_suzukiGroup_one hK M
  by_contra hlt
  have hlt16 : M.index < 16 := not_le.mp hlt
  interval_cases M.index <;> omega

/-! ### Main index and Maróti bounds for `SuzukiModel` -/

/-- Every proper subgroup `H` of a Suzuki model `S` (`²B₂(2^f)`) has index at least
`max 16 (2 ^ f)`. -/
theorem index_ge_of_suzukiModel {S : Type} [Group S] {p f : ℕ}
    (h : SuzukiModel S p f) (H : Subgroup S) (hH : H ≠ ⊤) :
    max 16 (2 ^ f) ≤ H.index := by
  obtain ⟨rfl, a, ha, K, _, _, rfl, hK, ⟨e⟩⟩ := h
  have hM : H.map (e : S →* suzukiGroup a K) ≠ ⊤ := by
    intro htop
    apply hH
    apply Subgroup.map_injective (f := (e : S →* suzukiGroup a K)) e.injective
    rw [htop, Subgroup.map_top_of_surjective _ e.surjective]
  rw [← Subgroup.index_map_equiv H e]
  rcases eq_or_ne a 1 with rfl | ha1
  · rw [show max 16 (2 ^ (2 * 1 + 1)) = 16 by decide]
    exact index_ge_16_of_suzukiGroup_one hK _ hM
  · have ha2 : 2 ≤ a := by omega
    have h16 : 16 ≤ 2 ^ (2 * a + 1) := by
      calc 16 = 2 ^ 4 := by decide
        _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by decide) (by omega)
    rw [max_eq_right h16, ← hK]
    exact index_ge_card_of_suzukiGroup ha hK _ hM

/-- For `²B₂(2^f)` (`f = 2a + 1`, `a ≥ 1`), `|S| · |Out(S)| ≤ bound (max 16 (2^f))`. -/
theorem card_mul_outerAut_le_bound_of_suzukiModel {S : Type} [Group S] {p f : ℕ}
    (h : SuzukiModel S p f) :
    Nat.card S * f ≤ bound (max 16 (2 ^ f)) := by
  obtain ⟨rfl, ⟨a, ha, rfl⟩, hcard⟩ := card_suzukiModel h
  rw [hcard]
  rcases eq_or_ne a 1 with rfl | ha1
  · decide
  · rcases eq_or_ne a 2 with rfl | ha2
    · decide
    · have ha3 : 3 ≤ a := by omega
      set q := 2 ^ (2 * a + 1)
      have h16 : 16 ≤ q := by
        calc 16 = 2 ^ 4 := by decide
          _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by decide) (by omega)
      rw [max_eq_right h16]
      have hfq : 2 * a + 1 ≤ q := (Nat.lt_pow_self (by decide : 1 < 2)).le
      have h64 : 2 ^ 6 ≤ q := Nat.pow_le_pow_right (by decide) (by omega)
      have hlog : 6 ≤ Nat.log 2 q := (Nat.le_log_iff_pow_le (by decide) (by omega)).2 h64
      calc ordSuzuki q * (2 * a + 1)
          ≤ q ^ 5 * q := Nat.mul_le_mul (ordSuzuki_le_pow q) hfq
        _ = q ^ 6 := by ring
        _ ≤ q ^ Nat.log 2 q := Nat.pow_le_pow_right (by omega) hlog
        _ ≤ bound q := pow_log_le_bound (by omega)

/-- Any primitive almost simple group `G ≤ Perm α` with socle `²B₂(2^f)` satisfies
`|G| ≤ bound |α|`. -/
theorem card_le_bound_of_suzukiModel {α : Type} [Finite α]
    {G : Subgroup (Equiv.Perm α)} [MulAction.IsPreprimitive G α]
    {S : Type} [Group S] {p f : ℕ} (hAS : IsAlmostSimpleWith G S)
    (h : SuzukiModel S p f) :
    Nat.card G ≤ bound (Nat.card α) :=
  hAS.card_le_bound_of_outerAut_le (index_ge_of_suzukiModel h)
    (card_outerAut_suzuki h).2 (card_mul_outerAut_le_bound_of_suzukiModel h)

end Maroti
