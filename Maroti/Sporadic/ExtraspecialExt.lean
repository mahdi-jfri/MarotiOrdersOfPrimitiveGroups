module

public import Maroti.MinDegree.Extraspecial

/-!
# Minimum index from normal extraspecial subgroups with simple quotient

Suppose `M ≤ G` has a normal extraspecial `p`-subgroup `Q ◁ M` of order `p ^ (1 + 2 * m)` such that
the quotient `M ⧸ Q` is simple and has a prime divisor `q`. For any proper subgroup `H` of a simple
group `S ≃* G`, choosing a conjugate `H'` of `H` avoiding `Z(Q)` and setting `K = H' ∩ M` and
`W = H' ∩ Q` gives `[M : K] = [M ⧸ Q : K Q ⧸ Q] * [Q : W]`.
* If `K` does not surject onto `M ⧸ Q`, then `[M ⧸ Q : K Q ⧸ Q] ≥ q` and `[Q : W] ≥ p ^ (m + 1)`,
  so `[S : H] ≥ q * p ^ (m + 1)`.
* If `K` surjects onto `M ⧸ Q`, then `W Z(Q) ⧸ Z(Q)` is invariant under the conjugation action of
  all of `M` on `Q ⧸ Z(Q)`. When `M` acts irreducibly on `Q ⧸ Z(Q)`, this forces `W = ⊥` (since `W`
  is abelian while `Q` is nonabelian), so `[S : H] ≥ p ^ (1 + 2 * m)`.
-/

@[expose] public section

namespace Maroti.ExtraspecialExt

open Subgroup
open scoped commutatorElement

variable {P : Type*} [Group P] [Finite P] {p : ℕ} [hp : Fact p.Prime]

section ExtraspecialDisjoint

variable (hP : CFSG.IsExtraspecialPGroup p P)
include hP

/-- If a subgroup `W` of an extraspecial `p`-group `P` does not contain `Subgroup.center P`, then
`W ⊓ Subgroup.center P = ⊥`. -/
theorem inf_center_eq_bot_of_not_le {W : Subgroup P} (hWZ : ¬ center P ≤ W) :
    W ⊓ center P = ⊥ := by
  let Z' : Subgroup (center P) := W.subgroupOf (center P)
  have hdvd : Nat.card Z' ∣ p := by
    rw [← hP.2.2.2]
    exact Subgroup.card_subgroup_dvd_card Z'
  rcases hp.out.eq_one_or_self_of_dvd _ hdvd with h1 | hp'
  · rw [eq_bot_iff]
    intro x hx
    have hxZ' : (⟨x, hx.2⟩ : center P) ∈ Z' := hx.1
    have hbot : Z' = ⊥ := Subgroup.card_eq_one.mp h1
    rw [hbot, Subgroup.mem_bot] at hxZ'
    exact congrArg Subtype.val hxZ'
  · exfalso
    apply hWZ
    have htop : Z' = ⊤ := Subgroup.eq_top_of_card_eq Z' (hp'.trans hP.2.2.2.symm)
    intro z hz
    have hz' : (⟨z, hz⟩ : center P) ∈ Z' := htop ▸ mem_top _
    exact hz'

/-- If `W ≤ P` does not contain `Subgroup.center P`, then `W` is abelian: any two elements of `W`
commute. -/
theorem mul_comm_of_mem_of_not_le {W : Subgroup P} (hWZ : ¬ center P ≤ W)
    {u v : P} (hu : u ∈ W) (hv : v ∈ W) :
    u * v = v * u := by
  have hcomm : ⁅u, v⁆ ∈ W ⊓ center P :=
    ⟨by
      rw [commutatorElement_def]
      exact W.mul_mem (W.mul_mem (W.mul_mem hu hv) (W.inv_mem hu)) (W.inv_mem hv),
      commutatorElement_mem_center_of_isExtraspecialPGroup hP u v⟩
  rw [inf_center_eq_bot_of_not_le hP hWZ, Subgroup.mem_bot] at hcomm
  exact commutatorElement_eq_one_iff_mul_comm.mp hcomm

/-- If `W ≤ P` does not contain `Subgroup.center P`, then every element of `W` has `p`-th power
equal to `1`. -/
theorem pow_prime_eq_one_of_mem_of_not_le {W : Subgroup P} (hWZ : ¬ center P ≤ W)
    {u : P} (hu : u ∈ W) :
    u ^ p = 1 := by
  have hpow : u ^ p ∈ W ⊓ center P :=
    ⟨W.pow_mem hu p, pow_prime_mem_center_of_isExtraspecialPGroup hP u⟩
  rw [inf_center_eq_bot_of_not_le hP hWZ, Subgroup.mem_bot] at hpow
  exact hpow

/-- If `W ≤ P` does not contain `Subgroup.center P`, then `W` cannot surject onto
`P ⧸ Subgroup.center P` (because `W` is abelian while `P` is nonabelian). -/
theorem not_forall_exists_inv_mul_mem_center_of_not_le {W : Subgroup P} (hWZ : ¬ center P ≤ W)
    (hsurj : ∀ q : P, ∃ w ∈ W, q⁻¹ * w ∈ center P) :
    False := by
  have hcomm_all : ∀ x y : P, ⁅x, y⁆ = 1 := by
    intro x y
    obtain ⟨u, huW, hxu⟩ := hsurj x
    obtain ⟨v, hvW, hyv⟩ := hsurj y
    set z₁ := x⁻¹ * u
    set z₂ := y⁻¹ * v
    have hx : x = u * z₁⁻¹ := by simp [z₁]
    have hy : y = v * z₂⁻¹ := by simp [z₂]
    have huv : u * v = v * u := mul_comm_of_mem_of_not_le hP hWZ huW hvW
    have hz₁ : ∀ g : P, z₁⁻¹ * g = g * z₁⁻¹ := fun g =>
      (Subgroup.mem_center_iff.mp (Subgroup.inv_mem _ hxu) g).symm
    have hz₂ : ∀ g : P, z₂⁻¹ * g = g * z₂⁻¹ := fun g =>
      (Subgroup.mem_center_iff.mp (Subgroup.inv_mem _ hyv) g).symm
    apply commutatorElement_eq_one_iff_mul_comm.mpr
    rw [hx, hy]
    calc
      u * z₁⁻¹ * (v * z₂⁻¹) = u * (z₁⁻¹ * v) * z₂⁻¹ := by group
      _ = u * (v * z₁⁻¹) * z₂⁻¹ := by rw [hz₁ v]
      _ = (u * v) * z₁⁻¹ * z₂⁻¹ := by group
      _ = (v * u) * (z₁⁻¹ * z₂⁻¹) := by rw [huv]; group
      _ = v * u * (z₂⁻¹ * z₁⁻¹) := by rw [hz₁ z₂⁻¹]
      _ = v * (u * z₂⁻¹) * z₁⁻¹ := by group
      _ = v * (z₂⁻¹ * u) * z₁⁻¹ := by rw [← hz₂ u]
      _ = v * z₂⁻¹ * (u * z₁⁻¹) := by group
  have hbot : commutator P = ⊥ := by
    rw [eq_bot_iff, _root_.commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [Subgroup.mem_bot]
    exact hcomm_all x y
  rw [hP.2.1] at hbot
  exact center_ne_bot_of_isExtraspecialPGroup hP hbot

end ExtraspecialDisjoint

section ZMod2Submodule

variable {Q : Type*} [Group Q] [Finite Q] (hQ : CFSG.IsExtraspecialPGroup 2 Q)
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
variable (ψ : Q → V) (hψ_one : ψ 1 = 0) (hψ_mul : ∀ a b : Q, ψ (a * b) = ψ a + ψ b)

/-- The `ZMod 2`-submodule of `V` spanned by the image of a subgroup `W ≤ Q` under an additive map
`ψ : Q → V`. -/
def submoduleOfSubgroup (W : Subgroup Q) : Submodule (ZMod 2) V where
  carrier := {v : V | ∃ w ∈ W, ψ w = v}
  zero_mem' := ⟨1, W.one_mem, hψ_one⟩
  add_mem' := by
    rintro _ _ ⟨w₁, hw₁, rfl⟩ ⟨w₂, hw₂, rfl⟩
    exact ⟨w₁ * w₂, W.mul_mem hw₁ hw₂, hψ_mul w₁ w₂⟩
  smul_mem' := by
    rintro c _ ⟨w, hw, rfl⟩
    rcases (show c = 0 ∨ c = 1 by revert c; decide) with rfl | rfl
    · exact ⟨1, W.one_mem, by rw [zero_smul, hψ_one]⟩
    · exact ⟨w, hw, by rw [one_smul]⟩

omit [Finite Q] in
theorem mem_submoduleOfSubgroup_iff {W : Subgroup Q} {v : V} :
    v ∈ submoduleOfSubgroup ψ hψ_one hψ_mul W ↔ ∃ w ∈ W, ψ w = v :=
  Iff.rfl

omit [Finite Q] [Module (ZMod 2) V] in
theorem psi_eq_of_inv_mul_mem_center (hψ_mul : ∀ a b : Q, ψ (a * b) = ψ a + ψ b)
    (hψ_ker : ∀ a : Q, ψ a = 0 ↔ a ∈ center Q)
    {a b : Q} (hab : a⁻¹ * b ∈ center Q) :
    ψ a = ψ b := by
  have h0 : ψ (a⁻¹ * b) = 0 := (hψ_ker (a⁻¹ * b)).mpr hab
  have hb : ψ b = ψ a + ψ (a⁻¹ * b) := by
    rw [← hψ_mul a (a⁻¹ * b), mul_inv_cancel_left]
  rw [hb, h0, add_zero]

include hQ in
omit [Module (ZMod 2) V] in
/-- If `W ≤ Q` does not contain `Subgroup.center Q`, then the image of `W` under `ψ` cannot cover
`ψ '' Set.univ`. Thus if every element of `ψ '' W` is `0` or `ψ '' W` covers `V`, then `W = ⊥`. -/
theorem eq_bot_of_forall_eq_zero_or_forall_exists
    (hψ_mul : ∀ a b : Q, ψ (a * b) = ψ a + ψ b)
    (hψ_ker : ∀ a : Q, ψ a = 0 ↔ a ∈ center Q)
    {W : Subgroup Q} (hWZ : ¬ center Q ≤ W)
    (hor : (∀ w ∈ W, ψ w = 0) ∨ (∀ v : V, ∃ w ∈ W, ψ w = v)) :
    W = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases hor with hbot | htop
  · rw [eq_bot_iff]
    intro w hw
    have hzc : w ∈ W ⊓ center Q := ⟨hw, (hψ_ker w).mp (hbot w hw)⟩
    rwa [inf_center_eq_bot_of_not_le hQ hWZ] at hzc
  · exfalso
    refine not_forall_exists_inv_mul_mem_center_of_not_le hQ hWZ fun q => ?_
    obtain ⟨w, hw, hqw⟩ := htop (ψ q)
    refine ⟨w, hw, (hψ_ker (q⁻¹ * w)).mp ?_⟩
    apply add_left_cancel (a := ψ q)
    rw [← hψ_mul q (q⁻¹ * w), mul_inv_cancel_left, hqw, add_zero]

include hQ in
/-- If `W ≤ Q` does not contain `Subgroup.center Q`, then `submoduleOfSubgroup ψ _ _ W` cannot be
`⊤`. Thus if it is either `⊥` or `⊤`, then `W = ⊥`. -/
theorem eq_bot_of_submoduleOfSubgroup_eq_bot_or_top
    (hψ_ker : ∀ a : Q, ψ a = 0 ↔ a ∈ center Q)
    {W : Subgroup Q} (hWZ : ¬ center Q ≤ W)
    (hor : submoduleOfSubgroup ψ hψ_one hψ_mul W = ⊥ ∨
      submoduleOfSubgroup ψ hψ_one hψ_mul W = ⊤) :
    W = ⊥ := by
  refine eq_bot_of_forall_eq_zero_or_forall_exists hQ ψ hψ_mul hψ_ker hWZ ?_
  rcases hor with hbot | htop
  · left
    intro w hw
    have hmem : ψ w ∈ submoduleOfSubgroup ψ hψ_one hψ_mul W := ⟨w, hw, rfl⟩
    rwa [hbot, Submodule.mem_bot] at hmem
  · right
    intro v
    have hmem : v ∈ submoduleOfSubgroup ψ hψ_one hψ_mul W := htop ▸ Submodule.mem_top
    exact hmem

end ZMod2Submodule

section Extension

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- Conjugating `q ∈ Q` by `m ∈ M` stays in `Q` when `Q ≤ M` and `(Q.subgroupOf M).Normal`. -/
theorem conj_mem_of_normal_subgroupOf {M Q : Subgroup G} (hQM : Q ≤ M)
    [hQn : (Q.subgroupOf M).Normal] {m : G} (hm : m ∈ M) {q : G} (hq : q ∈ Q) :
    m * q * m⁻¹ ∈ Q := by
  have hconj := hQn.conj_mem (⟨q, hQM hq⟩ : M) (Subgroup.mem_subgroupOf.mpr hq) (⟨m, hm⟩ : M)
  exact Subgroup.mem_subgroupOf.mp hconj

/-- Index factorization `[M : H' ∩ M] = [M ⧸ Q : π(H' ∩ M)] * [Q : H' ∩ Q]` for a normal subgroup
`Q ◁ M`. -/
theorem index_subgroupOf_eq_mul {M Q H' : Subgroup G} (hQM : Q ≤ M)
    [hQn : (Q.subgroupOf M).Normal] :
    (H'.subgroupOf M).index =
      ((H'.subgroupOf M).map (QuotientGroup.mk' (Q.subgroupOf M))).index *
        (H'.subgroupOf Q).index := by
  set Q_M : Subgroup M := Q.subgroupOf M
  set K : Subgroup M := H'.subgroupOf M
  set W : Subgroup Q := H'.subgroupOf Q
  set π : M →* M ⧸ Q_M := QuotientGroup.mk' Q_M
  set φ : K →* M ⧸ Q_M := π.comp K.subtype
  have hrange : φ.range = K.map π := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hker : φ.ker = Q_M.subgroupOf K := by
    ext x
    simp only [φ, MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype,
      π, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hker_equiv : ↥(Q_M.subgroupOf K) ≃ ↥W :=
    { toFun := fun x => ⟨⟨(x : G), x.2⟩, x.1.2⟩
      invFun := fun w => ⟨⟨⟨(w : G), hQM w.1.2⟩, w.2⟩, w.1.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hcard_ker : Nat.card φ.ker = Nat.card W := by
    rw [hker]
    exact Nat.card_congr hker_equiv
  have hcard_K : Nat.card W * Nat.card (K.map π) = Nat.card K := by
    rw [← hcard_ker, ← hrange]
    exact Subgroup.card_ker_mul_card_range φ
  have hcard_QM : Nat.card Q_M = Nat.card Q :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQM).toEquiv
  have hcard_M : Nat.card Q * Nat.card (M ⧸ Q_M) = Nat.card M := by
    rw [← hcard_QM, ← Subgroup.index_eq_card]
    exact Subgroup.card_mul_index Q_M
  have hW_mul : Nat.card W * W.index = Nat.card Q := Subgroup.card_mul_index W
  have hmap_mul : Nat.card (K.map π) * (K.map π).index = Nat.card (M ⧸ Q_M) :=
    Subgroup.card_mul_index (K.map π)
  have hK_mul : Nat.card K * K.index = Nat.card M := Subgroup.card_mul_index K
  have hprod : (Nat.card W * Nat.card (K.map π)) * K.index =
      (Nat.card W * Nat.card (K.map π)) * ((K.map π).index * W.index) := by
    calc
      (Nat.card W * Nat.card (K.map π)) * K.index = Nat.card K * K.index := by rw [hcard_K]
      _ = Nat.card M := hK_mul
      _ = Nat.card Q * Nat.card (M ⧸ Q_M) := hcard_M.symm
      _ = (Nat.card W * W.index) * (Nat.card (K.map π) * (K.map π).index) := by
        rw [hW_mul, hmap_mul]
      _ = (Nat.card W * Nat.card (K.map π)) * ((K.map π).index * W.index) := by ring
  have hpos : 0 < Nat.card W * Nat.card (K.map π) :=
    Nat.mul_pos Nat.card_pos Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_left hpos hprod

omit [Finite G] in
/-- If `K = H' ∩ M` surjects onto `M ⧸ Q`, then `W = H' ∩ Q` has `Q ⧸ Z(Q)`-image invariant under
conjugation by all of `M`: for every `m ∈ M` and `w ∈ W`, there exists `w' ∈ W` such that
`(m w m⁻¹)⁻¹ * w' ∈ Z(Q)`. -/
theorem exists_mem_center_of_map_eq_top {M Q H' : Subgroup G} (hQM : Q ≤ M)
    [hQn : (Q.subgroupOf M).Normal] {p : ℕ} (hQ : CFSG.IsExtraspecialPGroup p Q)
    (hsurj : (H'.subgroupOf M).map (QuotientGroup.mk' (Q.subgroupOf M)) = ⊤)
    {m : G} (hm : m ∈ M) {w : Q} (hw : w ∈ H'.subgroupOf Q) :
    ∃ w' ∈ H'.subgroupOf Q,
      (⟨m * (w : G) * m⁻¹, conj_mem_of_normal_subgroupOf hQM hm w.2⟩ : Q)⁻¹ * w' ∈ center Q := by
  set Q_M : Subgroup M := Q.subgroupOf M
  set K : Subgroup M := H'.subgroupOf M
  set π : M →* M ⧸ Q_M := QuotientGroup.mk' Q_M
  have hm_top : π ⟨m, hm⟩ ∈ K.map π := hsurj ▸ mem_top _
  obtain ⟨k, hkK, hkm⟩ := hm_top
  have hq_mem_QM : ⟨m, hm⟩ * k⁻¹ ∈ Q_M := by
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.coe_mk', map_mul, map_inv, hkm, mul_inv_cancel]
  have hq_mem_Q : m * (k : G)⁻¹ ∈ Q := Subgroup.mem_subgroupOf.mp hq_mem_QM
  set q₀ : Q := ⟨m * (k : G)⁻¹, hq_mem_Q⟩
  have hkw_mem_Q : (k : G) * (w : G) * (k : G)⁻¹ ∈ Q :=
    conj_mem_of_normal_subgroupOf hQM k.2 w.2
  set w' : Q := ⟨(k : G) * (w : G) * (k : G)⁻¹, hkw_mem_Q⟩
  have hkH' : (k : G) ∈ H' := Subgroup.mem_subgroupOf.mp hkK
  have hwH' : (w : G) ∈ H' := Subgroup.mem_subgroupOf.mp hw
  have hw'W : w' ∈ H'.subgroupOf Q := by
    rw [Subgroup.mem_subgroupOf]
    exact H'.mul_mem (H'.mul_mem hkH' hwH') (H'.inv_mem hkH')
  refine ⟨w', hw'W, ?_⟩
  have hconj_eq : (⟨m * (w : G) * m⁻¹, conj_mem_of_normal_subgroupOf hQM hm w.2⟩ : Q)⁻¹ * w' =
      ⁅q₀, w'⁻¹⁆ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def, inv_inv, w', q₀]
    group
  rw [hconj_eq]
  exact commutatorElement_mem_center_of_isExtraspecialPGroup hQ q₀ w'⁻¹

include hp in
/-- General lower bound on subgroup indices in a simple group `S` receiving an injective
homomorphism `f : M →* S` from a subgroup `M ≤ G` with normal extraspecial `p`-subgroup `Q ◁ M` of
order `p ^ (1 + 2 * m)` and simple quotient `M ⧸ Q` divisible by a prime `q`: if every
`M`-invariant subgroup `W ≤ Q` avoiding `Z(Q)` (modulo `Z(Q)`) is trivial, then every proper
subgroup `H ≠ ⊤` of `S` has index at least `n₀` whenever `n₀ ≤ q * p ^ (m + 1)` and
`n₀ ≤ p ^ (1 + 2 * m)`. -/
theorem index_ge_of_normal_extraspecial_subgroupOf_injective {M Q : Subgroup G} (hQM : Q ≤ M)
    [hQn : (Q.subgroupOf M).Normal] (hQ : CFSG.IsExtraspecialPGroup p Q) {m : ℕ}
    (hcardQ : Nat.card Q = p ^ (1 + 2 * m)) (hSimple : IsSimpleGroup (M ⧸ Q.subgroupOf M))
    {q : ℕ} (hq_prime : q.Prime) (hq_dvd : q ∣ Nat.card (M ⧸ Q.subgroupOf M))
    {n₀ : ℕ} (hn₀_mul : n₀ ≤ q * p ^ (m + 1)) (hn₀_pow : n₀ ≤ p ^ (1 + 2 * m))
    (hirr : ∀ (W : Subgroup Q), ¬ center Q ≤ W →
      (∀ (g : G) (hg : g ∈ M) (w : Q), w ∈ W → ∃ w' ∈ W,
        (⟨g * (w : G) * g⁻¹, conj_mem_of_normal_subgroupOf hQM hg w.2⟩ : Q)⁻¹ * w' ∈ center Q) →
      W = ⊥)
    {S : Type*} [Group S] [Finite S] [IsSimpleGroup S] (f : M →* S) (hf : Function.Injective f)
    {H : Subgroup S} (hH : H ≠ ⊤) :
    n₀ ≤ H.index := by
  have hZ_ne : (center Q).map (Subgroup.inclusion hQM) ≠ ⊥ := by
    intro hbot
    apply center_ne_bot_of_isExtraspecialPGroup hQ
    rw [eq_bot_iff]
    intro z hz
    have hz' : Subgroup.inclusion hQM z ∈ (center Q).map (Subgroup.inclusion hQM) := ⟨z, hz, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hz'
    exact Subgroup.inclusion_injective hQM hz'
  refine le_index_of_injective_of_forall_not_le_index hH f hf hZ_ne fun K₀ hK₀Z => ?_
  set H' : Subgroup G := K₀.map M.subtype
  have hK₀_eq : H'.subgroupOf M = K₀ :=
    Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective M) K₀
  set K : Subgroup M := H'.subgroupOf M
  set W : Subgroup Q := H'.subgroupOf Q
  have hWZ : ¬ center Q ≤ W := by
    intro hle
    apply hK₀Z
    rintro _ ⟨z₀, hz₀, rfl⟩
    obtain ⟨k, hkK, hkz⟩ := hle hz₀
    have hkeq : k = Subgroup.inclusion hQM z₀ := Subtype.ext hkz
    exact hkeq ▸ hkK
  have hW_idx : p ^ (m + 1) ≤ W.index :=
    pow_le_index_of_isExtraspecialPGroup hQ hcardQ hWZ
  have hK_eq : K.index =
      (K.map (QuotientGroup.mk' (Q.subgroupOf M))).index * W.index :=
    index_subgroupOf_eq_mul hQM
  rw [← hK₀_eq]
  by_cases hmap : K.map (QuotientGroup.mk' (Q.subgroupOf M)) = ⊤
  · have hW_bot : W = ⊥ :=
      hirr W hWZ (fun g hg w hw => exists_mem_center_of_map_eq_top hQM hQ hmap hg hw)
    have hW_card : W.index = p ^ (1 + 2 * m) := by
      rw [hW_bot, Subgroup.index_bot, hcardQ]
    have hmap_idx : (K.map (QuotientGroup.mk' (Q.subgroupOf M))).index = 1 := by
      rw [hmap, Subgroup.index_top]
    calc
      n₀ ≤ p ^ (1 + 2 * m) := hn₀_pow
      _ = 1 * W.index := by rw [one_mul, hW_card]
      _ = K.index := by rw [hK_eq, hmap_idx]
  · have hq_le : q ≤ (K.map (QuotientGroup.mk' (Q.subgroupOf M))).index :=
      prime_le_index_of_ne_top hmap hq_prime hq_dvd
    calc
      n₀ ≤ q * p ^ (m + 1) := hn₀_mul
      _ ≤ (K.map (QuotientGroup.mk' (Q.subgroupOf M))).index * W.index :=
        Nat.mul_le_mul hq_le hW_idx
      _ = K.index := hK_eq.symm

include hp in
/-- General lower bound on subgroup indices in a simple group `S ≃* G` containing a subgroup `M`
with normal extraspecial `p`-subgroup `Q ◁ M` of order `p ^ (1 + 2 * m)` and simple quotient
`M ⧸ Q` divisible by a prime `q`: if every `M`-invariant subgroup `W ≤ Q` avoiding `Z(Q)` (modulo
`Z(Q)`) is trivial, then every proper subgroup `H ≠ ⊤` of `S` has index at least `n₀` whenever
`n₀ ≤ q * p ^ (m + 1)` and `n₀ ≤ p ^ (1 + 2 * m)`. -/
theorem index_ge_of_normal_extraspecial_simple_quotient {M Q : Subgroup G} (hQM : Q ≤ M)
    [hQn : (Q.subgroupOf M).Normal] (hQ : CFSG.IsExtraspecialPGroup p Q) {m : ℕ}
    (hcardQ : Nat.card Q = p ^ (1 + 2 * m)) (hSimple : IsSimpleGroup (M ⧸ Q.subgroupOf M))
    {q : ℕ} (hq_prime : q.Prime) (hq_dvd : q ∣ Nat.card (M ⧸ Q.subgroupOf M))
    {n₀ : ℕ} (hn₀_mul : n₀ ≤ q * p ^ (m + 1)) (hn₀_pow : n₀ ≤ p ^ (1 + 2 * m))
    (hirr : ∀ (W : Subgroup Q), ¬ center Q ≤ W →
      (∀ (g : G) (hg : g ∈ M) (w : Q), w ∈ W → ∃ w' ∈ W,
        (⟨g * (w : G) * g⁻¹, conj_mem_of_normal_subgroupOf hQM hg w.2⟩ : Q)⁻¹ * w' ∈ center Q) →
      W = ⊥)
    {S : Type*} [Group S] [Finite S] [IsSimpleGroup S] (e : S ≃* G)
    {H : Subgroup S} (hH : H ≠ ⊤) :
    n₀ ≤ H.index :=
  index_ge_of_normal_extraspecial_subgroupOf_injective hQM hQ hcardQ hSimple hq_prime hq_dvd
    hn₀_mul hn₀_pow hirr (e.symm.toMonoidHom.comp M.subtype)
    (e.symm.injective.comp (Subgroup.subtype_injective M)) hH

/-- Variant of `index_ge_of_normal_extraspecial_simple_quotient` taking the local subgroup `M` as a
type with a normal extraspecial subgroup `Q : Subgroup M` and an injective homomorphism
`f : M →* S`. -/
theorem index_ge_of_normal_extraspecial_of_injective {M : Type*} [Group M] [Finite M]
    (Q : Subgroup M) [hQn : Q.Normal] {p : ℕ} [hp : Fact p.Prime]
    (hQ : CFSG.IsExtraspecialPGroup p Q) {m : ℕ} (hcardQ : Nat.card Q = p ^ (1 + 2 * m))
    (hSimple : IsSimpleGroup (M ⧸ Q)) {q : ℕ} (hq_prime : q.Prime)
    (hq_dvd : q ∣ Nat.card (M ⧸ Q)) {n₀ : ℕ} (hn₀_mul : n₀ ≤ q * p ^ (m + 1))
    (hn₀_pow : n₀ ≤ p ^ (1 + 2 * m))
    (hirr : ∀ (W : Subgroup Q), ¬ center Q ≤ W →
      (∀ (g : M) (w : Q), w ∈ W → ∃ w' ∈ W, (MulAut.conjNormal g w)⁻¹ * w' ∈ center Q) →
      W = ⊥)
    {S : Type*} [Group S] [Finite S] [IsSimpleGroup S] (f : M →* S) (hf : Function.Injective f)
    {H : Subgroup S} (hH : H ≠ ⊤) :
    n₀ ≤ H.index := by
  have hZ_ne : (center Q).map Q.subtype ≠ ⊥ := by
    intro hbot
    apply center_ne_bot_of_isExtraspecialPGroup hQ
    rw [eq_bot_iff]
    intro z hz
    have hz' : (z : M) ∈ (center Q).map Q.subtype := ⟨z, hz, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hz'
    exact Subtype.ext hz'
  refine le_index_of_injective_of_forall_not_le_index hH f hf hZ_ne fun K hKZ => ?_
  set W : Subgroup Q := K.subgroupOf Q
  have hWZ : ¬ center Q ≤ W := by
    intro hle
    apply hKZ
    rintro _ ⟨z₀, hz₀, rfl⟩
    exact hle hz₀
  have hW_idx : p ^ (m + 1) ≤ W.index :=
    pow_le_index_of_isExtraspecialPGroup hQ hcardQ hWZ
  set π : M →* M ⧸ Q := QuotientGroup.mk' Q
  set φ : K →* M ⧸ Q := π.comp K.subtype
  have hrange : φ.range = K.map π := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hker : φ.ker = Q.subgroupOf K := by
    ext x
    simp only [φ, MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype,
      π, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hker_equiv : ↥(Q.subgroupOf K) ≃ ↥W :=
    { toFun := fun x => ⟨⟨(x : M), x.2⟩, x.1.2⟩
      invFun := fun w => ⟨⟨(w : M), w.2⟩, w.1.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hcard_ker : Nat.card φ.ker = Nat.card W := by
    rw [hker]
    exact Nat.card_congr hker_equiv
  have hcard_K : Nat.card W * Nat.card (K.map π) = Nat.card K := by
    rw [← hcard_ker, ← hrange]
    exact Subgroup.card_ker_mul_card_range φ
  have hcard_M : Nat.card Q * Nat.card (M ⧸ Q) = Nat.card M := by
    rw [← Subgroup.index_eq_card]
    exact Subgroup.card_mul_index Q
  have hW_mul : Nat.card W * W.index = Nat.card Q := Subgroup.card_mul_index W
  have hmap_mul : Nat.card (K.map π) * (K.map π).index = Nat.card (M ⧸ Q) :=
    Subgroup.card_mul_index (K.map π)
  have hK_mul : Nat.card K * K.index = Nat.card M := Subgroup.card_mul_index K
  have hK_eq : K.index = (K.map π).index * W.index := by
    have hprod : (Nat.card W * Nat.card (K.map π)) * K.index =
        (Nat.card W * Nat.card (K.map π)) * ((K.map π).index * W.index) := by
      calc
        (Nat.card W * Nat.card (K.map π)) * K.index = Nat.card K * K.index := by rw [hcard_K]
        _ = Nat.card M := hK_mul
        _ = Nat.card Q * Nat.card (M ⧸ Q) := hcard_M.symm
        _ = (Nat.card W * W.index) * (Nat.card (K.map π) * (K.map π).index) := by
          rw [hW_mul, hmap_mul]
        _ = (Nat.card W * Nat.card (K.map π)) * ((K.map π).index * W.index) := by ring
    exact Nat.eq_of_mul_eq_mul_left (Nat.mul_pos Nat.card_pos Nat.card_pos) hprod
  by_cases hmap : K.map π = ⊤
  · have hW_bot : W = ⊥ := by
      refine hirr W hWZ fun g w hw => ?_
      have hg_top : π g ∈ K.map π := hmap ▸ mem_top _
      obtain ⟨k, hkK, hkg⟩ := hg_top
      have hq_mem : g * k⁻¹ ∈ Q := by
        rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.coe_mk', map_mul, map_inv, hkg,
          mul_inv_cancel]
      set q₀ : Q := ⟨g * k⁻¹, hq_mem⟩
      set w' : Q := MulAut.conjNormal k w
      have hw'W : w' ∈ W := by
        rw [Subgroup.mem_subgroupOf]
        exact K.mul_mem (K.mul_mem hkK (Subgroup.mem_subgroupOf.mp hw)) (K.inv_mem hkK)
      refine ⟨w', hw'W, ?_⟩
      have hconj_eq : (MulAut.conjNormal g w)⁻¹ * w' = ⁅q₀, w'⁻¹⁆ := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, MulAut.conjNormal_apply,
          commutatorElement_def, inv_inv, w', q₀]
        group
      rw [hconj_eq]
      exact commutatorElement_mem_center_of_isExtraspecialPGroup hQ q₀ w'⁻¹
    have hW_card : W.index = p ^ (1 + 2 * m) := by
      rw [hW_bot, Subgroup.index_bot, hcardQ]
    have hmap_idx : (K.map π).index = 1 := by
      rw [hmap, Subgroup.index_top]
    calc
      n₀ ≤ p ^ (1 + 2 * m) := hn₀_pow
      _ = 1 * W.index := by rw [one_mul, hW_card]
      _ = K.index := by rw [hK_eq, hmap_idx]
  · have hq_le : q ≤ (K.map π).index :=
      prime_le_index_of_ne_top hmap hq_prime hq_dvd
    calc
      n₀ ≤ q * p ^ (m + 1) := hn₀_mul
      _ ≤ (K.map π).index * W.index := Nat.mul_le_mul hq_le hW_idx
      _ = K.index := hK_eq.symm

end Extension

end Maroti.ExtraspecialExt
