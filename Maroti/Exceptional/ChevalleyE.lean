module

public import Maroti.Exceptional.AutBound
public import CFSG.SignalizerFunctorTheorem.NonLocal.HeisFam
import CFSG.Timmesfeld.Orders.Exceptional
import CFSG.SignalizerFunctorTheorem.NonLocalExc.HeisChevalley

/-!
# Untwisted Exceptional Groups of Types `E₆`, `E₇`, `E₈`

This file proves the subgroup index lower bounds and Maróti's bound `|G| ≤ bound |α|` for
primitive almost simple groups `G ≤ Perm α` with socle `E₆(q)`, `E₇(q)`, or `E₈(q)` (Maróti,
Section 2, Step 2, pages 634–635).

Using the root-pair Heisenberg data `HeisFacts` from
`CFSG.SignalizerFunctorTheorem.NonLocalExc.HeisFacts` (`10`, `16`, and `28` roots summing in pairs
to the highest root `heisα0 τ` for `E₆`, `E₇`, `E₈`), we construct a `HeisFam` on
`adjointGroup τ K` and deduce that every proper subgroup `H` of `E₆(q)`, `E₇(q)`, `E₈(q)` has
index at least `q ^ 10`, `q ^ 16`, `q ^ 28`, respectively.
-/

@[expose] public section

open scoped commutatorElement

namespace Maroti

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.SignalizerFunctorTheorem.NonLocal
open CFSG.SignalizerFunctorTheorem.NonLocalExc

/-! ### General subgroup index bounds from `HeisFam` -/

/-- If `Γ` is a finite simple group and `H : HeisFam Γ S P Zp` has a nontrivial central element
`H.z w ≠ 1` with `w ∈ H.Rg`, then every proper subgroup `M < Γ` has index at least
`Nat.card (∀ s, P s)`. -/
theorem HeisFam.card_le_index_of_isSimpleGroup {Γ : Type*} [Group Γ] [Finite Γ]
    [IsSimpleGroup Γ] {S : Type*} [Fintype S] [DecidableEq S]
    {P : S → Type*} [∀ s, AddCommGroup (P s)] [∀ s, Finite (P s)]
    {Zp : Type*} [AddCommGroup Zp] (H : HeisFam Γ S P Zp)
    (hnt : ∃ w ∈ H.Rg, H.z w ≠ 1) (M : Subgroup Γ) (hM : M ≠ ⊤) :
    Nat.card (∀ s, P s) ≤ M.index := by
  rw [Subgroup.index_eq_card]
  let π : Γ →* Equiv.Perm (Γ ⧸ M) := MulAction.toPermHom Γ (Γ ⧸ M)
  have hker_le : π.ker ≤ M := by
    intro g hg
    have h1 := congrArg (fun σ : Equiv.Perm (Γ ⧸ M) => σ (QuotientGroup.mk (1 : Γ))) hg
    simp only [π, MulAction.toPermHom_apply, MulAction.toPerm_apply,
      Equiv.Perm.coe_one, id_eq] at h1
    have h2 := QuotientGroup.leftRel_apply.mp (Quotient.exact h1)
    simpa using h2
  have hker_bot : π.ker = ⊥ :=
    (π.normal_ker.eq_bot_or_eq_top).resolve_right (fun htop => hM (top_unique (htop ▸ hker_le)))
  obtain ⟨w, hw, hzw⟩ := hnt
  refine H.card_le_perm π ⟨w, hw, fun hπ => hzw ?_⟩
  rwa [← MonoidHom.mem_ker, hker_bot, Subgroup.mem_bot] at hπ

/-- If `Γ` is a finite simple group and `H : HeisFam Γ S P Zp` has a central involution
`H.z w ≠ 1` with `H.z w * H.z w = 1` and `w ∈ H.Rg`, then every proper subgroup `M < Γ` has index
at least `2 * Nat.card (∀ s, P s)`. -/
theorem HeisFam.two_mul_card_le_index_of_isSimpleGroup {Γ : Type*} [Group Γ] [Finite Γ]
    [IsSimpleGroup Γ] {S : Type*} [Fintype S] [DecidableEq S]
    {P : S → Type*} [∀ s, AddCommGroup (P s)] [∀ s, Finite (P s)]
    {Zp : Type*} [AddCommGroup Zp] (H : HeisFam Γ S P Zp)
    (hnt : ∃ w ∈ H.Rg, H.z w * H.z w = 1 ∧ H.z w ≠ 1) (M : Subgroup Γ) (hM : M ≠ ⊤) :
    2 * Nat.card (∀ s, P s) ≤ M.index := by
  rw [Subgroup.index_eq_card]
  let π : Γ →* Equiv.Perm (Γ ⧸ M) := MulAction.toPermHom Γ (Γ ⧸ M)
  have hker_le : π.ker ≤ M := by
    intro g hg
    have h1 := congrArg (fun σ : Equiv.Perm (Γ ⧸ M) => σ (QuotientGroup.mk (1 : Γ))) hg
    simp only [π, MulAction.toPermHom_apply, MulAction.toPerm_apply,
      Equiv.Perm.coe_one, id_eq] at h1
    have h2 := QuotientGroup.leftRel_apply.mp (Quotient.exact h1)
    simpa using h2
  have hker_bot : π.ker = ⊥ :=
    (π.normal_ker.eq_bot_or_eq_top).resolve_right (fun htop => hM (top_unique (htop ▸ hker_le)))
  obtain ⟨w, hw, hsq, hzw⟩ := hnt
  refine H.two_mul_card_le_perm π ⟨w, hw, hsq, fun hπ => hzw ?_⟩
  rwa [← MonoidHom.mem_ker, hker_bot, Subgroup.mem_bot] at hπ

/-- General polynomial-to-`bound` comparison: if `2 ≤ q`, `2 ^ L ≤ q ^ k`, and `d + 4 ≤ k * L`,
then `q ^ d * (6 * q) ≤ bound (q ^ k)`. -/
theorem pow_mul_six_le_bound {q d k L : ℕ} (hq : 2 ≤ q) (hL : 2 ^ L ≤ q ^ k)
    (hd : d + 4 ≤ k * L) :
    q ^ d * (6 * q) ≤ bound (q ^ k) := by
  have hq0 : 0 < q := by omega
  have hqk0 : 0 < q ^ k := Nat.pow_pos hq0
  have h6q : 6 * q ≤ q ^ 4 := by
    calc 6 * q ≤ 2 ^ 3 * q ^ 1 := by
          rw [pow_one]
          exact Nat.mul_le_mul_right q (by decide)
      _ ≤ q ^ 3 * q ^ 1 := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hq 3)
      _ = q ^ 4 := by ring
  have hlog : L ≤ Nat.log 2 (q ^ k) := Nat.le_log_of_pow_le (by decide) hL
  calc q ^ d * (6 * q)
      ≤ q ^ d * q ^ 4 := Nat.mul_le_mul_left _ h6q
    _ = q ^ (d + 4) := (pow_add q d 4).symm
    _ ≤ q ^ (k * L) := Nat.pow_le_pow_right hq0 hd
    _ = (q ^ k) ^ L := pow_mul q k L
    _ ≤ (q ^ k) ^ Nat.log 2 (q ^ k) := Nat.pow_le_pow_right hqk0 hlog
    _ ≤ bound (q ^ k) := pow_log_le_bound hqk0

/-! ### Heisenberg family `HeisFam` on `adjointGroup τ K` for `τ ∈ {.E6, .E7, .E8}` -/

/-- Root subgroup element `pinnedX τ K α c` as an element of `adjointGroup τ K`. -/
private noncomputable def pinnedAdjoint (τ : Tag) (K : Type) [Field K]
    (α : Fin τ.rank → ℤ) (c : K) : ↥(adjointGroup τ K) :=
  ⟨pinnedX τ K α c, pinnedX_mem_adjointGroup α c⟩

private theorem pinnedAdjoint_add (τ : Tag) (K : Type) [Field K] (α : Fin τ.rank → ℤ) (c d : K) :
    pinnedAdjoint τ K α (c + d) = pinnedAdjoint τ K α c * pinnedAdjoint τ K α d :=
  Subtype.ext (pinnedX_add τ K α c d)

private theorem pinnedAdjoint_zero (τ : Tag) (K : Type) [Field K] (α : Fin τ.rank → ℤ) :
    pinnedAdjoint τ K α 0 = 1 :=
  Subtype.ext (pinnedX_zero τ K α)

private theorem pinnedAdjoint_neg (τ : Tag) (K : Type) [Field K] (α : Fin τ.rank → ℤ) (c : K) :
    (pinnedAdjoint τ K α c)⁻¹ = pinnedAdjoint τ K α (-c) :=
  Subtype.ext (pinnedX_neg τ K α c)

private theorem pinnedAdjoint_injective (τ : Tag) (K : Type) [Field K] (α : Fin τ.rank → ℤ) :
    Function.Injective (pinnedAdjoint τ K α) := fun _ _ h =>
  pinnedX_injective τ K α (congrArg Subtype.val h)

private theorem pinnedAdjoint_comm {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (K : Type) [Field K]
    {α β : Fin τ.rank → ℤ} (hα : IsRoot τ α) (hβ : IsRoot τ β) (hposα : 0 < height α)
    (hposβ : 0 < height β) (h : ¬ IsRoot τ (α + β)) (c d : K) :
    pinnedAdjoint τ K α c * pinnedAdjoint τ K β d =
      pinnedAdjoint τ K β d * pinnedAdjoint τ K α c :=
  Subtype.ext (pinned_comm_of_not_isRoot hτ hα hβ hposα hposβ h c d)

private theorem exists_pinnedAdjoint_comm_ss {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (hF : HeisFacts τ) (K : Type) [Field K] (β : Fin τ.rank → ℤ) (hβ : β ∈ heisS τ) :
    ∃ ε : K, ε ≠ 0 ∧ ∀ c d : K,
      ⁅(pinnedAdjoint τ K (heisα0 τ - β) c)⁻¹, pinnedAdjoint τ K β d⁆ =
        pinnedAdjoint τ K (heisα0 τ) (ε * c * d) := by
  have hβpos := hF.pos_of_mem β hβ
  have hγpos : 0 < height (heisα0 τ - β) := heis_gamma_pos (hF := hF) hβ
  have hne : heisα0 τ - β ≠ β := fun h => hF.sub_not_mem β hβ (by rw [h]; exact hβ)
  have hsum : heisα0 τ - β + β = heisα0 τ := sub_add_cancel _ _
  obtain ⟨ε', hε', hf⟩ := exists_pinned_comm_of_isRoot hτ (hF.isRoot_sub β hβ)
    (hF.isRoot_of_mem β hβ) hγpos hβpos hne (by rw [hsum]; exact hF.isRoot_α0)
  refine ⟨-(ε' : K), ?_, fun c d => ?_⟩
  · rcases hε' with rfl | rfl <;> simp
  · rw [pinnedAdjoint_neg]
    apply Subtype.ext
    have := hf K (-c) d
    simp only [hsum] at this
    change ⁅pinnedX τ K (heisα0 τ - β) (-c), pinnedX τ K β d⁆ = _
    rw [this]
    congr 1
    ring

/-- The Heisenberg family on `adjointGroup τ K` associated to `HeisFacts τ` for
`τ ∈ {.E6, .E7, .E8}`. -/
private noncomputable def adjointHeisFam {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (hF : HeisFacts τ) (hα0 : 0 < height (heisα0 τ)) (K : Type) [Field K] :
    HeisFam ↥(adjointGroup τ K) ↥(heisS τ) (fun _ => K) K where
  xa s c := pinnedAdjoint τ K s.1 c
  xb s c := pinnedAdjoint τ K (heisα0 τ - s.1) c
  z c := pinnedAdjoint τ K (heisα0 τ) c
  e s c d := Classical.choose (exists_pinnedAdjoint_comm_ss hτ hF K s.1 s.2) * c * d
  Rg := ⊤
  z_add c d := pinnedAdjoint_add τ K _ c d
  e_add_left s c c' d := by ring
  e_mem _ _ _ := trivial
  e_surj s c hc w _ := ⟨(Classical.choose (exists_pinnedAdjoint_comm_ss hτ hF K s.1 s.2) * c)⁻¹ * w,
    by
      have hε : Classical.choose (exists_pinnedAdjoint_comm_ss hτ hF K s.1 s.2) ≠ 0 :=
        (Classical.choose_spec (exists_pinnedAdjoint_comm_ss hτ hF K s.1 s.2)).1
      exact mul_inv_cancel_left₀ (mul_ne_zero hε hc) w⟩
  xa_comm s t c d := pinnedAdjoint_comm hτ K (hF.isRoot_of_mem _ s.2) (hF.isRoot_of_mem _ t.2)
    (hF.pos_of_mem _ s.2) (hF.pos_of_mem _ t.2) (hF.not_isRoot_SS _ s.2 _ t.2) c d
  xb_comm s t c d := pinnedAdjoint_comm hτ K (hF.isRoot_sub _ s.2) (hF.isRoot_sub _ t.2)
    (heis_gamma_pos (hF := hF) s.2) (heis_gamma_pos (hF := hF) t.2)
    (hF.not_isRoot_TT _ s.2 _ t.2) c d
  z_comm_a c s d := pinnedAdjoint_comm hτ K hF.isRoot_α0 (hF.isRoot_of_mem _ s.2) hα0
    (hF.pos_of_mem _ s.2) (hF.not_isRoot_α0_S _ s.2) c d
  z_comm_b c s d := pinnedAdjoint_comm hτ K hF.isRoot_α0 (hF.isRoot_sub _ s.2) hα0
    (heis_gamma_pos (hF := hF) s.2) (hF.not_isRoot_α0_T _ s.2) c d
  xab_comm s t hst c d := pinnedAdjoint_comm hτ K (hF.isRoot_sub _ s.2) (hF.isRoot_of_mem _ t.2)
    (heis_gamma_pos (hF := hF) s.2) (hF.pos_of_mem _ t.2)
    (by
      rw [add_comm]
      exact hF.not_isRoot_ST _ t.2 _ s.2 (fun h => hst (Subtype.ext h.symm))) c d
  comm_ss s c d := (Classical.choose_spec (exists_pinnedAdjoint_comm_ss hτ hF K s.1 s.2)).2 c d

/-- Every proper subgroup `H` of a simple group `S` modeled by `UntwistedChevalleyModel S τ q` for
`τ ∈ {.E6, .E7, .E8}` has index at least `q ^ (heisS τ).card`. -/
private theorem pow_card_heisS_le_index {S : Type} [Group S] [IsSimpleGroup S] {τ : Tag} {q : ℕ}
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hF : HeisFacts τ) (hS : (heisS τ).Nonempty)
    (hm : UntwistedChevalleyModel S τ q) (H : Subgroup S) (hH : H ≠ ⊤) :
    q ^ (heisS τ).card ≤ H.index := by
  classical
  obtain ⟨K, _, _, hK, ⟨e₀⟩⟩ := hm
  have e : S ≃* ↥(adjointGroup τ K) :=
    e₀.trans ((QuotientGroup.quotientMulEquivOfEq
      (center_adjointGroup_eq_bot (τ := τ) (K := K))).trans QuotientGroup.quotientBot)
  have : Finite (ModGL τ K) := finite_modGL
  have : Finite (adjointGroup τ K) := Subtype.finite
  have : IsSimpleGroup ↥(adjointGroup τ K) := e.symm.isSimpleGroup
  obtain ⟨β0, hβ0⟩ := hS
  have hα0 : 0 < height (heisα0 τ) := by
    have h1 := hF.two_height_lt β0 hβ0
    have h2 := hF.pos_of_mem β0 hβ0
    omega
  let Hfam := adjointHeisFam hτ hF hα0 K
  have hz1 : Hfam.z 1 ≠ 1 := by
    intro h1
    rw [← pinnedAdjoint_zero τ K (heisα0 τ)] at h1
    exact one_ne_zero (pinnedAdjoint_injective τ K (heisα0 τ) h1)
  have hM : H.map (e : S →* ↥(adjointGroup τ K)) ≠ ⊤ := by
    intro htop
    apply hH
    apply Subgroup.map_injective (f := (e : S →* ↥(adjointGroup τ K))) e.injective
    rw [htop, Subgroup.map_top_of_surjective _ e.surjective]
  have hle := HeisFam.card_le_index_of_isSimpleGroup Hfam ⟨1, trivial, hz1⟩
    (H.map (e : S →* ↥(adjointGroup τ K))) hM
  rw [Subgroup.index_map_equiv, Nat.card_fun, hK, Nat.card_eq_fintype_card, Fintype.card_coe] at hle
  exact hle

/-! ### The `E₆(q)`, `E₇(q)`, and `E₈(q)` cases of Maróti's theorem -/

/-- Any primitive almost simple group `G ≤ Perm α` with socle `E₆(p^f)` satisfies
`|G| ≤ bound |α|`. -/
theorem card_le_bound_of_chevalley_E6 {α : Type} [Finite α]
    {G : Subgroup (Equiv.Perm α)} [MulAction.IsPreprimitive G α]
    {S : Type} [Group S] {p f : ℕ} (hAS : IsAlmostSimpleWith G S)
    (h : ChevalleyExceptionalModel S .E6 p f) :
    Nat.card G ≤ bound (Nat.card α) := by
  have : IsSimpleGroup S := hAS.isSimpleGroup
  have hcard : Nat.card S = ordE6 (p ^ f) := card_chevalleyExceptionalModel h
  have hout := (card_outerAut_E6 h).2
  obtain ⟨⟨hp, hf, -⟩, hm⟩ := h
  have hS : (heisS .E6).Nonempty := Finset.card_pos.1 (by rw [card_heisS_E6]; decide)
  have hidx : ∀ H : Subgroup S, H ≠ ⊤ → (p ^ f) ^ 10 ≤ H.index := by
    intro H hH
    have := pow_card_heisS_le_index (Or.inl rfl) heisFacts_E6 hS hm H hH
    rwa [card_heisS_E6] at this
  have hq2 : 2 ≤ p ^ f := (Nat.pow_le_pow_left hp.two_le 1).trans (Nat.pow_le_pow_right hp.pos hf)
  have hfq : f ≤ p ^ f := (Nat.lt_pow_self hp.one_lt).le
  refine hAS.card_le_bound_of_outerAut_le hidx hout ?_
  rw [hcard]
  calc ordE6 (p ^ f) * (6 * f)
      ≤ (p ^ f) ^ 78 * (6 * (p ^ f)) :=
        Nat.mul_le_mul (ordE6_le_pow (p ^ f)) (Nat.mul_le_mul_left 6 hfq)
    _ ≤ bound ((p ^ f) ^ 10) :=
        pow_mul_six_le_bound hq2 (Nat.pow_le_pow_left hq2 10) (by decide)

/-- Any primitive almost simple group `G ≤ Perm α` with socle `E₇(p^f)` satisfies
`|G| ≤ bound |α|`. -/
theorem card_le_bound_of_chevalley_E7 {α : Type} [Finite α]
    {G : Subgroup (Equiv.Perm α)} [MulAction.IsPreprimitive G α]
    {S : Type} [Group S] {p f : ℕ} (hAS : IsAlmostSimpleWith G S)
    (h : ChevalleyExceptionalModel S .E7 p f) :
    Nat.card G ≤ bound (Nat.card α) := by
  have : IsSimpleGroup S := hAS.isSimpleGroup
  have hcard : Nat.card S = ordE7 (p ^ f) := card_chevalleyExceptionalModel h
  have hout := (card_outerAut_E7 h).2
  obtain ⟨⟨hp, hf, -⟩, hm⟩ := h
  have hS : (heisS .E7).Nonempty := Finset.card_pos.1 (by rw [card_heisS_E7]; decide)
  have hidx : ∀ H : Subgroup S, H ≠ ⊤ → (p ^ f) ^ 16 ≤ H.index := by
    intro H hH
    have := pow_card_heisS_le_index (Or.inr (Or.inl rfl)) heisFacts_E7 hS hm H hH
    rwa [card_heisS_E7] at this
  have hq2 : 2 ≤ p ^ f := (Nat.pow_le_pow_left hp.two_le 1).trans (Nat.pow_le_pow_right hp.pos hf)
  have hfq : f ≤ p ^ f := (Nat.lt_pow_self hp.one_lt).le
  refine hAS.card_le_bound_of_outerAut_le hidx hout ?_
  rw [hcard]
  calc ordE7 (p ^ f) * (2 * f)
      ≤ (p ^ f) ^ 133 * (6 * (p ^ f)) :=
        Nat.mul_le_mul (ordE7_le_pow (p ^ f)) (Nat.mul_le_mul (by decide) hfq)
    _ ≤ bound ((p ^ f) ^ 16) :=
        pow_mul_six_le_bound hq2 (Nat.pow_le_pow_left hq2 16) (by decide)

/-- Any primitive almost simple group `G ≤ Perm α` with socle `E₈(p^f)` satisfies
`|G| ≤ bound |α|`. -/
theorem card_le_bound_of_chevalley_E8 {α : Type} [Finite α]
    {G : Subgroup (Equiv.Perm α)} [MulAction.IsPreprimitive G α]
    {S : Type} [Group S] {p f : ℕ} (hAS : IsAlmostSimpleWith G S)
    (h : ChevalleyExceptionalModel S .E8 p f) :
    Nat.card G ≤ bound (Nat.card α) := by
  have : IsSimpleGroup S := hAS.isSimpleGroup
  have hcard : Nat.card S = ordE8 (p ^ f) := card_chevalleyExceptionalModel h
  have hout := (card_outerAut_E8 h).2
  obtain ⟨⟨hp, hf, -⟩, hm⟩ := h
  have hS : (heisS .E8).Nonempty := Finset.card_pos.1 (by rw [card_heisS_E8]; decide)
  have hidx : ∀ H : Subgroup S, H ≠ ⊤ → (p ^ f) ^ 28 ≤ H.index := by
    intro H hH
    have := pow_card_heisS_le_index (Or.inr (Or.inr rfl)) heisFacts_E8 hS hm H hH
    rwa [card_heisS_E8] at this
  have hq2 : 2 ≤ p ^ f := (Nat.pow_le_pow_left hp.two_le 1).trans (Nat.pow_le_pow_right hp.pos hf)
  have hfq : f ≤ p ^ f := (Nat.lt_pow_self hp.one_lt).le
  refine hAS.card_le_bound_of_outerAut_le hidx hout ?_
  rw [hcard]
  calc ordE8 (p ^ f) * f
      ≤ (p ^ f) ^ 248 * (6 * (p ^ f)) :=
        Nat.mul_le_mul (ordE8_le_pow (p ^ f))
          (hfq.trans (Nat.le_mul_of_pos_left _ (by decide : 0 < 6)))
    _ ≤ bound ((p ^ f) ^ 28) :=
        pow_mul_six_le_bound hq2 (Nat.pow_le_pow_left hq2 28) (by decide)

end Maroti
