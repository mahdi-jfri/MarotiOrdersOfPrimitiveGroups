module

public import Maroti.AlmostSimple.Basic

/-!
# Regular normal subgroups and the automorphism bound

This file proves the regular normal subgroup case of Step 1 in Section 2 of A. Maróti,
*On the orders of primitive groups*, J. Algebra 258 (2002), page 633.

For any finite group `M`, the automorphism group `MulAut M` has order at most
`∏_{i < ⌊log₂ |M|⌋} (|M| - 2^i)` (`card_mulAut_le_prod_sub_two_pow`). The proof bounds the order
of the pointwise stabilizer `fixSubgroup H ≤ MulAut M` of a subgroup `H ≤ M` by strong induction
on `|M| - |H|`. When `H` is a proper subgroup of `M` and `x ∉ H`, evaluating at `x` maps the
cosets of `fixSubgroup (H ⊔ ⟨x⟩)` in `fixSubgroup H` injectively into the complement `M \ H`,
while the subgroup `H ⊔ ⟨x⟩` has order at least `2 |H|`.

Any permutation `g : Perm α` that fixes a point `ω` and commutes with every element of a
transitive subgroup `N ≤ Perm α` is the identity (`eq_one_of_commute_transitive`, Wielandt,
*Finite Permutation Groups*, Theorem 4.2(a)). Consequently, if `M ≤ G` is a transitive normal
subgroup of `G ≤ Perm α`, the point stabilizer `G_ω` embeds into `MulAut M` by conjugation
(`stabilizer_conjHom_injective`). When `M_ω = ⊥` (in particular, when `M` is abelian or
centralizes a transitive subgroup), the order of `M` equals `|α|` and `|G| ≤ bound |α|`
(`card_le_bound_of_regular_normal`, `card_le_bound_of_centralizes_transitive`,
`card_le_bound_of_abelian_normal`).
-/

@[expose] public section

namespace Maroti

open Equiv MulAction

section AutBound

variable {M : Type*} [Group M]

/-- The subgroup of `M` fixed pointwise by an automorphism `φ : MulAut M`. -/
def fixedSubgroup (φ : MulAut M) : Subgroup M where
  carrier := {m | φ m = m}
  one_mem' := map_one φ
  mul_mem' {a b} ha hb := by
    change φ (a * b) = a * b
    rw [map_mul, ha, hb]
  inv_mem' {a} ha := by
    change φ a⁻¹ = a⁻¹
    rw [map_inv, ha]

@[simp]
theorem mem_fixedSubgroup_iff {φ : MulAut M} {m : M} :
    m ∈ fixedSubgroup φ ↔ φ m = m := Iff.rfl

/-- The subgroup of `MulAut M` fixing a subgroup `H ≤ M` pointwise. -/
def fixSubgroup (H : Subgroup M) : Subgroup (MulAut M) where
  carrier := {φ | H ≤ fixedSubgroup φ}
  one_mem' _ _ := rfl
  mul_mem' {φ ψ} hφ hψ m hm := by
    change φ (ψ m) = m
    rw [hψ hm, hφ hm]
  inv_mem' {φ} hφ m hm := by
    change φ.symm m = m
    exact φ.injective (by rw [φ.apply_symm_apply, hφ hm])

theorem mem_fixSubgroup_iff {H : Subgroup M} {φ : MulAut M} :
    φ ∈ fixSubgroup H ↔ ∀ h ∈ H, φ h = h := Iff.rfl

theorem fixSubgroup_anti : Antitone (fixSubgroup (M := M)) :=
  fun _ _ hle _ hφ => hle.trans hφ

@[simp]
theorem fixSubgroup_bot : fixSubgroup (⊥ : Subgroup M) = ⊤ := by
  ext φ
  simp [mem_fixSubgroup_iff]

@[simp]
theorem fixSubgroup_top : fixSubgroup (⊤ : Subgroup M) = ⊥ := by
  ext φ
  rw [mem_fixSubgroup_iff, Subgroup.mem_bot, MulEquiv.ext_iff]
  simp [MulAut.one_apply]

theorem apply_notMem_of_notMem {H : Subgroup M} {φ : MulAut M} (hφ : φ ∈ fixSubgroup H)
    {x : M} (hx : x ∉ H) : φ x ∉ H := by
  intro hx'
  have h1 : φ (φ x) = φ x := hφ hx'
  exact hx (φ.injective h1 ▸ hx')

theorem mem_fixSubgroup_sup_zpowers_iff {H : Subgroup M} {x : M} {φ : MulAut M} :
    φ ∈ fixSubgroup (H ⊔ Subgroup.zpowers x) ↔ φ ∈ fixSubgroup H ∧ φ x = x := by
  change H ⊔ Subgroup.zpowers x ≤ fixedSubgroup φ ↔ H ≤ fixedSubgroup φ ∧ φ x = x
  rw [sup_le_iff, Subgroup.zpowers_le, mem_fixedSubgroup_iff]

variable [Finite M]

theorem two_mul_card_le_sup_zpowers {H : Subgroup M} {x : M} (hx : x ∉ H) :
    2 * Nat.card H ≤ Nat.card ↥(H ⊔ Subgroup.zpowers x) := by
  let H' : Subgroup M := H ⊔ Subgroup.zpowers x
  let K : Subgroup H' := H.subgroupOf H'
  have hK : K ≠ ⊤ := by
    intro htop
    have hxH' : x ∈ H' := Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
    have hxK : (⟨x, hxH'⟩ : H') ∈ K := htop ▸ Subgroup.mem_top _
    exact hx (Subgroup.mem_subgroupOf.mp hxK)
  have h2 : 2 ≤ K.index := by
    have h0 : K.index ≠ 0 := K.index_ne_zero_of_finite
    have h1 : K.index ≠ 1 := mt Subgroup.index_eq_one.mp hK
    omega
  have hcard : Nat.card K = Nat.card H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv
  calc 2 * Nat.card H = Nat.card K * 2 := by rw [hcard, mul_comm]
    _ ≤ Nat.card K * K.index := Nat.mul_le_mul_left _ h2
    _ = Nat.card H' := K.card_mul_index

theorem card_compl_subgroup (H : Subgroup M) :
    Nat.card {m : M // m ∉ H} = Nat.card M - Nat.card H := by
  classical
  have := Fintype.ofFinite M
  have h1 : Nat.card {m : M // m ∉ H} + Nat.card H = Nat.card M := by
    simp only [Nat.card_eq_fintype_card]
    exact Fintype.card_subtype_compl (· ∈ H) ▸
      Nat.sub_add_cancel (Fintype.card_subtype_le (· ∈ H))
  omega

theorem card_fixSubgroup_le_mul_sup_zpowers {H : Subgroup M} {x : M} (hx : x ∉ H) :
    Nat.card ↥(fixSubgroup H) ≤
      (Nat.card M - Nat.card H) * Nat.card ↥(fixSubgroup (H ⊔ Subgroup.zpowers x)) := by
  let H' := H ⊔ Subgroup.zpowers x
  let K : Subgroup (fixSubgroup H) := (fixSubgroup H').subgroupOf (fixSubgroup H)
  let ev : fixSubgroup H ⧸ K → {m : M // m ∉ H} :=
    Quotient.lift (fun φ : fixSubgroup H => ⟨φ.1 x, apply_notMem_of_notMem φ.2 hx⟩)
      (fun φ ψ h => by
        have hmem : (φ⁻¹ * ψ : fixSubgroup H).1 ∈ fixSubgroup H' :=
          Subgroup.mem_subgroupOf.mp (QuotientGroup.leftRel_apply.mp h)
        have hx' : (φ.1⁻¹ * ψ.1) x = x := (mem_fixSubgroup_sup_zpowers_iff.mp hmem).2
        apply Subtype.ext
        calc φ.1 x = φ.1 ((φ.1⁻¹ * ψ.1) x) := by rw [hx']
          _ = ψ.1 x := by simp [MulAut.mul_apply])
  have hev : Function.Injective ev := by
    intro q₁ q₂ hq
    obtain ⟨φ, rfl⟩ := Quotient.exists_rep q₁
    obtain ⟨ψ, rfl⟩ := Quotient.exists_rep q₂
    apply Quotient.sound
    change (QuotientGroup.leftRel K) φ ψ
    rw [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf, mem_fixSubgroup_sup_zpowers_iff]
    refine ⟨(φ⁻¹ * ψ).2, ?_⟩
    have hval : φ.1 x = ψ.1 x := congrArg Subtype.val hq
    calc (φ.1⁻¹ * ψ.1) x = φ.1.symm (ψ.1 x) := rfl
      _ = φ.1.symm (φ.1 x) := by rw [← hval]
      _ = x := φ.1.symm_apply_apply x
  have hidx : K.index ≤ Nat.card M - Nat.card H := by
    rw [← card_compl_subgroup H]
    exact Nat.card_le_card_of_injective ev hev
  have hcardK : Nat.card K = Nat.card ↥(fixSubgroup H') :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (fixSubgroup_anti le_sup_left)).toEquiv
  calc Nat.card ↥(fixSubgroup H)
      = K.index * Nat.card K := by rw [mul_comm, K.card_mul_index]
    _ = K.index * Nat.card ↥(fixSubgroup H') := by rw [hcardK]
    _ ≤ (Nat.card M - Nat.card H) * Nat.card ↥(fixSubgroup H') :=
        Nat.mul_le_mul_right _ hidx

theorem card_fixSubgroup_le_prod_range :
    ∀ k : ℕ, ∀ (H : Subgroup M) (i : ℕ),
      Nat.card M - Nat.card H ≤ k → 2 ^ i ≤ Nat.card H →
      Nat.card ↥(fixSubgroup H) ≤
        ∏ j ∈ Finset.range (Nat.log 2 (Nat.card M) - i), (Nat.card M - 2 ^ (i + j))
  | 0, H, i, hk, _ => by
    have hle : Nat.card M ≤ Nat.card H := by omega
    have htop : H = ⊤ :=
      Subgroup.eq_top_of_card_eq H (le_antisymm (Subgroup.card_le_card_group H) hle)
    rw [htop, fixSubgroup_top]
    have h1 : Nat.card ↥(⊥ : Subgroup (MulAut M)) = 1 := Subgroup.card_bot
    rw [h1]
    apply Finset.one_le_prod
    intro j hj
    have hj' := Finset.mem_range.mp hj
    exact sub_two_pow_pos (by omega)
  | k + 1, H, i, hk, hi => by
    by_cases htop : H = ⊤
    · rw [htop, fixSubgroup_top]
      have h1 : Nat.card ↥(⊥ : Subgroup (MulAut M)) = 1 := Subgroup.card_bot
      rw [h1]
      apply Finset.one_le_prod
      intro j hj
      have hj' := Finset.mem_range.mp hj
      exact sub_two_pow_pos (by omega)
    · obtain ⟨x, hx⟩ : ∃ x : M, x ∉ H := by
        by_contra hall
        push Not at hall
        exact htop (eq_top_iff.mpr fun x _ => hall x)
      let H' := H ⊔ Subgroup.zpowers x
      have h2H : 2 * Nat.card H ≤ Nat.card H' := two_mul_card_le_sup_zpowers hx
      have hH'le : Nat.card H' ≤ Nat.card M := Subgroup.card_le_card_group H'
      have hi' : 2 ^ (i + 1) ≤ Nat.card H' := by
        calc 2 ^ (i + 1) = 2 * 2 ^ i := pow_succ' 2 i
          _ ≤ 2 * Nat.card H := Nat.mul_le_mul_left 2 hi
          _ ≤ Nat.card H' := h2H
      have hposH : 0 < Nat.card H :=
        Nat.lt_of_lt_of_le (Nat.two_pow_pos i) hi
      have hk' : Nat.card M - Nat.card H' ≤ k := by omega
      have hilt : i + 1 ≤ Nat.log 2 (Nat.card M) :=
        Nat.le_log_of_pow_le (by omega) (hi'.trans hH'le)
      have hstep := card_fixSubgroup_le_prod_range k H' (i + 1) hk' hi'
      have hsub : Nat.log 2 (Nat.card M) - i = (Nat.log 2 (Nat.card M) - (i + 1)) + 1 := by omega
      have hprod_eq : ∏ j ∈ Finset.range (Nat.log 2 (Nat.card M) - (i + 1)),
            (Nat.card M - 2 ^ (i + 1 + j)) =
          ∏ j ∈ Finset.range (Nat.log 2 (Nat.card M) - (i + 1)),
            (Nat.card M - 2 ^ (i + (j + 1))) := by
        refine Finset.prod_congr rfl fun j _ => ?_
        rw [show i + 1 + j = i + (j + 1) by omega]
      rw [hsub, Finset.prod_range_succ', add_zero, mul_comm _ (Nat.card M - 2 ^ i), ← hprod_eq]
      calc Nat.card ↥(fixSubgroup H)
          ≤ (Nat.card M - Nat.card H) * Nat.card ↥(fixSubgroup H') :=
            card_fixSubgroup_le_mul_sup_zpowers hx
        _ ≤ (Nat.card M - 2 ^ i) *
            ∏ j ∈ Finset.range (Nat.log 2 (Nat.card M) - (i + 1)),
              (Nat.card M - 2 ^ (i + 1 + j)) :=
            Nat.mul_le_mul (Nat.sub_le_sub_left hi _) hstep

/-- For every finite group `M`, `|MulAut M| ≤ ∏_{i < ⌊log₂ |M|⌋} (|M| - 2^i)`. -/
theorem card_mulAut_le_prod_sub_two_pow (M : Type*) [Group M] [Finite M] :
    Nat.card (MulAut M) ≤ ∏ i ∈ Finset.range (Nat.log 2 (Nat.card M)), (Nat.card M - 2 ^ i) := by
  have h1 : Nat.card (MulAut M) = Nat.card ↥(fixSubgroup (⊥ : Subgroup M)) := by
    rw [fixSubgroup_bot, Subgroup.card_top]
  have h2 := card_fixSubgroup_le_prod_range (Nat.card M) (⊥ : Subgroup M) 0 (Nat.sub_le _ _)
    (by rw [pow_zero, Subgroup.card_bot])
  simpa only [Nat.sub_zero, zero_add, ← h1] using h2

end AutBound

section RegularNormal

variable {α : Type*} {G : Subgroup (Perm α)}

/-- A permutation `g : Perm α` that fixes a point `ω` and commutes with a pretransitive subgroup
`N ≤ Perm α` is the identity. -/
theorem eq_one_of_commute_transitive {N : Subgroup (Perm α)} [IsPretransitive N α]
    {g : Perm α} {ω : α} (hω : g ω = ω) (hcomm : ∀ n ∈ N, g * n = n * g) : g = 1 := by
  ext x
  obtain ⟨⟨n, hn⟩, rfl⟩ := exists_smul_eq N ω x
  calc g (n ω) = (g * n) ω := rfl
    _ = (n * g) ω := by rw [hcomm n hn]
    _ = n (g ω) := rfl
    _ = n ω := by rw [hω]

/-- If `M ≤ G` acts pretransitively on `α` and is normalized by `G`, then the restriction of
`conjHom` to any point stabilizer `stabilizer G ω` is injective. -/
theorem stabilizer_conjHom_injective {M : Subgroup (Perm α)} [IsPretransitive M α]
    (hMnorm : ∀ g ∈ G, ∀ m ∈ M, g * m * g⁻¹ ∈ M) (ω : α) :
    Function.Injective ((conjHom hMnorm).comp (stabilizer G ω).subtype) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  apply Subtype.ext
  apply eq_one_of_commute_transitive (N := M) (ω := ω) (mem_stabilizer_iff.mp g.2)
  intro m hm
  have h1 := congrArg (fun φ : MulAut M => (φ ⟨m, hm⟩ : Perm α)) hg
  simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, conjHom_apply_coe, MulAut.one_apply] at h1
  calc (g.1 : Perm α) * m = ((g.1 : Perm α) * m * (g.1 : Perm α)⁻¹) * g.1 := by group
    _ = m * g.1 := by rw [h1]

/-- For any pretransitive normal subgroup `M ≤ G`, the point stabilizer `G_ω` has order at most
`|MulAut M|`. -/
theorem card_stabilizer_le_card_mulAut [Finite α] {M : Subgroup (Perm α)} [IsPretransitive M α]
    (hMnorm : ∀ g ∈ G, ∀ m ∈ M, g * m * g⁻¹ ∈ M) (ω : α) :
    Nat.card ↥(stabilizer G ω) ≤ Nat.card (MulAut M) :=
  Nat.card_le_card_of_injective _ (stabilizer_conjHom_injective hMnorm ω)

/-- If `G ≤ Perm α` is pretransitive and has a normal subgroup `M ≤ G` that acts pretransitively
on `α` with `Nat.card M ≤ Nat.card α` (in particular, if `M` acts regularly), then
`|G| ≤ bound |α|`. -/
theorem card_le_bound_of_normal_card_le [Finite α] [IsPretransitive G α]
    {M : Subgroup (Perm α)} [IsPretransitive M α]
    (hMnorm : ∀ g ∈ G, ∀ m ∈ M, g * m * g⁻¹ ∈ M) (hMcard : Nat.card M ≤ Nat.card α) (ω : α) :
    Nat.card G ≤ bound (Nat.card α) := by
  have h1 : Nat.card G = Nat.card α * Nat.card ↥(stabilizer G ω) := by
    rw [← (stabilizer G ω).card_mul_index, index_stabilizer_of_transitive G ω, mul_comm]
  have h2 : Nat.card ↥(stabilizer G ω) ≤
      ∏ i ∈ Finset.range (Nat.log 2 (Nat.card M)), (Nat.card M - 2 ^ i) :=
    (card_stabilizer_le_card_mulAut hMnorm ω).trans (card_mulAut_le_prod_sub_two_pow M)
  have h3 : Nat.card G ≤ Nat.card α *
      ∏ i ∈ Finset.range (Nat.log 2 (Nat.card M)), (Nat.card M - 2 ^ i) := by
    rw [h1]
    exact Nat.mul_le_mul_left (Nat.card α) h2
  have hcard : Nat.card M = Nat.card α := by
    have hdvd : Nat.card α ≤ Nat.card M := by
      rw [← index_stabilizer_of_transitive M ω, ← (stabilizer M ω).card_mul_index]
      exact Nat.le_mul_of_pos_left _ Nat.card_pos
    exact le_antisymm hMcard hdvd
  rw [hcard] at h3
  exact h3

/-- If `M ≤ G` is normalized by `G`, acts pretransitively on `α`, and `stabilizer M ω = ⊥`, then
`|G| ≤ bound |α|`. -/
theorem card_le_bound_of_regular_normal [Finite α] [IsPretransitive G α]
    {M : Subgroup (Perm α)} [IsPretransitive M α]
    (hMnorm : ∀ g ∈ G, ∀ m ∈ M, g * m * g⁻¹ ∈ M) (ω : α) (hreg : stabilizer M ω = ⊥) :
    Nat.card G ≤ bound (Nat.card α) := by
  apply card_le_bound_of_normal_card_le hMnorm _ ω
  rw [← (stabilizer M ω).card_mul_index, hreg, Subgroup.card_bot, one_mul,
    ← index_stabilizer_of_transitive M ω, hreg]

/-- If `M ≤ G` is normalized by `G`, acts pretransitively on `α`, and centralizes a pretransitive
subgroup `N ≤ Perm α`, then `|G| ≤ bound |α|`. -/
theorem card_le_bound_of_centralizes_transitive [Finite α] [IsPretransitive G α] (ω : α)
    {M N : Subgroup (Perm α)} [IsPretransitive M α] [IsPretransitive N α]
    (hMnorm : ∀ g ∈ G, ∀ m ∈ M, g * m * g⁻¹ ∈ M)
    (hcomm : ∀ m ∈ M, ∀ n ∈ N, m * n = n * m) :
    Nat.card G ≤ bound (Nat.card α) := by
  apply card_le_bound_of_regular_normal hMnorm ω
  rw [eq_bot_iff]
  intro m hm
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  exact eq_one_of_commute_transitive (N := N) (mem_stabilizer_iff.mp hm) (hcomm m m.2)

/-- If `M ≤ G` is an abelian normal subgroup of `G` that acts pretransitively on `α`, then
`|G| ≤ bound |α|`. -/
theorem card_le_bound_of_abelian_normal [Finite α] [IsPretransitive G α] (ω : α)
    {M : Subgroup (Perm α)} [IsPretransitive M α]
    (hMnorm : ∀ g ∈ G, ∀ m ∈ M, g * m * g⁻¹ ∈ M)
    (hab : ∀ a ∈ M, ∀ b ∈ M, a * b = b * a) :
    Nat.card G ≤ bound (Nat.card α) :=
  card_le_bound_of_centralizes_transitive ω hMnorm hab

end RegularNormal

end Maroti
