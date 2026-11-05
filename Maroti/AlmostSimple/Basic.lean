module

public import Maroti.Bound
public import Maroti.Interface
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.GroupTheory.Index

/-!
# Basic properties of primitive almost simple permutation groups

This file proves the general criteria used to bound the order of a primitive permutation group
`G ≤ Perm α` that is almost simple with socle `T ≃* S` (`Maroti.IsAlmostSimpleWith G S`).

Every nontrivial normal subgroup of a primitive permutation group acts transitively
(Wielandt, *Finite Permutation Groups*, Theorem 7.1). In particular, the socle `T` acts
transitively on `α` (`isPretransitive_socle`). For any point `ω : α`, the degree `Nat.card α`
equals the index of the point stabilizer `T_ω` in `T`, and `T_ω` is a proper subgroup of `T`.
Thus `S` has a proper subgroup of index `Nat.card α`
(`IsAlmostSimpleWith.exists_proper_subgroup_index_eq`).

Because the centralizer of `T` in `G` is trivial, conjugation by elements of `G` embeds `G`
into the automorphism group `MulAut T ≃* MulAut S` (`conjHom_injective`,
`IsAlmostSimpleWith.card_le_card_mulAut`). Combining the lower bound on the subgroup index with
the monotonicity of `Maroti.bound` shows that if every proper subgroup of `S` has index at least
`n₀` and `|MulAut S| ≤ bound n₀`, then `|G| ≤ bound |α|`
(`IsAlmostSimpleWith.card_le_bound_of_index_ge`,
`IsAlmostSimpleWith.card_le_bound_of_outerAut_le`).
-/

@[expose] public section

namespace Maroti

open Equiv MulAction

variable {α : Type*}

/-- In a faithful preprimitive group action, every nontrivial normal subgroup acts
pretransitively (Wielandt, *Finite Permutation Groups*, Theorem 7.1). -/
theorem isPretransitive_of_normal_ne_bot {G : Type*} [Group G] [MulAction G α]
    [FaithfulSMul G α] [IsPreprimitive G α] {N : Subgroup G} [N.Normal] (hN : N ≠ ⊥) :
    IsPretransitive N α := by
  apply IsQuasiPreprimitive.isPretransitive_of_normal
  intro hfix
  obtain ⟨n, hnN, hn1⟩ := (Subgroup.bot_or_exists_ne_one N).resolve_left hN
  apply hn1
  apply eq_of_smul_eq_smul (α := α)
  intro a
  have ha : a ∈ fixedPoints N α := hfix ▸ Set.mem_univ a
  simpa [one_smul] using ha ⟨n, hnN⟩

/-- If `G ≤ Perm α` acts preprimitively on `α` and `N ≤ G` is a nontrivial subgroup normalized by
`G`, then `N` acts pretransitively on `α`. -/
theorem isPretransitive_of_le_of_conj_mem {G : Subgroup (Perm α)} [IsPreprimitive G α]
    {N : Subgroup (Perm α)} (hNG : N ≤ G) (hNnorm : ∀ g ∈ G, ∀ n ∈ N, g * n * g⁻¹ ∈ N)
    (hN : N ≠ ⊥) : IsPretransitive N α := by
  let N' : Subgroup G := N.subgroupOf G
  have hN'norm : N'.Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hNnorm g g.2 n hn⟩
  have hN'ne : N' ≠ ⊥ := by
    obtain ⟨x, hxN, hx1⟩ := (Subgroup.bot_or_exists_ne_one N).resolve_left hN
    intro hbot
    apply hx1
    have hxN' : (⟨x, hNG hxN⟩ : G) ∈ N' := Subgroup.mem_subgroupOf.mpr hxN
    rw [hbot, Subgroup.mem_bot] at hxN'
    exact congrArg Subtype.val hxN'
  have htr : IsPretransitive N' α := isPretransitive_of_normal_ne_bot hN'ne
  refine ⟨fun x y => ?_⟩
  obtain ⟨⟨g, hg⟩, rfl⟩ := htr.exists_smul_eq x y
  exact ⟨⟨g, Subgroup.mem_subgroupOf.mp hg⟩, rfl⟩

/-- If `Perm α` contains a nontrivial subgroup, then `α` is nontrivial. -/
theorem nontrivial_of_nontrivial_subgroup {T : Subgroup (Perm α)} [Nontrivial T] :
    Nontrivial α := by
  obtain ⟨⟨t, ht⟩, ht1⟩ := exists_ne (1 : T)
  have ht' : t ≠ 1 := fun h => ht1 (Subtype.ext h)
  obtain ⟨a, ha⟩ : ∃ a : α, t a ≠ a := by
    by_contra hall
    push Not at hall
    exact ht' (Equiv.ext hall)
  exact ⟨⟨t a, a, ha⟩⟩

section Socle

variable {G : Subgroup (Perm α)} {T : Subgroup (Perm α)}

/-- The socle `T` of a primitive group `G` acts pretransitively on `α`. -/
theorem isPretransitive_socle [IsPreprimitive G α] (hTG : T ≤ G)
    (hTnorm : ∀ g ∈ G, ∀ t ∈ T, g * t * g⁻¹ ∈ T) [IsSimpleGroup T] :
    IsPretransitive T α :=
  isPretransitive_of_le_of_conj_mem hTG hTnorm
    ((Subgroup.nontrivial_iff_ne_bot T).mp inferInstance)

/-- The degree `Nat.card α` equals the index of the point stabilizer in `T`. -/
theorem card_eq_index_stabilizer_socle [Finite α] [IsPreprimitive G α] (hTG : T ≤ G)
    (hTnorm : ∀ g ∈ G, ∀ t ∈ T, g * t * g⁻¹ ∈ T) [IsSimpleGroup T] (ω : α) :
    Nat.card α = (stabilizer T ω).index := by
  have := isPretransitive_socle hTG hTnorm
  exact (index_stabilizer_of_transitive T ω).symm

/-- For every point `ω : α`, the stabilizer `T_ω` is a proper subgroup of `T`. -/
theorem stabilizer_socle_ne_top [IsPreprimitive G α] (hTG : T ≤ G)
    (hTnorm : ∀ g ∈ G, ∀ t ∈ T, g * t * g⁻¹ ∈ T) [IsSimpleGroup T] (ω : α) :
    stabilizer T ω ≠ ⊤ := by
  have : Nontrivial α := nontrivial_of_nontrivial_subgroup (T := T)
  have := isPretransitive_socle hTG hTnorm
  intro htop
  obtain ⟨ω', hω'⟩ := exists_ne ω
  obtain ⟨t, rfl⟩ := exists_smul_eq T ω ω'
  have ht : t ∈ stabilizer T ω := htop ▸ Subgroup.mem_top t
  exact hω' (mem_stabilizer_iff.mp ht)

/-- Conjugation of `T` by an element of `G` when `G` normalizes `T`. -/
def conjAut (hTnorm : ∀ g ∈ G, ∀ t ∈ T, g * t * g⁻¹ ∈ T) (g : G) : MulAut T where
  toFun t := ⟨(g : Perm α) * t * (g : Perm α)⁻¹, hTnorm g g.2 t t.2⟩
  invFun t := ⟨(g : Perm α)⁻¹ * t * (g : Perm α), by
    simpa using hTnorm (g : Perm α)⁻¹ (inv_mem g.2) t t.2⟩
  left_inv t := by
    apply Subtype.ext
    simp [mul_assoc]
  right_inv t := by
    apply Subtype.ext
    simp [mul_assoc]
  map_mul' a b := by
    apply Subtype.ext
    simp [mul_assoc]

/-- The conjugation homomorphism `G →* MulAut T`. -/
def conjHom (hTnorm : ∀ g ∈ G, ∀ t ∈ T, g * t * g⁻¹ ∈ T) : G →* MulAut T where
  toFun := conjAut hTnorm
  map_one' := by
    ext t
    simp [conjAut]
  map_mul' g h := by
    ext t
    simp [conjAut, mul_assoc]

@[simp]
theorem conjHom_apply_coe (hTnorm : ∀ g ∈ G, ∀ t ∈ T, g * t * g⁻¹ ∈ T) (g : G) (t : T) :
    (conjHom hTnorm g t : Perm α) = (g : Perm α) * t * (g : Perm α)⁻¹ := rfl

/-- If `C_G(T) = 1`, then `conjHom : G →* MulAut T` is injective. -/
theorem conjHom_injective (hTnorm : ∀ g ∈ G, ∀ t ∈ T, g * t * g⁻¹ ∈ T)
    (hTcent : ∀ g ∈ G, (∀ t ∈ T, g * t = t * g) → g = 1) :
    Function.Injective (conjHom hTnorm) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  apply hTcent g g.2
  intro t ht
  have h1 := congrArg (fun φ : MulAut T => (φ ⟨t, ht⟩ : Perm α)) hg
  simp only [conjHom_apply_coe, MulAut.one_apply] at h1
  calc (g : Perm α) * t = ((g : Perm α) * t * (g : Perm α)⁻¹) * g := by group
    _ = t * g := by rw [h1]

/-- On elements of `T`, `conjHom` agrees with inner conjugation `MulAut.conj`. -/
theorem conjHom_socle (hTG : T ≤ G) (hTnorm : ∀ g ∈ G, ∀ t ∈ T, g * t * g⁻¹ ∈ T) (t : T) :
    conjHom hTnorm ⟨t, hTG t.2⟩ = MulAut.conj t := by
  ext x
  rfl

end Socle

/-- The inner automorphism subgroup of a group `S`, namely `(MulAut.conj : S →* MulAut S).range`.
This is definitionally equal to `CFSG.ComponentClassification.OuterAutomorphisms.inner S`. -/
def innerAut (S : Type*) [Group S] : Subgroup (MulAut S) :=
  (MulAut.conj : S →* MulAut S).range

instance innerAut_normal (S : Type*) [Group S] : (innerAut S).Normal where
  conj_mem _ h φ := by
    obtain ⟨s, rfl⟩ := h
    refine ⟨φ s, ?_⟩
    ext x
    change φ s * x * (φ s)⁻¹ = φ (s * φ.symm x * s⁻¹)
    rw [map_mul, map_mul, map_inv, φ.apply_symm_apply]

/-- The outer automorphism group `MulAut S ⧸ innerAut S`.
This is definitionally equal to `CFSG.ComponentClassification.OuterAutomorphisms.Outer S`. -/
abbrev OuterAut (S : Type*) [Group S] := MulAut S ⧸ innerAut S

/-- For any finite group `S`, `|MulAut S| ≤ |S| · |OuterAut S|`. -/
theorem card_mulAut_le_card_mul_outerAut (S : Type*) [Group S] [Finite S] :
    Nat.card (MulAut S) ≤ Nat.card S * Nat.card (OuterAut S) := by
  rw [← (innerAut S).card_mul_index]
  apply Nat.mul_le_mul_right
  exact Nat.card_le_card_of_surjective (MulAut.conj : S →* MulAut S).rangeRestrict
    (MulAut.conj : S →* MulAut S).rangeRestrict_surjective

namespace IsAlmostSimpleWith

variable {G : Subgroup (Perm α)} {S : Type*} [Group S]

/-- The socle model `S` of an almost simple group is a simple group. -/
theorem isSimpleGroup (h : IsAlmostSimpleWith G S) : IsSimpleGroup S := by
  obtain ⟨T, -, -, hSimple, -, -, ⟨e⟩⟩ := h
  exact e.symm.isSimpleGroup

/-- The socle model `S` of an almost simple group is a nonabelian simple group. -/
theorem isNonabelianSimple {S : Type} [Group S] (h : IsAlmostSimpleWith G S) :
    IsNonabelianSimple S := by
  obtain ⟨T, -, -, hSimple, ⟨a, b, hab⟩, -, ⟨e⟩⟩ := h
  refine ⟨e.symm.isSimpleGroup, e a, e b, fun hcomm => hab (e.injective ?_)⟩
  simpa only [map_mul] using hcomm

/-- Transfer `IsAlmostSimpleWith` along a multiplicative equivalence of the socle. -/
theorem congr {S' : Type*} [Group S'] (h : IsAlmostSimpleWith G S) (e : S ≃* S') :
    IsAlmostSimpleWith G S' := by
  obtain ⟨T, h1, h2, h3, h4, h5, ⟨e₀⟩⟩ := h
  exact ⟨T, h1, h2, h3, h4, h5, ⟨e₀.trans e⟩⟩

/-- If `G` is almost simple on `α`, then `α` is nontrivial. -/
theorem nontrivial_alpha (h : IsAlmostSimpleWith G S) : Nontrivial α := by
  obtain ⟨T, -, -, hSimple, -, -, -⟩ := h
  exact nontrivial_of_nontrivial_subgroup (T := T)

/-- If `G` is almost simple on a finite type `α`, then `2 ≤ Nat.card α`. -/
theorem two_le_card [Finite α] (h : IsAlmostSimpleWith G S) : 2 ≤ Nat.card α := by
  have := h.nontrivial_alpha
  exact Finite.one_lt_card

/-- If `α` is finite and `IsAlmostSimpleWith G S`, then `S` is finite. -/
theorem finite [Finite α] (h : IsAlmostSimpleWith G S) : Finite S := by
  obtain ⟨T, -, -, -, -, -, ⟨e⟩⟩ := h
  exact Finite.of_equiv T e.toEquiv

/-- In a primitive almost simple group `G` with socle `S`, `S` has a proper subgroup of index
`Nat.card α`. -/
theorem exists_proper_subgroup_index_eq [Finite α] [IsPreprimitive G α]
    (h : IsAlmostSimpleWith G S) :
    ∃ H : Subgroup S, H ≠ ⊤ ∧ H.index = Nat.card α := by
  have := h.nontrivial_alpha
  obtain ⟨ω⟩ : Nonempty α := inferInstance
  obtain ⟨T, hTG, hTnorm, hSimple, -, -, ⟨e⟩⟩ := h
  refine ⟨(stabilizer T ω).map (e : T →* S), ?_, ?_⟩
  · intro htop
    apply stabilizer_socle_ne_top hTG hTnorm ω
    apply Subgroup.map_injective (f := (e : T →* S)) e.injective
    rw [htop, Subgroup.map_top_of_surjective _ e.surjective]
  · rw [Subgroup.index_map_equiv, ← card_eq_index_stabilizer_socle hTG hTnorm ω]

/-- An almost simple group `G` with socle `S` embeds into `MulAut S`. -/
theorem exists_injective_mulAut (h : IsAlmostSimpleWith G S) :
    ∃ φ : G →* MulAut S, Function.Injective φ := by
  obtain ⟨T, -, hTnorm, -, -, hTcent, ⟨e⟩⟩ := h
  refine ⟨(MulAut.congr e).toMonoidHom.comp (conjHom hTnorm), ?_⟩
  exact (MulAut.congr e).injective.comp (conjHom_injective hTnorm hTcent)

/-- An almost simple group `G` with socle `S` has order at most `|MulAut S|`. -/
theorem card_le_card_mulAut [Finite α] (h : IsAlmostSimpleWith G S) :
    Nat.card G ≤ Nat.card (MulAut S) := by
  have : Finite S := h.finite
  obtain ⟨φ, hφ⟩ := h.exists_injective_mulAut
  exact Nat.card_le_card_of_injective φ hφ

/-- An almost simple group `G` with socle `S` has order at most `|S| · |OuterAut S|`. -/
theorem card_le_card_mul_outerAut [Finite α] (h : IsAlmostSimpleWith G S) :
    Nat.card G ≤ Nat.card S * Nat.card (OuterAut S) := by
  have : Finite S := h.finite
  exact h.card_le_card_mulAut.trans (card_mulAut_le_card_mul_outerAut S)

/-- If `|OuterAut S| ≤ c`, then `|G| ≤ |S| · c`. -/
theorem card_le_of_outerAut_le [Finite α] (h : IsAlmostSimpleWith G S) {c : ℕ}
    (hc : Nat.card (OuterAut S) ≤ c) : Nat.card G ≤ Nat.card S * c :=
  h.card_le_card_mul_outerAut.trans (Nat.mul_le_mul_left (Nat.card S) hc)

/-- If `|OuterAut S|` divides `c > 0`, then `|G| ≤ |S| · c`. -/
theorem card_le_of_outerAut_dvd [Finite α] (h : IsAlmostSimpleWith G S) {c : ℕ} (hc0 : 0 < c)
    (hdvd : Nat.card (OuterAut S) ∣ c) : Nat.card G ≤ Nat.card S * c :=
  h.card_le_of_outerAut_le (Nat.le_of_dvd hc0 hdvd)

/-- If `n₀ ≤ Nat.card α` and `|MulAut S| ≤ bound n₀`, then `|G| ≤ bound (Nat.card α)`. -/
theorem card_le_bound_of_le_card [Finite α] (h : IsAlmostSimpleWith G S) {n₀ : ℕ}
    (hn : n₀ ≤ Nat.card α) (haut : Nat.card (MulAut S) ≤ bound n₀) :
    Nat.card G ≤ bound (Nat.card α) :=
  h.card_le_card_mulAut.trans (haut.trans (bound_mono hn))

/-- If `n₀ ≤ Nat.card α`, `|OuterAut S| ≤ c`, and `|S| · c ≤ bound n₀`, then
`|G| ≤ bound (Nat.card α)`. -/
theorem card_le_bound_of_le_card_of_outerAut_le [Finite α] (h : IsAlmostSimpleWith G S)
    {n₀ c : ℕ} (hn : n₀ ≤ Nat.card α) (hout : Nat.card (OuterAut S) ≤ c)
    (hbound : Nat.card S * c ≤ bound n₀) : Nat.card G ≤ bound (Nat.card α) :=
  (h.card_le_of_outerAut_le hout).trans (hbound.trans (bound_mono hn))

/-- Main criterion: if every proper subgroup of `S` has index at least `n₀` and
`|MulAut S| ≤ bound n₀`, then `|G| ≤ bound (Nat.card α)`. -/
theorem card_le_bound_of_index_ge [Finite α] [IsPreprimitive G α]
    (h : IsAlmostSimpleWith G S) {n₀ : ℕ} (hidx : ∀ H : Subgroup S, H ≠ ⊤ → n₀ ≤ H.index)
    (haut : Nat.card (MulAut S) ≤ bound n₀) : Nat.card G ≤ bound (Nat.card α) := by
  obtain ⟨H, hHne, hHidx⟩ := h.exists_proper_subgroup_index_eq
  exact h.card_le_bound_of_le_card (hHidx ▸ hidx H hHne) haut

/-- Outer-automorphism criterion: if every proper subgroup of `S` has index at least `n₀`,
`|OuterAut S| ≤ c`, and `|S| · c ≤ bound n₀`, then `|G| ≤ bound (Nat.card α)`. -/
theorem card_le_bound_of_outerAut_le [Finite α] [IsPreprimitive G α]
    (h : IsAlmostSimpleWith G S) {n₀ c : ℕ} (hidx : ∀ H : Subgroup S, H ≠ ⊤ → n₀ ≤ H.index)
    (hout : Nat.card (OuterAut S) ≤ c) (hbound : Nat.card S * c ≤ bound n₀) :
    Nat.card G ≤ bound (Nat.card α) := by
  obtain ⟨H, hHne, hHidx⟩ := h.exists_proper_subgroup_index_eq
  exact h.card_le_bound_of_le_card_of_outerAut_le (hHidx ▸ hidx H hHne) hout hbound

/-- Divisibility variant of the outer-automorphism criterion: if every proper subgroup of `S` has
index at least `n₀`, `|OuterAut S|` divides `c > 0`, and `|S| · c ≤ bound n₀`, then
`|G| ≤ bound (Nat.card α)`. -/
theorem card_le_bound_of_outerAut_dvd [Finite α] [IsPreprimitive G α]
    (h : IsAlmostSimpleWith G S) {n₀ c : ℕ} (hc0 : 0 < c)
    (hidx : ∀ H : Subgroup S, H ≠ ⊤ → n₀ ≤ H.index) (hout : Nat.card (OuterAut S) ∣ c)
    (hbound : Nat.card S * c ≤ bound n₀) : Nat.card G ≤ bound (Nat.card α) :=
  h.card_le_bound_of_outerAut_le hidx (Nat.le_of_dvd hc0 hout) hbound

end IsAlmostSimpleWith

/-- Every group of subset action type is of wreath type with `r = 1`. -/
theorem IsSubsetActionType.isWreathType {G : Subgroup (Perm α)}
    (h : IsSubsetActionType G) : IsWreathType G := by
  obtain ⟨m, k, e, hm5, hg, ha⟩ := h
  let u : (Fin 1 → KSubset m k) ≃ KSubset m k := Equiv.funUnique (Fin 1) (KSubset m k)
  refine ⟨m, k, 1, e.trans u.symm, hm5, ?_, ?_⟩
  · intro g hgG
    obtain ⟨h, hh⟩ := hg g hgG
    refine ⟨1, fun _ => h, ?_⟩
    apply Equiv.ext
    intro x
    funext i
    fin_cases i
    change u.symm ((e.permCongr g) (u x)) 0 = kSubsetPerm h (x 0)
    rw [hh]
    rfl
  · intro a
    have h1 : (e.trans u.symm).symm.permCongr (productActionPerm 1 fun i => (a i : Perm (Fin m))) =
        e.symm.permCongr (kSubsetPerm (a 0 : Perm (Fin m))) := by
      apply Equiv.ext
      intro x
      rfl
    rw [h1]
    exact ha (a 0)

/-- The conclusion `AlmostSimpleConclusion G` for an almost simple group implies `Conclusion G`. -/
theorem AlmostSimpleConclusion.conclusion {G : Subgroup (Perm α)}
    (h : AlmostSimpleConclusion G) : Conclusion G :=
  h.imp IsSubsetActionType.isWreathType id

/-- In a finite group `G`, if `A ≤ B`, then `B.index ≤ A.index`. -/
theorem index_le_of_le {G : Type*} [Group G] [Finite G] {A B : Subgroup G}
    (h : A ≤ B) : B.index ≤ A.index := by
  rw [← Subgroup.relIndex_mul_index h]
  exact Nat.le_mul_of_pos_left _ Nat.card_pos

/-- In a finite group `G`, for any subgroups `H, P` of `G`, `H.relIndex P ≤ H.index`. -/
theorem relIndex_le_index {G : Type*} [Group G] [Finite G] (H P : Subgroup G) :
    H.relIndex P ≤ H.index := by
  let f : P ⧸ H.subgroupOf P → G ⧸ H :=
    Quotient.lift (fun p : P => QuotientGroup.mk (p : G)) fun a b h => by
      have h1 : (QuotientGroup.mk a : P ⧸ H.subgroupOf P) = QuotientGroup.mk b := Quotient.sound h
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h1
      exact QuotientGroup.eq.mpr h1
  have hf : Function.Injective f := by
    intro x y hxy
    induction x using QuotientGroup.induction_on with | H a =>
    induction y using QuotientGroup.induction_on with | H b =>
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    exact QuotientGroup.eq.mp hxy
  exact Nat.card_le_card_of_injective f hf

/-- In a finite group `G`, for any subgroups `H, K, M` of `G` with `K ≤ M`,
`H.relIndex K ≤ H.relIndex M`. -/
theorem relIndex_le_relIndex_of_le {G : Type*} [Group G] [Finite G]
    (H K M : Subgroup G) (hKM : K ≤ M) :
    H.relIndex K ≤ H.relIndex M := by
  let f : K ⧸ H.subgroupOf K → M ⧸ H.subgroupOf M :=
    Quotient.lift (fun k : K => QuotientGroup.mk (⟨k.1, hKM k.2⟩ : M)) fun a b h => by
      have h1 : (QuotientGroup.mk a : K ⧸ H.subgroupOf K) = QuotientGroup.mk b := Quotient.sound h
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h1
      exact QuotientGroup.eq.mpr h1
  have hf : Function.Injective f := by
    intro x y hxy
    induction x using QuotientGroup.induction_on with | H a =>
    induction y using QuotientGroup.induction_on with | H b =>
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    exact (QuotientGroup.eq (s := H.subgroupOf M)).mp hxy
  exact Nat.card_le_card_of_injective f hf

/-- If conjugation by every element of `K` maps `X` into `X`, then `K` lies in the normalizer of
`X`. -/
theorem le_normalizer_of_conj_mem {G : Type*} [Group G] {K X : Subgroup G}
    (h : ∀ k ∈ K, X ≤ X.comap (MulAut.conj k).toMonoidHom) :
    K ≤ Subgroup.normalizer (X : Set G) := by
  intro k hk
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact h k hk hx
  · intro hkx
    have h1 : k⁻¹ * (k * x * k⁻¹) * (k⁻¹)⁻¹ ∈ X := h k⁻¹ (K.inv_mem hk) hkx
    have h2 : k⁻¹ * (k * x * k⁻¹) * (k⁻¹)⁻¹ = x := by group
    rwa [h2] at h1

/-- If a finite field `K` has cardinality `p ^ f` with `p` prime and `1 ≤ f`, then
`ringChar K = p`. -/
theorem ringChar_eq_of_card_eq {K : Type*} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime)
    (hf : 1 ≤ f) (hK : Nat.card K = p ^ f) : ringChar K = p := by
  have := Fintype.ofFinite K
  have hq := CharP.prime_ringChar K
  obtain ⟨m, -, hm⟩ := FiniteField.card K (ringChar K)
  rw [Nat.card_eq_fintype_card] at hK
  have hdvd : p ∣ ringChar K ^ (m : ℕ) := by
    rw [← hm, hK]
    exact dvd_pow_self p (by omega)
  exact ((Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow hdvd)).symm

/-- If a finite field `K` has cardinality `p ^ f` with `p` prime and `1 ≤ f`, then `CharP K p`. -/
theorem charP_of_card_eq {K : Type*} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime)
    (hf : 1 ≤ f) (hK : Nat.card K = p ^ f) : CharP K p :=
  ringChar_eq_of_card_eq hp hf hK ▸ (inferInstance : CharP K (ringChar K))

/-- A finite field `K` of cardinality `2` has characteristic `2`. -/
theorem charP_two_of_card_two {K : Type*} [Field K] [Finite K] (hK : Nat.card K = 2) :
    CharP K 2 :=
  charP_of_card_eq Nat.prime_two le_rfl (by rw [hK, pow_one])

/-- In a field `K` of prime characteristic `p ≠ 2`, `(2 : K) ≠ 0`. -/
theorem two_ne_zero_of_charP {K : Type*} [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp2 : p ≠ 2) : (2 : K) ≠ 0 := by
  have hq : (ringChar K).Prime := by
    rw [ringChar.eq K p]
    exact Fact.out
  intro h0
  have hdvd : ringChar K ∣ 2 := (ringChar.spec K 2).mp (by simpa using h0)
  have heq : ringChar K = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdvd
  rw [ringChar.eq K p] at heq
  exact hp2 heq

end Maroti
