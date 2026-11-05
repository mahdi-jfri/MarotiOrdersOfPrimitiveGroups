module

public import Maroti.Symplectic.PointRadicalCoords

/-!
# Point radical minimum degree bounds for `PSp(2n, 2^f)`

This file proves the minimum degree bounds for proper subgroups of `PSp(2n, 2^f)` using the
abelian point radical `Q = Lsp B hB v` and its normalizer `N = lineStabilizer B v`:

* The theorem `index_ge_psp_two`: for `StatedClassicalModel S .PSp n 2 1` and `H ≠ ⊤`,
  `2 ^ (2 * n - 2) - 2 ^ (n - 1) ≤ H.index`.
* The theorem `index_ge_psp_four_four`: for `StatedClassicalModel S .PSp 2 2 2` and `H ≠ ⊤`,
  `24 ≤ H.index`.
* The theorem `index_ge_psp_even_of_two_le_f`: for `StatedClassicalModel S .PSp n 2 f` with
  `2 ≤ f` and `H ≠ ⊤`, `(2 ^ f) ^ (2 * n - 2) ≤ H.index`.
-/

@[expose] public section

namespace Maroti

open CFSG.ClassicalGroups.Alternating CFSG.ClassicalGroups.Symplectic CFSG.ClassicalGroups
open CFSG.Open CFSG.Open.StatedAPI
open CFSG.LocalAnalysis.ComponentInitial
open LinearMap (BilinForm)
open Module

section TwoToOneBound

variable {K W : Type*} [Field K] [Finite K] [CharP K 2]
  [AddCommGroup W] [Module K W] [Finite W]

/-- For a map `a : W → K` satisfying `a (s • v) = a v * s`, the map `ψ v = (a v + 1) • v`
satisfies `(Nat.card K - 2) * (Nat.card W - 1) + 2 * (Nat.card K - 1) ≤
  2 * (Nat.card K - 1) * Nat.card (Set.range ψ)`. -/
theorem two_to_one_range_bound (a : W → K)
    (ha_smul : ∀ (s : K) (v : W), a (s • v) = a v * s) :
    (Nat.card K - 2) * (Nat.card W - 1) + 2 * (Nat.card K - 1) ≤
      2 * (Nat.card K - 1) * Nat.card (Set.range fun v : W => (a v + 1) • v) := by
  classical
  set ψ : W → W := fun v => (a v + 1) • v with hψ_def
  have hψ0 : ψ 0 = 0 := smul_zero _
  let S₁ := {v : W // v ≠ 0 ∧ ψ v = 0}
  let A := {w : W // ψ w ≠ 0}
  have hW_split : Nat.card W = 1 + Nat.card S₁ + Nat.card A := by
    let e : Option (S₁ ⊕ A) ≃ W :=
      { toFun := fun x =>
          match x with
          | none => 0
          | some (Sum.inl v) => v.1
          | some (Sum.inr w) => w.1
        invFun := fun w =>
          if hw0 : w = 0 then none
          else if hψw : ψ w = 0 then some (Sum.inl ⟨w, hw0, hψw⟩)
          else some (Sum.inr ⟨w, hψw⟩)
        left_inv := by
          rintro (_ | ⟨⟨v, hv0, hψv⟩ | ⟨w, hψw⟩⟩)
          · simp
          · simp [hv0, hψv]
          · have hw0 : w ≠ 0 := fun h => hψw (by rw [h, hψ0])
            simp [hw0, hψw]
        right_inv := fun w => by
          by_cases hw0 : w = 0
          · simp [hw0]
          · by_cases hψw : ψ w = 0 <;> simp [hw0, hψw] }
    have hcard := (Nat.card_congr e).symm
    let _ := Fintype.ofFinite S₁
    let _ := Fintype.ofFinite A
    simp only [Nat.card_eq_fintype_card, Fintype.card_option, Fintype.card_sum] at hcard ⊢
    omega
  have ha_eq_one : ∀ v : S₁, a v.1 = 1 := by
    intro v
    have h1 : (a v.1 + 1) • v.1 = 0 := v.2.2
    have h2 : a v.1 + 1 = 0 := (smul_eq_zero.mp h1).resolve_right v.2.1
    exact (char_two_eq_iff_add_eq_zero (K := K) (a v.1) 1).mpr h2
  let K₂ := {c : K // c ≠ 0 ∧ c ≠ 1}
  have hK_split : Nat.card K = Nat.card K₂ + 2 := by
    let eK : Option (Option K₂) ≃ K :=
      { toFun := fun x =>
          match x with
          | none => 0
          | some none => 1
          | some (some c) => c.1
        invFun := fun c =>
          if hc0 : c = 0 then none
          else if hc1 : c = 1 then some none
          else some (some ⟨c, hc0, hc1⟩)
        left_inv := by
          rintro (_ | _ | ⟨c, hc0, hc1⟩)
          · simp
          · simp [one_ne_zero]
          · simp [hc0, hc1]
        right_inv := fun c => by
          by_cases hc0 : c = 0
          · simp [hc0]
          · by_cases hc1 : c = 1 <;> simp [hc0, hc1] }
    have hcard := (Nat.card_congr eK).symm
    let _ := Fintype.ofFinite K₂
    simp only [Nat.card_eq_fintype_card, Fintype.card_option] at hcard ⊢
    omega
  have hmul_le : (Nat.card K - 2) * Nat.card S₁ ≤ Nat.card A := by
    let mulMap : K₂ × S₁ → A := fun p =>
      ⟨p.1.1 • p.2.1, by
        have ha_cv : a (p.1.1 • p.2.1) = p.1.1 := by
          rw [ha_smul, ha_eq_one p.2, one_mul]
        have hc1 : a (p.1.1 • p.2.1) + 1 ≠ 0 := by
          rw [ha_cv]
          exact fun h => p.1.2.2 ((char_two_eq_iff_add_eq_zero (K := K) p.1.1 1).mpr h)
        exact smul_ne_zero hc1 (smul_ne_zero p.1.2.1 p.2.2.1)⟩
    have hmul_inj : Function.Injective mulMap := by
      rintro ⟨c₁, v₁⟩ ⟨c₂, v₂⟩ h
      have hval : c₁.1 • v₁.1 = c₂.1 • v₂.1 := congrArg Subtype.val h
      have ha_eq : c₁.1 = c₂.1 := by
        have h1 := congrArg a hval
        rwa [ha_smul, ha_smul, ha_eq_one v₁, ha_eq_one v₂, one_mul, one_mul] at h1
      have hc_eq : c₁ = c₂ := Subtype.ext ha_eq
      subst hc_eq
      exact Prod.ext rfl (Subtype.ext (smul_right_inj c₁.2.1 |>.mp hval))
    have hcard := Nat.card_le_card_of_injective mulMap hmul_inj
    rw [Nat.card_prod] at hcard
    have hK2 : Nat.card K - 2 = Nat.card K₂ := by omega
    rwa [hK2]
  let f : A → W := fun w => ψ w.1
  let τ : A → A := fun w =>
    if h : ψ ((1 + (a w.1)⁻¹) • w.1) ≠ 0 then ⟨(1 + (a w.1)⁻¹) • w.1, h⟩ else w
  have htwo : ∀ w₁ w₂ : A, f w₁ = f w₂ → w₂ = w₁ ∨ w₂ = τ w₁ := by
    intro w₁ w₂ hfw
    have hw₁0 : w₁.1 ≠ 0 := fun h => w₁.2 (by rw [h, hψ0])
    have ha₁ : a w₁.1 + 1 ≠ 0 := fun h =>
      w₁.2 (by change (a w₁.1 + 1) • w₁.1 = 0; rw [h, zero_smul])
    have ha₂ : a w₂.1 + 1 ≠ 0 := fun h =>
      w₂.2 (by change (a w₂.1 + 1) • w₂.1 = 0; rw [h, zero_smul])
    set s : K := (a w₂.1 + 1)⁻¹ * (a w₁.1 + 1)
    have hsw : w₂.1 = s • w₁.1 := by
      calc w₂.1 = (a w₂.1 + 1)⁻¹ • ((a w₂.1 + 1) • w₂.1) := by
            rw [smul_smul, inv_mul_cancel₀ ha₂, one_smul]
        _ = (a w₂.1 + 1)⁻¹ • ((a w₁.1 + 1) • w₁.1) := by
            change (a w₂.1 + 1)⁻¹ • f w₂ = (a w₂.1 + 1)⁻¹ • f w₁
            rw [hfw]
        _ = s • w₁.1 := by rw [smul_smul]
    have hψ_eq : (a w₁.1 * 1 ^ 2 + 1) • w₁.1 = (a w₁.1 * s ^ 2 + s) • w₁.1 := by
      calc (a w₁.1 * 1 ^ 2 + 1) • w₁.1
          = ψ w₁.1 := by rw [one_pow, mul_one]
        _ = ψ w₂.1 := hfw
        _ = (a (s • w₁.1) + 1) • (s • w₁.1) := by rw [hsw]
        _ = (a w₁.1 * s ^ 2 + s) • w₁.1 := by
          rw [ha_smul, smul_smul]
          congr 1
          ring
    have hscalar : a w₁.1 * 1 ^ 2 + 1 = a w₁.1 * s ^ 2 + s :=
      smul_left_injective K hw₁0 hψ_eq
    rcases (mul_sq_add_self_eq_iff (a w₁.1) 1 s).mp hscalar with hs1 | hs2
    · left
      exact Subtype.ext (by rw [hsw, hs1, one_smul])
    · right
      apply Subtype.ext
      have hsw' : w₂.1 = (1 + (a w₁.1)⁻¹) • w₁.1 := by rw [hsw, hs2]
      have hne : ψ ((1 + (a w₁.1)⁻¹) • w₁.1) ≠ 0 := by
        rw [← hsw']
        exact w₂.2
      change w₂.1 = (if h : ψ ((1 + (a w₁.1)⁻¹) • w₁.1) ≠ 0 then
        (⟨(1 + (a w₁.1)⁻¹) • w₁.1, h⟩ : A) else w₁).1
      simp [hne, hsw']
  have hA_le : Nat.card A ≤ 2 * Nat.card (Set.range f) :=
    card_le_two_mul_card_range_of_two_to_one f τ htwo
  have hrange_le : Nat.card (Set.range f) + 1 ≤ Nat.card (Set.range ψ) := by
    let g : Option (Set.range f) → Set.range ψ := fun x =>
      match x with
      | none => ⟨0, 0, hψ0⟩
      | some y => ⟨y.1, (Classical.choose y.2).1, Classical.choose_spec y.2⟩
    have hg_inj : Function.Injective g := by
      rintro (_ | y₁) (_ | y₂) h
      · rfl
      · exfalso
        have h0 : (0 : W) = y₂.1 := congrArg Subtype.val h
        have hy₂ := Classical.choose_spec y₂.2
        exact (Classical.choose y₂.2).2 (hy₂.trans h0.symm)
      · exfalso
        have h0 : y₁.1 = (0 : W) := congrArg Subtype.val h
        have hy₁ := Classical.choose_spec y₁.2
        exact (Classical.choose y₁.2).2 (hy₁.trans h0)
      · have hval : (g (some y₁)).1 = (g (some y₂)).1 := congrArg Subtype.val h
        exact congrArg some (Subtype.ext hval)
    have hcard := Nat.card_le_card_of_injective g hg_inj
    let _ := Fintype.ofFinite (Set.range f)
    simp only [Nat.card_eq_fintype_card, Fintype.card_option] at hcard ⊢
    exact hcard
  have h1 : (Nat.card K - 2) * (Nat.card W - 1) ≤ (Nat.card K - 1) * Nat.card A := by
    have hW1 : Nat.card W - 1 = Nat.card S₁ + Nat.card A := by omega
    rw [hW1, mul_add]
    calc (Nat.card K - 2) * Nat.card S₁ + (Nat.card K - 2) * Nat.card A
        ≤ Nat.card A + (Nat.card K - 2) * Nat.card A :=
          Nat.add_le_add_right hmul_le _
      _ = (Nat.card K - 1) * Nat.card A := by
          have hK2 : 2 ≤ Nat.card K := Finite.one_lt_card
          calc Nat.card A + (Nat.card K - 2) * Nat.card A
              = (1 + (Nat.card K - 2)) * Nat.card A := by ring
            _ = (Nat.card K - 1) * Nat.card A := by congr 1; omega
  calc (Nat.card K - 2) * (Nat.card W - 1) + 2 * (Nat.card K - 1)
      ≤ (Nat.card K - 1) * Nat.card A + 2 * (Nat.card K - 1) :=
        Nat.add_le_add_right h1 _
    _ ≤ (Nat.card K - 1) * (2 * Nat.card (Set.range f)) + 2 * (Nat.card K - 1) :=
        Nat.add_le_add_right (Nat.mul_le_mul_left _ hA_le) _
    _ = 2 * (Nat.card K - 1) * (Nat.card (Set.range f) + 1) := by ring
    _ ≤ 2 * (Nat.card K - 1) * Nat.card (Set.range ψ) :=
        Nat.mul_le_mul_left _ hrange_le

end TwoToOneBound

section PointRadicalCharacters

variable {K V : Type*} [Field K] [Finite K] [CharP K 2]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V] {B : BilinForm K V}

/-- The symplectic group `Gsp B` is finite over a finite field. -/
instance instFiniteGsp : Finite (Gsp B) := by
  have : Finite V := Module.finite_of_finite K
  exact Finite.of_injective (fun g : Gsp B => g.app) (fun _ _ h => Gsp.ext' (congrFun h))

/-- The additive automorphism of `Additive (Lsp B hB v)` induced by `conjLsp hB v n`. -/
def conjLspAddHom (hB : B.IsAlt) (v : V) (n : lineStabilizer B v) :
    Additive (Lsp B hB v) →+ Additive (Lsp B hB v) where
  toFun q := Additive.ofMul (conjLsp hB v n (Additive.toMul q))
  map_zero' := by rw [toMul_zero, map_one, ofMul_one]
  map_add' x y := by rw [toMul_add, map_mul, ofMul_mul]

/-- For `n : lineStabilizer B v`, the conjugate subgroup
`(H.subgroupOf (Lsp B hB v)).comap (conjLsp hB v n⁻¹)` whose carrier is
`conjSub H (lineStabilizer B v) (Lsp B hB v) n`. -/
def conjSubgroup (hB : B.IsAlt) (v : V) (H : Subgroup (Gsp B)) (n : lineStabilizer B v) :
    Subgroup (Lsp B hB v) :=
  (H.subgroupOf (Lsp B hB v)).comap (conjLsp hB v n⁻¹).toMonoidHom

omit [Finite K] [CharP K 2] [FiniteDimensional K V] in
theorem mem_conjSubgroup_iff (hB : B.IsAlt) (v : V) (H : Subgroup (Gsp B))
    (n : lineStabilizer B v) (q : Lsp B hB v) :
    q ∈ conjSubgroup hB v H n ↔
      q ∈ conjSub H (lineStabilizer B v) (Lsp B hB v) n :=
  Iff.rfl

omit [Finite K] [CharP K 2] [FiniteDimensional K V] in
theorem index_conjSubgroup (hB : B.IsAlt) (v : V) (H : Subgroup (Gsp B))
    (n : lineStabilizer B v) :
    (conjSubgroup hB v H n).index = (H ⊓ Lsp B hB v).relIndex (Lsp B hB v) := by
  rw [conjSubgroup, Subgroup.index_comap_of_surjective _ (conjLsp hB v n⁻¹).surjective,
    Subgroup.inf_relIndex_right]
  rfl

omit [Finite K] [FiniteDimensional K V] in
theorem index_conjSubgroup_sup_tspSubgroup (hB : B.IsAlt) (v : V) (H : Subgroup (Gsp B))
    (n : lineStabilizer B v) :
    (conjSubgroup hB v H n ⊔ tspSubgroup hB v).index =
      (H.subgroupOf (Lsp B hB v) ⊔ tspSubgroup hB v).index := by
  have hsup : conjSubgroup hB v H n ⊔ tspSubgroup hB v =
      (H.subgroupOf (Lsp B hB v) ⊔ tspSubgroup hB v).comap (conjLsp hB v n⁻¹).toMonoidHom := by
    refine le_antisymm ?_ ?_
    · refine sup_le (Subgroup.comap_mono le_sup_left) (fun q hq => ?_)
      change conjLsp hB v n⁻¹ q ∈ H.subgroupOf (Lsp B hB v) ⊔ tspSubgroup hB v
      exact Subgroup.mem_sup_right (conjLsp_mem_tspSubgroup hB v n⁻¹ hq)
    · intro q hq
      have hq' : conjLsp hB v n⁻¹ q ∈ H.subgroupOf (Lsp B hB v) ⊔ tspSubgroup hB v := hq
      have h1 : q = conjLsp hB v n (conjLsp hB v n⁻¹ q) := by
        ext1
        dsimp [conjLsp]
        group
      rw [h1]
      have hmap : H.subgroupOf (Lsp B hB v) ⊔ tspSubgroup hB v ≤
          (conjSubgroup hB v H n ⊔ tspSubgroup hB v).comap (conjLsp hB v n).toMonoidHom := by
        refine sup_le (fun k hk => ?_) (fun z hz => ?_)
        · refine Subgroup.mem_sup_left ?_
          change conjLsp hB v n⁻¹ (conjLsp hB v n k) ∈ H.subgroupOf (Lsp B hB v)
          have hk' : conjLsp hB v n⁻¹ (conjLsp hB v n k) = k := by
            ext1; dsimp [conjLsp]; group
          rwa [hk']
        · exact Subgroup.mem_sup_right (conjLsp_mem_tspSubgroup hB v n hz)
      exact hmap hq'
  rw [hsup, Subgroup.index_comap_of_surjective _ (conjLsp hB v n⁻¹).surjective]

/-- In a finite additive group `A` of exponent `2`, the number of nonzero additive characters
`A →+ ZMod 2` vanishing on `U : AddSubgroup A` is `U.index - 1`. -/
theorem card_ne_zero_addMonoidHom_vanishing_eq_index_sub_one
    {A : Type*} [AddCommGroup A] [Finite A] (h2 : ∀ x : A, 2 • x = 0) (U : AddSubgroup A) :
    Nat.card {f : A →+ ZMod 2 // f ≠ 0 ∧ ∀ x ∈ U, f x = 0} = U.index - 1 := by
  classical
  let e : Option {f : A →+ ZMod 2 // f ≠ 0 ∧ ∀ x ∈ U, f x = 0} ≃
      {f : A →+ ZMod 2 // ∀ x ∈ U, f x = 0} :=
    { toFun := fun x =>
        match x with
        | none => ⟨0, fun _ _ => rfl⟩
        | some f => ⟨f.1, f.2.2⟩
      invFun := fun f =>
        if hf : f.1 = 0 then none else some ⟨f.1, hf, f.2⟩
      left_inv := by
        rintro (_ | ⟨f, hf0, hfU⟩)
        · simp
        · simp [hf0]
      right_inv := fun ⟨f, hfU⟩ => by
        by_cases hf : f = 0
        · subst hf; simp
        · simp [hf] }
  have hcard := Nat.card_congr e
  rw [card_addMonoidHom_vanishing_eq_index h2 U] at hcard
  let _ := Fintype.ofFinite {f : A →+ ZMod 2 // f ≠ 0 ∧ ∀ x ∈ U, f x = 0}
  simp only [Nat.card_eq_fintype_card, Fintype.card_option] at hcard ⊢
  omega

/-- Case (a) index bound in `Gsp B`: if `K₀ ⊔ Z₀ ≠ ⊤`, then
`2 * Nat.card K ^ (Module.finrank K V - 2) ≤ H.index`. -/
theorem index_ge_of_case_a (hB : B.IsAlt) (hBn : B.Nondegenerate)
    {v b : V} (hb : B v b = 1) {H : Subgroup (Gsp B)}
    (hZnot : ¬ (tspSubgroup hB v ≤ H.subgroupOf (Lsp B hB v)))
    (hCaseA : H.subgroupOf (Lsp B hB v) ⊔ tspSubgroup hB v ≠ ⊤) :
    2 * Nat.card K ^ (Module.finrank K V - 2) ≤ H.index := by
  have : Finite V := Module.finite_of_finite K
  have hv0 : v ≠ 0 := by rintro rfl; simp at hb
  obtain ⟨-, hsplit⟩ := alternating_hyperbolic_splitting hB hBn hv0
  obtain ⟨-, -, hmemW, hcompl, hndW, hdimW⟩ := hsplit b hb
  set P : Submodule K V := Submodule.span K {v, b}
  set W : Submodule K V := B.orthogonal P
  have horth : ∀ p ∈ P, ∀ w ∈ W, B p w = 0 := fun p hp w hw => by
    have := (hmemW w).mp hw p hp
    rw [← hB.neg_eq w p, this, neg_zero]
  have hvP : v ∈ P := Submodule.subset_span (by simp)
  have hB' : (B.restrict W).IsAlt := isAlt_restrict hB W
  set Q := Lsp B hB v
  set N := lineStabilizer B v
  set K₀ := H.subgroupOf Q
  set Z₀ := tspSubgroup hB v
  have hR_idx : Nat.card (Set.range (conjSub H N Q)) * (H ⊓ Q).relIndex Q ≤ H.index :=
    card_range_conjSub_mul_relIndex_le_index H N Q (Lsp_le_lineStabilizer hB v)
      (lineStabilizer_normalizes_Lsp hB v) (fun _ hx _ hy => Lsp_mul_comm hB hx hy)
  set d := (K₀ ⊔ Z₀).index
  have hd_ge_two : 2 ≤ d := by
    have hne1 : d ≠ 1 := mt Subgroup.index_eq_one.mp hCaseA
    have hne0 : d ≠ 0 := Subgroup.index_ne_zero_of_finite
    omega
  have hrel_ge_two : 2 ≤ K₀.relIndex (K₀ ⊔ Z₀) := by
    have hne1 : K₀.relIndex (K₀ ⊔ Z₀) ≠ 1 := by
      rw [Ne, Subgroup.relIndex_eq_one]
      intro hle
      exact hZnot (le_sup_right.trans hle)
    have hne0 : K₀.relIndex (K₀ ⊔ Z₀) ≠ 0 := Nat.card_pos.ne'
    omega
  have hK₀_idx : 2 * d ≤ (H ⊓ Q).relIndex Q := by
    rw [Subgroup.inf_relIndex_right]
    change 2 * d ≤ K₀.index
    rw [← Subgroup.relIndex_mul_index (le_sup_left : K₀ ≤ K₀ ⊔ Z₀)]
    exact Nat.mul_le_mul_right d hrel_ge_two
  let P_A : Set Q → (W →+ ZMod 2) → Prop := fun S ψ =>
    ψ ≠ 0 ∧ ∀ q : Q, q ∈ S → ψ (projW hB hb (Additive.ofMul q)) = 0
  have hP_A_card : ∀ n : N, Nat.card {ψ : W →+ ZMod 2 // P_A (conjSub H N Q n) ψ} ≤ d - 1 := by
    intro n
    let U_n := conjSubgroup hB v H n ⊔ Z₀
    let ι : {ψ : W →+ ZMod 2 // P_A (conjSub H N Q n) ψ} →
        {φ : Additive Q →+ ZMod 2 // φ ≠ 0 ∧ ∀ x ∈ U_n.toAddSubgroup, φ x = 0} :=
      fun ψ =>
        ⟨ψ.1.comp (projW hB hb), by
          refine ⟨fun h0 => ψ.2.1 ?_, ?_⟩
          · ext w
            have h1 := congrArg (fun f : Additive Q →+ ZMod 2 =>
              f (Additive.ofMul (sspEquiv hB hb (w, 0)))) h0
            change ψ.1 (projW hB hb (Additive.ofMul (sspEquiv hB hb (w, 0)))) = 0 at h1
            rwa [projW_sspEquiv] at h1
          · intro x hx
            let K_ψ : Subgroup Q :=
              { carrier := {q : Q | ψ.1 (projW hB hb (Additive.ofMul q)) = 0}
                one_mem' := by change ψ.1 (projW hB hb 0) = 0; rw [map_zero, map_zero]
                mul_mem' := fun {q₁ q₂} hq₁ hq₂ => by
                  change ψ.1 (projW hB hb (Additive.ofMul q₁ + Additive.ofMul q₂)) = 0
                  rw [map_add, map_add, hq₁, hq₂, add_zero]
                inv_mem' := fun {q₁} hq₁ => by
                  change ψ.1 (projW hB hb (-Additive.ofMul q₁)) = 0
                  rw [map_neg, map_neg, hq₁]
                  exact neg_zero }
            have hle : U_n ≤ K_ψ := by
              refine sup_le (fun q hq => ψ.2.2 q hq) (fun q hq => ?_)
              change ψ.1 (projW hB hb (Additive.ofMul q)) = 0
              rw [(mem_tspSubgroup_iff_projW_eq_zero hB hb q).mp hq, map_zero]
            have hx' : Additive.toMul x ∈ K_ψ := hle hx
            exact hx'⟩
    have hι_inj : Function.Injective ι := by
      intro ψ₁ ψ₂ h
      have h1 : ψ₁.1.comp (projW hB hb) = ψ₂.1.comp (projW hB hb) := congrArg Subtype.val h
      apply Subtype.ext
      ext w
      have h2 := congrArg (fun f : Additive Q →+ ZMod 2 =>
        f (Additive.ofMul (sspEquiv hB hb (w, 0)))) h1
      change ψ₁.1 (projW hB hb (Additive.ofMul (sspEquiv hB hb (w, 0)))) =
        ψ₂.1 (projW hB hb (Additive.ofMul (sspEquiv hB hb (w, 0)))) at h2
      rwa [projW_sspEquiv] at h2
    calc Nat.card {ψ : W →+ ZMod 2 // P_A (conjSub H N Q n) ψ}
        ≤ Nat.card {φ : Additive Q →+ ZMod 2 // φ ≠ 0 ∧ ∀ x ∈ U_n.toAddSubgroup, φ x = 0} :=
          Nat.card_le_card_of_injective ι hι_inj
      _ = U_n.toAddSubgroup.index - 1 :=
          card_ne_zero_addMonoidHom_vanishing_eq_index_sub_one
            (two_nsmul_additive_Lsp hB v) U_n.toAddSubgroup
      _ = d - 1 := by
          change U_n.index - 1 = d - 1
          rw [index_conjSubgroup_sup_tspSubgroup]
  have hnot_top : ¬ ((⊤ : AddSubgroup (Additive Q)) ≤ (K₀ ⊔ Z₀).toAddSubgroup) := by
    intro hle
    apply hCaseA
    rw [eq_top_iff]
    intro q hq
    exact hle (AddSubgroup.mem_top (Additive.ofMul q))
  obtain ⟨φ₀, hφ₀_van, q₀, -, hφ₀_ne⟩ :=
    exists_addMonoidHom_vanishing_not_le (two_nsmul_additive_Lsp hB v) hnot_top
  let ψ₀ : W →+ ZMod 2 :=
    { toFun := fun w => φ₀ (Additive.ofMul (sspEquiv hB hb (w, 0)))
      map_zero' := by
        rw [sspEquiv_apply, sspCoord_zero, ofMul_one, map_zero]
      map_add' := fun w₁ w₂ => by
        have hmul : sspEquiv hB hb (w₁ + w₂, 0) =
            sspEquiv hB hb (w₁, 0) * sspEquiv hB hb (w₂, 0) *
              sspEquiv hB hb (0, B (w₁ : V) (w₂ : V)) := by
          simp only [sspEquiv_apply, sspCoord_mul, add_zero, zero_add, Submodule.coe_zero,
            map_zero, CharTwo.add_self_eq_zero]
        have hz : sspEquiv hB hb (0, B (w₁ : V) (w₂ : V)) ∈ Z₀ := by
          rw [mem_tspSubgroup_iff_projW_eq_zero hB hb, projW_sspEquiv]
        have hz_sup : sspEquiv hB hb (0, B (w₁ : V) (w₂ : V)) ∈ K₀ ⊔ Z₀ :=
          Subgroup.mem_sup_right hz
        have hφz : φ₀ (Additive.ofMul (sspEquiv hB hb (0, B (w₁ : V) (w₂ : V)))) = 0 :=
          hφ₀_van (Additive.ofMul _) hz_sup
        rw [hmul, ofMul_mul, ofMul_mul, map_add, map_add, hφz, add_zero] }
  have hφ₀_eq : ∀ q : Q, φ₀ (Additive.ofMul q) = ψ₀ (projW hB hb (Additive.ofMul q)) := by
    intro q
    obtain ⟨⟨w, c⟩, rfl⟩ := (sspEquiv hB hb).surjective q
    rw [projW_sspEquiv]
    have hmul : sspEquiv hB hb (w, c) = sspEquiv hB hb (w, 0) * sspEquiv hB hb (0, c) := by
      simp only [sspEquiv_apply, sspCoord_mul, add_zero, zero_add, Submodule.coe_zero, map_zero]
    have hz : sspEquiv hB hb (0, c) ∈ Z₀ := by
      rw [mem_tspSubgroup_iff_projW_eq_zero hB hb, projW_sspEquiv]
    have hz_sup : sspEquiv hB hb (0, c) ∈ K₀ ⊔ Z₀ := Subgroup.mem_sup_right hz
    have hφz : φ₀ (Additive.ofMul (sspEquiv hB hb (0, c))) = 0 :=
      hφ₀_van (Additive.ofMul _) hz_sup
    rw [hmul, ofMul_mul, map_add, hφz, add_zero]
    rfl
  have hψ₀_ne : ψ₀ ≠ 0 := by
    intro h0
    apply hφ₀_ne
    have h1 := hφ₀_eq (Additive.toMul q₀)
    rw [ofMul_toMul] at h1
    rw [h1, h0, AddMonoidHom.zero_apply]
  obtain ⟨α₀, hα₀⟩ := exists_ne_zero_addMonoidHom_zmod_two (K := K)
  obtain ⟨u₀, hu₀_eq⟩ := (bilinAddHom_bijective hα₀ hndW).2 ψ₀
  have hu₀_ne : u₀ ≠ 0 := by
    rintro rfl
    apply hψ₀_ne
    rw [← hu₀_eq]
    ext w
    simp [bilinAddHom]
  have hU_cov : ∀ ψ ∈ {ψ : W →+ ZMod 2 | ψ ≠ 0}, ∃ n : N, P_A (conjSub H N Q n) ψ := by
    intro ψ hψ
    obtain ⟨u, hu_eq⟩ := (bilinAddHom_bijective hα₀ hndW).2 ψ
    have hu_ne : u ≠ 0 := by
      rintro rfl
      apply hψ
      rw [← hu_eq]
      ext w
      simp [bilinAddHom]
    obtain ⟨g₀, hg₀⟩ := exists_gsp_apply_eq hB' hndW hu₀_ne hu_ne
    let g : Gsp B := extId hcompl hB horth g₀
    have hgv : g.app v = v := extId_app_of_mem hcompl hB horth g₀ hvP
    let n : N := ⟨g, mem_lineStabilizer_of_app_eq_self hgv⟩
    refine ⟨n, hψ, fun q hq => ?_⟩
    obtain ⟨⟨w, c⟩, rfl⟩ := (sspEquiv hB hb).surjective q
    rw [projW_sspEquiv]
    have hconj : conjLsp hB v n⁻¹ (sspEquiv hB hb (w, c)) = sspEquiv hB hb (g₀⁻¹.app w, c) := by
      ext1
      change g⁻¹ * Ssp hB v (w : V) c * g⁻¹⁻¹ = Ssp hB v (g₀⁻¹.app w : V) c
      have hg_inv : g⁻¹ = extId hcompl hB horth g₀⁻¹ := (map_inv _ g₀).symm
      have hgv_inv : g⁻¹.app v = v := by
        rw [hg_inv]
        exact extId_app_of_mem hcompl hB horth g₀⁻¹ hvP
      have hgw_inv : g⁻¹.app (w : V) = (g₀⁻¹.app w : V) := by
        rw [hg_inv]
        simpa using extId_app hcompl hB horth g₀⁻¹ P.zero_mem w.2
      rw [Ssp_conj, hgv_inv, hgw_inv]
    have hq_mem : conjLsp hB v n⁻¹ (sspEquiv hB hb (w, c)) ∈ K₀ := hq
    have hq_sup : conjLsp hB v n⁻¹ (sspEquiv hB hb (w, c)) ∈ K₀ ⊔ Z₀ :=
      Subgroup.mem_sup_left hq_mem
    have hvan : φ₀ (Additive.ofMul (conjLsp hB v n⁻¹ (sspEquiv hB hb (w, c)))) = 0 :=
      hφ₀_van (Additive.ofMul _) hq_sup
    rw [hconj, hφ₀_eq, projW_sspEquiv, ← hu₀_eq, bilinAddHom_apply] at hvan
    rw [← hu_eq, bilinAddHom_apply, ← hg₀]
    have hform : (B.restrict W) w (g₀.app u₀) = (B.restrict W) (g₀⁻¹.app w) u₀ := by
      calc (B.restrict W) w (g₀.app u₀)
          = (B.restrict W) (g₀.app (g₀⁻¹.app w)) (g₀.app u₀) := by rw [Gsp.app_app_inv]
        _ = (B.restrict W) (g₀⁻¹.app w) u₀ := g₀.2 _ _
    rw [hform]
    exact hvan
  have hcard_U : Nat.card W - 1 ≤ Nat.card (Set.range (conjSub H N Q)) * (d - 1) := by
    have h1 := card_le_card_range_mul_of_forall_le (conjSub H N Q) P_A
      {ψ : W →+ ZMod 2 | ψ ≠ 0} (d - 1) hU_cov hP_A_card
    have h2 := card_ne_zero_addMonoidHom_vanishing_eq_index_sub_one
      (two_nsmul_eq_zero_of_char_two (K := K) (M := W)) (⊥ : AddSubgroup W)
    have hbot : (⊥ : AddSubgroup W).index = Nat.card W := by
      rw [AddSubgroup.index_bot]
    have heq : Nat.card {ψ : W →+ ZMod 2 | ψ ≠ 0} =
        Nat.card {f : W →+ ZMod 2 // f ≠ 0 ∧ ∀ x ∈ (⊥ : AddSubgroup W), f x = 0} := by
      refine Nat.card_congr
        { toFun := fun f => ⟨f.1, f.2, fun x hx => by rw [AddSubgroup.mem_bot.mp hx, map_zero]⟩
          invFun := fun f => ⟨f.1, f.2.1⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
    rw [heq, h2, hbot] at h1
    exact h1
  have hR_pos : 1 ≤ Nat.card (Set.range (conjSub H N Q)) := by
    have : Nonempty (Set.range (conjSub H N Q)) := ⟨⟨conjSub H N Q 1, 1, rfl⟩⟩
    exact Finite.card_pos
  have hW_card : Nat.card W = Nat.card K ^ (Module.finrank K V - 2) := by
    rw [Module.natCard_eq_pow_finrank (K := K), hdimW]
  have h2W : 2 * Nat.card W ≤ Nat.card (Set.range (conjSub H N Q)) * (2 * d) := by
    have hRd : Nat.card W ≤ Nat.card (Set.range (conjSub H N Q)) * d := by
      have : Nat.card (Set.range (conjSub H N Q)) * d =
          Nat.card (Set.range (conjSub H N Q)) * (d - 1) +
            Nat.card (Set.range (conjSub H N Q)) := by
        calc Nat.card (Set.range (conjSub H N Q)) * d
            = Nat.card (Set.range (conjSub H N Q)) * (d - 1 + 1) := by
              congr 1; omega
          _ = Nat.card (Set.range (conjSub H N Q)) * (d - 1) +
                Nat.card (Set.range (conjSub H N Q)) := by ring
      omega
    calc 2 * Nat.card W ≤ 2 * (Nat.card (Set.range (conjSub H N Q)) * d) :=
          Nat.mul_le_mul_left 2 hRd
      _ = Nat.card (Set.range (conjSub H N Q)) * (2 * d) := by ring
  rw [← hW_card]
  exact h2W.trans ((Nat.mul_le_mul_left _ hK₀_idx).trans hR_idx)

/-- Case (b) index bound in `Gsp B` when `Nat.card K = 2`: if `K₀ ⊔ Z₀ = ⊤`, then
`2 ^ (2 * m) - 2 ^ m ≤ H.index`. -/
theorem index_ge_of_case_b_two {m : ℕ} (hm : 1 ≤ m) (hK : Nat.card K = 2)
    (hB : B.IsAlt) (hBn : B.Nondegenerate) (hdim : Module.finrank K V = 2 * (m + 1))
    {v b : V} (hb : B v b = 1) {H : Subgroup (Gsp B)}
    (hZnot : ¬ (tspSubgroup hB v ≤ H.subgroupOf (Lsp B hB v)))
    (hCaseB : H.subgroupOf (Lsp B hB v) ⊔ tspSubgroup hB v = ⊤) :
    2 ^ (2 * m) - 2 ^ m ≤ H.index := by
  have : Finite V := Module.finite_of_finite K
  have hv0 : v ≠ 0 := by rintro rfl; simp at hb
  obtain ⟨-, hsplit⟩ := alternating_hyperbolic_splitting hB hBn hv0
  obtain ⟨-, -, hmemW, -, hndW, hdimW⟩ := hsplit b hb
  set P : Submodule K V := Submodule.span K {v, b}
  set W : Submodule K V := B.orthogonal P
  have hWv : ∀ w : W, B v (w : V) = 0 := fun w =>
    (isAlt_symm_of_char_two hB (w : V) v).symm.trans
      ((hmemW w).mp w.2 v (Submodule.subset_span (by simp)))
  have hB' : (B.restrict W).IsAlt := isAlt_restrict hB W
  have hdim' : Module.finrank K W = 2 * m := by rw [hdimW, hdim]; omega
  set Q := Lsp B hB v
  set N := lineStabilizer B v
  set K₀ := H.subgroupOf Q
  set Z₀ := tspSubgroup hB v
  have hR_idx : Nat.card (Set.range (conjSub H N Q)) * (H ⊓ Q).relIndex Q ≤ H.index :=
    card_range_conjSub_mul_relIndex_le_index H N Q (Lsp_le_lineStabilizer hB v)
      (lineStabilizer_normalizes_Lsp hB v) (fun _ hx _ hy => Lsp_mul_comm hB hx hy)
  have hZ₀_card : Nat.card Z₀ = 2 := by
    let eZ : K ≃ Z₀ :=
      { toFun := fun c => ⟨sspEquiv hB hb (0, c), by
          rw [mem_tspSubgroup_iff_projW_eq_zero hB hb, projW_sspEquiv]⟩
        invFun := fun z => ((sspEquiv hB hb).symm z.1).2
        left_inv := fun c => by
          change ((sspEquiv hB hb).symm (sspEquiv hB hb (0, c))).2 = c
          rw [Equiv.symm_apply_apply]
        right_inv := fun ⟨z, hz⟩ => by
          obtain ⟨⟨w, c⟩, rfl⟩ := (sspEquiv hB hb).surjective z
          have hw0 : w = 0 := by
            have := (mem_tspSubgroup_iff_projW_eq_zero hB hb (sspEquiv hB hb (w, c))).mp hz
            rwa [projW_sspEquiv] at this
          subst hw0
          ext1
          change sspEquiv hB hb (0, ((sspEquiv hB hb).symm (sspEquiv hB hb (0, c))).2) =
            sspEquiv hB hb (0, c)
          rw [Equiv.symm_apply_apply] }
    rw [← Nat.card_congr eZ, hK]
  have hK₀_le_two : K₀.index ≤ 2 := by
    have h1 : K₀.index = K₀.relIndex (Z₀ ⊔ K₀) := by
      rw [sup_comm, hCaseB, Subgroup.relIndex_top_right]
    rw [h1, Subgroup.relIndex_sup_right]
    calc K₀.relIndex Z₀ = (K₀.subgroupOf Z₀).index := rfl
      _ ≤ Nat.card Z₀ :=
          Nat.card_le_card_of_surjective
            (QuotientGroup.mk : Z₀ → Z₀ ⧸ K₀.subgroupOf Z₀) QuotientGroup.mk_surjective
      _ = 2 := hZ₀_card
  have hK₀_ge_two : 2 ≤ K₀.index := by
    have hne1 : K₀.index ≠ 1 := by
      rw [Ne, Subgroup.index_eq_one]
      intro htop
      exact hZnot (htop.symm ▸ le_top)
    have hne0 : K₀.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    omega
  have hK₀_eq_two : K₀.index = 2 := le_antisymm hK₀_le_two hK₀_ge_two
  let P_B : Set Q → (Additive Q →+ ZMod 2) → Prop := fun S φ =>
    φ ≠ 0 ∧ ∀ q : Q, q ∈ S → φ (Additive.ofMul q) = 0
  have hP_B_card : ∀ n : N, Nat.card {φ : Additive Q →+ ZMod 2 // P_B (conjSub H N Q n) φ} ≤ 1 := by
    intro n
    have h1 := card_ne_zero_addMonoidHom_vanishing_eq_index_sub_one
      (two_nsmul_additive_Lsp hB v) (conjSubgroup hB v H n).toAddSubgroup
    have h2 : (conjSubgroup hB v H n).toAddSubgroup.index = 2 := by
      change (conjSubgroup hB v H n).index = 2
      rw [index_conjSubgroup, Subgroup.inf_relIndex_right]
      exact hK₀_eq_two
    rw [h2] at h1
    exact h1.le
  obtain ⟨φ₀, hφ₀_van, z₀, hz₀_mem, hφ₀_ne⟩ :=
    exists_addMonoidHom_vanishing_not_le (two_nsmul_additive_Lsp hB v)
      (show ¬ (Z₀.toAddSubgroup ≤ K₀.toAddSubgroup) from hZnot)
  let orbChar : N → (Additive Q →+ ZMod 2) := fun n =>
    φ₀.comp (conjLspAddHom hB v n⁻¹)
  have horb_le : Nat.card (Set.range orbChar) ≤ Nat.card (Set.range (conjSub H N Q)) * 1 := by
    refine card_le_card_range_mul_of_forall_le (conjSub H N Q) P_B
      (Set.range orbChar) 1 (fun φ hφ => ?_) hP_B_card
    obtain ⟨n, rfl⟩ := hφ
    refine ⟨n, ?_, fun q hq => hφ₀_van (Additive.ofMul (conjLsp hB v n⁻¹ q)) hq⟩
    intro h0
    apply hφ₀_ne
    have h1 := congrArg (fun f : Additive Q →+ ZMod 2 =>
      f (Additive.ofMul (conjLsp hB v n (Additive.toMul z₀)))) h0
    have h2 : conjLsp hB v n⁻¹ (conjLsp hB v n (Additive.toMul z₀)) = Additive.toMul z₀ := by
      ext1; dsimp [conjLsp]; group
    change φ₀ (Additive.ofMul (conjLsp hB v n⁻¹ (conjLsp hB v n (Additive.toMul z₀)))) = 0 at h1
    rwa [h2, ofMul_toMul] at h1
  let α₀ : K →+ ZMod 2 :=
    { toFun := fun c => φ₀ (Additive.ofMul (sspEquiv hB hb (0, c)))
      map_zero' := by rw [sspEquiv_apply, sspCoord_zero, ofMul_one, map_zero]
      map_add' := fun c₁ c₂ => by
        have hmul : sspEquiv hB hb (0, c₁ + c₂) =
            sspEquiv hB hb (0, c₁) * sspEquiv hB hb (0, c₂) := by
          simp only [sspEquiv_apply, sspCoord_mul, add_zero, Submodule.coe_zero, map_zero]
        rw [hmul, ofMul_mul, map_add] }
  have hα₀ : α₀ ≠ 0 := by
    intro h0
    apply hφ₀_ne
    obtain ⟨⟨w, c⟩, hwc⟩ := (sspEquiv hB hb).surjective (Additive.toMul z₀)
    have hw0 : w = 0 := by
      have := (mem_tspSubgroup_iff_projW_eq_zero hB hb (Additive.toMul z₀)).mp hz₀_mem
      rwa [← hwc, projW_sspEquiv] at this
    subst hw0
    have h1 := congrArg (fun f : K →+ ZMod 2 => f c) h0
    change φ₀ (Additive.ofMul (sspEquiv hB hb (0, c))) = 0 at h1
    rwa [hwc, ofMul_toMul] at h1
  let η : W → ZMod 2 := fun w => φ₀ (Additive.ofMul (sspEquiv hB hb (w, 0)))
  have hη0 : η 0 = 0 := by
    change φ₀ (Additive.ofMul (sspEquiv hB hb (0, 0))) = 0
    rw [sspEquiv_apply, sspCoord_zero, ofMul_one, map_zero]
  have hη_polar : ∀ x y : W, η (x + y) = η x + η y + α₀ ((B.restrict W) x y) := by
    intro x y
    have hmul : sspEquiv hB hb (x, 0) * sspEquiv hB hb (y, 0) =
        sspEquiv hB hb (x + y, 0) * sspEquiv hB hb (0, (B.restrict W) x y) := by
      simp only [sspEquiv_apply, sspCoord_mul, add_zero, zero_add, Submodule.coe_zero, map_zero]
      rfl
    have h1 : φ₀ (Additive.ofMul (sspEquiv hB hb (x, 0) * sspEquiv hB hb (y, 0))) =
        η x + η y := map_add φ₀ _ _
    have h2 : φ₀ (Additive.ofMul (sspEquiv hB hb (x + y, 0) *
        sspEquiv hB hb (0, (B.restrict W) x y))) =
        η (x + y) + α₀ ((B.restrict W) x y) := map_add φ₀ _ _
    rw [hmul] at h1
    have h3 : η (x + y) + α₀ ((B.restrict W) x y) = η x + η y := h2.symm.trans h1
    rw [← h3, add_assoc, CharTwo.add_self_eq_zero, add_zero]
  have hzeros :=
    two_pow_le_card_zeros_of_quad hK hα₀ hm (B.restrict W) hB' hndW hdim' η hη0 hη_polar
  let n_tsp (u : W) : N :=
    ⟨Tsp hB (u : V) 1, mem_lineStabilizer_of_app_eq_self (by
      rw [Tsp_app, hWv u, mul_zero, zero_smul, add_zero])⟩
  let ιZ : {u : W // η u = 0} → Set.range orbChar := fun u =>
    ⟨orbChar (n_tsp u.1), n_tsp u.1, rfl⟩
  have hιZ_inj : Function.Injective ιZ := by
    intro u₁ u₂ h
    have h1 : orbChar (n_tsp u₁.1) = orbChar (n_tsp u₂.1) :=
      congrArg Subtype.val h
    have h_act : ∀ (u : {u : W // η u = 0}) (w : W),
        orbChar (n_tsp u.1) (Additive.ofMul (sspEquiv hB hb (w, 0))) =
          η w + bilinAddHom α₀ (B.restrict W) u.1 w := by
      intro u w
      have hconj : conjLsp hB v (n_tsp u.1)⁻¹ (sspEquiv hB hb (w, 0)) =
          sspEquiv hB hb (w + ((B.restrict W) w u.1) • u.1, 0) := by
        ext1
        change (Tsp hB (u.1 : V) 1)⁻¹ * Ssp hB v (w : V) 0 * (Tsp hB (u.1 : V) 1)⁻¹⁻¹ =
          Ssp hB v ((w + ((B.restrict W) w u.1) • u.1 : W) : V) 0
        have hinv : (Tsp hB (u.1 : V) 1)⁻¹ = Tsp hB (u.1 : V) 1 :=
          inv_eq_iff_mul_eq_one.mpr (Tsp_mul_self hB (u.1 : V) 1)
        rw [hinv, Tsp_conj_Ssp hB (hWv u.1) (w : V) 1 0, one_mul]
        rfl
      change φ₀ (Additive.ofMul (conjLsp hB v (n_tsp u.1)⁻¹ (sspEquiv hB hb (w, 0)))) = _
      rw [hconj]
      change η (w + ((B.restrict W) w u.1) • u.1) = _
      rw [hη_polar, bilinAddHom_apply]
      set t := (B.restrict W) w u.1
      rcases eq_zero_or_eq_one_of_natCard_two hK t with ht0 | ht1
      · rw [ht0, zero_smul, hη0, map_zero, add_zero]
      · rw [ht1, one_smul, u.2, add_zero, ← ht1]
    have hbilin : bilinAddHom α₀ (B.restrict W) u₁.1 = bilinAddHom α₀ (B.restrict W) u₂.1 := by
      ext w
      have hw := congrArg (fun f : Additive Q →+ ZMod 2 =>
        f (Additive.ofMul (sspEquiv hB hb (w, 0)))) h1
      rw [h_act u₁ w, h_act u₂ w] at hw
      exact add_left_cancel hw
    exact Subtype.ext ((bilinAddHom_bijective hα₀ hndW).1 hbilin)
  have hcard_zeros_le : Nat.card {u : W // η u = 0} ≤ Nat.card (Set.range (conjSub H N Q)) := by
    calc Nat.card {u : W // η u = 0}
        ≤ Nat.card (Set.range orbChar) := Nat.card_le_card_of_injective ιZ hιZ_inj
      _ ≤ Nat.card (Set.range (conjSub H N Q)) * 1 := horb_le
      _ = Nat.card (Set.range (conjSub H N Q)) := mul_one _
  have hrel_eq_two : (H ⊓ Q).relIndex Q = 2 := by
    rw [Subgroup.inf_relIndex_right]
    exact hK₀_eq_two
  rw [hrel_eq_two] at hR_idx
  have hpow : 2 ^ (2 * m) - 2 ^ m = (2 ^ (2 * m - 1) - 2 ^ (m - 1)) * 2 := by
    have h1 : 2 ^ (2 * m) = 2 ^ (2 * m - 1) * 2 := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega)]
    have h2 : 2 ^ m = 2 ^ (m - 1) * 2 := by
      rw [← pow_succ, Nat.sub_add_cancel hm]
    omega
  rw [hpow]
  exact (Nat.mul_le_mul_right 2 (hzeros.trans hcard_zeros_le)).trans hR_idx

/-- In Case (b) (`K₀ ⊔ Z₀ = ⊤`), there exists a map `a : W → K` satisfying `a (s • w) = a w * s`
such that `Nat.card K * Nat.card (Set.range fun w => (a w + 1) • w) ≤ H.index`. -/
theorem card_mul_range_psi_le_index_of_case_b
    (hB : B.IsAlt) (hBn : B.Nondegenerate)
    {v b : V} (hb : B v b = 1) {H : Subgroup (Gsp B)}
    (hZnot : ¬ (tspSubgroup hB v ≤ H.subgroupOf (Lsp B hB v)))
    (hCaseB : H.subgroupOf (Lsp B hB v) ⊔ tspSubgroup hB v = ⊤) :
    ∃ a : B.orthogonal (Submodule.span K {v, b}) → K,
      (∀ (s : K) (w : B.orthogonal (Submodule.span K {v, b})), a (s • w) = a w * s) ∧
      Nat.card K * Nat.card (Set.range fun w => (a w + 1) • w) ≤ H.index := by
  have : Finite V := Module.finite_of_finite K
  have hv0 : v ≠ 0 := by rintro rfl; simp at hb
  obtain ⟨-, hsplit⟩ := alternating_hyperbolic_splitting hB hBn hv0
  obtain ⟨-, -, hmemW, -, hndW, -⟩ := hsplit b hb
  set P : Submodule K V := Submodule.span K {v, b}
  set W : Submodule K V := B.orthogonal P
  have hWv : ∀ w : W, B v (w : V) = 0 := fun w =>
    (isAlt_symm_of_char_two hB (w : V) v).symm.trans
      ((hmemW w).mp w.2 v (Submodule.subset_span (by simp)))
  have hWb : ∀ w : W, B b (w : V) = 0 := fun w =>
    (isAlt_symm_of_char_two hB (w : V) b).symm.trans
      ((hmemW w).mp w.2 b (Submodule.subset_span (by simp)))
  have hB' : (B.restrict W).IsAlt := isAlt_restrict hB W
  set Q := Lsp B hB v
  set N := lineStabilizer B v
  set K₀ := H.subgroupOf Q
  set Z₀ := tspSubgroup hB v
  have hR_idx : Nat.card (Set.range (conjSub H N Q)) * (H ⊓ Q).relIndex Q ≤ H.index :=
    card_range_conjSub_mul_relIndex_le_index H N Q (Lsp_le_lineStabilizer hB v)
      (lineStabilizer_normalizes_Lsp hB v) (fun _ hx _ hy => Lsp_mul_comm hB hx hy)
  have hZ₀_card : Nat.card Z₀ = Nat.card K := by
    let eZ : K ≃ Z₀ :=
      { toFun := fun c => ⟨sspEquiv hB hb (0, c), by
          rw [mem_tspSubgroup_iff_projW_eq_zero hB hb, projW_sspEquiv]⟩
        invFun := fun z => ((sspEquiv hB hb).symm z.1).2
        left_inv := fun c => by
          change ((sspEquiv hB hb).symm (sspEquiv hB hb (0, c))).2 = c
          rw [Equiv.symm_apply_apply]
        right_inv := fun ⟨z, hz⟩ => by
          obtain ⟨⟨w, c⟩, rfl⟩ := (sspEquiv hB hb).surjective z
          have hw0 : w = 0 := by
            have := (mem_tspSubgroup_iff_projW_eq_zero hB hb (sspEquiv hB hb (w, c))).mp hz
            rwa [projW_sspEquiv] at this
          subst hw0
          ext1
          change sspEquiv hB hb (0, ((sspEquiv hB hb).symm (sspEquiv hB hb (0, c))).2) =
            sspEquiv hB hb (0, c)
          rw [Equiv.symm_apply_apply] }
    exact (Nat.card_congr eZ).symm
  have hK₀_le : K₀.index ≤ Nat.card K := by
    have h1 : K₀.index = K₀.relIndex (Z₀ ⊔ K₀) := by
      rw [sup_comm, hCaseB, Subgroup.relIndex_top_right]
    rw [h1, Subgroup.relIndex_sup_right]
    calc K₀.relIndex Z₀ = (K₀.subgroupOf Z₀).index := rfl
      _ ≤ Nat.card Z₀ :=
          Nat.card_le_card_of_surjective
            (QuotientGroup.mk : Z₀ → Z₀ ⧸ K₀.subgroupOf Z₀) QuotientGroup.mk_surjective
      _ = Nat.card K := hZ₀_card
  have hK₀_ge_two : 2 ≤ K₀.index := by
    have hne1 : K₀.index ≠ 1 := by
      rw [Ne, Subgroup.index_eq_one]
      intro htop
      exact hZnot (htop.symm ▸ le_top)
    have hne0 : K₀.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    omega
  let P_B : Set Q → (Additive Q →+ ZMod 2) → Prop := fun S φ =>
    φ ≠ 0 ∧ ∀ q : Q, q ∈ S → φ (Additive.ofMul q) = 0
  have hP_B_card : ∀ n : N,
      Nat.card {φ : Additive Q →+ ZMod 2 // P_B (conjSub H N Q n) φ} ≤ K₀.index - 1 := by
    intro n
    have h1 := card_ne_zero_addMonoidHom_vanishing_eq_index_sub_one
      (two_nsmul_additive_Lsp hB v) (conjSubgroup hB v H n).toAddSubgroup
    have h2 : (conjSubgroup hB v H n).toAddSubgroup.index = K₀.index := by
      change (conjSubgroup hB v H n).index = K₀.index
      rw [index_conjSubgroup, Subgroup.inf_relIndex_right]
      rfl
    rw [h2] at h1
    exact h1.le
  obtain ⟨φ₀, hφ₀_van, z₀, hz₀_mem, hφ₀_ne⟩ :=
    exists_addMonoidHom_vanishing_not_le (two_nsmul_additive_Lsp hB v)
      (show ¬ (Z₀.toAddSubgroup ≤ K₀.toAddSubgroup) from hZnot)
  let orbChar : N → (Additive Q →+ ZMod 2) := fun n =>
    φ₀.comp (conjLspAddHom hB v n⁻¹)
  have horb_le : Nat.card (Set.range orbChar) ≤
      Nat.card (Set.range (conjSub H N Q)) * (K₀.index - 1) := by
    refine card_le_card_range_mul_of_forall_le (conjSub H N Q) P_B
      (Set.range orbChar) (K₀.index - 1) (fun φ hφ => ?_) hP_B_card
    obtain ⟨n, rfl⟩ := hφ
    refine ⟨n, ?_, fun q hq => hφ₀_van (Additive.ofMul (conjLsp hB v n⁻¹ q)) hq⟩
    intro h0
    apply hφ₀_ne
    have h1 := congrArg (fun f : Additive Q →+ ZMod 2 =>
      f (Additive.ofMul (conjLsp hB v n (Additive.toMul z₀)))) h0
    have h2 : conjLsp hB v n⁻¹ (conjLsp hB v n (Additive.toMul z₀)) = Additive.toMul z₀ := by
      ext1; dsimp [conjLsp]; group
    change φ₀ (Additive.ofMul (conjLsp hB v n⁻¹ (conjLsp hB v n (Additive.toMul z₀)))) = 0 at h1
    rwa [h2, ofMul_toMul] at h1
  have hk_ineq : Nat.card K * (K₀.index - 1) ≤ (Nat.card K - 1) * K₀.index := by
    set k' := K₀.index - 1
    set q' := Nat.card K - 1
    have hk_eq : K₀.index = k' + 1 := by omega
    have hq_eq : Nat.card K = q' + 1 := by omega
    have hle : k' ≤ q' := by omega
    calc Nat.card K * (K₀.index - 1)
        = (q' + 1) * k' := by rw [hq_eq]
      _ = q' * k' + k' := by ring
      _ ≤ q' * k' + q' := Nat.add_le_add_left hle _
      _ = q' * (k' + 1) := by ring
      _ = (Nat.card K - 1) * K₀.index := by rw [← hk_eq]
  have hK_orb_le : Nat.card K * Nat.card (Set.range orbChar) ≤ (Nat.card K - 1) * H.index := by
    calc Nat.card K * Nat.card (Set.range orbChar)
        ≤ Nat.card K * (Nat.card (Set.range (conjSub H N Q)) * (K₀.index - 1)) :=
          Nat.mul_le_mul_left _ horb_le
      _ = Nat.card (Set.range (conjSub H N Q)) * (Nat.card K * (K₀.index - 1)) := by ring
      _ ≤ Nat.card (Set.range (conjSub H N Q)) * ((Nat.card K - 1) * K₀.index) :=
          Nat.mul_le_mul_left _ hk_ineq
      _ = (Nat.card K - 1) * (Nat.card (Set.range (conjSub H N Q)) * (H ⊓ Q).relIndex Q) := by
          have hrel : K₀.index = (H ⊓ Q).relIndex Q := (Subgroup.inf_relIndex_right H Q).symm
          rw [hrel]
          ring
      _ ≤ (Nat.card K - 1) * H.index := Nat.mul_le_mul_left _ hR_idx
  let α₀ : K →+ ZMod 2 :=
    { toFun := fun c => φ₀ (Additive.ofMul (sspEquiv hB hb (0, c)))
      map_zero' := by rw [sspEquiv_apply, sspCoord_zero, ofMul_one, map_zero]
      map_add' := fun c₁ c₂ => by
        have hmul : sspEquiv hB hb (0, c₁ + c₂) =
            sspEquiv hB hb (0, c₁) * sspEquiv hB hb (0, c₂) := by
          simp only [sspEquiv_apply, sspCoord_mul, add_zero, Submodule.coe_zero, map_zero]
        rw [hmul, ofMul_mul, map_add] }
  have hα₀ : α₀ ≠ 0 := by
    intro h0
    apply hφ₀_ne
    obtain ⟨⟨w, c⟩, hwc⟩ := (sspEquiv hB hb).surjective (Additive.toMul z₀)
    have hw0 : w = 0 := by
      have := (mem_tspSubgroup_iff_projW_eq_zero hB hb (Additive.toMul z₀)).mp hz₀_mem
      rwa [← hwc, projW_sspEquiv] at this
    subst hw0
    have h1 := congrArg (fun f : K →+ ZMod 2 => f c) h0
    change φ₀ (Additive.ofMul (sspEquiv hB hb (0, c))) = 0 at h1
    rwa [hwc, ofMul_toMul] at h1
  let η : W → ZMod 2 := fun w => φ₀ (Additive.ofMul (sspEquiv hB hb (w, 0)))
  have hη0 : η 0 = 0 := by
    change φ₀ (Additive.ofMul (sspEquiv hB hb (0, 0))) = 0
    rw [sspEquiv_apply, sspCoord_zero, ofMul_one, map_zero]
  have hη_polar : ∀ x y : W, η (x + y) = η x + η y + α₀ ((B.restrict W) x y) := by
    intro x y
    have hmul : sspEquiv hB hb (x, 0) * sspEquiv hB hb (y, 0) =
        sspEquiv hB hb (x + y, 0) * sspEquiv hB hb (0, (B.restrict W) x y) := by
      simp only [sspEquiv_apply, sspCoord_mul, add_zero, zero_add, Submodule.coe_zero, map_zero]
      rfl
    have h1 : φ₀ (Additive.ofMul (sspEquiv hB hb (x, 0) * sspEquiv hB hb (y, 0))) =
        η x + η y := map_add φ₀ _ _
    have h2 : φ₀ (Additive.ofMul (sspEquiv hB hb (x + y, 0) *
        sspEquiv hB hb (0, (B.restrict W) x y))) =
        η (x + y) + α₀ ((B.restrict W) x y) := map_add φ₀ _ _
    rw [hmul] at h1
    have h3 : η (x + y) + α₀ ((B.restrict W) x y) = η x + η y := h2.symm.trans h1
    rw [← h3, add_assoc, CharTwo.add_self_eq_zero, add_zero]
  let α₁ : K →+ ZMod 2 := sqMulAddHom α₀ 1
  have hα₁ : α₁ ≠ 0 := by
    intro h0
    have h1 : sqMulAddHom α₀ 1 = sqMulAddHom α₀ 0 := by
      ext t
      change α₁ t = sqMulAddHom α₀ 0 t
      rw [h0]
      simp [sqMulAddHom]
    exact one_ne_zero ((sqMulAddHom_bijective hα₀).1 h1)
  have hbij_lin : Function.Bijective (fun c : K => sqMulAddHom α₀ (c ^ 2)) :=
    (sqMulAddHom_bijective hα₀).comp sq_bijective_of_char_two
  let ηScalar (u : W) : K →+ ZMod 2 :=
    { toFun := fun t => η (t • u)
      map_zero' := by rw [zero_smul, hη0]
      map_add' := fun t₁ t₂ => by
        rw [add_smul, hη_polar]
        have hself : (B.restrict W) (t₁ • u) (t₂ • u) = 0 := by
          simp [hB.self_eq_zero (u : V)]
        rw [hself, map_zero, add_zero] }
  let a : W → K := fun u => Classical.choose (hbij_lin.2 (ηScalar u))
  have ha_spec : ∀ (u : W) (t : K), η (t • u) = α₁ (a u * t) := by
    intro u t
    have h1 := congrArg (fun f : K →+ ZMod 2 => f t)
      (Classical.choose_spec (hbij_lin.2 (ηScalar u)))
    change α₀ ((a u) ^ 2 * t ^ 2) = η (t • u) at h1
    rw [← h1]
    change α₀ ((a u) ^ 2 * t ^ 2) = α₀ (1 * (a u * t) ^ 2)
    congr 1
    ring
  have ha_smul : ∀ (s : K) (u : W), a (s • u) = a u * s := by
    intro s u
    apply hbij_lin.1
    ext t
    have h1 := ha_spec (s • u) t
    have h2 := ha_spec u (s * t)
    rw [smul_smul, mul_comm t s] at h1
    have h3 : α₁ (a (s • u) * t) = α₁ ((a u * s) * t) := by
      rw [← h1, h2, mul_assoc]
    change α₀ ((a (s • u)) ^ 2 * t ^ 2) = α₀ ((a u * s) ^ 2 * t ^ 2)
    have h4 : α₀ ((a (s • u)) ^ 2 * t ^ 2) = α₁ (a (s • u) * t) := by
      change α₀ ((a (s • u)) ^ 2 * t ^ 2) = α₀ (1 * (a (s • u) * t) ^ 2); congr 1; ring
    have h5 : α₀ ((a u * s) ^ 2 * t ^ 2) = α₁ ((a u * s) * t) := by
      change α₀ ((a u * s) ^ 2 * t ^ 2) = α₀ (1 * ((a u * s) * t) ^ 2); congr 1; ring
    rw [h4, h5, h3]
  set ψ : W → W := fun u => (a u + 1) • u
  have hη_tsp : ∀ (u w : W),
      η (w + ((B.restrict W) w u) • u) = η w + bilinAddHom α₁ (B.restrict W) (ψ u) w := by
    intro u w
    set t := (B.restrict W) w u
    rw [hη_polar, ha_spec u t, bilinAddHom_apply]
    have hbw : (B.restrict W) w (ψ u) = (a u + 1) * t := by
      change (B.restrict W) w ((a u + 1) • u) = (a u + 1) * t
      rw [map_smul, smul_eq_mul]
    have ht2 : α₀ ((B.restrict W) w (t • u)) = α₁ (1 * t) := by
      change α₀ ((B.restrict W) w (t • u)) = α₀ (1 * (1 * t) ^ 2)
      congr 1
      rw [map_smul, smul_eq_mul]
      change t * t = 1 * (1 * t) ^ 2
      ring
    rw [ht2, hbw, add_assoc, ← map_add, ← add_mul]
  let n_tsp (u : W) : N :=
    ⟨Tsp hB (u : V) 1, mem_lineStabilizer_of_app_eq_self (by
      rw [Tsp_app, hWv u, mul_zero, zero_smul, add_zero])⟩
  let n_torus (s : {s : K // s ≠ 0}) : N :=
    ⟨torusSp hB v b s.1, torusSp_mem_lineStabilizer hB hb s.2⟩
  let n_pair (s : {s : K // s ≠ 0}) (u : W) : N := (n_tsp u * n_torus s)⁻¹
  have h_act_z : ∀ (s : {s : K // s ≠ 0}) (u : W) (t : K),
      orbChar (n_pair s u) (Additive.ofMul (sspEquiv hB hb (0, t ^ 2))) =
        sqMulAddHom α₀ (s.1 ^ 2) t := by
    intro s u t
    have hconj : conjLsp hB v (n_pair s u)⁻¹ (sspEquiv hB hb (0, t ^ 2)) =
        sspEquiv hB hb (0, s.1 ^ 2 * t ^ 2) := by
      ext1
      change ((n_tsp u * n_torus s)⁻¹⁻¹ : N).1 * Ssp hB v 0 (t ^ 2) *
        (((n_tsp u * n_torus s)⁻¹⁻¹ : N).1)⁻¹ = Ssp hB v 0 (s.1 ^ 2 * t ^ 2)
      rw [inv_inv]
      change Tsp hB (u : V) 1 * torusSp hB v b s.1 * Ssp hB v 0 (t ^ 2) *
        (Tsp hB (u : V) 1 * torusSp hB v b s.1)⁻¹ = Ssp hB v 0 (s.1 ^ 2 * t ^ 2)
      have hmul : Tsp hB (u : V) 1 * torusSp hB v b s.1 * Ssp hB v 0 (t ^ 2) *
          (Tsp hB (u : V) 1 * torusSp hB v b s.1)⁻¹ =
          Tsp hB (u : V) 1 * (torusSp hB v b s.1 * Ssp hB v 0 (t ^ 2) *
            (torusSp hB v b s.1)⁻¹) * (Tsp hB (u : V) 1)⁻¹ := by group
      rw [hmul, torusSp_conj_Ssp hB hb (map_zero (B v)) (map_zero (B b)) s.2 (t ^ 2), smul_zero,
        Tsp_conj_Ssp hB (hWv u) 0 1 (s.1 ^ 2 * t ^ 2), map_zero, LinearMap.zero_apply,
        mul_zero, zero_smul, add_zero]
    change φ₀ (Additive.ofMul (conjLsp hB v (n_pair s u)⁻¹ (sspEquiv hB hb (0, t ^ 2)))) = _
    rw [hconj]
    rfl
  have h_act_w : ∀ (s : {s : K // s ≠ 0}) (u w : W),
      orbChar (n_pair s u) (Additive.ofMul (sspEquiv hB hb (s.1⁻¹ • w, 0))) =
        η w + bilinAddHom α₁ (B.restrict W) (ψ u) w := by
    intro s u w
    have hconj : conjLsp hB v (n_pair s u)⁻¹ (sspEquiv hB hb (s.1⁻¹ • w, 0)) =
        sspEquiv hB hb (w + ((B.restrict W) w u) • u, 0) := by
      ext1
      change ((n_tsp u * n_torus s)⁻¹⁻¹ : N).1 * Ssp hB v ((s.1⁻¹ • w : W) : V) 0 *
        (((n_tsp u * n_torus s)⁻¹⁻¹ : N).1)⁻¹ =
        Ssp hB v ((w + ((B.restrict W) w u) • u : W) : V) 0
      rw [inv_inv]
      change Tsp hB (u : V) 1 * torusSp hB v b s.1 * Ssp hB v ((s.1⁻¹ • w : W) : V) 0 *
        (Tsp hB (u : V) 1 * torusSp hB v b s.1)⁻¹ =
        Ssp hB v ((w + ((B.restrict W) w u) • u : W) : V) 0
      have hmul : Tsp hB (u : V) 1 * torusSp hB v b s.1 * Ssp hB v ((s.1⁻¹ • w : W) : V) 0 *
          (Tsp hB (u : V) 1 * torusSp hB v b s.1)⁻¹ =
          Tsp hB (u : V) 1 * (torusSp hB v b s.1 * Ssp hB v ((s.1⁻¹ • w : W) : V) 0 *
            (torusSp hB v b s.1)⁻¹) * (Tsp hB (u : V) 1)⁻¹ := by group
      have hsmul : s.1 • ((s.1⁻¹ • w : W) : V) = (w : V) := by
        rw [Submodule.coe_smul_of_tower, smul_smul, mul_inv_cancel₀ s.2, one_smul]
      rw [hmul, torusSp_conj_Ssp hB hb (hWv (s.1⁻¹ • w)) (hWb (s.1⁻¹ • w)) s.2 0,
        hsmul, mul_zero, Tsp_conj_Ssp hB (hWv u) (w : V) 1 0, one_mul]
      rfl
    change φ₀ (Additive.ofMul (conjLsp hB v (n_pair s u)⁻¹ (sspEquiv hB hb (s.1⁻¹ • w, 0)))) = _
    rw [hconj]
    exact hη_tsp u w
  let ιP : {s : K // s ≠ 0} × Set.range ψ → Set.range orbChar := fun p =>
    ⟨orbChar (n_pair p.1 (Classical.choose p.2.2)),
      n_pair p.1 (Classical.choose p.2.2), rfl⟩
  have hιP_inj : Function.Injective ιP := by
    rintro ⟨s₁, y₁⟩ ⟨s₂, y₂⟩ h
    set u₁ := Classical.choose y₁.2
    set u₂ := Classical.choose y₂.2
    have hu₁ : ψ u₁ = y₁.1 := Classical.choose_spec y₁.2
    have hu₂ : ψ u₂ = y₂.1 := Classical.choose_spec y₂.2
    have h1 : orbChar (n_pair s₁ u₁) = orbChar (n_pair s₂ u₂) := congrArg Subtype.val h
    have hs_eq : s₁ = s₂ := by
      apply Subtype.ext
      apply hbij_lin.1
      ext t
      have ht := congrArg (fun f : Additive Q →+ ZMod 2 =>
        f (Additive.ofMul (sspEquiv hB hb (0, t ^ 2)))) h1
      rwa [h_act_z s₁ u₁ t, h_act_z s₂ u₂ t] at ht
    subst hs_eq
    have hy_eq : y₁ = y₂ := by
      apply Subtype.ext
      rw [← hu₁, ← hu₂]
      apply (bilinAddHom_bijective hα₁ hndW).1
      ext w
      have hw := congrArg (fun f : Additive Q →+ ZMod 2 =>
        f (Additive.ofMul (sspEquiv hB hb (s₁.1⁻¹ • w, 0)))) h1
      rw [h_act_w s₁ u₁ w, h_act_w s₁ u₂ w] at hw
      exact add_left_cancel hw
    exact Prod.ext rfl hy_eq
  have hcard_K_ne_zero : Nat.card {s : K // s ≠ 0} = Nat.card K - 1 := by
    classical
    let eK : Option {s : K // s ≠ 0} ≃ K :=
      { toFun := fun x => match x with | none => 0 | some s => s.1
        invFun := fun s => if hs : s = 0 then none else some ⟨s, hs⟩
        left_inv := by
          rintro (_ | ⟨s, hs⟩)
          · simp
          · simp [hs]
        right_inv := fun s => by by_cases hs : s = 0 <;> simp [hs] }
    have hcard := (Nat.card_congr eK).symm
    let _ := Fintype.ofFinite {s : K // s ≠ 0}
    simp only [Nat.card_eq_fintype_card, Fintype.card_option] at hcard ⊢
    omega
  have hprod_le : (Nat.card K - 1) * Nat.card (Set.range ψ) ≤ Nat.card (Set.range orbChar) := by
    have hcard := Nat.card_le_card_of_injective ιP hιP_inj
    rwa [Nat.card_prod, hcard_K_ne_zero] at hcard
  have hmul_le : (Nat.card K - 1) * (Nat.card K * Nat.card (Set.range ψ)) ≤
      (Nat.card K - 1) * H.index := by
    calc (Nat.card K - 1) * (Nat.card K * Nat.card (Set.range ψ))
        = Nat.card K * ((Nat.card K - 1) * Nat.card (Set.range ψ)) := by ring
      _ ≤ Nat.card K * Nat.card (Set.range orbChar) := Nat.mul_le_mul_left _ hprod_le
      _ ≤ (Nat.card K - 1) * H.index := hK_orb_le
  have hK2 : 2 ≤ Nat.card K := Finite.one_lt_card
  exact ⟨a, ha_smul, Nat.le_of_mul_le_mul_left hmul_le (by omega)⟩

/-- Case (b) index bound in `Gsp B` when `Nat.card K = 4` and `Module.finrank K V = 4`:
`24 ≤ H.index`. -/
theorem index_ge_of_case_b_four_one (hK : Nat.card K = 4)
    (hB : B.IsAlt) (hBn : B.Nondegenerate) (hdim : Module.finrank K V = 4)
    {v b : V} (hb : B v b = 1) {H : Subgroup (Gsp B)}
    (hZnot : ¬ (tspSubgroup hB v ≤ H.subgroupOf (Lsp B hB v)))
    (hCaseB : H.subgroupOf (Lsp B hB v) ⊔ tspSubgroup hB v = ⊤) :
    24 ≤ H.index := by
  have : Finite V := Module.finite_of_finite K
  have hv0 : v ≠ 0 := by rintro rfl; simp at hb
  obtain ⟨-, hsplit⟩ := alternating_hyperbolic_splitting hB hBn hv0
  obtain ⟨-, -, -, -, -, hdimW⟩ := hsplit b hb
  set W : Submodule K V := B.orthogonal (Submodule.span K {v, b})
  have hW_card : Nat.card W = 16 := by
    rw [Module.natCard_eq_pow_finrank (K := K), hdimW, hdim, hK]
    norm_num
  obtain ⟨a, ha_smul, hidx⟩ := card_mul_range_psi_le_index_of_case_b hB hBn hb hZnot hCaseB
  have hbound := two_to_one_range_bound a ha_smul
  rw [hK, hW_card] at hbound
  rw [hK] at hidx
  omega

/-- Case (b) index bound in `Gsp B` when `4 ≤ Nat.card K` and `Module.finrank K V = 2 * (m + 1)`
(`1 ≤ m`): `Nat.card K ^ (2 * m) ≤ H.index`. -/
theorem index_ge_of_case_b_four {m : ℕ} (hm : 1 ≤ m) (hK : 4 ≤ Nat.card K)
    (hB : B.IsAlt) (hBn : B.Nondegenerate) (hdim : Module.finrank K V = 2 * (m + 1))
    {v b : V} (hb : B v b = 1) {H : Subgroup (Gsp B)}
    (hZnot : ¬ (tspSubgroup hB v ≤ H.subgroupOf (Lsp B hB v)))
    (hCaseB : H.subgroupOf (Lsp B hB v) ⊔ tspSubgroup hB v = ⊤) :
    Nat.card K ^ (2 * m) ≤ H.index := by
  have : Finite V := Module.finite_of_finite K
  have hv0 : v ≠ 0 := by rintro rfl; simp at hb
  obtain ⟨-, hsplit⟩ := alternating_hyperbolic_splitting hB hBn hv0
  obtain ⟨-, -, -, -, -, hdimW⟩ := hsplit b hb
  set W : Submodule K V := B.orthogonal (Submodule.span K {v, b})
  have hW_card : Nat.card W = Nat.card K ^ (2 * m) := by
    rw [Module.natCard_eq_pow_finrank (K := K), hdimW, hdim]
    rfl
  obtain ⟨a, ha_smul, hidx⟩ := card_mul_range_psi_le_index_of_case_b hB hBn hb hZnot hCaseB
  have hbound := two_to_one_range_bound a ha_smul
  rw [hW_card] at hbound
  set q := Nat.card K
  set X := q ^ (2 * m - 1)
  set R := Nat.card (Set.range fun w : W => (a w + 1) • w)
  have hqX : q ^ (2 * m) = q * X := by
    rw [← pow_succ', Nat.sub_add_cancel (by omega)]
  have hX1 : 1 ≤ X := Nat.one_le_pow _ _ (by omega)
  have h1 : 2 * (q - 1) * X ≤ (q - 2) * (q * X - 1) + 2 * (q - 1) := by
    set X' := X - 1
    set q' := q - 2
    have hX_eq : X = X' + 1 := by omega
    have hq_eq : q = q' + 2 := by omega
    have hq2 : 2 ≤ q' := by omega
    have hqX_sub : q * X - 1 = q * X' + (q - 1) := by
      rw [hX_eq]
      calc q * (X' + 1) - 1 = q * X' + q - 1 := by ring_nf
        _ = q * X' + (q - 1) := by omega
    have h2 : 2 * (q - 1) * X' ≤ q' * q * X' := by
      refine Nat.mul_le_mul_right X' ?_
      calc 2 * (q - 1) ≤ 2 * q := Nat.mul_le_mul_left 2 (by omega)
        _ ≤ q' * q := Nat.mul_le_mul_right q hq2
    have h3 : 2 * (q - 1) ≤ (q' + 2) * (q - 1) :=
      Nat.mul_le_mul_right (q - 1) (by omega)
    calc 2 * (q - 1) * X = 2 * (q - 1) * X' + 2 * (q - 1) := by rw [hX_eq]; ring
      _ ≤ q' * q * X' + (q' + 2) * (q - 1) := Nat.add_le_add h2 h3
      _ = q' * (q * X' + (q - 1)) + 2 * (q - 1) := by ring
      _ = (q - 2) * (q * X - 1) + 2 * (q - 1) := by rw [← hqX_sub]
  rw [hqX] at hbound ⊢
  have hXR : X ≤ R := by
    have hle := h1.trans hbound
    exact Nat.le_of_mul_le_mul_left hle (by omega)
  exact (Nat.mul_le_mul_left q hXR).trans hidx

end PointRadicalCharacters

section Transport

/-- For any `StatedClassicalModel S .PSp n 2 f` and proper subgroup `H ≠ ⊤` of `S`, there exists
a field `K` of characteristic `2` with `Nat.card K = 2 ^ f` and a proper subgroup
`H₀ : Subgroup (Gsp (spForm n K))` with `H₀ ≠ ⊤` and `H₀.index = H.index`. -/
theorem exists_proper_subgroup_gsp_of_psp {S : Type} [Group S] {n f : ℕ}
    (h : StatedClassicalModel S .PSp n 2 f) {H : Subgroup S} (hH : H ≠ ⊤) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2),
      Nat.card K = 2 ^ f ∧
      ∃ H₀ : Subgroup (Gsp (spForm n K)), H₀ ≠ ⊤ ∧ H₀.index = H.index := by
  obtain ⟨⟨hp, hf, hn, -⟩, K, _, _, hK, ⟨e⟩⟩ := h
  let _ : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
  let π : Gsp (spForm n K) →* S :=
    e.symm.toMonoidHom.comp
      ((QuotientGroup.mk' ((StatedScalars (Fin n ⊕ Fin n) K).subgroupOf (StatedSp n K))).comp
        (spEquiv (m := n) (K := K)).symm.toMonoidHom)
  have hπ : Function.Surjective π :=
    e.symm.surjective.comp
      ((QuotientGroup.mk'_surjective _).comp (spEquiv (m := n) (K := K)).symm.surjective)
  refine ⟨K, inferInstance, inferInstance, inferInstance, hK, H.comap π, ?_,
    Subgroup.index_comap_of_surjective H hπ⟩
  intro htop
  apply hH
  rw [eq_top_iff]
  intro s _
  obtain ⟨g, rfl⟩ := hπ s
  have hg : g ∈ H.comap π := htop ▸ Subgroup.mem_top g
  exact hg

/-- Minimum degree bound for `PSp(2n, 2)` (`f = 1`): every proper subgroup `H ≠ ⊤` has index
at least `2 ^ (2 * n - 2) - 2 ^ (n - 1)`. -/
theorem index_ge_psp_two {S : Type} [Group S] {n : ℕ}
    (h : StatedClassicalModel S .PSp n 2 1) {H : Subgroup S} (hH : H ≠ ⊤) :
    2 ^ (2 * n - 2) - 2 ^ (n - 1) ≤ H.index := by
  have hn : 2 ≤ n := h.1.2.2.1
  obtain ⟨K, _, _, _, hK, H₀, hH₀, hidx⟩ := exists_proper_subgroup_gsp_of_psp h hH
  rw [pow_one] at hK
  rw [← hidx]
  let i₀ : Fin n := ⟨0, by omega⟩
  let v : Fin n ⊕ Fin n → K := Pi.single (Sum.inl i₀) 1
  let b : Fin n ⊕ Fin n → K := Pi.single (Sum.inr i₀) 1
  have hb : spForm n K v b = 1 := by
    change spForm n K (Pi.single (Sum.inl i₀) 1) (Pi.single (Sum.inr i₀) 1) = 1
    simp [spForm_single_inl_inr]
  have hv0 : v ≠ 0 := by
    rintro h0; rw [h0, map_zero, LinearMap.zero_apply] at hb; exact zero_ne_one hb
  obtain ⟨H', hH'_idx, c, hc⟩ :=
    exists_conj_tsp_not_mem_of_ne_top spForm_isAlt spForm_nondegenerate hv0 hH₀
  rw [← hH'_idx]
  have hZnot :
      ¬ (tspSubgroup spForm_isAlt v ≤ H'.subgroupOf (Lsp (spForm n K) spForm_isAlt v)) := by
    intro hle
    exact hc (@hle ⟨Tsp spForm_isAlt v c, Tsp_mem_Lsp spForm_isAlt v c⟩ ⟨c, rfl⟩)
  have hdim : Module.finrank K (Fin n ⊕ Fin n → K) = 2 * ((n - 1) + 1) := by
    rw [finrank_spSpace]
    congr 1; omega
  by_cases hCase : H'.subgroupOf (Lsp (spForm n K) spForm_isAlt v) ⊔ tspSubgroup spForm_isAlt v = ⊤
  · have hb_two := index_ge_of_case_b_two (m := n - 1) (by omega) hK spForm_isAlt
      spForm_nondegenerate hdim hb hZnot hCase
    have h2n : 2 * (n - 1) = 2 * n - 2 := by omega
    rwa [h2n] at hb_two
  · have ha := index_ge_of_case_a spForm_isAlt spForm_nondegenerate hb hZnot hCase
    rw [finrank_spSpace, hK] at ha
    have hle : 2 ^ (2 * n - 2) - 2 ^ (n - 1) ≤ 2 * 2 ^ (2 * n - 2) :=
      (Nat.sub_le _ _).trans (Nat.le_mul_of_pos_left _ (by norm_num))
    exact hle.trans ha

/-- Minimum degree bound for `PSp(4, 4)` (`n = 2, f = 2`) from the point radical: every proper
subgroup `H ≠ ⊤` has index at least `24`. -/
theorem index_ge_psp_four_four {S : Type} [Group S]
    (h : StatedClassicalModel S .PSp 2 2 2) {H : Subgroup S} (hH : H ≠ ⊤) :
    24 ≤ H.index := by
  obtain ⟨K, _, _, _, hK, H₀, hH₀, hidx⟩ := exists_proper_subgroup_gsp_of_psp h hH
  have hK4 : Nat.card K = 4 := by rw [hK]; norm_num
  rw [← hidx]
  let i₀ : Fin 2 := ⟨0, by norm_num⟩
  let v : Fin 2 ⊕ Fin 2 → K := Pi.single (Sum.inl i₀) 1
  let b : Fin 2 ⊕ Fin 2 → K := Pi.single (Sum.inr i₀) 1
  have hb : spForm 2 K v b = 1 := by
    change spForm 2 K (Pi.single (Sum.inl i₀) 1) (Pi.single (Sum.inr i₀) 1) = 1
    simp [spForm_single_inl_inr]
  have hv0 : v ≠ 0 := by
    rintro h0; rw [h0, map_zero, LinearMap.zero_apply] at hb; exact zero_ne_one hb
  obtain ⟨H', hH'_idx, c, hc⟩ :=
    exists_conj_tsp_not_mem_of_ne_top spForm_isAlt spForm_nondegenerate hv0 hH₀
  rw [← hH'_idx]
  have hZnot :
      ¬ (tspSubgroup spForm_isAlt v ≤ H'.subgroupOf (Lsp (spForm 2 K) spForm_isAlt v)) := by
    intro hle
    exact hc (@hle ⟨Tsp spForm_isAlt v c, Tsp_mem_Lsp spForm_isAlt v c⟩ ⟨c, rfl⟩)
  have hdim : Module.finrank K (Fin 2 ⊕ Fin 2 → K) = 4 := by
    rw [finrank_spSpace]
  by_cases hCase : H'.subgroupOf (Lsp (spForm 2 K) spForm_isAlt v) ⊔ tspSubgroup spForm_isAlt v = ⊤
  · exact index_ge_of_case_b_four_one hK4 spForm_isAlt spForm_nondegenerate hdim hb hZnot hCase
  · have ha := index_ge_of_case_a spForm_isAlt spForm_nondegenerate hb hZnot hCase
    rw [finrank_spSpace, hK4] at ha
    omega

/-- Minimum degree bound for `PSp(2n, 2^f)` with `2 ≤ f`: every proper subgroup `H ≠ ⊤` has index
at least `(2 ^ f) ^ (2 * n - 2)`. -/
theorem index_ge_psp_even_of_two_le_f {S : Type} [Group S] {n f : ℕ}
    (h : StatedClassicalModel S .PSp n 2 f) (hf : 2 ≤ f) {H : Subgroup S} (hH : H ≠ ⊤) :
    (2 ^ f) ^ (2 * n - 2) ≤ H.index := by
  have hn : 2 ≤ n := h.1.2.2.1
  obtain ⟨K, _, _, _, hK, H₀, hH₀, hidx⟩ := exists_proper_subgroup_gsp_of_psp h hH
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  rw [← hidx, ← hK]
  let i₀ : Fin n := ⟨0, by omega⟩
  let v : Fin n ⊕ Fin n → K := Pi.single (Sum.inl i₀) 1
  let b : Fin n ⊕ Fin n → K := Pi.single (Sum.inr i₀) 1
  have hb : spForm n K v b = 1 := by
    change spForm n K (Pi.single (Sum.inl i₀) 1) (Pi.single (Sum.inr i₀) 1) = 1
    simp [spForm_single_inl_inr]
  have hv0 : v ≠ 0 := by
    rintro h0; rw [h0, map_zero, LinearMap.zero_apply] at hb; exact zero_ne_one hb
  obtain ⟨H', hH'_idx, c, hc⟩ :=
    exists_conj_tsp_not_mem_of_ne_top spForm_isAlt spForm_nondegenerate hv0 hH₀
  rw [← hH'_idx]
  have hZnot :
      ¬ (tspSubgroup spForm_isAlt v ≤ H'.subgroupOf (Lsp (spForm n K) spForm_isAlt v)) := by
    intro hle
    exact hc (@hle ⟨Tsp spForm_isAlt v c, Tsp_mem_Lsp spForm_isAlt v c⟩ ⟨c, rfl⟩)
  have hdim : Module.finrank K (Fin n ⊕ Fin n → K) = 2 * ((n - 1) + 1) := by
    rw [finrank_spSpace]
    congr 1; omega
  by_cases hCase : H'.subgroupOf (Lsp (spForm n K) spForm_isAlt v) ⊔ tspSubgroup spForm_isAlt v = ⊤
  · have hb_four := index_ge_of_case_b_four (m := n - 1) (by omega) hK4 spForm_isAlt
      spForm_nondegenerate hdim hb hZnot hCase
    have h2n : 2 * (n - 1) = 2 * n - 2 := by omega
    rwa [h2n] at hb_four
  · have ha := index_ge_of_case_a spForm_isAlt spForm_nondegenerate hb hZnot hCase
    rw [finrank_spSpace] at ha
    have hle : Nat.card K ^ (2 * n - 2) ≤ 2 * Nat.card K ^ (2 * n - 2) := by omega
    exact hle.trans ha

end Transport

end Maroti
