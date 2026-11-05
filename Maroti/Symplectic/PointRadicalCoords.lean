module

public import Maroti.Symplectic.QuadraticZeros
public import CFSG.ClassicalGroups.Symplectic.StatedSpTransport

/-!
# Point radical coordinates and orbit-stabilizer bounds in characteristic 2

This file sets up the group-theoretic and geometric machinery for the point radical `Lsp B hB v`
of a symplectic space `(V, B)` over a finite field `K` of characteristic `2`:

* The lemma `card_range_conjSub_mul_relIndex_le_index`: for a subgroup `N` normalizing an abelian
  subgroup `Q ≤ N` and any `H : Subgroup G`, the number of `N`-conjugates of `H ⊓ Q` times
  `(H ⊓ Q).relIndex Q` is at most `H.index`.
* The lemma `card_le_card_range_mul_of_forall_le`: double-counting bound for a relation between
  `Set.range F` and a finite type `X`.
* The lemma `card_le_two_mul_card_range_of_two_to_one`: if every fiber of `f : A → B` has size at
  most `2` (given by an involution/map `τ : A → A`), then `Nat.card A ≤ 2 * Nat.card (Set.range f)`.
* Coordinate parameterization `sspEquiv : W × K ≃ Lsp B hB v`, projection `projW`, transvection
  subgroup `tspSubgroup`, and the hyperbolic torus `torusSp`.
-/

@[expose] public section

namespace Maroti

open CFSG.ClassicalGroups.Alternating CFSG.ClassicalGroups.Symplectic CFSG.ClassicalGroups
open CFSG.LocalAnalysis.ComponentInitial
open LinearMap (BilinForm)
open Module

section OrbitStabilizerIndex

/-- If `B ≤ C`, then `A.relIndex B ≤ A.relIndex C`. -/
theorem relIndex_le_of_le_right {G₀ : Type*} [Group G₀] [Finite G₀]
    (A : Subgroup G₀) {B C : Subgroup G₀} (hBC : B ≤ C) :
    A.relIndex B ≤ A.relIndex C := by
  have key : ∀ x y : B,
      QuotientGroup.leftRel (A.subgroupOf B) x y ↔
        QuotientGroup.leftRel (A.subgroupOf C) (Subgroup.inclusion hBC x)
          (Subgroup.inclusion hBC y) := by
    intro x y
    simp only [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf]
    rfl
  refine Nat.card_le_card_of_injective
    (Quotient.map' (Subgroup.inclusion hBC) fun x y => (key x y).mp) ?_
  simp_rw [← Quotient.eq''] at key
  exact Quotient.ind' fun x => Quotient.ind' fun y => (key x y).mpr

/-- If `F : N → α` is right-invariant under both `H ⊓ N` and `Q` (with `Q ≤ N`), then
`Nat.card (Set.range F) * (H ⊓ Q).relIndex Q ≤ H.index`. -/
theorem card_range_mul_relIndex_le_index {G α : Type*} [Group G] [Finite G]
    (H N Q : Subgroup G) (hQN : Q ≤ N) (F : N → α)
    (hFH : ∀ (n m : N), (m : G) ∈ H → F (n * m) = F n)
    (hFQ : ∀ (n q : N), (q : G) ∈ Q → F (n * q) = F n) :
    Nat.card (Set.range F) * (H ⊓ Q).relIndex Q ≤ H.index := by
  let S_F : Subgroup N :=
    { carrier := {x : N | ∀ n : N, F (n * x) = F n}
      one_mem' := fun n => by rw [mul_one]
      mul_mem' := fun {x y} hx hy n => by rw [← mul_assoc, hy, hx]
      inv_mem' := fun {x} hx n => by
        have := hx (n * x⁻¹)
        rw [mul_assoc, inv_mul_cancel, mul_one] at this
        exact this.symm }
  have hMS : H.subgroupOf N ≤ S_F := fun m hm n => hFH n m hm
  have hQS : Q.subgroupOf N ≤ S_F := fun q hq n => hFQ n q hq
  have hcard : Nat.card (Set.range F) ≤ S_F.index := by
    let φ : N ⧸ S_F → Set.range F :=
      Quotient.lift (fun n : N => ⟨F n, n, rfl⟩) fun a b hab => by
        have h1 : a⁻¹ * b ∈ S_F := QuotientGroup.leftRel_apply.mp hab
        ext1
        dsimp
        have h2 := h1 a
        rw [← mul_assoc, mul_inv_cancel, one_mul] at h2
        exact h2.symm
    refine Nat.card_le_card_of_surjective φ ?_
    rintro ⟨_, n, rfl⟩
    exact ⟨QuotientGroup.mk n, rfl⟩
  calc Nat.card (Set.range F) * (H ⊓ Q).relIndex Q
      = Nat.card (Set.range F) * (H.subgroupOf N).relIndex (Q.subgroupOf N) := by
        rw [Subgroup.inf_relIndex_right, Subgroup.relIndex_subgroupOf hQN]
    _ ≤ S_F.index * (H.subgroupOf N).relIndex S_F :=
        Nat.mul_le_mul hcard (relIndex_le_of_le_right (H.subgroupOf N) hQS)
    _ = (H.subgroupOf N).relIndex S_F * S_F.index := mul_comm _ _
    _ = (H.subgroupOf N).index := Subgroup.relIndex_mul_index hMS
    _ = H.relIndex N := rfl
    _ ≤ H.index := by
        rw [← Subgroup.relIndex_top_right (H := H)]
        exact relIndex_le_of_le_right H le_top

/-- For `n : N`, the conjugate subset `{q : Q | (n : G)⁻¹ * (q : G) * (n : G) ∈ H}`. -/
def conjSub {G : Type*} [Group G] (H N Q : Subgroup G) (n : N) : Set Q :=
  {q : Q | (n : G)⁻¹ * (q : G) * (n : G) ∈ H}

/-- If `Q ≤ N`, `N` normalizes `Q`, and `Q` is abelian, then
`Nat.card (Set.range (conjSub H N Q)) * (H ⊓ Q).relIndex Q ≤ H.index`. -/
theorem card_range_conjSub_mul_relIndex_le_index {G : Type*} [Group G] [Finite G]
    (H N Q : Subgroup G) (hQN : Q ≤ N)
    (hQnorm : ∀ n ∈ N, ∀ q ∈ Q, n * q * n⁻¹ ∈ Q)
    (hQcomm : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x) :
    Nat.card (Set.range (conjSub H N Q)) * (H ⊓ Q).relIndex Q ≤ H.index := by
  refine card_range_mul_relIndex_le_index H N Q hQN (conjSub H N Q) ?_ ?_
  · intro n m hm
    ext q
    change ((n * m : N) : G)⁻¹ * (q : G) * ((n * m : N) : G) ∈ H ↔
      (n : G)⁻¹ * (q : G) * (n : G) ∈ H
    simp only [Subgroup.coe_mul, mul_inv_rev]
    have hmul : (m : G)⁻¹ * (n : G)⁻¹ * (q : G) * ((n : G) * (m : G)) =
        (m : G)⁻¹ * ((n : G)⁻¹ * (q : G) * (n : G)) * (m : G) := by group
    rw [hmul, H.mul_mem_cancel_right hm, H.mul_mem_cancel_left (inv_mem hm)]
  · intro n q₀ hq₀
    ext q
    change ((n * q₀ : N) : G)⁻¹ * (q : G) * ((n * q₀ : N) : G) ∈ H ↔
      (n : G)⁻¹ * (q : G) * (n : G) ∈ H
    simp only [Subgroup.coe_mul, mul_inv_rev]
    have hnq : (n : G)⁻¹ * (q : G) * (n : G) ∈ Q := by
      have := hQnorm (n : G)⁻¹ (inv_mem n.2) (q : G) q.2
      rwa [inv_inv] at this
    have hcomm : (q₀ : G)⁻¹ * ((n : G)⁻¹ * (q : G) * (n : G)) * (q₀ : G) =
        (n : G)⁻¹ * (q : G) * (n : G) := by
      rw [hQcomm _ (inv_mem hq₀) _ hnq, mul_assoc, inv_mul_cancel, mul_one]
    have hmul : (q₀ : G)⁻¹ * (n : G)⁻¹ * (q : G) * ((n : G) * (q₀ : G)) =
        (q₀ : G)⁻¹ * ((n : G)⁻¹ * (q : G) * (n : G)) * (q₀ : G) := by group
    rw [hmul, hcomm]

/-- Double-counting bound: if every `x ∈ U` satisfies `P (F i) x` for some `i : I`, and for every
`i : I` there are at most `C` elements `x : X` with `P (F i) x`, then
`Nat.card U ≤ Nat.card (Set.range F) * C`. -/
theorem card_le_card_range_mul_of_forall_le {I α X : Type*} [Finite I] [Finite X]
    (F : I → α) (P : α → X → Prop) (U : Set X) (C : ℕ)
    (hU : ∀ x ∈ U, ∃ i : I, P (F i) x)
    (hC : ∀ i : I, Nat.card {x : X // P (F i) x} ≤ C) :
    Nat.card U ≤ Nat.card (Set.range F) * C := by
  classical
  let _ := Fintype.ofFinite (Set.range F)
  let _ := Fintype.ofFinite X
  let φ : U → Σ s : Set.range F, {x : X // P s.1 x} := fun x =>
    let i := Classical.choose (hU x.1 x.2)
    ⟨⟨F i, i, rfl⟩, ⟨x.1, Classical.choose_spec (hU x.1 x.2)⟩⟩
  have hφ : Function.Injective φ := by
    intro x₁ x₂ h
    have := congrArg (fun p : Σ s : Set.range F, {x : X // P s.1 x} => p.2.1) h
    exact Subtype.ext this
  have h1 : Nat.card U ≤ Nat.card (Σ s : Set.range F, {x : X // P s.1 x}) :=
    Nat.card_le_card_of_injective φ hφ
  rw [Nat.card_sigma] at h1
  refine h1.trans ?_
  calc ∑ s : Set.range F, Nat.card {x : X // P s.1 x}
      ≤ ∑ _s : Set.range F, C := by
        refine Finset.sum_le_sum fun s _ => ?_
        obtain ⟨i, hi⟩ := s.2
        rw [← hi]
        exact hC i
    _ = Nat.card (Set.range F) * C := by
        rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, smul_eq_mul]

/-- If every fiber of `f : A → B` has size at most `2` (witnessed by `τ : A → A`), then
`Nat.card A ≤ 2 * Nat.card (Set.range f)`. -/
theorem card_le_two_mul_card_range_of_two_to_one {A B : Type*} [Finite A]
    (f : A → B) (τ : A → A)
    (htwo : ∀ x₁ x₂ : A, f x₁ = f x₂ → x₂ = x₁ ∨ x₂ = τ x₁) :
    Nat.card A ≤ 2 * Nat.card (Set.range f) := by
  let rep : Set.range f → A := fun y => Classical.choose y.2
  have hrep : ∀ y : Set.range f, f (rep y) = y.1 := fun y => Classical.choose_spec y.2
  let g : Bool × Set.range f → A := fun p => if p.1 then τ (rep p.2) else rep p.2
  have hg : Function.Surjective g := by
    intro x
    let y : Set.range f := ⟨f x, x, rfl⟩
    rcases htwo (rep y) x (hrep y) with h1 | h2
    · exact ⟨(false, y), h1.symm⟩
    · exact ⟨(true, y), h2.symm⟩
  calc Nat.card A ≤ Nat.card (Bool × Set.range f) := Nat.card_le_card_of_surjective g hg
    _ = 2 * Nat.card (Set.range f) := by simp [Nat.card_prod]

end OrbitStabilizerIndex

section PointRadicalCoords

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {B : BilinForm K V}

/-- Over a characteristic-2 field, any alternating bilinear form is symmetric. -/
theorem isAlt_symm_of_char_two [CharP K 2] (hB : B.IsAlt) (x y : V) : B x y = B y x := by
  rw [← hB.neg_eq y x, CharTwo.neg_eq]

/-- Conjugating `Tsp hB v c` by `g : Gsp B` gives `Tsp hB (g.app v) c`. -/
theorem Tsp_conj (hB : B.IsAlt) (g : Gsp B) (v : V) (c : K) :
    g * Tsp hB v c * g⁻¹ = Tsp hB (g.app v) c := by
  apply Subtype.ext
  exact SteinbergBQ.symplecticTransvection_conj hB (mem_bilinIsometryGroup.mp g.2) v c

/-- Scaling the vector in `Tsp hB (s • v) c` scales the scalar by `s ^ 2`. -/
theorem Tsp_smul (hB : B.IsAlt) (v : V) (s c : K) :
    Tsp hB (s • v) c = Tsp hB v (s ^ 2 * c) := by
  refine Gsp.ext' fun x => ?_
  rw [Tsp_app, Tsp_app, map_smul, smul_eq_mul, smul_smul]
  congr 2
  ring

/-- Conjugating `Ssp hB v w c` by `g : Gsp B` gives `Ssp hB (g.app v) (g.app w) c`. -/
theorem Ssp_conj (hB : B.IsAlt) (g : Gsp B) (v w : V) (c : K) :
    g * Ssp hB v w c * g⁻¹ = Ssp hB (g.app v) (g.app w) c :=
  Subtype.ext (siegel_conj hB g.2 v w c)

/-- Scaling the first vector in `Ssp` by `s` scales the second by `s` and the scalar by `s ^ 2`. -/
theorem Ssp_smul_left (hB : B.IsAlt) {v w : V} (hw : B v w = 0) (s c : K) :
    Ssp hB (s • v) w c = Ssp hB v (s • w) (s ^ 2 * c) :=
  Subtype.ext (siegel_smul_left hB hw s c)

/-- Product formula for `Ssp` elements with the same base vector `v`. -/
theorem Ssp_mul (hB : B.IsAlt) {v w w' : V} (hw : B v w = 0) (hw' : B v w' = 0) (c c' : K) :
    Ssp hB v w c * Ssp hB v w' c' = Ssp hB v (w + w') (c + c' + B w' w) :=
  Subtype.ext (siegel_mul hB hw hw' c c')

/-- The identity `Ssp hB v 0 0 = 1`. -/
theorem Ssp_zero (hB : B.IsAlt) (v : V) : Ssp hB v 0 0 = 1 :=
  Subtype.ext (siegel_zero hB v)

/-- The identity `Ssp hB v 0 c = Tsp hB v c`. -/
theorem Ssp_zero_left (hB : B.IsAlt) (v : V) (c : K) : Ssp hB v 0 c = Tsp hB v c :=
  Subtype.ext (siegel_zero_eq hB v c)

/-- Action of `Ssp hB v w c` on `x : V` when `B v w = 0`. -/
theorem Ssp_app (hB : B.IsAlt) {v w : V} (hvw : B v w = 0) (c : K) (x : V) :
    (Ssp hB v w c).app x = x + B x v • w + B x w • v + (c * B x v) • v :=
  siegel_apply hB hvw c x

/-- Every element of `Lsp B hB v` fixes `v`. -/
theorem Lsp_app_self (hB : B.IsAlt) {v : V} {g : Gsp B} (hg : g ∈ Lsp B hB v) :
    g.app v = v :=
  apply_self_of_mem_pointRadical hB hg

/-- In a module over a characteristic-2 field, `x + x = 0`. -/
theorem add_self_eq_zero_of_char_two [CharP K 2] (x : V) : x + x = 0 :=
  (char_two_eq_iff_add_eq_zero (K := K) x x).mp rfl

/-- In characteristic `2`, every element of `Lsp B hB v` has order dividing `2`. -/
theorem Lsp_mul_self [CharP K 2] (hB : B.IsAlt) {v : V} {g : Gsp B} (hg : g ∈ Lsp B hB v) :
    g * g = 1 := by
  obtain ⟨w, c, hw, hgw⟩ := mem_Lsp.mp hg
  have : g = Ssp hB v w c := Subtype.ext hgw.symm
  rw [this, Ssp_mul hB hw hw, add_self_eq_zero_of_char_two (K := K) w,
    CharTwo.add_self_eq_zero c, hB.self_eq_zero, zero_add, Ssp_zero]

/-- In characteristic `2`, `Lsp B hB v` is abelian. -/
theorem Lsp_mul_comm [CharP K 2] (hB : B.IsAlt) {v : V} {g h : Gsp B}
    (hg : g ∈ Lsp B hB v) (hh : h ∈ Lsp B hB v) : g * h = h * g := by
  have hg2 := Lsp_mul_self hB hg
  have hh2 := Lsp_mul_self hB hh
  calc g * h = (h * h) * (g * h) * (g * g) := by rw [hh2, hg2, one_mul, mul_one]
    _ = h * (h * g * (h * g)) * g := by group
    _ = h * 1 * g := by rw [Lsp_mul_self hB (mul_mem hh hg)]
    _ = h * g := by rw [mul_one]

/-- Commutative group instance on `Lsp B hB v` in characteristic `2`. -/
instance instCommGroupLsp [CharP K 2] (hB : B.IsAlt) (v : V) : CommGroup (Lsp B hB v) :=
  { (Lsp B hB v).toGroup with
    mul_comm := fun a b => Subtype.ext (Lsp_mul_comm hB a.2 b.2) }

/-- In `Additive (Lsp B hB v)`, every element has additive order dividing `2`. -/
theorem two_nsmul_additive_Lsp [CharP K 2] (hB : B.IsAlt) (v : V)
    (x : Additive (Lsp B hB v)) : 2 • x = 0 := by
  rw [two_nsmul]
  change Additive.ofMul (x.toMul * x.toMul) = 0
  have h1 : (x.toMul : Gsp B) * (x.toMul : Gsp B) = 1 :=
    Lsp_mul_self hB x.toMul.2
  have h2 : x.toMul * x.toMul = 1 := Subtype.ext h1
  rw [h2, ofMul_one]

/-- The subgroup of `Gsp B` stabilizing the line `K ∙ v` (for `v ≠ 0`). -/
def lineStabilizer (B : BilinForm K V) (v : V) : Subgroup (Gsp B) where
  carrier := {g : Gsp B | ∃ s : K, s ≠ 0 ∧ g.app v = s • v}
  one_mem' := ⟨1, one_ne_zero, by simp [Gsp.app_one]⟩
  mul_mem' := by
    rintro g₁ g₂ ⟨s₁, hs₁, hg₁⟩ ⟨s₂, hs₂, hg₂⟩
    refine ⟨s₂ * s₁, mul_ne_zero hs₂ hs₁, ?_⟩
    rw [Gsp.app_mul, hg₂, Gsp.map_smul, hg₁, smul_smul]
  inv_mem' := by
    rintro g ⟨s, hs, hg⟩
    refine ⟨s⁻¹, inv_ne_zero hs, ?_⟩
    have h1 := Gsp.app_inv_app g v
    rw [hg, Gsp.map_smul] at h1
    have h2 := congrArg (s⁻¹ • ·) h1
    rwa [smul_smul, inv_mul_cancel₀ hs, one_smul] at h2

/-- Any `g : Gsp B` fixing `v` belongs to `lineStabilizer B v`. -/
theorem mem_lineStabilizer_of_app_eq_self {v : V} {g : Gsp B} (hg : g.app v = v) :
    g ∈ lineStabilizer B v :=
  ⟨1, one_ne_zero, by rw [hg, one_smul]⟩

/-- The point radical `Lsp B hB v` is contained in `lineStabilizer B v`. -/
theorem Lsp_le_lineStabilizer (hB : B.IsAlt) (v : V) : Lsp B hB v ≤ lineStabilizer B v :=
  fun _ hg => mem_lineStabilizer_of_app_eq_self (Lsp_app_self hB hg)

/-- The subgroup `lineStabilizer B v` normalizes `Lsp B hB v`. -/
theorem lineStabilizer_normalizes_Lsp (hB : B.IsAlt) (v : V) :
    ∀ n ∈ lineStabilizer B v, ∀ q ∈ Lsp B hB v, n * q * n⁻¹ ∈ Lsp B hB v := by
  rintro n ⟨s, hs, hn⟩ q hq
  have h1 := conj_mem_Lsp hB n hq
  rwa [hn, Lsp_smul hB hs] at h1

/-- Conjugation of `Lsp B hB v` by an element `n : lineStabilizer B v` as a `MulEquiv`. -/
def conjLsp (hB : B.IsAlt) (v : V) (n : lineStabilizer B v) :
    Lsp B hB v ≃* Lsp B hB v where
  toFun q := ⟨(n : Gsp B) * q.1 * (n : Gsp B)⁻¹, lineStabilizer_normalizes_Lsp hB v n.1 n.2 q.1 q.2⟩
  invFun q := ⟨(n : Gsp B)⁻¹ * q.1 * (n : Gsp B), by
    have := lineStabilizer_normalizes_Lsp hB v (n⁻¹ : lineStabilizer B v).1 (inv_mem n.2) q.1 q.2
    simpa using this⟩
  left_inv q := by ext1; dsimp; group
  right_inv q := by ext1; dsimp; group
  map_mul' q₁ q₂ := by ext1; dsimp; group

/-- Weyl-type element `Tsp hB v t * Tsp hB b t⁻¹ * Tsp hB v t` on a hyperbolic pair `(v, b)`. -/
def weylSp (hB : B.IsAlt) (v b : V) (t : K) : Gsp B :=
  Tsp hB v t * Tsp hB b t⁻¹ * Tsp hB v t

/-- Hyperbolic torus element scaling `v` by `s`, `b` by `s⁻¹`, and fixing `{v, b}⊥`. -/
def torusSp (hB : B.IsAlt) (v b : V) (s : K) : Gsp B :=
  weylSp hB v b s * weylSp hB v b 1

theorem weylSp_app_left [CharP K 2] (hB : B.IsAlt) {v b : V} (hb : B v b = 1) {t : K}
    (ht : t ≠ 0) : (weylSp hB v b t).app v = t⁻¹ • b := by
  have hbv : B b v = 1 := by rw [isAlt_symm_of_char_two hB, hb]
  have h1 : (Tsp hB v t).app v = v := by
    rw [Tsp_app, hB.self_eq_zero, mul_zero, zero_smul, add_zero]
  have h2 : (Tsp hB b t⁻¹).app v = v + t⁻¹ • b := by
    rw [Tsp_app, hb, mul_one]
  rw [weylSp, Gsp.app_mul, Gsp.app_mul, h1, h2, Tsp_app]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    hB.self_eq_zero, hbv, mul_one, zero_add, mul_inv_cancel₀ ht, one_smul]
  rw [add_comm v (t⁻¹ • b), add_assoc, add_self_eq_zero_of_char_two (K := K) v, add_zero]

theorem weylSp_app_right [CharP K 2] (hB : B.IsAlt) {v b : V} (hb : B v b = 1) {t : K}
    (ht : t ≠ 0) : (weylSp hB v b t).app b = t • v := by
  have hbv : B b v = 1 := by rw [isAlt_symm_of_char_two hB, hb]
  have h1 : (Tsp hB v t).app b = b + t • v := by
    rw [Tsp_app, hbv, mul_one]
  have h2 : (Tsp hB b t⁻¹).app (b + t • v) = t • v := by
    rw [Tsp_app]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      hB.self_eq_zero, hb, mul_one, zero_add, inv_mul_cancel₀ ht, one_smul]
    rw [add_comm b (t • v), add_assoc, add_self_eq_zero_of_char_two (K := K) b, add_zero]
  rw [weylSp, Gsp.app_mul, Gsp.app_mul, h1, h2, Tsp_app, map_smul, LinearMap.smul_apply,
    hB.self_eq_zero, smul_zero, mul_zero, zero_smul, add_zero]

theorem weylSp_app_orth (hB : B.IsAlt) {v b w : V} (hvw : B v w = 0) (hbw : B b w = 0) (t : K) :
    (weylSp hB v b t).app w = w := by
  have hwv : B w v = 0 := by rw [← hB.neg_eq v w, hvw, neg_zero]
  have hwb : B w b = 0 := by rw [← hB.neg_eq b w, hbw, neg_zero]
  have h1 : (Tsp hB v t).app w = w := by rw [Tsp_app, hwv, mul_zero, zero_smul, add_zero]
  have h2 : (Tsp hB b t⁻¹).app w = w := by rw [Tsp_app, hwb, mul_zero, zero_smul, add_zero]
  rw [weylSp, Gsp.app_mul, Gsp.app_mul, h1, h2, h1]

theorem torusSp_app_left [CharP K 2] (hB : B.IsAlt) {v b : V} (hb : B v b = 1) {s : K}
    (hs : s ≠ 0) : (torusSp hB v b s).app v = s • v := by
  rw [torusSp, Gsp.app_mul, weylSp_app_left hB hb one_ne_zero, inv_one, one_smul,
    weylSp_app_right hB hb hs]

theorem torusSp_app_orth (hB : B.IsAlt) {v b w : V} (hvw : B v w = 0) (hbw : B b w = 0) (s : K) :
    (torusSp hB v b s).app w = w := by
  rw [torusSp, Gsp.app_mul, weylSp_app_orth hB hvw hbw 1, weylSp_app_orth hB hvw hbw s]

theorem torusSp_mem_lineStabilizer [CharP K 2] (hB : B.IsAlt) {v b : V} (hb : B v b = 1) {s : K}
    (hs : s ≠ 0) : torusSp hB v b s ∈ lineStabilizer B v :=
  ⟨s, hs, torusSp_app_left hB hb hs⟩

/-- Conjugating `Ssp hB v w c` by `torusSp hB v b s` (for `w` orthogonal to `v, b`). -/
theorem torusSp_conj_Ssp [CharP K 2] (hB : B.IsAlt) {v b w : V} (hb : B v b = 1)
    (hvw : B v w = 0) (hbw : B b w = 0) {s : K} (hs : s ≠ 0) (c : K) :
    torusSp hB v b s * Ssp hB v w c * (torusSp hB v b s)⁻¹ =
      Ssp hB v (s • w) (s ^ 2 * c) := by
  rw [Ssp_conj, torusSp_app_left hB hb hs, torusSp_app_orth hB hvw hbw s,
    Ssp_smul_left hB hvw s c]

/-- Conjugating `Ssp hB v w c` by `Tsp hB u r` when `B v u = 0`. -/
theorem Tsp_conj_Ssp (hB : B.IsAlt) {v u : V} (hvu : B v u = 0) (w : V)
    (r c : K) :
    Tsp hB u r * Ssp hB v w c * (Tsp hB u r)⁻¹ =
      Ssp hB v (w + (r * B w u) • u) c := by
  rw [Ssp_conj, Tsp_app, hvu, mul_zero, zero_smul, add_zero, Tsp_app]

/-- Coordinate map `(w, c) ↦ Ssp hB v w c` into `Lsp B hB v`. -/
noncomputable def sspCoord (hB : B.IsAlt) (v : V) (W : Submodule K V)
    (hWv : ∀ w : W, B v (w : V) = 0) (p : W × K) : Lsp B hB v :=
  ⟨Ssp hB v (p.1 : V) p.2, Ssp_mem_Lsp hB (hWv p.1) p.2⟩

theorem sspCoord_mul [CharP K 2] (hB : B.IsAlt) (v : V) (W : Submodule K V)
    (hWv : ∀ w : W, B v (w : V) = 0) (p₁ p₂ : W × K) :
    sspCoord hB v W hWv p₁ * sspCoord hB v W hWv p₂ =
      sspCoord hB v W hWv (p₁.1 + p₂.1, p₁.2 + p₂.2 + B (p₁.1 : V) (p₂.1 : V)) := by
  ext1
  change Ssp hB v (p₁.1 : V) p₁.2 * Ssp hB v (p₂.1 : V) p₂.2 =
    Ssp hB v ((p₁.1 + p₂.1 : W) : V) (p₁.2 + p₂.2 + B (p₁.1 : V) (p₂.1 : V))
  rw [Ssp_mul hB (hWv p₁.1) (hWv p₂.1), Submodule.coe_add,
    isAlt_symm_of_char_two hB (p₂.1 : V) (p₁.1 : V)]

theorem sspCoord_zero (hB : B.IsAlt) (v : V) (W : Submodule K V)
    (hWv : ∀ w : W, B v (w : V) = 0) :
    sspCoord hB v W hWv (0, 0) = 1 := by
  ext1
  exact Ssp_zero hB v

/-- When `W = (span K {v, b})⊥` for a hyperbolic pair `B v b = 1`, `sspCoord` is bijective. -/
theorem sspCoord_bijective (hB : B.IsAlt) {v b : V} (hb : B v b = 1) :
    Function.Bijective
      (sspCoord hB v (B.orthogonal (Submodule.span K {v, b}))
        (fun w => w.2 v (Submodule.subset_span (by simp)))) := by
  set W := B.orthogonal (Submodule.span K {v, b}) with hWdef
  have hWmem : ∀ x : V, x ∈ W ↔ B v x = 0 ∧ B b x = 0 := by
    intro x
    rw [hWdef, LinearMap.BilinForm.mem_orthogonal_iff]
    constructor
    · intro h
      exact ⟨h v (Submodule.subset_span (by simp)), h b (Submodule.subset_span (by simp))⟩
    · rintro ⟨h1, h2⟩ n hn
      obtain ⟨s, r, rfl⟩ := Submodule.mem_span_pair.mp hn
      simp [h1, h2]
  have hWv : ∀ x : W, B v (x : V) = 0 := fun x => ((hWmem (x : V)).mp x.2).1
  have hWb : ∀ x : W, B b (x : V) = 0 := fun x => ((hWmem (x : V)).mp x.2).2
  have hbv : B b v = -1 := by rw [← hB.neg_eq, hb]
  have hbw : ∀ w : V, B b w = -B w b := fun w => (hB.neg_eq w b).symm
  constructor
  · rintro ⟨x, c⟩ ⟨y, d⟩ hxy
    have h1 : siegel B hB v (x : V) c = siegel B hB v (y : V) d :=
      congrArg (fun q : Lsp B hB v => (q.1 : LinearMap.GeneralLinearGroup K V)) hxy
    have h2 : (siegel B hB v (x : V) c : V →ₗ[K] V) b =
        (siegel B hB v (y : V) d : V →ₗ[K] V) b := by rw [h1]
    rw [siegel_apply_partner hB hbv (hWv x) (hWb x),
      siegel_apply_partner hB hbv (hWv y) (hWb y)] at h2
    have h3 := congrArg (B b) h2
    simp only [map_sub, map_smul, smul_eq_mul, hB.self_eq_zero, hWb x, hWb y, hbv] at h3
    have hcd : c = d := by linear_combination h3
    rw [hcd] at h2
    have h4 : (x : V) = y := sub_right_inj.mp (sub_left_inj.mp h2)
    exact Prod.ext (Subtype.ext h4) hcd
  · rintro ⟨g, hg⟩
    obtain ⟨w, c, hw, hgw⟩ := mem_Lsp.mp hg
    have hw₀v : B v (w - (B w b) • v) = 0 := by simp [hw, hB.self_eq_zero]
    have hw₀ : w - (B w b) • v ∈ W := by
      rw [hWmem]
      refine ⟨hw₀v, ?_⟩
      rw [map_sub, map_smul, smul_eq_mul, hbv, hbw w]
      ring
    refine ⟨(⟨w - (B w b) • v, hw₀⟩, c + 2 * B w b), Subtype.ext (Subtype.ext ?_)⟩
    show siegel B hB v (w - (B w b) • v) (c + 2 * B w b) = (g : LinearMap.GeneralLinearGroup K V)
    rw [← siegel_add_smul_self hB hw₀v (B w b) c, sub_add_cancel, hgw]

/-- Equivalence `W × K ≃ Lsp B hB v` for `W = (span K {v, b})⊥`. -/
noncomputable def sspEquiv (hB : B.IsAlt) {v b : V} (hb : B v b = 1) :
    B.orthogonal (Submodule.span K {v, b}) × K ≃ Lsp B hB v :=
  Equiv.ofBijective _ (sspCoord_bijective hB hb)

@[simp]
theorem sspEquiv_apply (hB : B.IsAlt) {v b : V} (hb : B v b = 1)
    (p : B.orthogonal (Submodule.span K {v, b}) × K) :
    sspEquiv hB hb p =
      sspCoord hB v (B.orthogonal (Submodule.span K {v, b}))
        (fun w => w.2 v (Submodule.subset_span (by simp))) p :=
  rfl

/-- Additive homomorphism `projW : Additive (Lsp B hB v) →+ W` projecting onto the
`W`-coordinate. -/
noncomputable def projW [CharP K 2] (hB : B.IsAlt) {v b : V} (hb : B v b = 1) :
    Additive (Lsp B hB v) →+ B.orthogonal (Submodule.span K {v, b}) where
  toFun q := ((sspEquiv hB hb).symm q.toMul).1
  map_zero' := by
    change ((sspEquiv hB hb).symm 1).1 = 0
    rw [← sspCoord_zero hB v (B.orthogonal (Submodule.span K {v, b}))
      (fun w => w.2 v (Submodule.subset_span (by simp))), ← sspEquiv_apply hB hb,
      Equiv.symm_apply_apply]
  map_add' q₁ q₂ := by
    obtain ⟨⟨w₁, c₁⟩, h₁⟩ := (sspEquiv hB hb).surjective q₁.toMul
    obtain ⟨⟨w₂, c₂⟩, h₂⟩ := (sspEquiv hB hb).surjective q₂.toMul
    change ((sspEquiv hB hb).symm (q₁.toMul * q₂.toMul)).1 =
      ((sspEquiv hB hb).symm q₁.toMul).1 +
        ((sspEquiv hB hb).symm q₂.toMul).1
    rw [← h₁, ← h₂, Equiv.symm_apply_apply, Equiv.symm_apply_apply, sspEquiv_apply,
      sspEquiv_apply, sspCoord_mul, ← sspEquiv_apply hB hb, Equiv.symm_apply_apply]

@[simp]
theorem projW_sspEquiv [CharP K 2] (hB : B.IsAlt) {v b : V} (hb : B v b = 1)
    (w : B.orthogonal (Submodule.span K {v, b})) (c : K) :
    projW hB hb (Additive.ofMul (sspEquiv hB hb (w, c))) = w := by
  change ((sspEquiv hB hb).symm (sspEquiv hB hb (w, c))).1 = w
  rw [Equiv.symm_apply_apply]

/-- The central transvection subgroup `Z₀ = {Tsp hB v c | c : K}` inside `Lsp B hB v`. -/
def tspSubgroup [CharP K 2] (hB : B.IsAlt) (v : V) : Subgroup (Lsp B hB v) where
  carrier := {q : Lsp B hB v | ∃ c : K, q.1 = Tsp hB v c}
  one_mem' := ⟨0, Subtype.ext (symplecticTransvection_zero hB v).symm⟩
  mul_mem' := by
    rintro q₁ q₂ ⟨c₁, h₁⟩ ⟨c₂, h₂⟩
    refine ⟨c₁ + c₂, ?_⟩
    change q₁.1 * q₂.1 = Tsp hB v (c₁ + c₂)
    rw [h₁, h₂]
    exact Subtype.ext (symplecticTransvection_mul hB v c₁ c₂)
  inv_mem' := by
    rintro q ⟨c, h⟩
    refine ⟨c, ?_⟩
    change q.1⁻¹ = Tsp hB v c
    rw [h, inv_eq_iff_mul_eq_one]
    exact Tsp_mul_self hB v c

theorem mem_tspSubgroup [CharP K 2] {hB : B.IsAlt} {v : V} {q : Lsp B hB v} :
    q ∈ tspSubgroup hB v ↔ ∃ c : K, q.1 = Tsp hB v c := Iff.rfl

theorem mem_tspSubgroup_iff_projW_eq_zero [CharP K 2] (hB : B.IsAlt) {v b : V} (hb : B v b = 1)
    (q : Lsp B hB v) :
    q ∈ tspSubgroup hB v ↔ projW hB hb (Additive.ofMul q) = 0 := by
  obtain ⟨⟨w, c⟩, rfl⟩ := (sspEquiv hB hb).surjective q
  rw [projW_sspEquiv, mem_tspSubgroup]
  constructor
  · rintro ⟨d, hd⟩
    have h1 : sspEquiv hB hb (w, c) = sspEquiv hB hb (0, d) := by
      ext1
      change Ssp hB v (w : V) c = Ssp hB v 0 d
      rw [Ssp_zero_left]
      exact hd
    exact congrArg Prod.fst ((sspEquiv hB hb).injective h1)
  · rintro rfl
    exact ⟨c, Ssp_zero_left hB v c⟩

/-- The subgroup `lineStabilizer B v` preserves `tspSubgroup hB v` under `conjLsp`. -/
theorem conjLsp_mem_tspSubgroup [CharP K 2] (hB : B.IsAlt) (v : V) (n : lineStabilizer B v)
    {q : Lsp B hB v} (hq : q ∈ tspSubgroup hB v) :
    conjLsp hB v n q ∈ tspSubgroup hB v := by
  obtain ⟨c, hc⟩ := mem_tspSubgroup.mp hq
  obtain ⟨s, hs, hn⟩ := n.2
  rw [mem_tspSubgroup]
  refine ⟨s ^ 2 * c, ?_⟩
  change (n : Gsp B) * q.1 * (n : Gsp B)⁻¹ = Tsp hB v (s ^ 2 * c)
  rw [hc, Tsp_conj, hn, Tsp_smul]

/-- If `H` is a proper subgroup of `Gsp B` and `v ≠ 0`, some conjugate of `H` in `Gsp B` does not
contain all transvections `Tsp hB v c` (`c : K`). -/
theorem exists_conj_tsp_not_mem_of_ne_top [FiniteDimensional K V] (hB : B.IsAlt)
    (hBn : B.Nondegenerate) {v : V} (hv : v ≠ 0) {H : Subgroup (Gsp B)} (hH : H ≠ ⊤) :
    ∃ (H' : Subgroup (Gsp B)), H'.index = H.index ∧ ∃ c : K, Tsp hB v c ∉ H' := by
  by_contra! hall
  apply hH
  rw [eq_top_iff]
  have hgen : bilinIsometryGroup B ≤ H.map (bilinIsometryGroup B).subtype := by
    refine (alternating_transvection_generation hB hBn).le.trans ?_
    rw [Subgroup.closure_le]
    rintro _ ⟨a, c, rfl⟩
    by_cases ha : a = 0
    · subst ha
      refine ⟨1, H.one_mem, ?_⟩
      exact Units.ext (LinearMap.ext fun x => by simp [symplecticTransvection_apply])
    · obtain ⟨g, hg⟩ := exists_gsp_apply_eq hB hBn hv ha
      let H' := H.comap (MulAut.conj g).toMonoidHom
      have hidx : H'.index = H.index :=
        Subgroup.index_comap_of_surjective H (MulAut.conj g).surjective
      have hmem : Tsp hB v c ∈ H' := hall H' hidx c
      have hmem' : g * Tsp hB v c * g⁻¹ ∈ H := hmem
      rw [Tsp_conj, hg] at hmem'
      exact ⟨Tsp hB a c, hmem', rfl⟩
  intro x _
  obtain ⟨y, hyH, hyx⟩ := hgen x.2
  have : x = y := Subtype.ext hyx.symm
  rwa [this]

end PointRadicalCoords

end Maroti
