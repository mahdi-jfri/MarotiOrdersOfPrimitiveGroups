module

public import Maroti.AlmostSimple.Basic
public import Maroti.Sporadic.AutBound
import Maroti.Sporadic.CubicWitness
import CFSG.Sporadic.He
import CFSG.Certificates.Kernel.LocalQTSecSound
import CFSG.Certificates.Kernel.LocalQTSecLemmas
import Certificates.Kernel.LocalQT.SR.HeLocal
import all CFSG.Blueprint.NativeSporadic

/-!
# Sporadic Simple Group `He`

This file proves Maróti's bound `Nat.card G ≤ bound (Nat.card α)` for primitive almost simple
groups `G` whose socle `S` is isomorphic to Held's group `He`.

Using the kernel certificate data `CFSG.KD.LQT.He7` (`Certificates/Kernel/LocalQT/SR/HeLocal.lean`),
`He` has an extraspecial Sylow `7`-subgroup `Q = Subgroup.closure {x, y}` of order `7³ = 343` and
exponent `7` normalized by two elements `g₁` (acting on `Q / Z(Q) ≅ (ZMod 7)²` as `diag(2, 1)`) and
`g₂` (acting on `Q / Z(Q)` by `(i, j) ↦ (6 j, 6 i)`, corresponding to SSA entry `V 18` of
`CFSG.KD.LQT.He7`). Since `g₁` and `g₂` have no common invariant line in `(ZMod 7)²`,
`Maroti.CubicWitness.two_mul_sq_le_index_of_pair_of_ne_top` shows that every proper subgroup of `He`
has index at least `2 * 7² = 98 ≥ 51`.
-/

@[expose] public section

namespace Maroti

open CFSG.Blueprint CFSG.KC.Ord CFSG.KC.LQT CFSG.KS.Ord CFSG.SectionRank
open scoped commutatorElement

/-- Kernel boolean check that the SSA entry `V ih2` in a precomputed LQT table has order dividing
`oh2` and conjugates `V ix`, `V iy`, and `commM c r (V ix) (V iy)` into the specified normal-form
words. -/
private noncomputable def heConj3OK (c : Lay) (V : Nat → Nat)
    (N ix iy ih2 r oh2 a2 b2 cc2 dd2 k2 l2 μ2 : Nat) : Bool :=
  andB (Nat.blt ih2 N) (andB (Nat.blt (nat_lit 0) oh2) (andB (Nat.beq (c.pow (V ih2) oh2) c.ONE)
  (strictB (commM c r (V ix) (V iy)) fun Z =>
  (andB (conjOK c (V ih2) (V ix) (c.mul (c.mul (c.pow (V ix) a2) (c.pow (V iy) b2)) (c.pow Z k2)))
  (andB (conjOK c (V ih2) (V iy) (c.mul (c.mul (c.pow (V ix) cc2) (c.pow (V iy) dd2)) (c.pow Z l2)))
    (conjOK c (V ih2) Z (c.pow Z μ2)))))))

private theorem cub_pair_sound (c : Lay) (hc : c.ok = true) {LA LB : List Char} {V P : ℕ → ℕ}
    {N ix iy ih r oh a b cc dd k l μ t : ℕ} {σ : List ℕ}
    {ih2 oh2 a2 b2 cc2 dd2 k2 l2 μ2 : ℕ}
    (hA : decOK c (V 0) LA = true) (hB : decOK c (V 1) LB = true) (h1 : V 2 = c.ONE)
    (hs : StepsTo (stepOK c V P) N)
    (hq : cubOK c V N ix iy ih r oh a b cc dd k l μ t σ = true)
    (hq2 : heConj3OK c V N ix iy ih2 r oh2 a2 b2 cc2 dd2 k2 l2 μ2 = true) :
    ∃ x y g₁ g₂ : (NativeSporadic.seedMonoid c.p c.d 1 (String.ofList LA) (String.ofList LB))ˣ,
      x ^ r = 1 ∧ y ^ r = 1 ∧ ⁅x, y⁆ ≠ 1 ∧ Commute ⁅x, y⁆ x ∧ Commute ⁅x, y⁆ y ∧
      Nat.card (Subgroup.closure ({x, y} : Set _)) = r ^ 3 ∧
      g₁ * x * g₁⁻¹ = x ^ a * y ^ b * ⁅x, y⁆ ^ k ∧
      g₁ * y * g₁⁻¹ = x ^ cc * y ^ dd * ⁅x, y⁆ ^ l ∧
      g₁ * ⁅x, y⁆ * g₁⁻¹ = ⁅x, y⁆ ^ μ ∧
      g₂ * x * g₂⁻¹ = x ^ a2 * y ^ b2 * ⁅x, y⁆ ^ k2 ∧
      g₂ * y * g₂⁻¹ = x ^ cc2 * y ^ dd2 * ⁅x, y⁆ ^ l2 ∧
      g₂ * ⁅x, y⁆ * g₂⁻¹ = ⁅x, y⁆ ^ μ2 := by
  set S := NativeSporadic.seedMonoid c.p c.d 1 (String.ofList LA) (String.ofList LB)
  have hv := SecS.vals_sound c hc hA hB h1 hs
  unfold cubOK at hq
  obtain ⟨hix, hq⟩ := SecS.andT hq
  obtain ⟨hiy, hq⟩ := SecS.andT hq
  obtain ⟨hih, hq⟩ := SecS.andT hq
  obtain ⟨hr, hq⟩ := SecS.andT hq
  obtain ⟨hoh, hq⟩ := SecS.andT hq
  obtain ⟨hXr, hq⟩ := SecS.andT hq
  obtain ⟨hYr, hq⟩ := SecS.andT hq
  obtain ⟨hHo, hq⟩ := SecS.andT hq
  rw [SecS.strictB_eq] at hq
  obtain ⟨hZt, hq⟩ := SecS.andT hq
  obtain ⟨hZX, hq⟩ := SecS.andT hq
  obtain ⟨hZY, hq⟩ := SecS.andT hq
  obtain ⟨hHX, hq⟩ := SecS.andT hq
  obtain ⟨hHY, hq⟩ := SecS.andT hq
  obtain ⟨hHZ, hnf⟩ := SecS.andT hq
  unfold heConj3OK at hq2
  obtain ⟨hih2, hq2⟩ := SecS.andT hq2
  obtain ⟨hoh2, hq2⟩ := SecS.andT hq2
  obtain ⟨hH2o, hq2⟩ := SecS.andT hq2
  rw [SecS.strictB_eq] at hq2
  obtain ⟨hH2X, hq2⟩ := SecS.andT hq2
  obtain ⟨hH2Y, hH2Z⟩ := SecS.andT hq2
  have ht : t < c.d := Nat.blt_eq.mp (SecS.andT hnf).1
  obtain ⟨cX, mX⟩ := hv _ (Nat.blt_eq.mp hix)
  obtain ⟨cY, mY⟩ := hv _ (Nat.blt_eq.mp hiy)
  obtain ⟨cH, mH⟩ := hv _ (Nat.blt_eq.mp hih)
  obtain ⟨cH2, mH2⟩ := hv _ (Nat.blt_eq.mp hih2)
  have hr' : 0 < r := Nat.blt_eq.mp hr
  have hoh' : 0 < oh := Nat.blt_eq.mp hoh
  have hoh2' : 0 < oh2 := Nat.blt_eq.mp hoh2
  have eX := SecS.pow_one_of c hc cX hXr
  have eY := SecS.pow_one_of c hc cY hYr
  have eH := SecS.pow_one_of c hc cH hHo
  have eH2 := SecS.pow_one_of c hc cH2 hH2o
  let x := LocalWitness.unitOf S mX hr'.ne' eX
  let y := LocalWitness.unitOf S mY hr'.ne' eY
  let g₁ := LocalWitness.unitOf S mH hoh'.ne' eH
  let g₂ := LocalWitness.unitOf S mH2 hoh2'.ne' eH2
  have fx : LocalWitness.valHom S x = ordMat c.p c.d c.w c.S (V ix) :=
    LocalWitness.valHom_unitOf S _ _ _
  have fy : LocalWitness.valHom S y = ordMat c.p c.d c.w c.S (V iy) :=
    LocalWitness.valHom_unitOf S _ _ _
  have fg₁ : LocalWitness.valHom S g₁ = ordMat c.p c.d c.w c.S (V ih) :=
    LocalWitness.valHom_unitOf S _ _ _
  have fg₂ : LocalWitness.valHom S g₂ = ordMat c.p c.d c.w c.S (V ih2) :=
    LocalWitness.valHom_unitOf S _ _ _
  have hx : x ^ r = 1 := LocalWitness.unitOf_pow S mX _ eX
  have hy : y ^ r = 1 := LocalWitness.unitOf_pow S mY _ eY
  have hZ : Canon c.p c.d c.w (commM c r (V ix) (V iy)) ∧
      LocalWitness.valHom S ⁅x, y⁆ = ordMat c.p c.d c.w c.S (commM c r (V ix) (V iy)) := by
    obtain ⟨d1, g1⟩ := SecS.mul_sound c hc cX cY
    obtain ⟨d2, g2⟩ := SecS.pow_sound c hc cX (r - 1)
    obtain ⟨d3, g3⟩ := SecS.pow_sound c hc cY (r - 1)
    obtain ⟨d4, g4⟩ := SecS.mul_sound c hc d1 d2
    obtain ⟨d5, g5⟩ := SecS.mul_sound c hc d4 d3
    refine ⟨d5, ?_⟩
    rw [commutatorElement_def, map_mul, map_mul, map_mul,
      LocalWitness.valHom_inv_of_pow S hr'.ne' hx, LocalWitness.valHom_inv_of_pow S hr'.ne' hy,
      fx, fy]
    change _ = ordMat c.p c.d c.w c.S
      (c.mul (c.mul (c.mul (V ix) (V iy)) (c.pow (V ix) (r - 1))) (c.pow (V iy) (r - 1)))
    rw [g5, g4, g1, g2, g3]
  obtain ⟨cZ, fz⟩ := hZ
  have comm : ∀ {u : Sˣ} {U : ℕ}, Canon c.p c.d c.w U →
      LocalWitness.valHom S u = ordMat c.p c.d c.w c.S U →
      Nat.beq (c.mul (commM c r (V ix) (V iy)) U) (c.mul U (commM c r (V ix) (V iy))) = true →
      Commute ⁅x, y⁆ u := by
    intro u U cU fu hcm
    apply LocalWitness.valHom_injective S
    rw [map_mul, map_mul, fz, fu]
    exact SecS.mul_eq_of c hc cZ cU cU cZ hcm
  have conj : ∀ {g w u : Sˣ} {H W U : ℕ}, Canon c.p c.d c.w H →
      LocalWitness.valHom S g = ordMat c.p c.d c.w c.S H → Canon c.p c.d c.w W →
      LocalWitness.valHom S w = ordMat c.p c.d c.w c.S W → Canon c.p c.d c.w U →
      LocalWitness.valHom S u = ordMat c.p c.d c.w c.S U → conjOK c H U W = true →
      g * u * g⁻¹ = w := by
    intro g w u H W U cH fg cW fw cU fu hcj
    rw [mul_inv_eq_iff_eq_mul]
    apply LocalWitness.valHom_injective S
    rw [map_mul, map_mul, fg, fu, fw]
    exact SecS.conj_mat c hc cH cU cW hcj
  have word : ∀ i j k : ℕ, Canon c.p c.d c.w (c.mul (c.mul (c.pow (V ix) i) (c.pow (V iy) j))
      (c.pow (commM c r (V ix) (V iy)) k)) ∧
      LocalWitness.valHom S (x ^ i * y ^ j * ⁅x, y⁆ ^ k) = ordMat c.p c.d c.w c.S
        (c.mul (c.mul (c.pow (V ix) i) (c.pow (V iy) j)) (c.pow (commM c r (V ix) (V iy)) k)) := by
    intro i j k
    obtain ⟨d1, g1⟩ := SecS.pow_sound c hc cX i
    obtain ⟨d2, g2⟩ := SecS.pow_sound c hc cY j
    obtain ⟨d3, g3⟩ := SecS.pow_sound c hc cZ k
    obtain ⟨d4, g4⟩ := SecS.mul_sound c hc d1 d2
    obtain ⟨d5, g5⟩ := SecS.mul_sound c hc d4 d3
    exact ⟨d5, by rw [map_mul, map_mul, map_pow, map_pow, map_pow, fx, fy, fz, g5, g4, g1, g2, g3]⟩
  have hz1 : ⁅x, y⁆ ≠ 1 := by
    intro he
    apply SecS.mat_ne_one c hc ht cZ hZt
    rw [← fz, he, map_one]
  have hzx : Commute ⁅x, y⁆ x := comm cX fx hZX
  have hzy : Commute ⁅x, y⁆ y := comm cY fy hZY
  obtain ⟨cP, fP⟩ := SecS.pow_sound c hc cZ μ
  obtain ⟨cP2, fP2⟩ := SecS.pow_sound c hc cZ μ2
  refine ⟨x, y, g₁, g₂, hx, hy, hz1, hzx, hzy, ?_,
    conj cH fg₁ (word a b k).1 (word a b k).2 cX fx hHX,
    conj cH fg₁ (word cc dd l).1 (word cc dd l).2 cY fy hHY,
    conj cH fg₁ cP (by rw [map_pow, fz, fP]) cZ fz hHZ,
    conj cH2 fg₂ (word a2 b2 k2).1 (word a2 b2 k2).2 cX fx hH2X,
    conj cH2 fg₂ (word cc2 dd2 l2).1 (word cc2 dd2 l2).2 cY fy hH2Y,
    conj cH2 fg₂ cP2 (by rw [map_pow, fz, fP2]) cZ fz hH2Z⟩
  refine LocalWitness.card_closure_eq_cube hr' hx hy hzx hzy ?_
  rintro ⟨i, j, k⟩ ⟨i', j', k'⟩ hijk
  have hm := congrArg (LocalWitness.valHom S) hijk
  simp only [map_mul, map_pow, fx, fy, fz] at hm
  obtain ⟨e1, e2, e3⟩ := SecS.normal3_inj c hc cX cY cZ hr' hnf i.isLt j.isLt k.isLt i'.isLt
    j'.isLt k'.isLt hm
  exact Prod.ext (Fin.ext e1) (Prod.ext (Fin.ext e2) (Fin.ext e3))

set_option maxRecDepth 100000 in
private theorem he7_conj2 :
    heConj3OK CFSG.KD.LQT.He7.lay CFSG.KD.LQT.He7.V 37 CFSG.KD.LQT.He7.ix CFSG.KD.LQT.He7.iy
      18 7 2 0 6 6 0 0 0 6 = true := by
  decide +kernel

private theorem he_sylow7_pair_witness :
    ∃ x y g₁ g₂ : NativeSporadic.He,
      x ^ 7 = 1 ∧ y ^ 7 = 1 ∧ ⁅x, y⁆ ≠ 1 ∧ Commute ⁅x, y⁆ x ∧ Commute ⁅x, y⁆ y ∧
      Nat.card (Subgroup.closure ({x, y} : Set NativeSporadic.He)) = 7 ^ 3 ∧
      g₁ * x * g₁⁻¹ = x ^ 2 * y ^ 0 * ⁅x, y⁆ ^ 3 ∧
      g₁ * y * g₁⁻¹ = x ^ 0 * y ^ 1 * ⁅x, y⁆ ^ 0 ∧
      g₁ * ⁅x, y⁆ * g₁⁻¹ = ⁅x, y⁆ ^ 2 ∧
      g₂ * x * g₂⁻¹ = x ^ 0 * y ^ 6 * ⁅x, y⁆ ^ 0 ∧
      g₂ * y * g₂⁻¹ = x ^ 6 * y ^ 0 * ⁅x, y⁆ ^ 0 ∧
      g₂ * ⁅x, y⁆ * g₂⁻¹ = ⁅x, y⁆ ^ 6 := by
  have h := cub_pair_sound _ CFSG.KD.LQT.He7.lay_ok CFSG.KD.LQT.He7.decA CFSG.KD.LQT.He7.decB
    CFSG.KD.LQT.He7.one CFSG.KD.LQT.He7.steps CFSG.KD.LQT.He7.cub he7_conj2
  rw [← CFSG.KD.LQT.He7.LA_eq, ← CFSG.KD.LQT.He7.LB_eq] at h
  exact h

/-- Every proper subgroup of `He` has index at least `98`. -/
theorem index_ge_He {S : Type*} [Group S] [Finite S] [IsSimpleGroup S]
    (e : S ≃* NativeSporadic.Carrier .He) {H : Subgroup S} (hH : H ≠ ⊤) :
    98 ≤ H.index := by
  have : Fact (Nat.Prime 7) := ⟨by decide⟩
  obtain ⟨x, y, g₁, g₂, hx, hy, hz1, hzx, hzy, hcard,
    hg₁x, hg₁y, hg₁z, hg₂x, hg₂y, hg₂z⟩ := he_sylow7_pair_witness
  have hirr : ∀ i j : ZMod 7, (i ≠ 0 ∨ j ≠ 0) →
      (∀ m : ZMod 7, ((2 : ℕ) * i + (0 : ℕ) * j : ZMod 7) ≠ m * i ∨
        ((0 : ℕ) * i + (1 : ℕ) * j : ZMod 7) ≠ m * j) ∨
      (∀ m : ZMod 7, ((0 : ℕ) * i + (6 : ℕ) * j : ZMod 7) ≠ m * i ∨
        ((6 : ℕ) * i + (0 : ℕ) * j : ZMod 7) ≠ m * j) := by decide +revert
  exact CubicWitness.two_mul_sq_le_index_of_pair_of_ne_top
    hx hy hz1 hzx hzy hcard hg₁x hg₁y hg₁z hg₂x hg₂y hg₂z hirr e hH

/-- Maróti's bound for primitive almost simple groups with socle `He`. -/
theorem sporadicCase_He {α : Type} [Finite α] (G : Subgroup (Equiv.Perm α)) (S : Type)
    [Group S] [MulAction.IsPreprimitive G α] (hS : IsAlmostSimpleWith G S)
    (he : Nonempty (S ≃* NativeSporadic.Carrier .He)) :
    Nat.card G ≤ bound (Nat.card α) := by
  have : Finite S := hS.finite
  have : IsSimpleGroup S := hS.isSimpleGroup
  obtain ⟨e⟩ := he
  have hcard : Nat.card S = 4030387200 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.He.card_He
  refine hS.card_le_bound_of_outerAut_dvd (n₀ := 98) (c := 2) (by decide)
    (fun H hH => index_ge_He e hH)
    (card_outer_dvd_two_of_sporadicSocle ⟨.He, ⟨e⟩⟩) ?_
  rw [hcard]
  decide

end Maroti
