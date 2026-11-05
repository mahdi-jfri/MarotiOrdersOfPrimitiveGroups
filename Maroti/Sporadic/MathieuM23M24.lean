module

public import Maroti.AlmostSimple.Basic
public import Maroti.Sporadic.AutBound
import Maroti.MinDegree.Basic
import Maroti.Sporadic.Mathieu
import CFSG.Sporadic.M23.M23Properties
import CFSG.Sporadic.Mathieu.M23
import CFSG.Sporadic.Schreier.MathieuOddCoreM23
import CFSG.Sporadic.Bridge.M23Surj
import CFSG.Sporadic.Mathieu.M24
import CFSG.Sporadic.Schreier.MathieuOddCoreM24
import CFSG.Sporadic.Bridge.M24Surj

/-!
# Mathieu Groups `M₂₃` and `M₂₄`

This file proves `sporadicCase_M23` and `sporadicCase_M24`.
For both groups we bound the normalizer of a Sylow `11`-subgroup by `220` to rule out subgroups
of order `425040` (index `24` in `M₂₃`, or point-stabilizer of a transitive index-`24` subgroup in
`M₂₄`), and combine `validOrbits` with `not_exists_subgroup_index_sub_one` to rule out index `23`
and `27` in `M₂₄`.
-/

@[expose] public section

namespace Maroti

open CFSG.Blueprint MulAction

/-! ### `M₂₃` -/

namespace M23Proof

open CFSG.M23.M23Group

private def x11Perm : Perm23 := a * b⁻¹ * a * b * a * b * a * b

private theorem x11Perm_mem : x11Perm ∈ H0 := by
  have ha : a ∈ H0 := baseGen_mem 0
  have hb : b ∈ H0 := baseGen_mem 1
  unfold x11Perm
  repeat' apply H0.mul_mem
  all_goals first | exact ha | exact hb | exact H0.inv_mem hb

private def x11 : H0 := ⟨x11Perm, x11Perm_mem⟩

private theorem orderOf_x11 : orderOf x11 = 11 := by
  rw [← Subgroup.orderOf_coe]
  have : Fact (Nat.Prime 11) := ⟨by decide⟩
  exact orderOf_eq_prime
    (by decide +kernel : x11Perm ^ 11 = 1)
    (by decide +kernel : x11Perm ≠ 1)

private abbrev P11 : Subgroup H0 := Subgroup.zpowers x11

private theorem card_P11 : Nat.card P11 = 11 := by
  rw [Nat.card_zpowers, orderOf_x11]

private abbrev C11 : Subgroup H0 := Subgroup.centralizer (P11 : Set H0)

private theorem comm_x11_pow (g : C11) (k : ℕ) (p : Fin 23) :
    (g.1 : Perm23) ((x11Perm ^ k) p) = (x11Perm ^ k) ((g.1 : Perm23) p) := by
  have hcomm : x11 * g.1 = g.1 * x11 :=
    Subgroup.mem_centralizer_iff.mp g.2 x11 (Subgroup.mem_zpowers x11)
  have hcomm' : Commute (g.1 : Perm23) x11Perm :=
    (congrArg Subtype.val hcomm).symm
  have hpow : (g.1 : Perm23) * x11Perm ^ k = x11Perm ^ k * (g.1 : Perm23) :=
    hcomm'.pow_right k
  exact Equiv.Perm.ext_iff.mp hpow p

private theorem x11_orb1 : x11Perm 0 = 1 := by decide +kernel
private theorem x11_orb2 : (x11Perm ^ 10) 0 = 2 := by decide +kernel
private theorem x11_orb3 : (x11Perm ^ 3) 0 = 3 := by decide +kernel
private theorem x11_orb4 : (x11Perm ^ 4) 0 = 4 := by decide +kernel
private theorem x11_orb5 : (x11Perm ^ 2) 0 = 5 := by decide +kernel
private theorem x11_fix14 : x11Perm 14 = 14 := by decide +kernel

private theorem stabilizer_C11_zero_eq_bot : stabilizer C11 (0 : Fin 23) = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  have h0 : (g.1 : Perm23) 0 = 0 := hg
  have h1 : (g.1 : Perm23) 1 = 1 := by
    rw [← x11_orb1, ← pow_one x11Perm, comm_x11_pow g 1 0, pow_one, h0, x11_orb1]
  have h2 : (g.1 : Perm23) 2 = 2 := by
    rw [← x11_orb2, comm_x11_pow g 10 0, h0, x11_orb2]
  have h3 : (g.1 : Perm23) 3 = 3 := by
    rw [← x11_orb3, comm_x11_pow g 3 0, h0, x11_orb3]
  have h4 : (g.1 : Perm23) 4 = 4 := by
    rw [← x11_orb4, comm_x11_pow g 4 0, h0, x11_orb4]
  have h5 : (g.1 : Perm23) 5 = 5 := by
    rw [← x11_orb5, comm_x11_pow g 2 0, h0, x11_orb5]
  let g6 : H6 := ⟨inH5 g.1.1 g.1.2 h0 h1 h2 h3 h4, h5⟩
  have hg6 : g6 = 1 := @Subsingleton.elim H6 H6_subsingleton g6 1
  have hval : (g.1 : Perm23) = 1 :=
    congrArg (fun z : H6 => (z.1.1.1.1.1.1 : Perm23)) hg6
  exact Subtype.ext (Subtype.ext hval)

private theorem not_mem_orbit_C11_fourteen : (14 : Fin 23) ∉ orbit C11 (0 : Fin 23) := by
  rintro ⟨g, hg⟩
  have h0 : (g.1 : Perm23) 0 = 14 := hg
  have h1 : (g.1 : Perm23) 1 = 14 := by
    rw [← x11_orb1, ← pow_one x11Perm, comm_x11_pow g 1 0, pow_one, h0, x11_fix14]
  have heq : (1 : Fin 23) = 0 := (g.1 : Perm23).injective (h1.trans h0.symm)
  exact (by decide : (1 : Fin 23) ≠ 0) heq

private theorem card_C11_dvd : Nat.card C11 ∣ 22 := by
  have hstab : Nat.card (stabilizer C11 (0 : Fin 23)) = 1 := by
    rw [stabilizer_C11_zero_eq_bot, Subgroup.card_bot]
  have hcard_eq : Nat.card C11 = Nat.card (orbit C11 (0 : Fin 23)) := by
    have h := (stabilizer C11 (0 : Fin 23)).index_mul_card
    rw [hstab, mul_one, index_stabilizer C11 (0 : Fin 23), ← Nat.card_coe_set_eq] at h
    exact h.symm
  let emb : orbit C11 (0 : Fin 23) → {p : Fin 23 // p ≠ 14} :=
    fun x => ⟨x.1, fun h => not_mem_orbit_C11_fourteen (h ▸ x.2)⟩
  have hemb : Function.Injective emb :=
    fun x y h => Subtype.ext (congrArg (fun z : {p : Fin 23 // p ≠ 14} => z.1) h)
  have h22 : Nat.card {p : Fin 23 // p ≠ 14} = 22 := by
    rw [Nat.card_eq_fintype_card]
    decide
  have hle : Nat.card C11 ≤ 22 :=
    (hcard_eq.trans_le (Nat.card_le_card_of_injective emb hemb)).trans h22.le
  have hP_le_C : P11 ≤ C11 := by
    intro y hy z hz
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    simp only [← zpow_add, add_comm]
  have hdvd11 : 11 ∣ Nat.card C11 := by
    rw [← card_P11]
    exact Subgroup.card_dvd_of_le hP_le_C
  have hpos : 0 < Nat.card C11 := Nat.card_pos
  obtain ⟨k, hk⟩ := hdvd11
  have hk_cases : k = 1 ∨ k = 2 := by omega
  rcases hk_cases with rfl | rfl
  · rw [hk]; decide
  · rw [hk]

private theorem card_normalizer_P11_dvd :
    Nat.card (Subgroup.normalizer (P11 : Set H0)) ∣ 220 := by
  have : Fact (Nat.Prime 11) := ⟨by decide⟩
  have h1 := card_normalizer_dvd_mul_totient P11 card_P11
  have h2 : Nat.card C11 * (11 - 1) ∣ 22 * 10 :=
    mul_dvd_mul card_C11_dvd (dvd_refl 10)
  exact h1.trans h2

private theorem not_exists_subgroup_index_24_H0 (H : Subgroup H0) : H.index ≠ 24 := by
  intro hidx
  have hcard_H0 : Nat.card H0 = 10200960 := by
    rw [Nat.card_eq_fintype_card, card_M23]
  have hcard_H : Nat.card H = 425040 := by
    have h := H.index_mul_card
    rw [hidx, hcard_H0] at h
    omega
  have : Fact (Nat.Prime 11) := ⟨by decide⟩
  have hval := hasValidSylowNormalizer_of_dvd P11 card_P11
    (by rw [hcard_H0]; decide) card_normalizer_P11_dvd (by decide)
    (H := H) (by rw [hcard_H]; decide)
  rw [hcard_H] at hval
  exact absurd hval (by decide)

private def x23Perm : Perm23 := a * b

private theorem x23Perm_mem : x23Perm ∈ H0 :=
  H0.mul_mem (baseGen_mem 0) (baseGen_mem 1)

private def x23 : H0 := ⟨x23Perm, x23Perm_mem⟩

private theorem orderOf_x23 : orderOf x23 = 23 := by
  rw [← Subgroup.orderOf_coe]
  have : Fact (Nat.Prime 23) := ⟨by decide⟩
  exact orderOf_eq_prime
    (by decide +kernel : x23Perm ^ 23 = 1)
    (by decide +kernel : x23Perm ≠ 1)

private abbrev P23 : Subgroup H0 := Subgroup.zpowers x23

private theorem card_P23 : Nat.card P23 = 23 := by
  rw [Nat.card_zpowers, orderOf_x23]

private abbrev C23 : Subgroup H0 := Subgroup.centralizer (P23 : Set H0)

private theorem comm_x23_pow (g : C23) (k : ℕ) (p : Fin 23) :
    (g.1 : Perm23) ((x23Perm ^ k) p) = (x23Perm ^ k) ((g.1 : Perm23) p) := by
  have hcomm : x23 * g.1 = g.1 * x23 :=
    Subgroup.mem_centralizer_iff.mp g.2 x23 (Subgroup.mem_zpowers x23)
  have hcomm' : Commute (g.1 : Perm23) x23Perm :=
    (congrArg Subtype.val hcomm).symm
  have hpow : (g.1 : Perm23) * x23Perm ^ k = x23Perm ^ k * (g.1 : Perm23) :=
    hcomm'.pow_right k
  exact Equiv.Perm.ext_iff.mp hpow p

private theorem x23_orb1 : (x23Perm ^ 11) 0 = 1 := by decide +kernel
private theorem x23_orb2 : (x23Perm ^ 10) 0 = 2 := by decide +kernel
private theorem x23_orb3 : (x23Perm ^ 5) 0 = 3 := by decide +kernel
private theorem x23_orb4 : (x23Perm ^ 6) 0 = 4 := by decide +kernel
private theorem x23_orb5 : (x23Perm ^ 20) 0 = 5 := by decide +kernel

private theorem stabilizer_C23_zero_eq_bot : stabilizer C23 (0 : Fin 23) = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  have h0 : (g.1 : Perm23) 0 = 0 := hg
  have h1 : (g.1 : Perm23) 1 = 1 := by
    rw [← x23_orb1, comm_x23_pow g 11 0, h0, x23_orb1]
  have h2 : (g.1 : Perm23) 2 = 2 := by
    rw [← x23_orb2, comm_x23_pow g 10 0, h0, x23_orb2]
  have h3 : (g.1 : Perm23) 3 = 3 := by
    rw [← x23_orb3, comm_x23_pow g 5 0, h0, x23_orb3]
  have h4 : (g.1 : Perm23) 4 = 4 := by
    rw [← x23_orb4, comm_x23_pow g 6 0, h0, x23_orb4]
  have h5 : (g.1 : Perm23) 5 = 5 := by
    rw [← x23_orb5, comm_x23_pow g 20 0, h0, x23_orb5]
  let g6 : H6 := ⟨inH5 g.1.1 g.1.2 h0 h1 h2 h3 h4, h5⟩
  have hg6 : g6 = 1 := @Subsingleton.elim H6 H6_subsingleton g6 1
  have hval : (g.1 : Perm23) = 1 :=
    congrArg (fun z : H6 => (z.1.1.1.1.1.1 : Perm23)) hg6
  exact Subtype.ext (Subtype.ext hval)

private theorem card_C23_dvd : Nat.card C23 ∣ 23 := by
  have hstab : Nat.card (stabilizer C23 (0 : Fin 23)) = 1 := by
    rw [stabilizer_C23_zero_eq_bot, Subgroup.card_bot]
  have hcard_eq : Nat.card C23 = Nat.card (orbit C23 (0 : Fin 23)) := by
    have h := (stabilizer C23 (0 : Fin 23)).index_mul_card
    rw [hstab, mul_one, index_stabilizer C23 (0 : Fin 23), ← Nat.card_coe_set_eq] at h
    exact h.symm
  have hle : Nat.card C23 ≤ 23 := by
    have h23 : Nat.card (Fin 23) = 23 := Nat.card_fin 23
    exact
      (hcard_eq.trans_le (Nat.card_le_card_of_injective Subtype.val Subtype.val_injective)).trans
        h23.le
  have hP_le_C : P23 ≤ C23 := by
    intro y hy z hz
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    simp only [← zpow_add, add_comm]
  have hdvd23 : 23 ∣ Nat.card C23 := by
    have hdvd := Subgroup.card_dvd_of_le hP_le_C
    rwa [card_P23] at hdvd
  have hpos : 0 < Nat.card C23 := Nat.card_pos
  obtain ⟨k, hk⟩ := hdvd23
  have hk1 : k = 1 := by omega
  subst hk1
  rw [hk]

private theorem card_normalizer_P23_dvd :
    Nat.card (Subgroup.normalizer (P23 : Set H0)) ∣ 506 := by
  have : Fact (Nat.Prime 23) := ⟨by decide⟩
  have h1 := card_normalizer_dvd_mul_totient P23 card_P23
  have h2 : Nat.card C23 * (23 - 1) ∣ 23 * 22 :=
    mul_dvd_mul card_C23_dvd (dvd_refl 22)
  exact h1.trans h2

private theorem not_exists_subgroup_index_28_H0 (H : Subgroup H0) : H.index ≠ 28 := by
  intro hidx
  have hcard_H0 : Nat.card H0 = 10200960 := by
    rw [Nat.card_eq_fintype_card, card_M23]
  have hcard_H : Nat.card H = 364320 := by
    have h := H.index_mul_card
    rw [hidx, hcard_H0] at h
    omega
  have : Fact (Nat.Prime 23) := ⟨by decide⟩
  have hval := hasValidSylowNormalizer_of_dvd P23 card_P23
    (by rw [hcard_H0]; decide) card_normalizer_P23_dvd (by decide)
    (H := H) (by rw [hcard_H]; decide)
  rw [hcard_H] at hval
  exact absurd hval (by decide +kernel)

end M23Proof

/-- Every proper subgroup of `M₂₃` has index at least `23`. -/
theorem index_ge_M23 {S : Type*} [Group S] [Finite S] [IsSimpleGroup S]
    (e : S ≃* NativeSporadic.Carrier .M23) {H : Subgroup S} (hH : H ≠ ⊤) :
    23 ≤ H.index := by
  have hcard : Nat.card S = 10200960 := by
    rw [Nat.card_congr e.toEquiv]
    change Nat.card NativeSporadic.M23 = 10200960
    rw [CFSG.Sporadic.Mathieu.nativeM23_eq, Nat.card_eq_fintype_card]
    exact CFSG.M23.M23Group.card_M23
  exact prime_le_index_of_ne_top hH (by decide : Nat.Prime 23) (by rw [hcard]; decide)

/-- Maróti's theorem for primitive almost simple groups with socle `M₂₃`. -/
theorem sporadicCase_M23 {α : Type} [Finite α] (G : Subgroup (Equiv.Perm α)) (S : Type) [Group S]
    [IsPreprimitive G α] (hS : IsAlmostSimpleWith G S)
    (he : Nonempty (S ≃* NativeSporadic.Carrier .M23)) :
    AlmostSimpleConclusion G := by
  have : Finite S := hS.finite
  have : IsSimpleGroup S := hS.isSimpleGroup
  obtain ⟨e⟩ := he
  have hcard_M23 : Nat.card NativeSporadic.M23 = 10200960 := by
    rw [CFSG.Sporadic.Mathieu.nativeM23_eq, Nat.card_eq_fintype_card]
    exact CFSG.M23.M23Group.card_M23
  have hcardS : Nat.card S = 10200960 := by
    rw [Nat.card_congr e.toEquiv]
    exact hcard_M23
  have hAut : Nat.card (MulAut S) ≤ 10200960 := by
    rw [Nat.card_congr (MulAut.congr e).toEquiv]
    exact CFSG.Sporadic.Schreier.m23_mulAut_card.trans hcard_M23.le
  have hG_le : Nat.card G ≤ 10200960 := hS.card_le_card_mulAut.trans hAut
  obtain ⟨H, hH_ne, hH_idx⟩ := hS.exists_proper_subgroup_index_eq
  have hn23 : 23 ≤ Nat.card α := hH_idx ▸ index_ge_M23 e hH_ne
  rcases le_or_gt 29 (Nat.card α) with hn29 | hn29
  · right; right
    exact hG_le.trans ((by decide : 10200960 ≤ bound 29).trans (bound_mono hn29))
  · have hdvd : Nat.card α ∣ 10200960 := by
      rw [← hcardS, ← hH_idx]
      exact Subgroup.index_dvd_card H
    let eH0 : S ≃* CFSG.M23.M23Group.H0 :=
      e.trans (MulEquiv.subgroupCongr CFSG.Sporadic.Mathieu.nativeM23_eq)
    rcases (by omega :
        Nat.card α = 23 ∨ Nat.card α = 24 ∨ Nat.card α = 25 ∨
        Nat.card α = 26 ∨ Nat.card α = 27 ∨ Nat.card α = 28) with
      hn_eq | hn24 | hn25 | hn26 | hn27 | hn28
    · obtain ⟨eGS⟩ := mulEquiv_of_card_le hS (hG_le.trans hcardS.symm.le)
      let eGM : G ≃* NativeSporadic.M23 := eGS.trans e
      let eGH0 : G ≃* CFSG.M23.M23Group.H0 := eGS.trans eH0
      obtain ⟨eBridge⟩ := CFSG.Sporadic.Bridge.M23.nonempty_mulEquiv
      right; left
      refine ⟨(.M23, 23), by simp [fourTransitiveMathieu], hn_eq, ?_, ⟨eGM.trans eBridge⟩⟩
      have hcard23 : Nat.card (Fin 23) = 23 := Nat.card_fin 23
      have : IsMultiplyPretransitive CFSG.M23.M23Group.H0 (Fin 23) 4 :=
        CFSG.M23.M23Group.four_pretransitive
      have : IsMultiplyPretransitive CFSG.M23.M23Group.H0 (Fin 23) (3 + 1) :=
        CFSG.M23.M23Group.four_pretransitive
      have : IsPretransitive CFSG.M23.M23Group.H0 (Fin 23) :=
        is_one_pretransitive_iff.mp
          (isMultiplyPretransitive_of_le (m := 1) (n := 4) (by decide) (by rw [hcard23]; decide))
      apply isMultiplyPretransitive_of_le_stabilizer eGH0.symm (hn_eq.trans hcard23.symm)
      intro K hK
      apply exists_le_stabilizer_of_orbit_one_or_sub_one (by rw [hcard23]; decide) K
      intro x
      have hcard_H0 : Nat.card CFSG.M23.M23Group.H0 = 10200960 := by
        rw [Nat.card_eq_fintype_card, CFSG.M23.M23Group.card_M23]
      have hmem := mem_validOrbits (Γ := CFSG.M23.M23Group.H0) (X := Fin 23) 3
        (by rw [hcard23]; decide) K x
      rw [hK, hcard23, hcard_H0] at hmem
      have hvo : validOrbits 3 23 10200960 23 = [1, 22] := by decide
      rw [hvo, List.mem_cons, List.mem_singleton] at hmem
      simpa [hcard23] using hmem
    · exfalso
      have hH'_idx : (H.map (eH0 : S →* CFSG.M23.M23Group.H0)).index = 24 := by
        rw [Subgroup.index_map_equiv, hH_idx, hn24]
      exact M23Proof.not_exists_subgroup_index_24_H0 _ hH'_idx
    · exfalso; rw [hn25] at hdvd; exact absurd hdvd (by decide)
    · exfalso; rw [hn26] at hdvd; exact absurd hdvd (by decide)
    · exfalso; rw [hn27] at hdvd; exact absurd hdvd (by decide)
    · exfalso
      have hH'_idx : (H.map (eH0 : S →* CFSG.M23.M23Group.H0)).index = 28 := by
        rw [Subgroup.index_map_equiv, hH_idx, hn28]
      exact M23Proof.not_exists_subgroup_index_28_H0 _ hH'_idx

/-! ### `M₂₄` -/

namespace M24Proof

open CFSG.Sporadic.Mathieu CFSG.Sporadic.Mathieu.Native CFSG.Sporadic.Th

private instance isMultiplyPretransitive_M24_four :
    IsMultiplyPretransitive NativeSporadic.M24 (Fin 24) 4 := by
  rw [isMultiplyPretransitive_iff]
  intro e f
  have hex : ∀ x : Fin 4 ↪ Fin 24, ∃ g : NativeSporadic.M24,
      ∀ i : Fin 4, g • (⟨i.val, by omega⟩ : Fin 24) = x i := by
    intro x
    obtain ⟨g, hg⟩ := maps m24_hyp 4 le_rfl
      (fun j => if h : j < 4 then x ⟨j, h⟩ else 0) (by
        intro i hi j hj hij
        rw [dite_eq_left hi, dite_eq_left (lt_trans hj hi)] at hij
        have heq : (⟨i, hi⟩ : Fin 4) = ⟨j, lt_trans hj hi⟩ := x.injective hij
        have : i = j := congrArg Fin.val heq
        omega)
    refine ⟨g, fun i => ?_⟩
    have hgi := hg i.val i.isLt ⟨i.val, by omega⟩ rfl
    rw [dite_eq_left i.isLt] at hgi
    exact hgi
  obtain ⟨ge, hge⟩ := hex e
  obtain ⟨gf, hgf⟩ := hex f
  refine ⟨gf * ge⁻¹, ?_⟩
  apply DFunLike.ext
  intro i
  change gf • (ge⁻¹ • e i) = f i
  rw [inv_smul_eq_iff.mpr (hge i).symm, hgf i]

private theorem eq_one_of_fix_seven (g : NativeSporadic.M24)
    (h0 : (g : Equiv.Perm (Fin 24)) 0 = 0) (h1 : (g : Equiv.Perm (Fin 24)) 1 = 1)
    (h2 : (g : Equiv.Perm (Fin 24)) 2 = 2) (h3 : (g : Equiv.Perm (Fin 24)) 3 = 3)
    (h4 : (g : Equiv.Perm (Fin 24)) 4 = 4) (h5 : (g : Equiv.Perm (Fin 24)) 5 = 5)
    (h6 : (g : Equiv.Perm (Fin 24)) 6 = 6) : g = 1 := by
  have hC := chain m24_hyp
  have hl0 : g ∈ lvl (m24Data ()) m24a m24b 0 := by
    rw [lvl_zero m24_hyp]
    trivial
  have hstep : ∀ (i : ℕ) (hi : i < 7) (hlt : i < 24),
      (m24Data ()).base[i]! = i →
      (g : Equiv.Perm (Fin 24)) ⟨i, hlt⟩ = ⟨i, hlt⟩ →
      g ∈ lvl (m24Data ()) m24a m24b i →
      g ∈ lvl (m24Data ()) m24a m24b (i + 1) := by
    intro i hi hlt hbi hfix hgi
    have hib : i < (m24Data ()).base.size := by change i < 7; exact hi
    refine (hC.2.1 i hib g hgi).1 ?_
    rw [hbi, idx_of_lt g hlt]
    exact congrArg Fin.val hfix
  have hl1 := hstep 0 (by decide) (by decide) rfl h0 hl0
  have hl2 := hstep 1 (by decide) (by decide) rfl h1 hl1
  have hl3 := hstep 2 (by decide) (by decide) rfl h2 hl2
  have hl4 := hstep 3 (by decide) (by decide) rfl h3 hl3
  have hl5 := hstep 4 (by decide) (by decide) rfl h4 hl4
  have hl6 := hstep 5 (by decide) (by decide) rfl h5 hl5
  have hl7 := hstep 6 (by decide) (by decide) rfl h6 hl6
  have hcard7 : Nat.card (lvl (m24Data ()) m24a m24b 7) = 1 := by
    have := hC.2.2 7 (by decide)
    have hsz : (m24Data ()).base.size = 7 := rfl
    rw [hsz, Finset.Ico_self, Finset.prod_empty] at this
    exact this
  have hbot : lvl (m24Data ()) m24a m24b 7 = ⊥ := Subgroup.card_eq_one.mp hcard7
  rwa [hbot, Subgroup.mem_bot] at hl7

private abbrev gA : Equiv.Perm (Fin 24) :=
  List.formPerm [0, 3] * List.formPerm [1, 6] * List.formPerm [2, 16] *
    List.formPerm [4, 12] * List.formPerm [5, 8] * List.formPerm [7, 14] *
    List.formPerm [9, 18] * List.formPerm [10, 17] * List.formPerm [11, 20] *
    List.formPerm [13, 15] * List.formPerm [19, 23] * List.formPerm [21, 22]

private abbrev gB : Equiv.Perm (Fin 24) :=
  List.formPerm [0, 3, 5] * List.formPerm [1, 20, 13] * List.formPerm [2, 8, 14] *
    List.formPerm [4, 17, 9] * List.formPerm [12, 16, 15] * List.formPerm [18, 23, 22]

private abbrev a24 : NativeSporadic.M24 :=
  ⟨gA, Subgroup.subset_closure (Set.mem_insert _ _)⟩

private abbrev b24 : NativeSporadic.M24 :=
  ⟨gB, Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)⟩

private abbrev w11Part1 : NativeSporadic.M24 :=
  b24 * a24 * b24 * a24 * b24 * a24 * b24⁻¹ * a24 * b24

private abbrev w11Part2 : NativeSporadic.M24 :=
  a24 * b24⁻¹ * a24 * b24 * a24 * b24 * a24 * b24 * a24

private abbrev w11Part3 : NativeSporadic.M24 :=
  b24 * a24 * b24⁻¹ * a24 * b24⁻¹ * a24 * b24 * a24 * b24

private abbrev w11Part4 : NativeSporadic.M24 :=
  a24 * b24⁻¹ * a24 * b24 * a24 * b24⁻¹ * a24 * b24⁻¹ * a24 * b24⁻¹

private abbrev c1Perm : Equiv.Perm (Fin 24) :=
  List.formPerm [0, 2, 3, 6, 10] * List.formPerm [1, 17, 4, 19, 8] *
    List.formPerm [5, 7, 14, 9, 20] * List.formPerm [12, 15, 22, 23, 16]

private abbrev c2Perm : Equiv.Perm (Fin 24) :=
  List.formPerm [0, 5, 4, 3, 8, 14, 11, 17, 23, 19, 10, 9, 22, 13, 12, 21, 7, 1, 6, 2, 15, 20, 18]

private abbrev c3Perm : Equiv.Perm (Fin 24) :=
  List.formPerm [0, 15, 16, 12, 14, 13, 8, 3] * List.formPerm [1, 20, 21, 9, 2, 5, 17, 4] *
    List.formPerm [7, 23, 22, 11] * List.formPerm [10, 18]

private abbrev c4Perm : Equiv.Perm (Fin 24) :=
  List.formPerm [0, 17, 6] *
    List.formPerm [1, 5, 11, 20, 18, 9, 7, 8, 23, 21, 22, 13, 15, 4, 10] *
    List.formPerm [2, 3, 16, 19, 12]

private abbrev x11Perm : Equiv.Perm (Fin 24) :=
  List.formPerm [0, 6, 5, 17, 3, 21, 4, 2, 7, 1, 16] *
    List.formPerm [8, 13, 12, 19, 11, 14, 15, 10, 18, 22, 9]

private abbrev m24x11 : NativeSporadic.M24 :=
  w11Part1 * w11Part2 * w11Part3 * w11Part4

private theorem w11Part1_val : (w11Part1 : Equiv.Perm (Fin 24)) = c1Perm := by decide +kernel
private theorem w11Part2_val : (w11Part2 : Equiv.Perm (Fin 24)) = c2Perm := by decide +kernel
private theorem w11Part3_val : (w11Part3 : Equiv.Perm (Fin 24)) = c3Perm := by decide +kernel
private theorem w11Part4_val : (w11Part4 : Equiv.Perm (Fin 24)) = c4Perm := by decide +kernel

private theorem m24x11_val : (m24x11 : Equiv.Perm (Fin 24)) = x11Perm := by
  change (w11Part1 : Equiv.Perm (Fin 24)) * (w11Part2 : Equiv.Perm (Fin 24)) *
    (w11Part3 : Equiv.Perm (Fin 24)) * (w11Part4 : Equiv.Perm (Fin 24)) = x11Perm
  rw [w11Part1_val, w11Part2_val, w11Part3_val, w11Part4_val]
  decide +kernel

private theorem m24x11_pow_11 : m24x11 ^ 11 = 1 := by
  apply Subtype.ext
  change (m24x11 : Equiv.Perm (Fin 24)) ^ 11 = 1
  rw [m24x11_val]
  decide +kernel

private theorem m24x11_ne_one : m24x11 ≠ 1 := by
  intro h
  have hval : (m24x11 : Equiv.Perm (Fin 24)) = 1 := congrArg Subtype.val h
  rw [m24x11_val] at hval
  exact (by decide +kernel : x11Perm ≠ 1) hval

private theorem orderOf_m24x11 : orderOf m24x11 = 11 := by
  have hdvd : orderOf m24x11 ∣ 11 := orderOf_dvd_of_pow_eq_one m24x11_pow_11
  rcases (Nat.dvd_prime (by decide : Nat.Prime 11)).mp hdvd with h1 | h11
  · exact absurd (orderOf_eq_one_iff.mp h1) m24x11_ne_one
  · exact h11

private abbrev P11 : Subgroup NativeSporadic.M24 := Subgroup.zpowers m24x11

private theorem card_P11 : Nat.card P11 = 11 := by
  rw [Nat.card_zpowers, orderOf_m24x11]

private abbrev C11 : Subgroup NativeSporadic.M24 :=
  Subgroup.centralizer (P11 : Set NativeSporadic.M24)

private theorem comm_m24x11_pow (g : C11) (k : ℕ) (p : Fin 24) :
    (g.1 : Equiv.Perm (Fin 24)) ((x11Perm ^ k) p) =
      (x11Perm ^ k) ((g.1 : Equiv.Perm (Fin 24)) p) := by
  have hcomm : m24x11 * g.1 = g.1 * m24x11 :=
    Subgroup.mem_centralizer_iff.mp g.2 m24x11 (Subgroup.mem_zpowers m24x11)
  have hcomm' : Commute (g.1 : Equiv.Perm (Fin 24)) x11Perm := by
    rw [← m24x11_val]
    exact (congrArg Subtype.val hcomm).symm
  have hpow : (g.1 : Equiv.Perm (Fin 24)) * x11Perm ^ k =
      x11Perm ^ k * (g.1 : Equiv.Perm (Fin 24)) :=
    hcomm'.pow_right k
  exact Equiv.Perm.ext_iff.mp hpow p

private theorem m24x11_orb1 : (x11Perm ^ 9) 0 = 1 := by decide +kernel
private theorem m24x11_orb2 : (x11Perm ^ 7) 0 = 2 := by decide +kernel
private theorem m24x11_orb3 : (x11Perm ^ 4) 0 = 3 := by decide +kernel
private theorem m24x11_orb4 : (x11Perm ^ 6) 0 = 4 := by decide +kernel
private theorem m24x11_orb5 : (x11Perm ^ 2) 0 = 5 := by decide +kernel
private theorem m24x11_orb6 : (x11Perm ^ 1) 0 = 6 := by decide +kernel
private theorem m24x11_fix20 : (x11Perm ^ 1) 20 = 20 := by decide +kernel
private theorem m24x11_fix23 : (x11Perm ^ 1) 23 = 23 := by decide +kernel

private theorem stabilizer_C11_zero_eq_bot : stabilizer C11 (0 : Fin 24) = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  have h0 : (g.1 : Equiv.Perm (Fin 24)) 0 = 0 := hg
  have h1 : (g.1 : Equiv.Perm (Fin 24)) 1 = 1 := by
    rw [← m24x11_orb1, comm_m24x11_pow g 9 0, h0, m24x11_orb1]
  have h2 : (g.1 : Equiv.Perm (Fin 24)) 2 = 2 := by
    rw [← m24x11_orb2, comm_m24x11_pow g 7 0, h0, m24x11_orb2]
  have h3 : (g.1 : Equiv.Perm (Fin 24)) 3 = 3 := by
    rw [← m24x11_orb3, comm_m24x11_pow g 4 0, h0, m24x11_orb3]
  have h4 : (g.1 : Equiv.Perm (Fin 24)) 4 = 4 := by
    rw [← m24x11_orb4, comm_m24x11_pow g 6 0, h0, m24x11_orb4]
  have h5 : (g.1 : Equiv.Perm (Fin 24)) 5 = 5 := by
    rw [← m24x11_orb5, comm_m24x11_pow g 2 0, h0, m24x11_orb5]
  have h6 : (g.1 : Equiv.Perm (Fin 24)) 6 = 6 := by
    rw [← m24x11_orb6, comm_m24x11_pow g 1 0, h0, m24x11_orb6]
  exact Subtype.ext (eq_one_of_fix_seven g.1 h0 h1 h2 h3 h4 h5 h6)

private theorem not_mem_orbit_C11_twenty : (20 : Fin 24) ∉ orbit C11 (0 : Fin 24) := by
  rintro ⟨g, hg⟩
  have h0 : (g.1 : Equiv.Perm (Fin 24)) 0 = 20 := hg
  have h6 : (g.1 : Equiv.Perm (Fin 24)) 6 = 20 := by
    rw [← m24x11_orb6, comm_m24x11_pow g 1 0, h0, m24x11_fix20]
  have heq : (6 : Fin 24) = 0 := (g.1 : Equiv.Perm (Fin 24)).injective (h6.trans h0.symm)
  exact (by decide : (6 : Fin 24) ≠ 0) heq

private theorem not_mem_orbit_C11_twentyThree : (23 : Fin 24) ∉ orbit C11 (0 : Fin 24) := by
  rintro ⟨g, hg⟩
  have h0 : (g.1 : Equiv.Perm (Fin 24)) 0 = 23 := hg
  have h6 : (g.1 : Equiv.Perm (Fin 24)) 6 = 23 := by
    rw [← m24x11_orb6, comm_m24x11_pow g 1 0, h0, m24x11_fix23]
  have heq : (6 : Fin 24) = 0 := (g.1 : Equiv.Perm (Fin 24)).injective (h6.trans h0.symm)
  exact (by decide : (6 : Fin 24) ≠ 0) heq

private theorem card_C11_dvd : Nat.card C11 ∣ 22 := by
  have hstab : Nat.card (stabilizer C11 (0 : Fin 24)) = 1 := by
    rw [stabilizer_C11_zero_eq_bot, Subgroup.card_bot]
  have hcard_eq : Nat.card C11 = Nat.card (orbit C11 (0 : Fin 24)) := by
    have h := (stabilizer C11 (0 : Fin 24)).index_mul_card
    rw [hstab, mul_one, index_stabilizer C11 (0 : Fin 24), ← Nat.card_coe_set_eq] at h
    exact h.symm
  let emb : orbit C11 (0 : Fin 24) → {p : Fin 24 // p ≠ 20 ∧ p ≠ 23} :=
    fun x => ⟨x.1, ⟨fun h => not_mem_orbit_C11_twenty (h ▸ x.2),
      fun h => not_mem_orbit_C11_twentyThree (h ▸ x.2)⟩⟩
  have hemb : Function.Injective emb :=
    fun x y h => Subtype.ext (congrArg (fun z : {p : Fin 24 // p ≠ 20 ∧ p ≠ 23} => z.1) h)
  have h22 : Nat.card {p : Fin 24 // p ≠ 20 ∧ p ≠ 23} = 22 := by
    rw [Nat.card_eq_fintype_card]
    decide
  have hle : Nat.card C11 ≤ 22 :=
    (hcard_eq.trans_le (Nat.card_le_card_of_injective emb hemb)).trans h22.le
  have hP_le_C : P11 ≤ C11 := by
    intro y hy z hz
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    simp only [← zpow_add, add_comm]
  have hdvd11 : 11 ∣ Nat.card C11 := by
    rw [← card_P11]
    exact Subgroup.card_dvd_of_le hP_le_C
  have hpos : 0 < Nat.card C11 := Nat.card_pos
  obtain ⟨k, hk⟩ := hdvd11
  have hk_cases : k = 1 ∨ k = 2 := by omega
  rcases hk_cases with rfl | rfl
  · rw [hk]; decide
  · rw [hk]

private theorem card_normalizer_P11_dvd :
    Nat.card (Subgroup.normalizer (P11 : Set NativeSporadic.M24)) ∣ 220 := by
  have : Fact (Nat.Prime 11) := ⟨by decide⟩
  have h1 := card_normalizer_dvd_mul_totient P11 card_P11
  have h2 : Nat.card C11 * (11 - 1) ∣ 22 * 10 :=
    mul_dvd_mul card_C11_dvd (dvd_refl 10)
  exact h1.trans h2

private theorem not_exists_subgroup_card_425040 (K : Subgroup NativeSporadic.M24) :
    Nat.card K ≠ 425040 := by
  intro hcard_K
  have : Fact (Nat.Prime 11) := ⟨by decide⟩
  have hval := hasValidSylowNormalizer_of_dvd P11 card_P11
    (by rw [card_M24]; decide) card_normalizer_P11_dvd (by decide)
    (H := K) (by rw [hcard_K]; decide)
  rw [hcard_K] at hval
  exact absurd hval (by decide)

private abbrev x23Perm : Equiv.Perm (Fin 24) :=
  List.formPerm [0, 3, 16, 14, 5, 4, 11, 1, 15, 20, 6, 2, 18, 17, 12, 21, 23, 9, 22, 19, 10, 13, 7]

private abbrev m24x23 : NativeSporadic.M24 :=
  a24 * b24⁻¹ * a24 * b24⁻¹ * a24

private theorem m24x23_val : (m24x23 : Equiv.Perm (Fin 24)) = x23Perm := by decide +kernel

private theorem m24x23_pow_23 : m24x23 ^ 23 = 1 := by
  apply Subtype.ext
  change (m24x23 : Equiv.Perm (Fin 24)) ^ 23 = 1
  rw [m24x23_val]
  decide +kernel

private theorem m24x23_ne_one : m24x23 ≠ 1 := by
  intro h
  have hval : (m24x23 : Equiv.Perm (Fin 24)) = 1 := congrArg Subtype.val h
  rw [m24x23_val] at hval
  exact (by decide +kernel : x23Perm ≠ 1) hval

private theorem orderOf_m24x23 : orderOf m24x23 = 23 := by
  have hdvd : orderOf m24x23 ∣ 23 := orderOf_dvd_of_pow_eq_one m24x23_pow_23
  rcases (Nat.dvd_prime (by decide : Nat.Prime 23)).mp hdvd with h1 | h23
  · exact absurd (orderOf_eq_one_iff.mp h1) m24x23_ne_one
  · exact h23

private abbrev P23 : Subgroup NativeSporadic.M24 := Subgroup.zpowers m24x23

private theorem card_P23 : Nat.card P23 = 23 := by
  rw [Nat.card_zpowers, orderOf_m24x23]

private abbrev C23 : Subgroup NativeSporadic.M24 :=
  Subgroup.centralizer (P23 : Set NativeSporadic.M24)

private theorem comm_m24x23_pow (g : C23) (k : ℕ) (p : Fin 24) :
    (g.1 : Equiv.Perm (Fin 24)) ((x23Perm ^ k) p) =
      (x23Perm ^ k) ((g.1 : Equiv.Perm (Fin 24)) p) := by
  have hcomm : m24x23 * g.1 = g.1 * m24x23 :=
    Subgroup.mem_centralizer_iff.mp g.2 m24x23 (Subgroup.mem_zpowers m24x23)
  have hcomm' : Commute (g.1 : Equiv.Perm (Fin 24)) x23Perm := by
    rw [← m24x23_val]
    exact (congrArg Subtype.val hcomm).symm
  have hpow : (g.1 : Equiv.Perm (Fin 24)) * x23Perm ^ k =
      x23Perm ^ k * (g.1 : Equiv.Perm (Fin 24)) :=
    hcomm'.pow_right k
  exact Equiv.Perm.ext_iff.mp hpow p

private theorem m24x23_orb1 : (x23Perm ^ 7) 0 = 1 := by decide +kernel
private theorem m24x23_orb2 : (x23Perm ^ 11) 0 = 2 := by decide +kernel
private theorem m24x23_orb3 : (x23Perm ^ 1) 0 = 3 := by decide +kernel
private theorem m24x23_orb4 : (x23Perm ^ 5) 0 = 4 := by decide +kernel
private theorem m24x23_orb5 : (x23Perm ^ 4) 0 = 5 := by decide +kernel
private theorem m24x23_orb6 : (x23Perm ^ 10) 0 = 6 := by decide +kernel
private theorem m24x23_fix8 : (x23Perm ^ 1) 8 = 8 := by decide +kernel

private theorem stabilizer_C23_zero_eq_bot : stabilizer C23 (0 : Fin 24) = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  have h0 : (g.1 : Equiv.Perm (Fin 24)) 0 = 0 := hg
  have h1 : (g.1 : Equiv.Perm (Fin 24)) 1 = 1 := by
    rw [← m24x23_orb1, comm_m24x23_pow g 7 0, h0, m24x23_orb1]
  have h2 : (g.1 : Equiv.Perm (Fin 24)) 2 = 2 := by
    rw [← m24x23_orb2, comm_m24x23_pow g 11 0, h0, m24x23_orb2]
  have h3 : (g.1 : Equiv.Perm (Fin 24)) 3 = 3 := by
    rw [← m24x23_orb3, comm_m24x23_pow g 1 0, h0, m24x23_orb3]
  have h4 : (g.1 : Equiv.Perm (Fin 24)) 4 = 4 := by
    rw [← m24x23_orb4, comm_m24x23_pow g 5 0, h0, m24x23_orb4]
  have h5 : (g.1 : Equiv.Perm (Fin 24)) 5 = 5 := by
    rw [← m24x23_orb5, comm_m24x23_pow g 4 0, h0, m24x23_orb5]
  have h6 : (g.1 : Equiv.Perm (Fin 24)) 6 = 6 := by
    rw [← m24x23_orb6, comm_m24x23_pow g 10 0, h0, m24x23_orb6]
  exact Subtype.ext (eq_one_of_fix_seven g.1 h0 h1 h2 h3 h4 h5 h6)

private theorem not_mem_orbit_C23_eight : (8 : Fin 24) ∉ orbit C23 (0 : Fin 24) := by
  rintro ⟨g, hg⟩
  have h0 : (g.1 : Equiv.Perm (Fin 24)) 0 = 8 := hg
  have h3 : (g.1 : Equiv.Perm (Fin 24)) 3 = 8 := by
    rw [← m24x23_orb3, comm_m24x23_pow g 1 0, h0, m24x23_fix8]
  have heq : (3 : Fin 24) = 0 := (g.1 : Equiv.Perm (Fin 24)).injective (h3.trans h0.symm)
  exact (by decide : (3 : Fin 24) ≠ 0) heq

private theorem card_C23_dvd : Nat.card C23 ∣ 23 := by
  have hstab : Nat.card (stabilizer C23 (0 : Fin 24)) = 1 := by
    rw [stabilizer_C23_zero_eq_bot, Subgroup.card_bot]
  have hcard_eq : Nat.card C23 = Nat.card (orbit C23 (0 : Fin 24)) := by
    have h := (stabilizer C23 (0 : Fin 24)).index_mul_card
    rw [hstab, mul_one, index_stabilizer C23 (0 : Fin 24), ← Nat.card_coe_set_eq] at h
    exact h.symm
  let emb : orbit C23 (0 : Fin 24) → {p : Fin 24 // p ≠ 8} :=
    fun x => ⟨x.1, fun h => not_mem_orbit_C23_eight (h ▸ x.2)⟩
  have hemb : Function.Injective emb :=
    fun x y h => Subtype.ext (congrArg (fun z : {p : Fin 24 // p ≠ 8} => z.1) h)
  have h23 : Nat.card {p : Fin 24 // p ≠ 8} = 23 := by
    rw [Nat.card_eq_fintype_card]
    decide
  have hle : Nat.card C23 ≤ 23 :=
    (hcard_eq.trans_le (Nat.card_le_card_of_injective emb hemb)).trans h23.le
  have hP_le_C : P23 ≤ C23 := by
    intro y hy z hz
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    simp only [← zpow_add, add_comm]
  have hdvd23 : 23 ∣ Nat.card C23 := by
    have hdvd := Subgroup.card_dvd_of_le hP_le_C
    rwa [card_P23] at hdvd
  have hpos : 0 < Nat.card C23 := Nat.card_pos
  obtain ⟨k, hk⟩ := hdvd23
  have hk1 : k = 1 := by omega
  subst hk1
  rw [hk]

private theorem card_normalizer_P23_dvd :
    Nat.card (Subgroup.normalizer (P23 : Set NativeSporadic.M24)) ∣ 506 := by
  have : Fact (Nat.Prime 23) := ⟨by decide⟩
  have h1 := card_normalizer_dvd_mul_totient P23 card_P23
  have h2 : Nat.card C23 * (23 - 1) ∣ 23 * 22 :=
    mul_dvd_mul card_C23_dvd (dvd_refl 22)
  exact h1.trans h2

private theorem not_exists_subgroup_of_sylow23 (H : Subgroup NativeSporadic.M24)
    {c : ℕ} (hcard : Nat.card H = c) (hdvd : 23 ∣ c)
    (hno : hasValidSylowNormalizer 23 506 c = false) : False := by
  have : Fact (Nat.Prime 23) := ⟨by decide⟩
  have hval := hasValidSylowNormalizer_of_dvd P23 card_P23
    (by rw [card_M24]; decide) card_normalizer_P23_dvd (by decide)
    (H := H) (by rwa [hcard])
  rw [hcard, hno] at hval
  exact Bool.noConfusion hval

private theorem not_exists_subgroup_index_23 (H : Subgroup NativeSporadic.M24) :
    H.index ≠ 23 := by
  intro hH_idx
  have hcard24 : Nat.card (Fin 24) = 24 := Nat.card_fin 24
  have : IsMultiplyPretransitive NativeSporadic.M24 (Fin 24) (3 + 1) :=
    isMultiplyPretransitive_M24_four
  have hmem0 := mem_validOrbits (Γ := NativeSporadic.M24) (X := Fin 24) 3
    (by rw [hcard24]; decide) H (0 : Fin 24)
  rw [hH_idx, hcard24, card_M24] at hmem0
  have hvo0 : validOrbits 3 24 244823040 23 = [24] := by decide
  rw [hvo0, List.mem_singleton] at hmem0
  set S₀ := stabilizer NativeSporadic.M24 (0 : Fin 24)
  set X₀ := SubMulAction.ofStabilizer NativeSporadic.M24 (0 : Fin 24)
  set H₀ := H.subgroupOf S₀
  have hX₀_card : Nat.card X₀ = 23 := by
    rw [SubMulAction.nat_card_ofStabilizer_eq, hcard24]
  have h1 : IsMultiplyPretransitive NativeSporadic.M24 (Fin 24) 1 :=
    isMultiplyPretransitive_of_le (m := 1) (n := 4) (by decide) (by rw [hcard24]; decide)
  have : IsPretransitive NativeSporadic.M24 (Fin 24) := is_one_pretransitive_iff.mp h1
  have hS₀_idx : S₀.index = 24 := by
    rw [index_stabilizer_of_transitive, hcard24]
  have hS₀_card : Nat.card S₀ = 10200960 := by
    have h := S₀.index_mul_card
    rw [hS₀_idx, card_M24] at h
    omega
  have hrel_S₀ : S₀.relIndex H = 24 := by
    change (stabilizer H (0 : Fin 24)).index = 24
    rw [index_stabilizer H (0 : Fin 24), ← Nat.card_coe_set_eq, hmem0]
  have hH₀_idx : H₀.index = 23 := by
    change H.relIndex S₀ = 23
    have hinf : H.relIndex S₀ * S₀.index = S₀.relIndex H * H.index := by
      rw [← Subgroup.index_inf, ← Subgroup.index_inf, inf_comm]
    rw [hS₀_idx, hrel_S₀, hH_idx] at hinf
    omega
  have : IsMultiplyPretransitive S₀ X₀ (2 + 1) := by
    have : IsMultiplyPretransitive NativeSporadic.M24 (Fin 24) ((2 + 1) + 1) :=
      isMultiplyPretransitive_M24_four
    exact SubMulAction.ofStabilizer.isMultiplyPretransitive.mp this
  refine not_exists_subgroup_index_sub_one (Γ := NativeSporadic.M24) (X := Fin 24)
    (by rw [hcard24]; decide) H (by rw [hH_idx, hcard24]) (0 : Fin 24)
    (by rw [hmem0, hcard24]) ?_
  intro z
  have hmem1 := mem_validOrbits (Γ := S₀) (X := X₀) 2 (by rw [hX₀_card]; decide) H₀ z
  rw [hH₀_idx, hX₀_card, hS₀_card] at hmem1
  have hvo1 : validOrbits 2 23 10200960 23 = [1, 22] := by decide
  rw [hvo1, List.mem_cons, List.mem_singleton] at hmem1
  simpa [hcard24] using hmem1

private theorem orbit_one_or_23_of_index_24
    (H : Subgroup NativeSporadic.M24) (hH_idx : H.index = 24)
    (x : Fin 24) :
    Nat.card (orbit H x) = 1 ∨ Nat.card (orbit H x) = 23 := by
  have hcard24 : Nat.card (Fin 24) = 24 := Nat.card_fin 24
  have : IsMultiplyPretransitive NativeSporadic.M24 (Fin 24) (3 + 1) :=
    isMultiplyPretransitive_M24_four
  have hmem := mem_validOrbits (Γ := NativeSporadic.M24) (X := Fin 24) 3
    (by rw [hcard24]; decide) H x
  rw [hH_idx, hcard24, card_M24] at hmem
  have hvo : validOrbits 3 24 244823040 24 = [1, 23, 24] := by decide
  rw [hvo, List.mem_cons, List.mem_cons, List.mem_singleton] at hmem
  rcases hmem with h1 | h23 | h24
  · exact Or.inl h1
  · exact Or.inr h23
  · exfalso
    set S_x := stabilizer NativeSporadic.M24 x
    have hrel : S_x.relIndex H = 24 := by
      change (stabilizer H x).index = 24
      rw [index_stabilizer H x, ← Nat.card_coe_set_eq, h24]
    have hinf_idx : (S_x ⊓ H).index = 576 := by
      rw [Subgroup.index_inf, hrel, hH_idx]
    have hinf_card : Nat.card (S_x ⊓ H : Subgroup NativeSporadic.M24) = 425040 := by
      have h := (S_x ⊓ H).index_mul_card
      rw [hinf_idx, card_M24] at h
      omega
    exact not_exists_subgroup_card_425040 (S_x ⊓ H) hinf_card

end M24Proof

/-- Every proper subgroup of `M₂₄` has index at least `24`. -/
theorem index_ge_M24 {S : Type*} [Group S] [Finite S] [IsSimpleGroup S]
    (e : S ≃* NativeSporadic.Carrier .M24) {H : Subgroup S} (hH : H ≠ ⊤) :
    24 ≤ H.index := by
  have hcard : Nat.card S = 244823040 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.Mathieu.card_M24
  have h23 : 23 ≤ H.index :=
    prime_le_index_of_ne_top hH (by decide : Nat.Prime 23) (by rw [hcard]; decide)
  rcases eq_or_lt_of_le h23 with h23_eq | h24
  · exfalso
    let e' : S ≃* NativeSporadic.M24 := e
    have hH'_idx : (H.map (e' : S →* NativeSporadic.M24)).index = 23 := by
      rw [Subgroup.index_map_equiv, ← h23_eq]
    exact M24Proof.not_exists_subgroup_index_23 _ hH'_idx
  · omega

/-- Maróti's theorem for primitive almost simple groups with socle `M₂₄`. -/
theorem sporadicCase_M24 {α : Type} [Finite α] (G : Subgroup (Equiv.Perm α)) (S : Type) [Group S]
    [IsPreprimitive G α] (hS : IsAlmostSimpleWith G S)
    (he : Nonempty (S ≃* NativeSporadic.Carrier .M24)) :
    AlmostSimpleConclusion G := by
  have : Finite S := hS.finite
  have : IsSimpleGroup S := hS.isSimpleGroup
  obtain ⟨e⟩ := he
  let e' : S ≃* NativeSporadic.M24 := e
  have hcardM24 : Nat.card (NativeSporadic.Carrier .M24) = 244823040 :=
    CFSG.Sporadic.Mathieu.card_M24
  have hcardS : Nat.card S = 244823040 := by
    rw [Nat.card_congr e.toEquiv]
    exact hcardM24
  have hAut : Nat.card (MulAut S) ≤ 244823040 := by
    rw [Nat.card_congr (MulAut.congr e).toEquiv]
    exact CFSG.Sporadic.Schreier.m24_mulAut_card.trans CFSG.Sporadic.Mathieu.card_M24.le
  have hG_le : Nat.card G ≤ 244823040 := hS.card_le_card_mulAut.trans hAut
  obtain ⟨H, hH_ne, hH_idx⟩ := hS.exists_proper_subgroup_index_eq
  have hn24 : 24 ≤ Nat.card α := hH_idx ▸ index_ge_M24 e hH_ne
  rcases le_or_gt 32 (Nat.card α) with hn32 | hn32
  · right; right
    exact hG_le.trans ((by decide : 244823040 ≤ bound 32).trans (bound_mono hn32))
  · have hdvd : Nat.card α ∣ 244823040 := by
      rw [← hcardS, ← hH_idx]
      exact Subgroup.index_dvd_card H
    rcases (by omega :
        Nat.card α = 24 ∨ Nat.card α = 25 ∨ Nat.card α = 26 ∨ Nat.card α = 27 ∨
        Nat.card α = 28 ∨ Nat.card α = 29 ∨ Nat.card α = 30 ∨ Nat.card α = 31) with
      hn_eq | hn25 | hn26 | hn27 | hn28 | hn29 | hn30 | hn31
    · obtain ⟨eGS⟩ := mulEquiv_of_card_le hS (hG_le.trans hcardS.symm.le)
      let eGM : G ≃* NativeSporadic.M24 := eGS.trans e'
      obtain ⟨eBridge⟩ := CFSG.Sporadic.Bridge.M24.nonempty_mulEquiv
      right; left
      refine ⟨(.M24, 24), by simp [fourTransitiveMathieu], hn_eq, ?_, ⟨eGM.trans eBridge⟩⟩
      have hcard24 : Nat.card (Fin 24) = 24 := Nat.card_fin 24
      have : IsMultiplyPretransitive NativeSporadic.M24 (Fin 24) 4 :=
        M24Proof.isMultiplyPretransitive_M24_four
      have : IsPretransitive NativeSporadic.M24 (Fin 24) :=
        is_one_pretransitive_iff.mp
          (isMultiplyPretransitive_of_le (m := 1) (n := 4) (by decide) (by rw [hcard24]; decide))
      apply isMultiplyPretransitive_of_le_stabilizer eGM.symm (hn_eq.trans hcard24.symm)
      intro K hK
      rw [hcard24] at hK
      apply exists_le_stabilizer_of_orbit_one_or_sub_one (by rw [hcard24]; decide) K
      intro x
      simpa [hcard24] using M24Proof.orbit_one_or_23_of_index_24 K hK x
    · exfalso; rw [hn25] at hdvd; exact absurd hdvd (by decide)
    · exfalso; rw [hn26] at hdvd; exact absurd hdvd (by decide)
    · exfalso
      have hH'_idx : (H.map (e' : S →* NativeSporadic.M24)).index = 27 := by
        rw [Subgroup.index_map_equiv, hH_idx, hn27]
      have hH'_card : Nat.card (H.map (e' : S →* NativeSporadic.M24)) = 9067520 := by
        have h := (H.map (e' : S →* NativeSporadic.M24)).index_mul_card
        rw [hH'_idx, CFSG.Sporadic.Mathieu.card_M24] at h
        omega
      exact M24Proof.not_exists_subgroup_of_sylow23 _ hH'_card
        (by decide) (by decide +kernel)
    · exfalso
      have hH'_idx : (H.map (e' : S →* NativeSporadic.M24)).index = 28 := by
        rw [Subgroup.index_map_equiv, hH_idx, hn28]
      have hH'_card : Nat.card (H.map (e' : S →* NativeSporadic.M24)) = 8743680 := by
        have h := (H.map (e' : S →* NativeSporadic.M24)).index_mul_card
        rw [hH'_idx, CFSG.Sporadic.Mathieu.card_M24] at h
        omega
      exact M24Proof.not_exists_subgroup_of_sylow23 _ hH'_card
        (by decide) (by decide +kernel)
    · exfalso; rw [hn29] at hdvd; exact absurd hdvd (by decide)
    · exfalso
      have hH'_idx : (H.map (e' : S →* NativeSporadic.M24)).index = 30 := by
        rw [Subgroup.index_map_equiv, hH_idx, hn30]
      have hH'_card : Nat.card (H.map (e' : S →* NativeSporadic.M24)) = 8160768 := by
        have h := (H.map (e' : S →* NativeSporadic.M24)).index_mul_card
        rw [hH'_idx, CFSG.Sporadic.Mathieu.card_M24] at h
        omega
      exact M24Proof.not_exists_subgroup_of_sylow23 _ hH'_card
        (by decide) (by decide +kernel)
    · exfalso; rw [hn31] at hdvd; exact absurd hdvd (by decide)

end Maroti
