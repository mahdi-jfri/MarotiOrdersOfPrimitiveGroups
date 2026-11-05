module

public import Maroti.Exceptional.AutBound
public import Maroti.Exceptional.TorusHeis
public import Maroti.Exceptional.ChevalleyE
import CFSG.LieType.Ree.SmallReeFrattini
import CFSG.LieType.Ree.SmallReeModelSchreier
import CFSG.LieType.Ree.LargeReeInvolutionCoordinates
import CFSG.LieType.Ree.LargeReeModelSchreier

/-!
# The Small and Large Ree Groups `²G₂(q)` and `²F₄(q)`

This file proves the subgroup index lower bounds and Maróti's bound for primitive almost simple
groups with socle `²G₂(q)` (`q = 3^(2a+1)`, `a ≥ 1`) or `²F₄(q)` (`q = 2^(2a+1)`, `a ≥ 1`)
(Maróti, Section 2, Step 2, pages 634–635):
- For `²G₂(q)`: using the unipotent radical `smallReeCoordU` (`CFSG/LieType/Ree/SmallReeFrattini`)
  and the normalizing torus `small_Ree_positive_torus_action`, every proper subgroup `H` has index
  at least `(q - 1) * q + 1`.
- For `²F₄(q)`: using the 3-pair Heisenberg subgroup inside `F4.reeFixedPosUnipotent K a` formed
  by `sylowD`, `sylowF`, `sylowL`, `sylowA`, `sylowJ`, and center `sylowH a K 0`
  (`CFSG/LieType/Ree/LargeReeInvolutionCoordinates`), every proper subgroup `H` has index at least
  `q ^ 3 + 1`.
-/

@[expose] public section

namespace Maroti

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.LieType.Ree.ReeTag
open CFSG.LieType.Ree.LargeReeInvolution
open CFSG.Open

private theorem pow_le_bound' {n k : ℕ} (hk : 2 ^ k ≤ n) : n ^ k ≤ bound n := by
  have hn0 : n ≠ 0 := by
    have : 0 < 2 ^ k := Nat.two_pow_pos k
    omega
  have hlog : k ≤ Nat.log 2 n := (Nat.le_log_iff_pow_le (by decide) hn0).2 hk
  calc n ^ k ≤ n ^ Nat.log 2 n := Nat.pow_le_pow_right (by omega) hlog
    _ ≤ bound n := pow_log_le_bound (by omega)

/-! ### Small Ree groups `²G₂(3^(2a+1))` -/

private theorem pow_three_pow_injective {K : Type} [Field K] [CharP K 3] (a : ℕ) :
    Function.Injective fun x : K => x ^ 3 ^ a := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro x y h
  have h' : iterateFrobenius K 3 a x = iterateFrobenius K 3 a y := by
    simpa [iterateFrobenius_def] using h
  exact (iterateFrobenius K 3 a).injective h'

private theorem index_ge_of_smallReeGamma {K : Type} [Field K] [Finite K] [CharP K ReeTag.G2.prime]
    {a : ℕ} (hK : Nat.card K = 3 ^ (2 * a + 1))
    [IsSimpleGroup ↥(ReeTag.G2.reeGamma K a)]
    (M : Subgroup ↥(ReeTag.G2.reeGamma K a)) (hM : M ≠ ⊤) :
    (Nat.card K - 1) * Nat.card K + 1 ≤ M.index := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : CharP K 3 := by simpa [ReeTag.prime] using (inferInstance : CharP K ReeTag.G2.prime)
  have hle : ReeTag.G2.reeFixedPosUnipotent K a ≤ ReeTag.G2.reeGamma K a := inf_le_right
  let ι := Subgroup.inclusion hle
  let u : K → K → K → ↥(ReeTag.G2.reeGamma K a) := fun t b c =>
    ι (ReeTag.smallReeCoordU hK t b c)
  have hu_mul : ∀ t b c s d e, u t b c * u s d e =
      u (t + s) (b + d + smallReeSigma a t * s) (c + e - b * s + smallReeSigma a t * s ^ 2) :=
    fun t b c s d e => by
      simp only [u, ← map_mul, ReeTag.smallReeCoordU_mul hK]
  have hu_zero : u 0 0 0 = 1 := by
    simp only [u, ReeTag.smallReeCoordU_zero hK, map_one]
  have hσ0 : smallReeSigma a (0 : K) = 0 := smallReeSigma_zero
  let z : Multiplicative K →* ↥(ReeTag.G2.reeGamma K a) :=
    { toFun := fun c => u 0 0 (Multiplicative.toAdd c)
      map_one' := hu_zero
      map_mul' := fun c c' => by
        rw [hu_mul]
        simp [hσ0] }
  let A : Multiplicative K →* ↥(ReeTag.G2.reeGamma K a) :=
    { toFun := fun b => u 0 (Multiplicative.toAdd b) 0
      map_one' := hu_zero
      map_mul' := fun b b' => by
        rw [hu_mul]
        simp [hσ0] }
  let B : K → ↥(ReeTag.G2.reeGamma K a) := fun v => u v 0 0
  have hinv :
      ∀ t : K, (u t 0 0)⁻¹ = u (-t) (t * smallReeSigma a t) (-(t ^ 2 * smallReeSigma a t)) := by
    intro t
    rw [inv_eq_iff_mul_eq_one, hu_mul, ← hu_zero]
    congr 1 <;> ring
  have hzA : ∀ c b, z c * A b = A b * z c := by
    intro c b
    show u 0 0 _ * u 0 _ 0 = u 0 _ 0 * u 0 0 _
    rw [hu_mul, hu_mul]
    simp [hσ0]
  have hBz : ∀ (c : Multiplicative K) (v : K), B v * z c = z c * B v := by
    intro c v
    show u v 0 0 * u 0 0 _ = u 0 0 _ * u v 0 0
    rw [hu_mul, hu_mul]
    simp [hσ0]
  have hBA : ∀ (b v : K), B v * A (Multiplicative.ofAdd b) * (B v)⁻¹ =
      A (Multiplicative.ofAdd b) * z (Multiplicative.ofAdd (b * v)) := by
    intro b v
    show u v 0 0 * u 0 b 0 * (u v 0 0)⁻¹ = u 0 b 0 * u 0 0 (b * v)
    rw [hinv, hu_mul, hu_mul, hu_mul]
    congr 1 <;> simp [hσ0] <;> ring
  have hinj : ∀ (c b : K), z (Multiplicative.ofAdd c) * A (Multiplicative.ofAdd b) = 1 →
      c = 0 ∧ b = 0 := by
    intro c b h
    have h1 : u 0 b c = u 0 0 0 := by
      have h2 : z (Multiplicative.ofAdd c) * A (Multiplicative.ofAdd b) = u 0 b c := by
        show u 0 0 c * u 0 b 0 = u 0 b c
        rw [hu_mul]
        simp [hσ0]
      rw [← h2, h, hu_zero]
    have h3 := ReeTag.smallReeCoordU_injective hK (Subgroup.inclusion_injective hle h1)
    exact ⟨h3.2.2, h3.2.1⟩
  obtain ⟨⟨φ, hφ⟩, hconj, -, -⟩ := small_Ree_positive_torus_action a K hK
  let t : Kˣ →* ↥(ReeTag.G2.reeGamma K a) :=
    (Subgroup.inclusion (inf_le_right : ReeTag.G2.reeFixedTorus K a ≤ ReeTag.G2.reeGamma K a)).comp
      φ.toMonoidHom
  have ht : ∀ s, ((t s : ↥(ReeTag.G2.reeGamma K a)) : ModGL ReeTag.G2.tag K) =
      smallReeTorusElt a K s := fun s => hφ s
  let χ : Kˣ →* Kˣ := powMonoidHom (3 ^ a)
  have htz : ∀ (s : Kˣ) (c : K), t s * z (Multiplicative.ofAdd c) * (t s)⁻¹ =
      z (Multiplicative.ofAdd ((χ s : K) * c)) := by
    intro s c
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, ht]
    have := hconj s 0 0 c
    simp only [mul_zero] at this
    rw [show ((χ s : Kˣ) : K) = (s : K) ^ 3 ^ a by simp [χ]]
    exact this
  have hta : ∀ (s : Kˣ) (b : K), ∃ b', t s * A (Multiplicative.ofAdd b) * (t s)⁻¹ =
      A (Multiplicative.ofAdd b') := by
    intro s b
    refine ⟨(((s ^ (1 - (3 ^ a : ℤ)) : Kˣ) : K) * b), Subtype.ext ?_⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, ht]
    have := hconj s 0 b 0
    simp only [mul_zero] at this
    exact this
  have hχ : Nat.card χ.range = Nat.card K - 1 := by
    have hinjχ : Function.Injective χ := by
      intro s s' h
      apply Units.ext
      apply pow_three_pow_injective (K := K) a
      have := congrArg (fun x : Kˣ => (x : K)) h
      simpa [χ] using this
    rw [← Nat.card_congr (MonoidHom.ofInjective hinjχ).toEquiv, Nat.card_units]
  have hmain := card_range_mul_card_add_one_le_index_of_heis_root
    (K := K) (V := K) z A B (LinearMap.mul K K)
    (fun v hv => ⟨1, by simpa using hv⟩) hinj hzA
    (fun b v => by simpa [LinearMap.mul_apply'] using hBA b v) hBz t χ htz hta M hM
  rwa [hχ] at hmain

/-- Every proper subgroup `H` of a small Ree group model `S` (`²G₂(3^f)`) has index at least
`(3^f - 1) * 3^f + 1`. -/
theorem index_ge_of_reeTitsModel_twistedG2 {S : Type} [Group S] [IsSimpleGroup S] {p f : ℕ}
    (h : ReeTitsModel S .twistedG2 p f) (H : Subgroup S) (hH : H ≠ ⊤) :
    (3 ^ f - 1) * 3 ^ f + 1 ≤ H.index := by
  obtain ⟨-, -, rfl, ⟨a, ha, hfa⟩, hiso⟩ := small_Ree_model_Schreier S p f h
  obtain ⟨-, a', hfa', K, _, _, hK, hw⟩ := h
  have ha' : a' = a := by omega
  subst ha'
  have : Fintype K := Fintype.ofFinite K
  have : CharP K ReeTag.G2.prime := charP_of_card_eq_prime_pow (f := f) (by
    rw [← Nat.card_eq_fintype_card, hK]
    rfl)
  obtain ⟨E⟩ := hiso a' K hfa hK hw
  have : IsSimpleGroup ↥(ReeTag.G2.reeGamma K a') := E.symm.isSimpleGroup
  have hK' : Nat.card K = 3 ^ (2 * a' + 1) := by rw [hK, hfa]
  have hMH : H.map (E : S →* ↥(ReeTag.G2.reeGamma K a')) ≠ ⊤ := by
    intro htop
    apply hH
    apply Subgroup.map_injective (f := (E : S →* ↥(ReeTag.G2.reeGamma K a'))) E.injective
    rw [htop, Subgroup.map_top_of_surjective _ E.surjective]
  have hidx := index_ge_of_smallReeGamma hK' (H.map (E : S →* ↥(ReeTag.G2.reeGamma K a'))) hMH
  rwa [Subgroup.index_map_equiv H E, hK] at hidx

/-- For `²G₂(3^f)` (`f = 2a + 1`, `a ≥ 1`), `|S| · |Out(S)| ≤ bound ((3^f - 1) * 3^f + 1)`. -/
theorem card_mul_outerAut_le_bound_of_reeTitsModel_twistedG2 {S : Type} [Group S] {p f : ℕ}
    (h : ReeTitsModel S .twistedG2 p f) :
    Nat.card S * f ≤ bound ((3 ^ f - 1) * 3 ^ f + 1) := by
  obtain ⟨rfl, ⟨a, ha, hfa⟩, hcard⟩ := card_reeTitsModel_twistedG2 h
  rw [hcard]
  set q := 3 ^ f
  have hf3 : 3 ≤ f := by omega
  have hq27 : 27 ≤ q := by
    calc 27 = 3 ^ 3 := by decide
      _ ≤ 3 ^ f := Nat.pow_le_pow_right (by decide) hf3
  have hfq : f ≤ q := (Nat.lt_pow_self (by decide : 1 < 3)).le
  have hq_le : q ≤ (q - 1) * q + 1 := by
    have : 1 * q ≤ (q - 1) * q := Nat.mul_le_mul_right q (by omega)
    omega
  have h512 : 2 ^ 9 ≤ (q - 1) * q + 1 := by
    have : 26 * 27 ≤ (q - 1) * q := Nat.mul_le_mul (by omega) hq27
    omega
  calc ordRee q * f
      ≤ q ^ 7 * q := Nat.mul_le_mul (ordRee_le_pow q) hfq
    _ = q ^ 8 := by ring
    _ ≤ q ^ 9 := Nat.pow_le_pow_right (by omega) (by decide)
    _ ≤ ((q - 1) * q + 1) ^ 9 := Nat.pow_le_pow_left hq_le 9
    _ ≤ bound ((q - 1) * q + 1) := pow_le_bound' h512

/-- Any primitive almost simple group `G ≤ Perm α` with socle `²G₂(3^f)` satisfies
`|G| ≤ bound |α|`. -/
theorem card_le_bound_of_reeTitsModel_twistedG2 {α : Type} [Finite α]
    {G : Subgroup (Equiv.Perm α)} [MulAction.IsPreprimitive G α]
    {S : Type} [Group S] {p f : ℕ} (hAS : IsAlmostSimpleWith G S)
    (h : ReeTitsModel S .twistedG2 p f) :
    Nat.card G ≤ bound (Nat.card α) := by
  have : IsSimpleGroup S := hAS.isSimpleGroup
  exact hAS.card_le_bound_of_outerAut_le (index_ge_of_reeTitsModel_twistedG2 h)
    (card_outerAut_twistedG2 h).le (card_mul_outerAut_le_bound_of_reeTitsModel_twistedG2 h)

/-! ### Large Ree groups `²F₄(2^(2a+1))` -/

private def reeF4Val {K : Type} [Field K] (m : ℕ) (x0 x1 x2 x3 x4 x5 : K) : ℕ → K
  | 0 => x0
  | 1 => x1
  | 2 => x2
  | 3 => x3
  | 4 => x4
  | 5 => x5
  | 6 => largeReeSigma m x0
  | 7 => largeReeSigma m x1
  | 8 => largeReeSigma m x2
  | 9 => largeReeSigma m x3
  | 10 => largeReeSigma m x4
  | 11 => largeReeSigma m x5
  | _ => 0

private def reeF4AWord1 : Word :=
  [(36, [[0]]), (39, [[6]]), (43, [[1]]), (46, [[7]]), (41, [[2]]), (45, [[8]])]

private def reeF4AWord2 : Word :=
  [(36, [[3]]), (39, [[9]]), (43, [[4]]), (46, [[10]]), (41, [[5]]), (45, [[11]])]

private def reeF4AWord12 : Word :=
  [(36, [[0], [3]]), (39, [[6], [9]]), (43, [[1], [4]]), (46, [[7], [10]]),
   (41, [[2], [5]]), (45, [[8], [11]])]

private def reeF4ATable : List Poly :=
  [[], [], [], [], [], [], [], [], [], [], [], [], [[0], [3]], [], [], [[6], [9]], [],
   [[2], [5]], [], [[1], [4]], [], [[8], [11]], [[7], [10]], []]

private theorem reeF4A_check1 :
    collectCheck 100 (reeF4AWord1 ++ reeF4AWord2) reeF4ATable = true := by
  decide +kernel

private theorem reeF4A_check2 : collectCheck 100 reeF4AWord12 reeF4ATable = true := by
  decide +kernel

private def reeF4ZWord0 : Word := [(44, [[0]]), (47, [[6]])]
private def reeF4ZWord3 : Word := [(44, [[3]]), (47, [[9]])]
private def reeF4ZWord03 : Word := [(44, [[0], [3]]), (47, [[6], [9]])]

private def reeF4ZTable : List Poly :=
  [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [],
   [[0], [3]], [], [], [[6], [9]]]

private theorem reeF4Z_check1 :
    collectCheck 50 (reeF4ZWord0 ++ reeF4ZWord3) reeF4ZTable = true := by
  decide +kernel

private theorem reeF4Z_check2 : collectCheck 50 reeF4ZWord03 reeF4ZTable = true := by
  decide +kernel

private def reeF4ZATable : List Poly :=
  [[], [], [], [], [], [], [], [], [], [], [], [], [[0]], [], [], [[6]], [], [[2]], [],
   [[1]], [[3]], [[8]], [[7]], [[9]]]

private theorem reeF4ZA_check1 :
    collectCheck 100 (reeF4ZWord3 ++ reeF4AWord1) reeF4ZATable = true := by
  decide +kernel

private theorem reeF4ZA_check2 :
    collectCheck 100 (reeF4AWord1 ++ reeF4ZWord3) reeF4ZATable = true := by
  decide +kernel

private def reeF4BWord : Word :=
  [(24, [[4]]), (33, [[10]]), (26, [[5]]), (34, [[11]]), (39, [[5, 5, 11]]),
   (31, [[3]]), (40, [[9]])]

private def reeF4BZTable : List Poly :=
  [[[4]], [], [[5]], [], [], [], [], [[3]], [], [[10]], [[11]], [], [], [], [[3, 10]],
   [[5, 5, 11]], [[9]], [[3, 11]], [], [], [[0]], [[3, 3, 10]], [[3, 3, 11]],
   [[3, 3, 10, 11], [6]]]

private theorem reeF4BZ_check1 :
    collectCheck 150 (reeF4BWord ++ reeF4ZWord0) reeF4BZTable = true := by
  decide +kernel

private theorem reeF4BZ_check2 :
    collectCheck 150 (reeF4ZWord0 ++ reeF4BWord) reeF4BZTable = true := by
  decide +kernel

private def reeF4ZPairWord : Word :=
  [(44, [[0, 3], [1, 4], [2, 5]]), (47, [[6, 9], [7, 10], [8, 11]])]

private def reeF4BATable : List Poly :=
  [[[4]], [], [[5]], [], [], [], [], [[3]], [], [[10]], [[11]], [], [[0]], [], [[3, 10]],
   [[5, 5, 11], [6]], [[9]], [[2], [3, 11]], [], [[1]], [], [[3, 3, 10], [8]],
   [[3, 3, 11], [7]], [[3, 3, 10, 11], [6, 9]]]

private theorem reeF4BA_check1 :
    collectCheck 200 (reeF4BWord ++ reeF4AWord1) reeF4BATable = true := by
  decide +kernel

private theorem reeF4BA_check2 :
    collectCheck 300 (reeF4AWord1 ++ reeF4ZPairWord ++ reeF4BWord) reeF4BATable = true := by
  decide +kernel

private theorem largeReeSigma_add {K : Type} [Field K] [Finite K] {m : ℕ}
    (hK : Nat.card K = 2 ^ (2 * m + 1)) (x y : K) :
    largeReeSigma m (x + y) = largeReeSigma m x + largeReeSigma m y := by
  obtain ⟨σ, hσ, -⟩ := exists_sigma hK
  rw [← hσ, ← hσ, ← hσ, map_add]

private theorem largeReeSigma_mul' {K : Type} [Field K] (m : ℕ) (x y : K) :
    largeReeSigma m (x * y) = largeReeSigma m x * largeReeSigma m y :=
  mul_pow x y _

private def dot3 (K : Type) [Field K] : (Fin 3 → K) →ₗ[K] (Fin 3 → K) →ₗ[K] K :=
  LinearMap.mk₂ K (fun u v => u 0 * v 0 + u 1 * v 1 + u 2 * v 2)
    (fun u u' v => by simp only [Pi.add_apply]; ring)
    (fun c u v => by simp only [Pi.smul_apply, smul_eq_mul]; ring)
    (fun u v v' => by simp only [Pi.add_apply]; ring)
    (fun c u v => by simp only [Pi.smul_apply, smul_eq_mul]; ring)

private theorem dot3_apply {K : Type} [Field K] (u v : Fin 3 → K) :
    dot3 K u v = u 0 * v 0 + u 1 * v 1 + u 2 * v 2 :=
  rfl

private noncomputable def reeF4AElt {K : Type} [Field K] (m : ℕ) (u : Fin 3 → K) : ModGL F4.tag K :=
  sylowD m K 0 (u 0) * sylowF m K 0 (u 1) * sylowL m K (u 2)

private noncomputable def reeF4BElt {K : Type} [Field K] (m : ℕ) (v : Fin 3 → K) : ModGL F4.tag K :=
  sylowA m K (v 1) * sylowD m K (v 2) 0 * sylowJ m K (v 0)

private theorem index_ge_of_largeReeGamma {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]
    {m : ℕ} (hK : Nat.card K = 2 ^ (2 * m + 1))
    [IsSimpleGroup ↥(ReeTag.F4.reeGamma K m)]
    (M : Subgroup ↥(ReeTag.F4.reeGamma K m)) (hM : M ≠ ⊤) :
    Nat.card K ^ 3 + 1 ≤ M.index := by
  classical
  have : CharP K 2 := ‹CharP K ReeTag.F4.prime›
  have hle : ReeTag.F4.reeFixedPosUnipotent K m ≤ ReeTag.F4.reeGamma K m := inf_le_right
  have hmemV : ∀ a b c d e f g h i j k l : K,
      sylowV m K a b c d e f g h i j k l ∈ ReeTag.F4.reeGamma K m := by
    intro a b c d e f g h i j k l
    have hm : sylowVec m K ![a, b, c, d, e, f, g, h, i, j, k, l] ∈
        ReeTag.F4.reeFixedPosUnipotent K m :=
      (bijOn_sylowVec hK).1 (Set.mem_univ _)
    exact hle hm
  have hzeroX : ∀ r, sylowX K r 0 = 1 := fun r => pinnedX_zero _ _ _
  have hσ0 : largeReeSigma m (0 : K) = 0 := largeReeSigma_zero
  have hA0 : sylowA m K 0 = 1 := by simp [sylowA, hσ0, hzeroX]
  have hB0 : sylowB m K 0 0 = 1 := by simp [sylowB, hσ0, hzeroX]
  have hD0 : sylowD m K 0 0 = 1 := by simp [sylowD, hσ0, hzeroX]
  have hF0 : sylowF m K 0 0 = 1 := by simp [sylowF, hσ0, hzeroX]
  have hH0 : sylowH m K 0 0 = 1 := by simp [sylowH, hσ0, hzeroX]
  have hJ0 : sylowJ m K 0 = 1 := by simp [sylowJ, hσ0, hzeroX]
  have hK0 : sylowK m K 0 = 1 := by simp [sylowK, hσ0, hzeroX]
  have hL0 : sylowL m K 0 = 1 := by simp [sylowL, hσ0, hzeroX]
  have hz_eq_V : ∀ c : K, sylowH m K 0 c = sylowV m K 0 0 0 0 0 0 0 0 c 0 0 0 := by
    intro c
    simp [sylowV, hA0, hB0, hD0, hF0, hJ0, hK0, hL0]
  have ha_eq_V : ∀ u : Fin 3 → K,
      reeF4AElt m u = sylowV m K 0 0 0 0 (u 0) 0 (u 1) 0 0 0 0 (u 2) := by
    intro u
    simp [reeF4AElt, sylowV, hA0, hB0, hH0, hJ0, hK0]
  have hb_eq_V : ∀ v : Fin 3 → K,
      reeF4BElt m v = sylowV m K (v 1) 0 0 (v 2) 0 0 0 0 0 (v 0) 0 0 := by
    intro v
    simp [reeF4BElt, sylowV, hB0, hF0, hH0, hK0, hL0]
  have hz_mem : ∀ c : K, sylowH m K 0 c ∈ ReeTag.F4.reeGamma K m := fun c => by
    rw [hz_eq_V]
    exact hmemV _ _ _ _ _ _ _ _ _ _ _ _
  have ha_mem : ∀ u : Fin 3 → K, reeF4AElt m u ∈ ReeTag.F4.reeGamma K m := fun u => by
    rw [ha_eq_V]
    exact hmemV _ _ _ _ _ _ _ _ _ _ _ _
  have hb_mem : ∀ v : Fin 3 → K, reeF4BElt m v ∈ ReeTag.F4.reeGamma K m := fun v => by
    rw [hb_eq_V]
    exact hmemV _ _ _ _ _ _ _ _ _ _ _ _
  have hz_word0 : ∀ x0 x1 x2 x3 x4 x5 : K,
      wordEval K (reeF4Val m x0 x1 x2 x3 x4 x5) reeF4ZWord0 = sylowH m K 0 x0 := by
    intro x0 x1 x2 x3 x4 x5
    simp [reeF4ZWord0, wordEval, polyEval, monoEval, reeF4Val, sylowH, sylowX, hσ0, pinnedX_zero]
  have hz_word3 : ∀ x0 x1 x2 x3 x4 x5 : K,
      wordEval K (reeF4Val m x0 x1 x2 x3 x4 x5) reeF4ZWord3 = sylowH m K 0 x3 := by
    intro x0 x1 x2 x3 x4 x5
    simp [reeF4ZWord3, wordEval, polyEval, monoEval, reeF4Val, sylowH, sylowX, hσ0, pinnedX_zero]
  have ha_word1 : ∀ u : Fin 3 → K, ∀ x3 x4 x5 : K,
      wordEval K (reeF4Val m (u 0) (u 1) (u 2) x3 x4 x5) reeF4AWord1 = reeF4AElt m u := by
    intro u x3 x4 x5
    simp [reeF4AWord1, reeF4AElt, wordEval, polyEval, monoEval, reeF4Val, sylowD, sylowF, sylowL,
      sylowX, hσ0, pinnedX_zero, mul_assoc]
  have ha_word2 : ∀ x0 x1 x2 : K, ∀ v : Fin 3 → K,
      wordEval K (reeF4Val m x0 x1 x2 (v 0) (v 1) (v 2)) reeF4AWord2 = reeF4AElt m v := by
    intro x0 x1 x2 v
    simp [reeF4AWord2, reeF4AElt, wordEval, polyEval, monoEval, reeF4Val, sylowD, sylowF, sylowL,
      sylowX, hσ0, pinnedX_zero, mul_assoc]
  have ha_word12 : ∀ u v : Fin 3 → K,
      wordEval K (reeF4Val m (u 0) (u 1) (u 2) (v 0) (v 1) (v 2)) reeF4AWord12 =
        reeF4AElt m (u + v) := by
    intro u v
    simp [reeF4AWord12, reeF4AElt, wordEval, polyEval, monoEval, reeF4Val, sylowD, sylowF, sylowL,
      sylowX, hσ0, pinnedX_zero, largeReeSigma_add hK, mul_assoc]
  have hb_word : ∀ x0 x1 x2 : K, ∀ v : Fin 3 → K,
      wordEval K (reeF4Val m x0 x1 x2 (v 0) (v 1) (v 2)) reeF4BWord = reeF4BElt m v := by
    intro x0 x1 x2 v
    simp [reeF4BWord, reeF4BElt, wordEval, polyEval, monoEval, reeF4Val, sylowA, sylowD, sylowJ,
      sylowX, hσ0, pinnedX_zero, sq, mul_assoc]
  have hz_pair_word : ∀ u v : Fin 3 → K,
      wordEval K (reeF4Val m (u 0) (u 1) (u 2) (v 0) (v 1) (v 2)) reeF4ZPairWord =
        sylowH m K 0 (dot3 K u v) := by
    intro u v
    simp [reeF4ZPairWord, wordEval, polyEval, monoEval, reeF4Val, sylowH, sylowX, hσ0,
      pinnedX_zero, dot3_apply, largeReeSigma_add hK, largeReeSigma_mul', add_assoc]
  let z : Multiplicative K →* ↥(ReeTag.F4.reeGamma K m) :=
    { toFun := fun c => ⟨sylowH m K 0 (Multiplicative.toAdd c), hz_mem _⟩
      map_one' := Subtype.ext hH0
      map_mul' := fun c d => Subtype.ext <| by
        change sylowH m K 0 (Multiplicative.toAdd c + Multiplicative.toAdd d) =
          sylowH m K 0 (Multiplicative.toAdd c) * sylowH m K 0 (Multiplicative.toAdd d)
        set c' := Multiplicative.toAdd c
        set d' := Multiplicative.toAdd d
        have h := ((wordEval_eq_iff reeF4Z_check1 reeF4Z_check2
          (reeF4Val m c' 0 0 d' 0 0)).2 fun _ => rfl).symm
        rw [wordEval_append, hz_word0, hz_word3] at h
        refine (?_ : sylowH m K 0 (c' + d') =
          wordEval K (reeF4Val m c' 0 0 d' 0 0) reeF4ZWord03).trans h
        simp [reeF4ZWord03, wordEval, polyEval, monoEval, reeF4Val, sylowH, sylowX, hσ0,
          pinnedX_zero, largeReeSigma_add hK] }
  let A : Multiplicative (Fin 3 → K) →* ↥(ReeTag.F4.reeGamma K m) :=
    { toFun := fun u => ⟨reeF4AElt m (Multiplicative.toAdd u), ha_mem (Multiplicative.toAdd u)⟩
      map_one' := Subtype.ext <| by
        change reeF4AElt m 0 = 1
        simp [reeF4AElt, hD0, hF0, hL0]
      map_mul' := fun u v => Subtype.ext <| by
        set u' := Multiplicative.toAdd u
        set v' := Multiplicative.toAdd v
        change reeF4AElt m (u' + v') = reeF4AElt m u' * reeF4AElt m v'
        have h := ((wordEval_eq_iff reeF4A_check1 reeF4A_check2
          (reeF4Val m (u' 0) (u' 1) (u' 2) (v' 0) (v' 1) (v' 2))).2 fun _ => rfl).symm
        rw [wordEval_append, ha_word1, ha_word2, ha_word12] at h
        exact h }
  let B : (Fin 3 → K) → ↥(ReeTag.F4.reeGamma K m) := fun v => ⟨reeF4BElt m v, hb_mem v⟩
  have hz_inj : ∀ c : K, z (Multiplicative.ofAdd c) = 1 → c = 0 := by
    intro c hc
    have hc' : sylowH m K 0 c = sylowH m K 0 0 := (congrArg Subtype.val hc).trans hH0.symm
    rw [sylowH_eq, sylowH_eq] at hc'
    exact (fourCoordG_injective hK 3 hc').2
  have hzA : ∀ c u, z c * A u = A u * z c := by
    intro c u
    apply Subtype.ext
    set c' := Multiplicative.toAdd c
    set u' := Multiplicative.toAdd u
    have h := (wordEval_eq_iff reeF4ZA_check1 reeF4ZA_check2
      (reeF4Val m (u' 0) (u' 1) (u' 2) c' 0 0)).2 fun _ => rfl
    rw [wordEval_append, wordEval_append, hz_word3, ha_word1] at h
    exact h
  have hBz : ∀ (c : Multiplicative K) (v : Fin 3 → K), B v * z c = z c * B v := by
    intro c v
    apply Subtype.ext
    set c' := Multiplicative.toAdd c
    have h := (wordEval_eq_iff reeF4BZ_check1 reeF4BZ_check2
      (reeF4Val m c' 0 0 (v 0) (v 1) (v 2))).2 fun _ => rfl
    rw [wordEval_append, wordEval_append, hb_word, hz_word0] at h
    exact h
  have hBA : ∀ (u v : Fin 3 → K), B v * A (Multiplicative.ofAdd u) * (B v)⁻¹ =
      A (Multiplicative.ofAdd u) * z (Multiplicative.ofAdd (dot3 K u v)) := by
    intro u v
    rw [mul_inv_eq_iff_eq_mul]
    apply Subtype.ext
    change reeF4BElt m v * reeF4AElt m u =
      reeF4AElt m u * sylowH m K 0 (dot3 K u v) * reeF4BElt m v
    have h := (wordEval_eq_iff reeF4BA_check1 reeF4BA_check2
      (reeF4Val m (u 0) (u 1) (u 2) (v 0) (v 1) (v 2))).2 fun _ => rfl
    rw [wordEval_append, wordEval_append, wordEval_append, hb_word, ha_word1, hz_pair_word] at h
    exact h
  have hβ : ∀ v : Fin 3 → K, v ≠ 0 → ∃ u, dot3 K u v ≠ 0 := by
    intro v hv
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hv
    refine ⟨Pi.single i 1, ?_⟩
    fin_cases i <;> simpa [dot3_apply] using hi
  have hβl : ∀ u : Fin 3 → K, u ≠ 0 → ∃ v, dot3 K u v ≠ 0 := by
    intro u hu
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hu
    refine ⟨Pi.single i 1, ?_⟩
    fin_cases i <;> simpa [dot3_apply] using hi
  have hmain := card_add_one_le_index_of_heis_root_of_inj_one
    (K := K) (V := Fin 3 → K) z A B (dot3 K) hβ hβl hz_inj hzA hBA hBz M hM
  have hcardV : Nat.card (Fin 3 → K) = Nat.card K ^ 3 := by
    rw [Nat.card_fun, Nat.card_fin]
  rwa [hcardV] at hmain

/-- Every proper subgroup `H` of a large Ree group model `S` (`²F₄(2^f)`) has index at least
`(2^f) ^ 3 + 1`. -/
theorem index_ge_of_reeTitsModel_twistedF4 {S : Type} [Group S] [IsSimpleGroup S] {p f : ℕ}
    (h : ReeTitsModel S .twistedF4 p f) (H : Subgroup S) (hH : H ≠ ⊤) :
    (2 ^ f) ^ 3 + 1 ≤ H.index := by
  have hp : p = 2 := h.1.2.2.2.1
  subst hp
  have hS := large_Ree_model_Schreier S 2 f h
  obtain ⟨hadm, a, hfa, K, _, _, hK, ⟨e⟩⟩ := h
  have : Fintype K := Fintype.ofFinite K
  have : CharP K ReeTag.F4.prime := charP_of_card_eq_prime_pow (f := f) (by
    rw [← Nat.card_eq_fintype_card, hK]
    rfl)
  obtain ⟨E⟩ := hS.2.2.2.2.2 a K hfa hK ⟨e⟩
  have : IsSimpleGroup ↥(ReeTag.F4.reeGamma K a) := E.symm.isSimpleGroup
  have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK, hfa]
  have hMH : H.map (E : S →* ↥(ReeTag.F4.reeGamma K a)) ≠ ⊤ := by
    intro htop
    apply hH
    apply Subgroup.map_injective (f := (E : S →* ↥(ReeTag.F4.reeGamma K a))) E.injective
    rw [htop, Subgroup.map_top_of_surjective _ E.surjective]
  have hidx := index_ge_of_largeReeGamma hK' (H.map (E : S →* ↥(ReeTag.F4.reeGamma K a))) hMH
  rwa [Subgroup.index_map_equiv H E, hK] at hidx

/-- For `²F₄(2^f)` (`f = 2a + 1`, `a ≥ 1`), `|S| · |Out(S)| ≤ bound ((2^f) ^ 3 + 1)`. -/
theorem card_mul_outerAut_le_bound_of_reeTitsModel_twistedF4 {S : Type} [Group S] {p f : ℕ}
    (h : ReeTitsModel S .twistedF4 p f) :
    Nat.card S * f ≤ bound ((2 ^ f) ^ 3 + 1) := by
  obtain ⟨rfl, ⟨a, ha, hfa⟩, hcard⟩ := card_reeTitsModel_twistedF4 h
  rw [hcard]
  set q := 2 ^ f
  have hf3 : 3 ≤ f := by omega
  have hq8 : 8 ≤ q := by
    calc 8 = 2 ^ 3 := by decide
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by decide) hf3
  have hfq : f ≤ q := (Nat.lt_pow_self (by decide : 1 < 2)).le
  have h512 : 2 ^ 9 ≤ q ^ 3 + 1 := by
    have : 8 ^ 3 ≤ q ^ 3 := Nat.pow_le_pow_left hq8 3
    omega
  calc ordTwistedF4 q * f
      ≤ q ^ 26 * q := Nat.mul_le_mul (ordTwistedF4_le_pow q) hfq
    _ = (q ^ 3) ^ 9 := by ring
    _ ≤ (q ^ 3 + 1) ^ 9 := Nat.pow_le_pow_left (Nat.le_succ _) 9
    _ ≤ bound (q ^ 3 + 1) := pow_le_bound' h512

/-- Any primitive almost simple group `G ≤ Perm α` with socle `²F₄(2^f)` satisfies
`|G| ≤ bound |α|`. -/
theorem card_le_bound_of_reeTitsModel_twistedF4 {α : Type} [Finite α]
    {G : Subgroup (Equiv.Perm α)} [MulAction.IsPreprimitive G α]
    {S : Type} [Group S] {p f : ℕ} (hAS : IsAlmostSimpleWith G S)
    (h : ReeTitsModel S .twistedF4 p f) :
    Nat.card G ≤ bound (Nat.card α) := by
  have : IsSimpleGroup S := hAS.isSimpleGroup
  exact hAS.card_le_bound_of_outerAut_le (index_ge_of_reeTitsModel_twistedF4 h)
    (card_outerAut_twistedF4 h).le (card_mul_outerAut_le_bound_of_reeTitsModel_twistedF4 h)

end Maroti
