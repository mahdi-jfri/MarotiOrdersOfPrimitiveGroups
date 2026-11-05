module

public import Maroti.Linear.OrderAut
public import Maroti.Bound

/-!
# Numerical bounds comparing `|Aut(PSL(t, q))|` with `Maroti.bound n`

This file proves the numerical inequalities comparing the automorphism group upper bound
`pslAutUpper t p f` (and `|PSL(t, 2)|` when `n = 2^t - 1`) with `Maroti.bound n`:

* The theorem `Maroti.pslOuterBound_mul_card_le_pslAutUpper` shows that
  `pslOuterBound t p f * |S| ≤ pslAutUpper t p f`.
* The theorem `Maroti.pslAutUpper_le_pow` shows that
  `pslAutUpper t p f ≤ (if t = 2 then 1 else 2) * f * (p^f)^(t^2 - 1)`.
* The theorem `Maroti.simple_lower_le_bound` establishes power lower bounds for `Maroti.bound`.
* The theorem `Maroti.card_le_bound_two_pow_sub_one` shows `|PSL(t, 2)| ≤ bound (2^t - 1)` for
  `t ≥ 3`.
* The theorem `Maroti.pslAutUpper_le_bound_two_pow` shows `pslAutUpper t 2 1 ≤ bound n` for `t ≥ 3`
  and `2^t ≤ n`.
* The theorem `Maroti.pslAutUpper_le_bound_of_three_le` shows `pslAutUpper t p f ≤ bound n` for
  `t ≥ 3`, `p^f ≥ 3`, and `n ≥ (p^f)^(t - 1)` (away from `(t, p^f) ∈ {(3, 3), (4, 3)}`, where
  `n ≥ 13` and `n ≥ 32` suffice).
* The theorem `Maroti.pslAutUpper_le_bound_of_two` proves the corresponding bounds for `t = 2`.
-/

@[expose] public section

namespace Maroti

open CFSG.Open

/-- Explicit upper bound for `|Aut(PSL(t, p^f))|` obtained by dropping the `gcd(t, p^f - 1)`
denominator in `|PSL(t, p^f)|` against the `gcd(t, p^f - 1)` factor in `pslOuterBound t p f`. -/
def pslAutUpper (t p f : ℕ) : ℕ :=
  (if t = 2 then 1 else 2) * f *
    ((p ^ f) ^ (t * (t - 1) / 2) * ∏ i ∈ Finset.Icc 2 t, ((p ^ f) ^ i - 1))

theorem pslOuterBound_mul_card_le_pslAutUpper {S : Type} [Group S] {t p f : ℕ}
    (h : StatedClassicalModel S .PSL t p f) :
    pslOuterBound t p f * Nat.card S ≤ pslAutUpper t p f := by
  have h' := h
  obtain ⟨⟨_, _, ht2, -⟩, -⟩ := h'
  have hcard := StatedAPI.card_of_statedClassicalModel_psl (by omega : 0 < t) h
  rw [hcard]
  unfold pslOuterBound pslAutUpper
  rw [mul_assoc ((if t = 2 then 1 else 2) * f)]
  exact Nat.mul_le_mul_left _ (Nat.mul_div_le _ _)

theorem mul_self_sub_one_div_two_succ (t : ℕ) :
    (t + 1) * t / 2 = t * (t - 1) / 2 + t := by
  rcases t with _ | t
  · rfl
  · have h1 : (t + 2) * (t + 1) = (t + 1) * t + (t + 1) * 2 := by ring
    rw [Nat.add_sub_cancel, h1, Nat.add_mul_div_right _ _ (by omega : 0 < 2)]

/-- For `t ≥ 2`, `q^(t(t-1)/2) * ∏_{i=2}^t (q^i - 1) ≤ q^(t^2 - 1)`. -/
theorem pow_mul_prod_Icc_le_pow {t q : ℕ} (ht : 2 ≤ t) :
    q ^ (t * (t - 1) / 2) * ∏ i ∈ Finset.Icc 2 t, (q ^ i - 1) ≤ q ^ (t ^ 2 - 1) := by
  induction t, ht using Nat.le_induction with
  | base =>
    have hprod : ∏ i ∈ Finset.Icc 2 2, (q ^ i - 1) = q ^ 2 - 1 := by simp
    have hpow : 2 * (2 - 1) / 2 = 1 := rfl
    have hsq : 2 ^ 2 - 1 = 3 := rfl
    rw [hprod, hpow, hsq, pow_one]
    calc q * (q ^ 2 - 1) ≤ q * q ^ 2 := Nat.mul_le_mul_left q (Nat.sub_le _ _)
      _ = q ^ 3 := by ring
  | succ t ht ih =>
    have hIcc : Finset.Icc 2 (t + 1) = insert (t + 1) (Finset.Icc 2 t) := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have hnotmem : t + 1 ∉ Finset.Icc 2 t := by
      simp only [Finset.mem_Icc]
      omega
    rw [Nat.add_sub_cancel, mul_self_sub_one_div_two_succ, hIcc, Finset.prod_insert hnotmem]
    calc q ^ (t * (t - 1) / 2 + t) * ((q ^ (t + 1) - 1) * ∏ i ∈ Finset.Icc 2 t, (q ^ i - 1))
      _ = q ^ t * (q ^ (t * (t - 1) / 2) * ∏ i ∈ Finset.Icc 2 t, (q ^ i - 1)) *
            (q ^ (t + 1) - 1) := by
          rw [pow_add]
          ring
      _ ≤ q ^ t * q ^ (t ^ 2 - 1) * q ^ (t + 1) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left (q ^ t) ih) (Nat.sub_le _ _)
      _ = q ^ (t + (t ^ 2 - 1) + (t + 1)) := by rw [← pow_add, ← pow_add]
      _ = q ^ ((t + 1) ^ 2 - 1) := by
          congr 1
          have : 4 ≤ t ^ 2 := by nlinarith
          have : (t + 1) ^ 2 = t ^ 2 + 2 * t + 1 := by ring
          omega

theorem pslAutUpper_le_pow {t p f : ℕ} (ht : 2 ≤ t) :
    pslAutUpper t p f ≤ (if t = 2 then 1 else 2) * f * (p ^ f) ^ (t ^ 2 - 1) := by
  unfold pslAutUpper
  exact Nat.mul_le_mul_left _ (pow_mul_prod_Icc_le_pow ht)

/-- For any `k ≥ 1` with `2^k ≤ n`, `n * (n - 2^(k-1))^k ≤ bound n`. -/
theorem simple_lower_le_bound {n k : ℕ} (hk : 1 ≤ k) (hpow : 2 ^ k ≤ n) :
    n * (n - 2 ^ (k - 1)) ^ k ≤ bound n := by
  unfold bound
  refine Nat.mul_le_mul_left n ?_
  have hn_pos : 0 < n := lt_of_lt_of_le (by positivity) hpow
  have hk_log : k ≤ Nat.log 2 n :=
    (Nat.le_log_iff_pow_le (by omega : 1 < 2) (by omega)).mpr hpow
  calc (n - 2 ^ (k - 1)) ^ k
    _ = ∏ _i ∈ Finset.range k, (n - 2 ^ (k - 1)) := by
        rw [Finset.prod_const, Finset.card_range]
    _ ≤ ∏ i ∈ Finset.range k, (n - 2 ^ i) := by
        refine Finset.prod_le_prod fun i hi => ?_
        have hi_le : i ≤ k - 1 := by
          have := Finset.mem_range.mp hi
          omega
        exact Nat.sub_le_sub_left (Nat.pow_le_pow_right (by omega) hi_le) n
    _ ≤ ∏ i ∈ Finset.range (Nat.log 2 n), (n - 2 ^ i) := by
        refine Finset.prod_le_prod_of_subset_of_one_le (Finset.range_mono hk_log) fun i hi _ => ?_
        have hi_lt : i < Nat.log 2 n := Finset.mem_range.mp hi
        have hpow_lt : 2 ^ i < n :=
          lt_of_lt_of_le (Nat.pow_lt_pow_right (by omega) hi_lt)
            (Nat.pow_log_le_self 2 (by omega))
        omega

private theorem two_pow_triangular_eq_prod_range (m : ℕ) :
    2 ^ ((m + 1) * m / 2) = ∏ k ∈ Finset.range m, 2 ^ (k + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [mul_self_sub_one_div_two_succ (m + 1), Nat.add_sub_cancel, pow_add, ih,
      Finset.prod_range_succ]

private theorem prod_Icc_two_pow_sub_one_eq_prod_range (m : ℕ) :
    ∏ i ∈ Finset.Icc 2 m, (2 ^ i - 1) = ∏ j ∈ Finset.range m, (2 ^ (j + 1) - 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rcases m with _ | m
    · simp
    · have hIcc : Finset.Icc 2 (m + 2) = insert (m + 2) (Finset.Icc 2 (m + 1)) := by
        ext x
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      have hnotmem : m + 2 ∉ Finset.Icc 2 (m + 1) := by
        simp only [Finset.mem_Icc]
        omega
      rw [hIcc, Finset.prod_insert hnotmem, ih,
        Finset.prod_range_succ (fun j => 2 ^ (j + 1) - 1) (m + 1), mul_comm]

/-- For `t ≥ 3`, `|PSL(t, 2)| ≤ bound (2^t - 1)`. -/
theorem card_le_bound_two_pow_sub_one {S : Type} [Group S] {t : ℕ} (ht : 3 ≤ t)
    (h : StatedClassicalModel S .PSL t 2 1) :
    Nat.card S ≤ bound (2 ^ t - 1) := by
  have hcard := StatedAPI.card_of_statedClassicalModel_psl (by omega : 0 < t) h
  rw [hcard]
  simp only [pow_one, show 2 - 1 = 1 from rfl, Nat.gcd_one_right, Nat.div_one]
  set m := t - 1 with hm_def
  have htm : t = m + 1 := by omega
  have hIcc : Finset.Icc 2 t = insert t (Finset.Icc 2 m) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hnotmem : t ∉ Finset.Icc 2 m := by
    simp only [Finset.mem_Icc]
    omega
  rw [hIcc, Finset.prod_insert hnotmem, ← mul_assoc, mul_comm (2 ^ (t * (t - 1) / 2)), mul_assoc]
  unfold bound
  refine Nat.mul_le_mul_left (2 ^ t - 1) ?_
  have hpow_eq : 2 ^ (t * (t - 1) / 2) = ∏ k ∈ Finset.range m, 2 ^ (k + 1) := by
    rw [htm, Nat.add_sub_cancel]
    exact two_pow_triangular_eq_prod_range m
  have hprod_eq : ∏ i ∈ Finset.Icc 2 m, (2 ^ i - 1) =
      ∏ k ∈ Finset.range m, (2 ^ (m - k) - 1) := by
    rw [prod_Icc_two_pow_sub_one_eq_prod_range m,
      ← Finset.prod_range_reflect (fun j => 2 ^ (j + 1) - 1) m]
    refine Finset.prod_congr rfl fun k hk => ?_
    have hk_lt : k < m := Finset.mem_range.mp hk
    congr 2
    omega
  rw [hpow_eq, hprod_eq, ← Finset.prod_mul_distrib]
  have hm_le_log : m ≤ Nat.log 2 (2 ^ t - 1) := by
    have h2t : 2 ^ t = 2 * 2 ^ m := by
      rw [htm, pow_succ']
    have h2m_pos : 1 ≤ 2 ^ m := Nat.one_le_pow m 2 (by omega)
    rw [Nat.le_log_iff_pow_le (by omega : 1 < 2) (by omega)]
    omega
  calc ∏ k ∈ Finset.range m, (2 ^ (k + 1) * (2 ^ (m - k) - 1))
    _ ≤ ∏ k ∈ Finset.range m, (2 ^ t - 1 - 2 ^ k) := by
        refine Finset.prod_le_prod fun k hk => ?_
        have hk_lt : k < m := Finset.mem_range.mp hk
        have hadd : (k + 1) + (m - k) = t := by omega
        have hmul : 2 ^ (k + 1) * (2 ^ (m - k) - 1) = 2 ^ t - 2 ^ (k + 1) := by
          rw [Nat.mul_sub_one, ← pow_add, hadd]
        have h2k : 2 ^ k + 1 ≤ 2 ^ (k + 1) := by
          have : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by omega)
          rw [pow_succ]
          omega
        omega
    _ ≤ ∏ i ∈ Finset.range (Nat.log 2 (2 ^ t - 1)), (2 ^ t - 1 - 2 ^ i) := by
        refine Finset.prod_le_prod_of_subset_of_one_le
          (Finset.range_mono hm_le_log) fun i hi _ => ?_
        have hi_lt : i < Nat.log 2 (2 ^ t - 1) := Finset.mem_range.mp hi
        have hpos : 2 ^ t - 1 ≠ 0 := by
          have : 8 ≤ 2 ^ t := le_trans (by decide : 8 ≤ 2 ^ 3) (Nat.pow_le_pow_right (by omega) ht)
          omega
        have hpow_lt : 2 ^ i < 2 ^ t - 1 :=
          lt_of_lt_of_le (Nat.pow_lt_pow_right (by omega) hi_lt)
            (Nat.pow_log_le_self 2 hpos)
        omega

/-- For `t ≥ 3` and `2^t ≤ n`, `pslAutUpper t 2 1 ≤ bound n`. -/
theorem pslAutUpper_le_bound_two_pow {t n : ℕ} (ht : 3 ≤ t) (hn : 2 ^ t ≤ n) :
    pslAutUpper t 2 1 ≤ bound n := by
  refine le_trans ?_ (bound_mono hn)
  have h1 : pslAutUpper t 2 1 ≤ 2 * 2 ^ (t ^ 2 - 1) := by
    have := pslAutUpper_le_pow (p := 2) (f := 1) (by omega : 2 ≤ t)
    have ht_ne : t ≠ 2 := by omega
    simpa [ht_ne] using this
  have hsub : 2 ^ t - 2 ^ (t - 1) = 2 ^ (t - 1) := by
    have hsplit : 2 ^ t = 2 ^ (t - 1) + 2 ^ (t - 1) := by
      calc 2 ^ t = 2 ^ ((t - 1) + 1) := by congr 1; omega
        _ = 2 ^ (t - 1) + 2 ^ (t - 1) := by rw [pow_succ]; ring
    rw [hsplit, Nat.add_sub_cancel]
  have h2 : 2 * 2 ^ (t ^ 2 - 1) = 2 ^ t * (2 ^ t - 2 ^ (t - 1)) ^ t := by
    rw [hsub, ← pow_mul, ← pow_add, ← pow_succ']
    congr 1
    zify [show 1 ≤ t by omega, show 1 ≤ t ^ 2 by nlinarith]
    ring
  refine le_trans h1 ?_
  rw [h2]
  exact simple_lower_le_bound (by omega) le_rfl

/-- Helper for `t ≥ 3, q ≥ 3`: if `2^(k-1) ≤ (q - 1) * q^(t - 2)` and `2^k ≤ q^(t - 1)`, then
`q^((t - 1) + (t - 2) * k) ≤ bound (q^(t - 1))`. -/
theorem pow_le_bound_of_pow_le {t q k : ℕ} (ht : 2 ≤ t) (hq : 1 ≤ q) (hk : 1 ≤ k)
    (hpow1 : 2 ^ (k - 1) ≤ (q - 1) * q ^ (t - 2)) (hpow2 : 2 ^ k ≤ q ^ (t - 1)) :
    q ^ ((t - 1) + (t - 2) * k) ≤ bound (q ^ (t - 1)) := by
  have htexp : t - 2 + 1 = t - 1 := by omega
  have hsplit : q ^ (t - 1) = q ^ (t - 2) + (q - 1) * q ^ (t - 2) := by
    calc q ^ (t - 1) = (1 + (q - 1)) * q ^ (t - 2) := by
          rw [Nat.add_sub_of_le hq, ← pow_succ', htexp]
      _ = q ^ (t - 2) + (q - 1) * q ^ (t - 2) := by
          rw [add_mul, one_mul]
  have hsub : q ^ (t - 2) ≤ q ^ (t - 1) - 2 ^ (k - 1) := by omega
  calc q ^ ((t - 1) + (t - 2) * k)
    _ = q ^ (t - 1) * (q ^ (t - 2)) ^ k := by rw [pow_add, pow_mul]
    _ ≤ q ^ (t - 1) * (q ^ (t - 1) - 2 ^ (k - 1)) ^ k :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsub k)
    _ ≤ bound (q ^ (t - 1)) := simple_lower_le_bound hk hpow2

private theorem two_pow_le_two_mul_three_pow {t : ℕ} (ht : 7 ≤ t) :
    2 ^ (t + 1) ≤ 2 * 3 ^ (t - 2) ∧ 2 ^ (t + 2) ≤ 3 ^ (t - 1) := by
  induction t, ht using Nat.le_induction with
  | base => decide
  | succ t ht ih =>
    have h1 : 2 ^ (t + 2) ≤ 2 * 3 ^ (t - 1) := by
      calc 2 ^ (t + 2) = 2 * 2 ^ (t + 1) := by rw [pow_succ']
        _ ≤ 2 * (2 * 3 ^ (t - 2)) := Nat.mul_le_mul_left 2 ih.1
        _ ≤ 3 * (2 * 3 ^ (t - 2)) := Nat.mul_le_mul_right _ (by omega)
        _ = 2 * (3 * 3 ^ (t - 2)) := by ring
        _ = 2 * 3 ^ (t - 1) := by
            rw [← pow_succ', show t - 2 + 1 = t - 1 by omega]
    have h2 : 2 ^ (t + 3) ≤ 3 ^ t := by
      calc 2 ^ (t + 3) = 2 * 2 ^ (t + 2) := by rw [pow_succ']
        _ ≤ 3 * 3 ^ (t - 1) := Nat.mul_le_mul (by omega) ih.2
        _ = 3 ^ t := by
            rw [← pow_succ', show t - 1 + 1 = t by omega]
    simpa [Nat.add_sub_cancel] using And.intro h1 h2

/-- For `t ≥ 3` and `q ≥ 3` with `(t, q) ∉ {(3, 3), (4, 3)}`, `q^(t^2) ≤ bound (q^(t - 1))`. -/
theorem pow_sq_le_bound_pow_pred {t q : ℕ} (ht : 3 ≤ t) (hq : 3 ≤ q)
    (h33 : ¬ (t = 3 ∧ q = 3)) (h43 : ¬ (t = 4 ∧ q = 3)) :
    q ^ (t ^ 2) ≤ bound (q ^ (t - 1)) := by
  rcases Nat.lt_or_ge t 7 with ht7 | ht7
  · interval_cases t
    · rcases Nat.lt_or_ge q 12 with hq12 | hq12
      · interval_cases q <;> first | exact False.elim (h33 ⟨rfl, rfl⟩) | decide
      · have h1 : 2 ^ 6 ≤ (q - 1) * q ^ 1 := by
          rw [pow_one]
          exact le_trans (by decide : 2 ^ 6 ≤ 11 * 12) (Nat.mul_le_mul (by omega) hq12)
        have h2 : 2 ^ 7 ≤ q ^ 2 :=
          le_trans (by decide : 2 ^ 7 ≤ 12 ^ 2) (Nat.pow_le_pow_left hq12 2)
        simpa using pow_le_bound_of_pow_le (t := 3) (q := q) (k := 7)
          (by omega) (by omega) (by omega) h1 h2
    · rcases Nat.lt_or_ge q 6 with hq6 | hq6
      · interval_cases q <;> first | exact False.elim (h43 ⟨rfl, rfl⟩) | decide
      · have hq2 : 36 ≤ q ^ 2 := Nat.pow_le_pow_left hq6 2
        have h1 : 2 ^ 6 ≤ (q - 1) * q ^ 2 :=
          le_trans (by decide : 2 ^ 6 ≤ 5 * 36) (Nat.mul_le_mul (by omega) hq2)
        have h2 : 2 ^ 7 ≤ q ^ 3 :=
          le_trans (by decide : 2 ^ 7 ≤ 6 ^ 3) (Nat.pow_le_pow_left hq6 3)
        refine le_trans (Nat.pow_le_pow_right (by omega) (show 4 ^ 2 ≤ 3 + 2 * 7 by decide)) ?_
        simpa using pow_le_bound_of_pow_le (t := 4) (q := q) (k := 7)
          (by omega) (by omega) (by omega) h1 h2
    · rcases eq_or_lt_of_le hq with rfl | hq4
      · decide
      · have hq3_pow : 64 ≤ q ^ 3 := Nat.pow_le_pow_left hq4 3
        have h1 : 2 ^ 6 ≤ (q - 1) * q ^ 3 :=
          le_trans (by decide : 2 ^ 6 ≤ 3 * 64) (Nat.mul_le_mul (by omega) hq3_pow)
        have h2 : 2 ^ 7 ≤ q ^ 4 :=
          le_trans (by decide : 2 ^ 7 ≤ 4 ^ 4) (Nat.pow_le_pow_left hq4 4)
        simpa using pow_le_bound_of_pow_le (t := 5) (q := q) (k := 7)
          (by omega) (by omega) (by omega) h1 h2
    · rcases eq_or_lt_of_le hq with rfl | hq4
      · decide
      · have hq4_pow : 256 ≤ q ^ 4 := Nat.pow_le_pow_left hq4 4
        have h1 : 2 ^ 7 ≤ (q - 1) * q ^ 4 :=
          le_trans (by decide : 2 ^ 7 ≤ 3 * 256) (Nat.mul_le_mul (by omega) hq4_pow)
        have h2 : 2 ^ 8 ≤ q ^ 5 :=
          le_trans (by decide : 2 ^ 8 ≤ 4 ^ 5) (Nat.pow_le_pow_left hq4 5)
        refine le_trans (Nat.pow_le_pow_right (by omega) (show 6 ^ 2 ≤ 5 + 4 * 8 by decide)) ?_
        simpa using pow_le_bound_of_pow_le (t := 6) (q := q) (k := 8)
          (by omega) (by omega) (by omega) h1 h2
  · obtain ⟨hb1, hb2⟩ := two_pow_le_two_mul_three_pow ht7
    have h1 : 2 ^ (t + 1) ≤ (q - 1) * q ^ (t - 2) := by
      calc 2 ^ (t + 1) ≤ 2 * 3 ^ (t - 2) := hb1
        _ ≤ (q - 1) * q ^ (t - 2) :=
            Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left hq (t - 2))
    have h2 : 2 ^ (t + 2) ≤ q ^ (t - 1) :=
      le_trans hb2 (Nat.pow_le_pow_left hq (t - 1))
    have hexp : t ^ 2 ≤ (t - 1) + (t - 2) * (t + 2) := by
      have : (t - 2) * (t + 2) = t ^ 2 - 4 := by
        zify [show 2 ≤ t by omega, show 4 ≤ t ^ 2 by nlinarith]
        ring
      omega
    exact le_trans (Nat.pow_le_pow_right (by omega) hexp)
      (pow_le_bound_of_pow_le (k := t + 2) (by omega) (by omega) (by omega) h1 h2)

/-- Main numeric bound for `t ≥ 3` and `q = p^f ≥ 3`. -/
theorem pslAutUpper_le_bound_of_three_le {t p f n : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (ht : 3 ≤ t) (hq3 : 3 ≤ p ^ f) (h33 : ¬ (t = 3 ∧ p ^ f = 3)) (h43 : ¬ (t = 4 ∧ p ^ f = 3))
    (hn : (p ^ f) ^ (t - 1) ≤ n) :
    pslAutUpper t p f ≤ bound n := by
  refine le_trans ?_ (bound_mono hn)
  refine le_trans ?_ (pow_sq_le_bound_pow_pred ht hq3 h33 h43)
  have ht_ne : t ≠ 2 := by omega
  have h1 := pslAutUpper_le_pow (t := t) (p := p) (f := f) (by omega)
  simp only [ht_ne, ↓reduceIte] at h1
  refine le_trans h1 ?_
  have htsq : t ^ 2 - 1 + 1 = t ^ 2 := by
    have : 1 ≤ t ^ 2 := by nlinarith
    omega
  calc 2 * f * (p ^ f) ^ (t ^ 2 - 1)
    _ ≤ (p ^ f) * (p ^ f) ^ (t ^ 2 - 1) :=
        Nat.mul_le_mul_right _ (two_mul_le_pow_of_two_le hp.two_le hf)
    _ = (p ^ f) ^ (t ^ 2) := by
        rw [← pow_succ', htsq]

theorem pslAutUpper_three_three_le_bound {n : ℕ} (hn : 13 ≤ n) :
    pslAutUpper 3 3 1 ≤ bound n :=
  le_trans (by decide : pslAutUpper 3 3 1 ≤ bound 13) (bound_mono hn)

theorem pslAutUpper_four_three_le_bound {n : ℕ} (hn : 32 ≤ n) :
    pslAutUpper 4 3 1 ≤ bound n :=
  le_trans (by decide : pslAutUpper 4 3 1 ≤ bound 32) (bound_mono hn)

/-- For `t = 2, f = 1` and `11 ≤ p ≤ n`, `pslAutUpper 2 p 1 ≤ bound n`. -/
theorem pslAutUpper_two_one_le_bound {p n : ℕ} (hp : 11 ≤ p) (hn : p ≤ n) :
    pslAutUpper 2 p 1 ≤ bound n := by
  refine le_trans ?_ (bound_mono hn)
  have h1 : pslAutUpper 2 p 1 ≤ p ^ 3 := by
    have := pslAutUpper_le_pow (t := 2) (p := p) (f := 1) le_rfl
    simpa using this
  refine le_trans h1 ?_
  have hp1 : p ≤ 2 * (p - 4) := by omega
  have hp2 : 4 ≤ p - 4 := by omega
  have hp_sq : p ^ 2 ≤ (p - 4) ^ 3 := calc
    p ^ 2 ≤ (2 * (p - 4)) ^ 2 := Nat.pow_le_pow_left hp1 2
    _ = 4 * (p - 4) ^ 2 := by ring
    _ ≤ (p - 4) * (p - 4) ^ 2 := Nat.mul_le_mul_right _ hp2
    _ = (p - 4) ^ 3 := by ring
  calc p ^ 3 = p * p ^ 2 := by ring
    _ ≤ p * (p - 4) ^ 3 := Nat.mul_le_mul_left p hp_sq
    _ ≤ bound p := simple_lower_le_bound (k := 3) (by omega) (by omega)

private theorem le_two_pow_sub_two {f : ℕ} (hf : 4 ≤ f) : f ≤ 2 ^ (f - 2) := by
  induction f, hf using Nat.le_induction with
  | base => decide
  | succ f hf ih =>
    have : 1 ≤ 2 ^ (f - 2) := Nat.one_le_pow _ 2 (by omega)
    have hsub : f + 1 - 2 = (f - 2) + 1 := by omega
    rw [hsub, pow_succ]
    omega

/-- For `t = 2, p = 2, f ≥ 4` and `2^f ≤ n`, `pslAutUpper 2 2 f ≤ bound n`. -/
theorem pslAutUpper_two_two_le_bound {f n : ℕ} (hf : 4 ≤ f) (hn : 2 ^ f ≤ n) :
    pslAutUpper 2 2 f ≤ bound n := by
  refine le_trans ?_ (bound_mono hn)
  have h1 : pslAutUpper 2 2 f ≤ f * (2 ^ f) ^ 3 := by
    have := pslAutUpper_le_pow (t := 2) (p := 2) (f := f) le_rfl
    simpa using this
  refine le_trans h1 ?_
  have hf_pow : f ≤ 2 ^ (f - 2) := le_two_pow_sub_two hf
  have hexp : (f - 2) + f * 3 ≤ f ^ 2 := by
    zify [show 2 ≤ f by omega]
    nlinarith
  have hsub : 2 ^ f - 2 ^ (f - 1) = 2 ^ (f - 1) := by
    have hsplit : 2 ^ f = 2 ^ (f - 1) + 2 ^ (f - 1) := by
      calc 2 ^ f = 2 ^ ((f - 1) + 1) := by congr 1; omega
        _ = 2 ^ (f - 1) + 2 ^ (f - 1) := by rw [pow_succ]; ring
    rw [hsplit, Nat.add_sub_cancel]
  have h2 : 2 ^ (f ^ 2) = 2 ^ f * (2 ^ f - 2 ^ (f - 1)) ^ f := by
    rw [hsub, ← pow_mul, ← pow_add]
    congr 1
    zify [show 1 ≤ f by omega]
    ring
  calc f * (2 ^ f) ^ 3
    _ ≤ 2 ^ (f - 2) * 2 ^ (f * 3) := by
        rw [← pow_mul]
        exact Nat.mul_le_mul_right _ hf_pow
    _ = 2 ^ ((f - 2) + f * 3) := by rw [← pow_add]
    _ ≤ 2 ^ (f ^ 2) := Nat.pow_le_pow_right (by omega) hexp
    _ = 2 ^ f * (2 ^ f - 2 ^ (f - 1)) ^ f := h2
    _ ≤ bound (2 ^ f) := simple_lower_le_bound (by omega) le_rfl

/-- For `t = 2, p ≥ 3, 2 ≤ f ≤ 3` and `49 ≤ p^f` with `(p^f + 1) / 2 ≤ n`,
`pslAutUpper 2 p f ≤ bound n`. -/
theorem pslAutUpper_two_odd_small_f_le_bound {p f n : ℕ} (_hf2 : 2 ≤ f) (hf3 : f ≤ 3)
    (hq : 49 ≤ p ^ f) (hn : (p ^ f + 1) / 2 ≤ n) :
    pslAutUpper 2 p f ≤ bound n := by
  refine le_trans ?_ (bound_mono hn)
  set q := p ^ f
  set m := (q + 1) / 2
  have hm25 : 25 ≤ m := by omega
  have h1 : pslAutUpper 2 p f ≤ 3 * q ^ 3 := by
    have hpow := pslAutUpper_le_pow (t := 2) (p := p) (f := f) le_rfl
    simp only [↓reduceIte, one_mul, show 2 ^ 2 - 1 = 3 from rfl] at hpow
    exact le_trans hpow (Nat.mul_le_mul_right _ hf3)
  refine le_trans h1 ?_
  have hq_le : q ≤ 3 * (m - 8) := by omega
  have hq2 : q ^ 2 ≤ 9 * (m - 8) ^ 2 := calc
    q ^ 2 ≤ (3 * (m - 8)) ^ 2 := Nat.pow_le_pow_left hq_le 2
    _ = 9 * (m - 8) ^ 2 := by ring
  have hm8_sq : 54 ≤ (m - 8) ^ 2 := by
    have : 17 ≤ m - 8 := by omega
    calc 54 ≤ 17 ^ 2 := by decide
      _ ≤ (m - 8) ^ 2 := Nat.pow_le_pow_left this 2
  have h6q2 : 6 * q ^ 2 ≤ (m - 8) ^ 4 := calc
    6 * q ^ 2 ≤ 6 * (9 * (m - 8) ^ 2) := Nat.mul_le_mul_left 6 hq2
    _ = 54 * (m - 8) ^ 2 := by ring
    _ ≤ (m - 8) ^ 2 * (m - 8) ^ 2 := Nat.mul_le_mul_right _ hm8_sq
    _ = (m - 8) ^ 4 := by ring
  have h3q : 3 * q ≤ 6 * m := by omega
  calc 3 * q ^ 3 = (3 * q) * q ^ 2 := by ring
    _ ≤ (6 * m) * q ^ 2 := Nat.mul_le_mul_right _ h3q
    _ = m * (6 * q ^ 2) := by ring
    _ ≤ m * (m - 8) ^ 4 := Nat.mul_le_mul_left m h6q2
    _ ≤ bound m := simple_lower_le_bound (k := 4) (by omega) (by omega)

private theorem two_pow_pred_le_three_pow_sub_two {f : ℕ} (hf : 4 ≤ f) :
    2 ^ (f - 1) ≤ 3 ^ (f - 2) := by
  induction f, hf using Nat.le_induction with
  | base => decide
  | succ f hf ih =>
    have h1 : f + 1 - 1 = (f - 1) + 1 := by omega
    have h2 : f + 1 - 2 = (f - 2) + 1 := by omega
    rw [h1, h2, pow_succ, pow_succ]
    exact Nat.mul_le_mul ih (by omega)

/-- For `t = 2, p ≥ 3, f ≥ 4` and `(p^f + 1) / 2 ≤ n`, `pslAutUpper 2 p f ≤ bound n`. -/
theorem pslAutUpper_two_odd_four_le_f_le_bound {p f n : ℕ} (hp3 : 3 ≤ p) (hf4 : 4 ≤ f)
    (hn : (p ^ f + 1) / 2 ≤ n) :
    pslAutUpper 2 p f ≤ bound n := by
  refine le_trans ?_ (bound_mono hn)
  set q := p ^ f with hq_def
  set m := (q + 1) / 2
  have hpow := pslAutUpper_le_pow (t := 2) (p := p) (f := f) le_rfl
  simp only [↓reduceIte, one_mul, show 2 ^ 2 - 1 = 3 from rfl] at hpow
  refine le_trans hpow ?_
  have h2p : 2 ^ (f - 1) ≤ p ^ (f - 2) :=
    le_trans (two_pow_pred_le_three_pow_sub_two hf4) (Nat.pow_le_pow_left hp3 (f - 2))
  have hsum_le_m : p ^ (f - 1) + p ^ (f - 2) ≤ m := by
    have hq_split : p * p ^ (f - 2) = p ^ (f - 1) := by
      rw [← pow_succ', show f - 2 + 1 = f - 1 by omega]
    have hq_split2 : p * p ^ (f - 1) = q := by
      rw [hq_def, ← pow_succ', show f - 1 + 1 = f by omega]
    have h1 : 2 * p ^ (f - 2) ≤ p ^ (f - 1) := by
      rw [← hq_split]
      exact Nat.mul_le_mul_right _ (by omega)
    have h2 : 3 * p ^ (f - 1) ≤ q := by
      rw [← hq_split2]
      exact Nat.mul_le_mul_right _ hp3
    omega
  have h2f_le_m : 2 ^ f ≤ m := by
    have hsplit : 2 ^ f = 2 ^ (f - 1) + 2 ^ (f - 1) := by
      calc 2 ^ f = 2 ^ ((f - 1) + 1) := by congr 1; omega
        _ = 2 ^ (f - 1) + 2 ^ (f - 1) := by rw [pow_succ]; ring
    have : p ^ (f - 2) ≤ p ^ (f - 1) := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have hsub : p ^ (f - 1) ≤ m - 2 ^ (f - 1) := by omega
  have hf_pow : f ≤ p ^ (f - 1) := by
    have hle2 : f ≤ 2 ^ (f - 1) :=
      le_trans (le_two_pow_sub_two hf4) (Nat.pow_le_pow_right (by omega) (by omega))
    exact le_trans hle2 (le_trans h2p (Nat.pow_le_pow_right (by omega) (by omega)))
  have hexp : (f - 1) + f * 3 ≤ (f - 1) + (f - 1) * f := by
    zify [show 1 ≤ f by omega]
    nlinarith
  calc f * q ^ 3
    _ ≤ p ^ (f - 1) * p ^ (f * 3) := by
        rw [hq_def, ← pow_mul]
        exact Nat.mul_le_mul_right _ hf_pow
    _ = p ^ ((f - 1) + f * 3) := by rw [← pow_add]
    _ ≤ p ^ ((f - 1) + (f - 1) * f) := Nat.pow_le_pow_right (by omega) hexp
    _ = p ^ (f - 1) * (p ^ (f - 1)) ^ f := by rw [pow_add, pow_mul]
    _ ≤ m * (m - 2 ^ (f - 1)) ^ f :=
        Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left hsub f)
    _ ≤ bound m := simple_lower_le_bound (by omega) h2f_le_m

theorem pslAutUpper_two_five_one_le_bound {n : ℕ} (hn : 6 ≤ n) :
    pslAutUpper 2 5 1 ≤ bound n :=
  le_trans (by decide : pslAutUpper 2 5 1 ≤ bound 6) (bound_mono hn)

theorem pslAutUpper_two_two_two_le_bound {n : ℕ} (hn : 6 ≤ n) :
    pslAutUpper 2 2 2 ≤ bound n :=
  le_trans (by decide : pslAutUpper 2 2 2 ≤ bound 6) (bound_mono hn)

theorem pslAutUpper_two_two_three_le_bound {n : ℕ} (hn : 9 ≤ n) :
    pslAutUpper 2 2 3 ≤ bound n :=
  le_trans (by decide : pslAutUpper 2 2 3 ≤ bound 9) (bound_mono hn)

theorem pslAutUpper_two_three_two_le_bound {n : ℕ} (hn : 9 ≤ n) :
    pslAutUpper 2 3 2 ≤ bound n :=
  le_trans (by decide : pslAutUpper 2 3 2 ≤ bound 9) (bound_mono hn)

theorem pslAutUpper_two_five_two_le_bound {n : ℕ} (hn : 16 ≤ n) :
    pslAutUpper 2 5 2 ≤ bound n :=
  le_trans (by decide : pslAutUpper 2 5 2 ≤ bound 16) (bound_mono hn)

theorem pslAutUpper_two_three_three_le_bound {n : ℕ} (hn : 16 ≤ n) :
    pslAutUpper 2 3 3 ≤ bound n :=
  le_trans (by decide : pslAutUpper 2 3 3 ≤ bound 16) (bound_mono hn)

end Maroti
