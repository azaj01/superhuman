import Mathlib
open Real
noncomputable abbrev putnam_2025_b6_solution : ℝ := 1 / 4

noncomputable def exponent_seq (r : ℝ) : ℕ → ℝ
| 0 => (1 : ℝ)
| n + 1 => r * (exponent_seq r n)^2 + (1 : ℝ)

theorem putnam_solution_eq : putnam_2025_b6_solution = ((1 : ℝ) / (4 : ℝ)) :=
by
  rfl

theorem putnam_2025_b6_witness_pos (n : ℕ) (hn : 0 < n) : 0 < n^2 :=
by
  positivity

theorem putnam_2025_b6_witness_works (n : ℕ) (hn : 0 < n) :
    (((n^2)^2 : ℕ) : ℝ)^((1 : ℝ) / (4 : ℝ)) ≤ (((n + 1)^2 : ℕ) : ℝ) - ((n^2 : ℕ) : ℝ) :=
by
  have h_LHS : (((n^2)^2 : ℕ) : ℝ)^((1 : ℝ) / (4 : ℝ)) = (n : ℝ) := by
    have h1 : (((n^2)^2 : ℕ) : ℝ) = (n : ℝ)^4 := by
      push_cast
      ring
    rw [h1]
    have h_nonneg : 0 ≤ (n : ℝ) := by positivity
    have h2 := Real.rpow_natCast_mul h_nonneg (4 : ℕ) ((1 : ℝ) / (4 : ℝ))
    rw [← h2]
    have h_exp : ((4 : ℕ) : ℝ) * ((1 : ℝ) / (4 : ℝ)) = (1 : ℝ) := by
      push_cast
      norm_num
    rw [h_exp, Real.rpow_one]

  have h_RHS : (((n + 1)^2 : ℕ) : ℝ) - ((n^2 : ℕ) : ℝ) = (2 : ℝ) * (n : ℝ) + (1 : ℝ) := by
    push_cast
    ring

  rw [h_LHS, h_RHS]
  have : 0 ≤ (n : ℝ) := by positivity
  linarith

theorem g_strictly_increasing (g : ℕ → ℕ) (r : ℝ)
    (h1 : ∀ n : ℕ, 0 < n → 0 < g n)
    (h2 : ∀ n : ℕ, 0 < n → (g (g n) : ℝ)^r ≤ (g (n + 1) : ℝ) - (g n : ℝ)) :
    ∀ n : ℕ, 0 < n → g n < g (n + 1) :=
by
  intro n hn
  have h_gn_pos : 0 < g n := h1 n hn
  have h_ggn_pos : 0 < g (g n) := h1 (g n) h_gn_pos
  have h_ggn_real_pos : (0 : ℝ) < (g (g n) : ℝ) := by exact_mod_cast h_ggn_pos
  have h_pow_pos : (0 : ℝ) < (g (g n) : ℝ)^r := by positivity
  have h_le := h2 n hn
  have h_lt : (g n : ℝ) < (g (n + 1) : ℝ) := by linarith
  exact_mod_cast h_lt

theorem g_tendsto_inf (g : ℕ → ℕ) (h_inc : ∀ n : ℕ, 0 < n → g n < g (n + 1)) (K : ℕ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → K ≤ g n :=
by
  use K + 1
  intro n hn
  have h_bound : ∀ k : ℕ, k ≤ g (k + 1) := by
    intro k
    induction k with
    | zero => exact Nat.zero_le _
    | succ k ih =>
      have hz : 0 < k + 1 := by omega
      have h_step := h_inc (k + 1) hz
      omega
  have h2 : n - 1 + 1 = n := by omega
  have h3 := h_bound (n - 1)
  rw [h2] at h3
  omega

theorem my_g_strictly_increasing (g : ℕ → ℕ) (r : ℝ) (h1 : ∀ n : ℕ, 0 < n → 0 < g n)
  (h2 : ∀ n : ℕ, 0 < n → (g (g n) : ℝ)^r ≤ (g (n + 1) : ℝ) - (g n : ℝ)) :
  ∀ n : ℕ, 0 < n → g n < g (n + 1) :=
by
  intro n hn
  have hgn : 0 < g n := h1 n hn
  have hggn : 0 < g (g n) := h1 (g n) hgn
  have hggn_real : (0 : ℝ) < (g (g n) : ℝ) := by exact_mod_cast hggn
  have hpow : (0 : ℝ) < (g (g n) : ℝ)^r := by positivity
  have h2n : (g (g n) : ℝ)^r ≤ (g (n + 1) : ℝ) - (g n : ℝ) := h2 n hn
  have h3 : (g n : ℝ) < (g (n + 1) : ℝ) := by linarith
  exact_mod_cast h3

theorem my_g_tendsto_inf (g : ℕ → ℕ) (h_inc : ∀ n : ℕ, 0 < n → g n < g (n + 1)) (N : ℕ) :
  ∃ M : ℕ, ∀ n : ℕ, M ≤ n → N ≤ g n :=
by
  have h_bound : ∀ k : ℕ, k ≤ g (k + 1) := by
    intro k
    induction k with
    | zero => omega
    | succ k ih =>
      have h_step := h_inc (k + 1) (by omega)
      omega
  use N + 1
  intro n hn
  cases n with
  | zero => omega
  | succ m =>
    have hb := h_bound m
    omega

theorem my_g_ge_n (g : ℕ → ℕ) (h1 : ∀ n : ℕ, 0 < n → 0 < g n) (h_inc : ∀ n : ℕ, 0 < n → g n < g (n + 1)) (n : ℕ) (hn : 0 < n) :
  n ≤ g n :=
by
  revert hn
  induction n with
  | zero =>
    intro hn
    omega
  | succ k ih =>
    intro _
    cases k with
    | zero =>
      change 1 ≤ g 1
      have h_base : 0 < g 1 := h1 1 (by omega)
      omega
    | succ k' =>
      have hk0 : 0 < k' + 1 := by omega
      have h_k : k' + 1 ≤ g (k' + 1) := ih hk0
      have h_step : g (k' + 1) < g (k' + 2) := h_inc (k' + 1) hk0
      change k' + 2 ≤ g (k' + 2)
      omega

theorem my_exponent_seq_zero (r : ℝ) : exponent_seq r 0 = (1 : ℝ) :=
by
  rfl

theorem my_exponent_seq_succ (r : ℝ) (k : ℕ) : exponent_seq r (k + 1) = r * (exponent_seq r k)^2 + (1 : ℝ) :=
by
  rfl

theorem my_base_case_arith (n : ℝ) : (1 : ℝ) * n ^ (1 : ℝ) = n :=
by
  rw [Real.rpow_one, one_mul]

theorem my_N1_properties (N M : ℕ) :
  ∃ N1 : ℕ, N ≤ N1 ∧ (∀ n : ℕ, N1 ≤ n → M ≤ n) ∧ 0 < N1 :=
by
  use N + M + 1
  constructor
  · omega
  · constructor
    · intro n hn
      omega
    · omega

theorem my_pos_mul_sq (r : ℝ) (hr : (0 : ℝ) < r) (x : ℝ) : (0 : ℝ) ≤ r * x^2 :=
by
  positivity

theorem my_pos_rpow (c : ℝ) (hc : (0 : ℝ) < c) (p : ℝ) : (0 : ℝ) < c ^ p :=
Real.rpow_pos_of_pos hc p

theorem my_g_diff_to_g_bound (g : ℕ → ℕ) (p : ℝ) (hp : (0 : ℝ) ≤ p) (c' : ℝ) (hc' : (0 : ℝ) < c') (N1 : ℕ)
  (h_diff : ∀ n : ℕ, N1 ≤ n → c' * (n : ℝ)^p ≤ (g (n + 1) : ℝ) - (g n : ℝ)) :
  ∃ c'' : ℝ, (0 : ℝ) < c'' ∧ ∃ N2 : ℕ, ∀ n : ℕ, N2 ≤ n →
    c'' * (n : ℝ)^(p + (1 : ℝ)) ≤ (g n : ℝ) :=
by
  use c' * ((1 : ℝ) / (2 : ℝ)) * ((1 : ℝ) / (4 : ℝ))^p
  constructor
  · positivity
  · use 2 * N1 + 2
    intro n hn
    have hn_pos : 0 < (n : ℝ) := by
      have : 0 < n := by omega
      exact_mod_cast this
    let m := n / 2
    have hm1 : N1 ≤ m := by omega
    have hm2 : m ≤ n := by omega

    have h_nm : (n : ℝ) / (2 : ℝ) ≤ ((n - m : ℕ) : ℝ) := by
      have : n ≤ 2 * (n - m) := by omega
      have h_cast : (n : ℝ) ≤ (2 : ℝ) * ((n - m : ℕ) : ℝ) := by exact_mod_cast this
      linarith

    have hm3 : (n : ℝ) / (4 : ℝ) ≤ (m : ℝ) := by
      have : n ≤ 4 * m := by omega
      have h_cast : (n : ℝ) ≤ (4 : ℝ) * (m : ℝ) := by exact_mod_cast this
      linarith

    have h_tele : ∀ d : ℕ, ∑ i ∈ Finset.Ico m (m + d), ((g (i + 1) : ℝ) - (g i : ℝ)) = (g (m + d) : ℝ) - (g m : ℝ) := by
      intro d
      induction d with
      | zero => simp
      | succ d ih =>
        have heq : m + Nat.succ d = (m + d) + 1 := by omega
        rw [heq]
        rw [Finset.sum_Ico_succ_top (by omega)]
        rw [ih]
        ring

    have h_tele_n : ∑ i ∈ Finset.Ico m n, ((g (i + 1) : ℝ) - (g i : ℝ)) = (g n : ℝ) - (g m : ℝ) := by
      have hd : n = m + (n - m) := by omega
      have H := h_tele (n - m)
      rw [← hd] at H
      exact H

    have h_sum_lower : ∑ i ∈ Finset.Ico m n, c' * ((n : ℝ) / (4 : ℝ))^p ≤ ∑ i ∈ Finset.Ico m n, ((g (i + 1) : ℝ) - (g i : ℝ)) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [Finset.mem_Ico] at hi
      have hi1 : N1 ≤ i := by omega
      have hi2 : (n : ℝ) / (4 : ℝ) ≤ (i : ℝ) := by
        have h_mi : m ≤ i := hi.1
        have h_mi_real : (m : ℝ) ≤ (i : ℝ) := by exact_mod_cast h_mi
        linarith
      have h_diff_i := h_diff i hi1
      have hn_div_pos : 0 ≤ (n : ℝ) / (4 : ℝ) := by positivity
      have h_pow_le : ((n : ℝ) / (4 : ℝ))^p ≤ (i : ℝ)^p := by
        apply Real.rpow_le_rpow hn_div_pos hi2 hp
      have hc_le : 0 ≤ c' := by linarith
      have h_mul_le : c' * ((n : ℝ) / (4 : ℝ))^p ≤ c' * (i : ℝ)^p := mul_le_mul_of_nonneg_left h_pow_le hc_le
      linarith

    have h_sum_const : ∑ i ∈ Finset.Ico m n, c' * ((n : ℝ) / (4 : ℝ))^p = ((n - m : ℕ) : ℝ) * (c' * ((n : ℝ) / (4 : ℝ))^p) := by
      rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]

    have h_sum_lower2 : ((n : ℝ) / (2 : ℝ)) * (c' * ((n : ℝ) / (4 : ℝ))^p) ≤ ∑ i ∈ Finset.Ico m n, ((g (i + 1) : ℝ) - (g i : ℝ)) := by
      calc
        ((n : ℝ) / (2 : ℝ)) * (c' * ((n : ℝ) / (4 : ℝ))^p) ≤ ((n - m : ℕ) : ℝ) * (c' * ((n : ℝ) / (4 : ℝ))^p) := by
          apply mul_le_mul_of_nonneg_right h_nm
          positivity
        _ = ∑ i ∈ Finset.Ico m n, c' * ((n : ℝ) / (4 : ℝ))^p := h_sum_const.symm
        _ ≤ ∑ i ∈ Finset.Ico m n, ((g (i + 1) : ℝ) - (g i : ℝ)) := h_sum_lower

    have h_g_diff : ((n : ℝ) / (2 : ℝ)) * (c' * ((n : ℝ) / (4 : ℝ))^p) ≤ (g n : ℝ) - (g m : ℝ) := by
      rw [← h_tele_n]
      exact h_sum_lower2

    have h_c_eq : ((n : ℝ) / (2 : ℝ)) * (c' * ((n : ℝ) / (4 : ℝ))^p) = (c' * ((1 : ℝ) / (2 : ℝ)) * ((1 : ℝ) / (4 : ℝ))^p) * (n : ℝ)^(p + (1 : ℝ)) := by
      have h_n4 : (n : ℝ) / (4 : ℝ) = (n : ℝ) * ((1 : ℝ) / (4 : ℝ)) := by ring
      rw [h_n4]
      have h_pow_mul : ((n : ℝ) * ((1 : ℝ) / (4 : ℝ)))^p = (n : ℝ)^p * ((1 : ℝ) / (4 : ℝ))^p := Real.mul_rpow (by positivity) (by positivity)
      rw [h_pow_mul]
      have h_pow_add : (n : ℝ)^(p + (1 : ℝ)) = (n : ℝ)^p * (n : ℝ) := by
        rw [Real.rpow_add hn_pos, Real.rpow_one]
      rw [h_pow_add]
      ring

    rw [h_c_eq] at h_g_diff
    have h_gm_nonneg : 0 ≤ (g m : ℝ) := by positivity
    linarith

theorem my_g_bound_to_diff_bound (g : ℕ → ℕ) (r : ℝ) (hr : (0 : ℝ) < r) (k : ℕ) (c : ℝ) (hc : (0 : ℝ) < c) (N : ℕ)
  (H : ∀ n : ℕ, N ≤ n → c * (n : ℝ)^(exponent_seq r k) ≤ (g n : ℝ))
  (h2 : ∀ n : ℕ, 0 < n → (g (g n) : ℝ)^r ≤ (g (n + 1) : ℝ) - (g n : ℝ))
  (N1 : ℕ) (hN1_1 : N ≤ N1) (hN1_2 : ∀ n : ℕ, N1 ≤ n → N ≤ g n) (hN1_3 : 0 < N1) :
  ∀ n : ℕ, N1 ≤ n → c^(r * ((1 : ℝ) + exponent_seq r k)) * (n : ℝ)^(r * (exponent_seq r k)^2) ≤ (g (n + 1) : ℝ) - (g n : ℝ) :=
by
  intro n hn
  have hn_pos_nat : 0 < n := lt_of_lt_of_le hN1_3 hn
  have hn_N : N ≤ n := le_trans hN1_1 hn
  have h_gn_N : N ≤ g n := hN1_2 n hn

  have h_E_pos : ∀ m, (0 : ℝ) < exponent_seq r m := by
    intro m
    induction m with
    | zero => exact zero_lt_one
    | succ m ih =>
      have hr_nn : (0 : ℝ) ≤ r := le_of_lt hr
      have hsq : (0 : ℝ) ≤ exponent_seq r m ^ 2 := sq_nonneg _
      have hmul : (0 : ℝ) ≤ r * exponent_seq r m ^ 2 := mul_nonneg hr_nn hsq
      have h_le : (1 : ℝ) ≤ r * exponent_seq r m ^ 2 + (1 : ℝ) := by linarith
      have h_eq : r * exponent_seq r m ^ 2 + (1 : ℝ) = exponent_seq r (Nat.succ m) := rfl
      calc (0 : ℝ) < (1 : ℝ) := zero_lt_one
        _ ≤ r * exponent_seq r m ^ 2 + (1 : ℝ) := h_le
        _ = exponent_seq r (Nat.succ m) := h_eq

  have hEk_pos : (0 : ℝ) < exponent_seq r k := h_E_pos k
  have hEk_nn : (0 : ℝ) ≤ exponent_seq r k := le_of_lt hEk_pos
  have hr_nn : (0 : ℝ) ≤ r := le_of_lt hr

  have h_n_pos_R : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h_gn_pos_R : (0 : ℝ) ≤ g n := Nat.cast_nonneg (g n)
  have h_c_pos_R : (0 : ℝ) ≤ c := le_of_lt hc

  have h1 : c * (g n : ℝ) ^ exponent_seq r k ≤ (g (g n) : ℝ) := H (g n) h_gn_N
  have h3 : c * (n : ℝ) ^ exponent_seq r k ≤ (g n : ℝ) := H n hn_N
  have h2_ineq : (g (g n) : ℝ) ^ r ≤ (g (n + 1) : ℝ) - (g n : ℝ) := h2 n hn_pos_nat

  have h_nE_pos : (0 : ℝ) ≤ (n : ℝ) ^ exponent_seq r k := by
    first | exact Real.rpow_nonneg h_n_pos_R _ | exact Real.rpow_nonneg h_n_pos_R | positivity
  have h_cnE_pos : (0 : ℝ) ≤ c * (n : ℝ) ^ exponent_seq r k := by
    first | exact mul_nonneg h_c_pos_R h_nE_pos | positivity
  have h_rE_pos : (0 : ℝ) ≤ r * exponent_seq r k := by
    first | exact mul_nonneg hr_nn hEk_nn | positivity
  have h_gnE_pos : (0 : ℝ) ≤ (g n : ℝ) ^ exponent_seq r k := by
    first | exact Real.rpow_nonneg h_gn_pos_R _ | exact Real.rpow_nonneg h_gn_pos_R | positivity
  have h_cgnE_pos : (0 : ℝ) ≤ c * (g n : ℝ) ^ exponent_seq r k := by
    first | exact mul_nonneg h_c_pos_R h_gnE_pos | positivity
  have hc_r_pos : (0 : ℝ) ≤ c ^ r := by
    first | exact Real.rpow_nonneg h_c_pos_R _ | exact Real.rpow_nonneg h_c_pos_R | positivity

  have H_add : c ^ (r + r * exponent_seq r k) = c ^ r * c ^ (r * exponent_seq r k) := by
    first
    | exact Real.rpow_add hc r (r * exponent_seq r k)
    | exact Real.rpow_add hc _ _
    | exact Real.rpow_add hc
    | exact Real.rpow_add (ne_of_gt hc) r (r * exponent_seq r k)
    | exact Real.rpow_add (ne_of_gt hc) _ _
    | exact Real.rpow_add (ne_of_gt hc)

  have h_exp : r * ((1 : ℝ) + exponent_seq r k) = r + r * exponent_seq r k := by ring

  have step2 : c ^ (r * exponent_seq r k) * (n : ℝ) ^ (r * (exponent_seq r k) ^ 2) =
      (c * (n : ℝ) ^ exponent_seq r k) ^ (r * exponent_seq r k) := by
    have H_mul : (c * (n : ℝ) ^ exponent_seq r k) ^ (r * exponent_seq r k) =
        c ^ (r * exponent_seq r k) * ((n : ℝ) ^ exponent_seq r k) ^ (r * exponent_seq r k) := by
      first
      | exact Real.mul_rpow h_c_pos_R h_nE_pos
      | exact Real.mul_rpow h_c_pos_R h_nE_pos _
    rw [H_mul]
    have h_ring : r * exponent_seq r k ^ 2 = exponent_seq r k * (r * exponent_seq r k) := by ring
    rw [h_ring]
    have H_pow : (n : ℝ) ^ (exponent_seq r k * (r * exponent_seq r k)) =
        ((n : ℝ) ^ exponent_seq r k) ^ (r * exponent_seq r k) := by
      first
      | exact Real.rpow_mul h_n_pos_R (exponent_seq r k) (r * exponent_seq r k)
      | exact (Real.rpow_mul h_n_pos_R (exponent_seq r k) (r * exponent_seq r k)).symm
      | exact Real.rpow_mul h_n_pos_R _ _
      | exact (Real.rpow_mul h_n_pos_R _ _).symm
      | exact Real.rpow_mul h_n_pos_R
      | exact (Real.rpow_mul h_n_pos_R).symm
    rw [H_pow]

  have step3 : (c * (n : ℝ) ^ exponent_seq r k) ^ (r * exponent_seq r k) ≤
      (g n : ℝ) ^ (r * exponent_seq r k) := by
    first
    | exact Real.rpow_le_rpow h_cnE_pos h3 h_rE_pos
    | exact Real.rpow_le_rpow h_cnE_pos h3

  have step4 : (g n : ℝ) ^ (r * exponent_seq r k) = ((g n : ℝ) ^ exponent_seq r k) ^ r := by
    have h_ring2 : r * exponent_seq r k = exponent_seq r k * r := by ring
    rw [h_ring2]
    have H_pow2 : (g n : ℝ) ^ (exponent_seq r k * r) = ((g n : ℝ) ^ exponent_seq r k) ^ r := by
      first
      | exact Real.rpow_mul h_gn_pos_R (exponent_seq r k) r
      | exact (Real.rpow_mul h_gn_pos_R (exponent_seq r k) r).symm
      | exact Real.rpow_mul h_gn_pos_R _ _
      | exact (Real.rpow_mul h_gn_pos_R _ _).symm
      | exact Real.rpow_mul h_gn_pos_R
      | exact (Real.rpow_mul h_gn_pos_R).symm
    rw [H_pow2]

  have step5 : c ^ r * ((g n : ℝ) ^ exponent_seq r k) ^ r =
      (c * (g n : ℝ) ^ exponent_seq r k) ^ r := by
    have H_mul2 : (c * (g n : ℝ) ^ exponent_seq r k) ^ r =
        c ^ r * ((g n : ℝ) ^ exponent_seq r k) ^ r := by
      first
      | exact Real.mul_rpow h_c_pos_R h_gnE_pos
      | exact Real.mul_rpow h_c_pos_R h_gnE_pos _
    rw [H_mul2]

  have step6 : (c * (g n : ℝ) ^ exponent_seq r k) ^ r ≤ (g (g n) : ℝ) ^ r := by
    first
    | exact Real.rpow_le_rpow h_cgnE_pos h1 hr_nn
    | exact Real.rpow_le_rpow h_cgnE_pos h1

  calc c ^ (r * ((1 : ℝ) + exponent_seq r k)) * (n : ℝ) ^ (r * (exponent_seq r k) ^ 2)
    _ = c ^ (r + r * exponent_seq r k) * (n : ℝ) ^ (r * (exponent_seq r k) ^ 2) := by rw [h_exp]
    _ = c ^ r * c ^ (r * exponent_seq r k) * (n : ℝ) ^ (r * (exponent_seq r k) ^ 2) := by rw [H_add]
    _ = c ^ r * (c ^ (r * exponent_seq r k) * (n : ℝ) ^ (r * (exponent_seq r k) ^ 2)) := by ring
    _ = c ^ r * (c * (n : ℝ) ^ exponent_seq r k) ^ (r * exponent_seq r k) := by rw [step2]
    _ ≤ c ^ r * (g n : ℝ) ^ (r * exponent_seq r k) := mul_le_mul_of_nonneg_left step3 hc_r_pos
    _ = c ^ r * ((g n : ℝ) ^ exponent_seq r k) ^ r := by rw [step4]
    _ = (c * (g n : ℝ) ^ exponent_seq r k) ^ r := step5
    _ ≤ (g (g n) : ℝ) ^ r := step6
    _ ≤ (g (n + 1) : ℝ) - (g n : ℝ) := h2_ineq

theorem g_lower_bound_iterated (g : ℕ → ℕ) (r : ℝ) (hr : (0 : ℝ) < r)
    (h1 : ∀ n : ℕ, 0 < n → 0 < g n)
    (h2 : ∀ n : ℕ, 0 < n → (g (g n) : ℝ)^r ≤ (g (n + 1) : ℝ) - (g n : ℝ))
    (k : ℕ) :
    ∃ c : ℝ, (0 : ℝ) < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → c * (n : ℝ)^(exponent_seq r k) ≤ (g n : ℝ) :=
by
  induction k with
  | zero =>
    have h_inc := my_g_strictly_increasing g r h1 h2
    have h_ge := my_g_ge_n g h1 h_inc
    use (1 : ℝ)
    refine ⟨by norm_num, 1, ?_⟩
    intro n hn
    rw [my_exponent_seq_zero]
    rw [my_base_case_arith]
    have hn_pos : 0 < n := by linarith
    have h_ge_n := h_ge n hn_pos
    exact Nat.cast_le.mpr h_ge_n
  | succ k ih =>
    rcases ih with ⟨c, hc, N, hN⟩
    have h_inc := my_g_strictly_increasing g r h1 h2
    rcases my_g_tendsto_inf g h_inc N with ⟨M, hM⟩
    rcases my_N1_properties N M with ⟨N1, hN1_1, hN1_M, hN1_3⟩
    have hN1_2 : ∀ n : ℕ, N1 ≤ n → N ≤ g n := fun n hn => hM n (hN1_M n hn)
    have h_diff_bound := my_g_bound_to_diff_bound g r hr k c hc N hN h2 N1 hN1_1 hN1_2 hN1_3

    have hp : (0 : ℝ) ≤ r * (exponent_seq r k)^2 := my_pos_mul_sq r hr (exponent_seq r k)
    have hc' : (0 : ℝ) < c ^ (r * ((1 : ℝ) + exponent_seq r k)) := my_pos_rpow c hc _

    rcases my_g_diff_to_g_bound g (r * (exponent_seq r k)^2) hp (c ^ (r * ((1 : ℝ) + exponent_seq r k))) hc' N1 h_diff_bound with ⟨c'', hc'', N2, hN2⟩
    use c''
    refine ⟨hc'', N2, ?_⟩
    intro n hn
    have h_exp_succ : exponent_seq r (k + 1) = r * (exponent_seq r k)^2 + (1 : ℝ) := my_exponent_seq_succ r k
    have h_goal : c'' * (n : ℝ)^(exponent_seq r (k + 1)) ≤ (g n : ℝ) := by
      rw [h_exp_succ]
      exact hN2 n hn
    exact h_goal

theorem exponent_seq_unbounded (r : ℝ) (hr : ((1 : ℝ) / (4 : ℝ)) < r) (M : ℝ) :
    ∃ k : ℕ, M < exponent_seq r k :=
by
  have hr_pos : (0 : ℝ) < r := by linarith
  let c := 1 - 1 / (4 * r)
  have hc_def : c = 1 - 1 / (4 * r) := rfl
  have hc : (0 : ℝ) < c := by
    rw [hc_def, sub_pos]
    have h1 : (0 : ℝ) < 4 * r := by linarith
    rw [div_lt_iff₀ h1]
    linarith

  have step : ∀ n : ℕ, exponent_seq r n + c ≤ exponent_seq r (n + 1) := by
    intro n
    have hr0 : r ≠ 0 := by linarith
    have h2r : (2 : ℝ) * r ≠ 0 := by linarith
    have hA : r * (2 * exponent_seq r n * (1 / (2 * r))) = exponent_seq r n := by
      calc r * (2 * exponent_seq r n * (1 / (2 * r)))
        _ = exponent_seq r n * (2 * r * (1 / (2 * r))) := by ring
        _ = exponent_seq r n * ((2 * r) / (2 * r)) := by
          have : (2 : ℝ) * r * (1 / (2 * r)) = (2 * r) / (2 * r) := by rw [mul_one_div]
          rw [this]
        _ = exponent_seq r n * 1 := by rw [div_self h2r]
        _ = exponent_seq r n := mul_one _
    have hB : r * (1 / (2 * r)) ^ 2 = 1 / (4 * r) := by
      calc r * (1 / (2 * r)) ^ 2
        _ = r * ((1 / (2 * r)) * (1 / (2 * r))) := by rw [sq]
        _ = r * (1 * 1 / (2 * r * (2 * r))) := by rw [div_mul_div_comm]
        _ = r * (1 / (r * (4 * r))) := by
          have h_num : (1 : ℝ) * 1 = 1 := by ring
          have h_den : (2 : ℝ) * r * (2 * r) = r * (4 * r) := by ring
          rw [h_num, h_den]
        _ = r / (r * (4 * r)) := by rw [mul_one_div]
        _ = (r / r) / (4 * r) := by rw [← div_div]
        _ = 1 / (4 * r) := by rw [div_self hr0]
    have H2 : exponent_seq r n + c + r * (exponent_seq r n - 1 / (2 * r)) ^ 2 = r * (exponent_seq r n) ^ 2 + 1 := by
      rw [hc_def]
      calc exponent_seq r n + (1 - 1 / (4 * r)) + r * (exponent_seq r n - 1 / (2 * r)) ^ 2
        _ = exponent_seq r n + 1 - 1 / (4 * r) + r * (exponent_seq r n) ^ 2 - r * (2 * exponent_seq r n * (1 / (2 * r))) + r * (1 / (2 * r)) ^ 2 := by ring
        _ = exponent_seq r n + 1 - 1 / (4 * r) + r * (exponent_seq r n) ^ 2 - exponent_seq r n + r * (1 / (2 * r)) ^ 2 := by rw [hA]
        _ = exponent_seq r n + 1 - 1 / (4 * r) + r * (exponent_seq r n) ^ 2 - exponent_seq r n + 1 / (4 * r) := by rw [hB]
        _ = r * (exponent_seq r n) ^ 2 + 1 := by ring
    have h_seq : exponent_seq r (n + 1) = r * (exponent_seq r n)^2 + 1 := rfl
    rw [h_seq]
    calc exponent_seq r n + c
      _ ≤ exponent_seq r n + c + r * (exponent_seq r n - 1 / (2 * r)) ^ 2 := by
        have : 0 ≤ r * (exponent_seq r n - 1 / (2 * r)) ^ 2 := mul_nonneg (le_of_lt hr_pos) (sq_nonneg _)
        linarith
      _ = r * (exponent_seq r n) ^ 2 + 1 := H2

  have lower_bound : ∀ n : ℕ, 1 + (n : ℝ) * c ≤ exponent_seq r n := by
    intro n
    induction n with
    | zero =>
      have h_seq : exponent_seq r 0 = 1 := rfl
      rw [h_seq]
      have h_zero : ((0 : ℕ) : ℝ) = 0 := by push_cast; rfl
      rw [h_zero, zero_mul, add_zero]
    | succ n ih =>
      have h_cast : (((n + 1 : ℕ) : ℝ)) = (n : ℝ) + 1 := by push_cast; ring
      calc 1 + ((n + 1 : ℕ) : ℝ) * c
        _ = 1 + ((n : ℝ) + 1) * c := by rw [h_cast]
        _ = 1 + (n : ℝ) * c + c := by ring
        _ ≤ exponent_seq r n + c := by linarith
        _ ≤ exponent_seq r (n + 1) := step n

  obtain ⟨k, hk⟩ := exists_nat_gt ((M - 1) / c)
  use k
  have hk2 : M - 1 < (k : ℝ) * c := (div_lt_iff₀ hc).mp hk
  have hk3 : M < 1 + (k : ℝ) * c := by linarith
  have hk4 : 1 + (k : ℝ) * c ≤ exponent_seq r k := lower_bound k
  linarith

theorem g_ge_n_plus_two (g : ℕ → ℕ) (r : ℝ) (hr : (0 : ℝ) < r)
    (h1 : ∀ n : ℕ, 0 < n → 0 < g n)
    (h2 : ∀ n : ℕ, 0 < n → (g (g n) : ℝ)^r ≤ (g (n + 1) : ℝ) - (g n : ℝ)) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → n + 2 ≤ g n :=
by
  have h_g_inc : ∀ k, 1 ≤ k → g k + 1 ≤ g (k + 1) := by
    intro k hk
    have hgk_pos : 0 < g k := h1 k (by omega)
    have hggk_pos : 0 < g (g k) := h1 _ hgk_pos
    have hggk_ge_1_nat : 1 ≤ g (g k) := by omega
    have hggk_ge_1 : (1 : ℝ) ≤ (g (g k) : ℝ) := by exact_mod_cast hggk_ge_1_nat
    have hrpow : (1 : ℝ) ≤ (g (g k) : ℝ)^r := by
      have h1_rpow : (1 : ℝ) = (1 : ℝ)^r := (Real.one_rpow r).symm
      rw [h1_rpow]
      apply Real.rpow_le_rpow (by norm_num) hggk_ge_1 (le_of_lt hr)
    have h2k := h2 k (by omega)
    have h_le2 : (((g k) + 1 : ℕ) : ℝ) ≤ (g (k + 1) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast h_le2

  have h_g_ge : ∀ n, n + 1 ≤ g (n + 1) := by
    intro n
    induction n with
    | zero =>
      have hg1 : 0 < g 1 := h1 1 (by omega)
      change 1 ≤ g 1
      omega
    | succ m ih =>
      have hk : 1 ≤ m + 1 := by omega
      have hinc := h_g_inc (m + 1) hk
      have heq : Nat.succ m + 1 = m + 1 + 1 := by omega
      rw [heq]
      omega

  have h_g_ge_le : ∀ n, 1 ≤ n → n ≤ g n := by
    intro n hn
    obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    subst hm
    exact h_g_ge m

  have h2r : (1 : ℝ) < 2^r := by
    have H1 : (0 : ℝ) ≤ 1 := by norm_num
    have H2 : (1 : ℝ) < 2 := by norm_num
    have H3 := Real.rpow_lt_rpow H1 H2 hr
    rw [Real.one_rpow] at H3
    exact H3

  have h_g_inc2 : ∀ k, 1 ≤ k → 2 ≤ g (g k) → (g k) + 2 ≤ g (k + 1) := by
    intro k hk hggk2
    have hggk_ge_2 : (2 : ℝ) ≤ (g (g k) : ℝ) := by exact_mod_cast hggk2
    have hrpow2 : (2 : ℝ)^r ≤ (g (g k) : ℝ)^r := by
      apply Real.rpow_le_rpow (by norm_num) hggk_ge_2 (le_of_lt hr)
    have h2k := h2 k hk
    have h_strict : (((g k) + 1 : ℕ) : ℝ) < (g (k + 1) : ℝ) := by
      push_cast
      calc
        (g k : ℝ) + 1 < (g k : ℝ) + 2^r := by linarith [h2r]
        _ ≤ (g k : ℝ) + (g (g k) : ℝ)^r := by linarith [hrpow2]
        _ ≤ (g (k + 1) : ℝ) := by linarith [h2k]
    have h_strict2 : (g k) + 1 < g (k + 1) := by exact_mod_cast h_strict
    omega

  have hg2 : 2 ≤ g 2 := by
    exact h_g_ge 1

  have hgg2 : 2 ≤ g (g 2) := by
    have h1_ineq : 1 ≤ g 2 := by omega
    have h2_ineq := h_g_ge_le (g 2) h1_ineq
    omega

  have hg3 : g 2 + 2 ≤ g 3 := by
    exact h_g_inc2 2 (by omega) hgg2

  have hg3_ge_4 : 4 ≤ g 3 := by omega

  have hgg3 : 2 ≤ g (g 3) := by
    have h1_ineq : 1 ≤ g 3 := by omega
    have h2_ineq := h_g_ge_le (g 3) h1_ineq
    omega

  have hg4 : g 3 + 2 ≤ g 4 := by
    exact h_g_inc2 3 (by omega) hgg3

  have hg4_ge_6 : 6 ≤ g 4 := by omega

  use 4
  intro n hn
  obtain ⟨m, hm⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  subst hm
  induction m with
  | zero =>
    exact hg4_ge_6
  | succ m ih =>
    have hk : 1 ≤ m + 4 := by omega
    have hinc := h_g_inc (m + 4) hk
    have heq : Nat.succ m + 4 = m + 4 + 1 := by omega
    rw [heq]
    omega

theorem g_upper_bound_ineq (g : ℕ → ℕ) (r : ℝ) (hr : (0 : ℝ) < r)
    (h_inc : ∀ n : ℕ, 0 < n → g n < g (n + 1))
    (h_ge : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → n + 2 ≤ g n)
    (h2 : ∀ n : ℕ, 0 < n → (g (g n) : ℝ)^r ≤ (g (n + 1) : ℝ) - (g n : ℝ)) :
    ∃ N_u : ℕ, ∀ n : ℕ, N_u ≤ n → (g (g n) : ℝ) < ((g n : ℝ))^((1 : ℝ) / (r^2)) :=
by
  have h_inc_le : ∀ a b, 0 < a → a ≤ b → g a ≤ g b := by
    intro a b ha hab
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hab
    subst hd
    clear hab -- We clear this so `ih` evaluates directly without generalizing over the inequality assumption
    induction d with
    | zero => exact le_rfl
    | succ d ih =>
      have h_eq : a + Nat.succ d = a + d + 1 := by omega
      rw [h_eq]
      have h_step : g (a + d) < g (a + d + 1) := h_inc (a + d) (by omega)
      exact le_trans ih (le_of_lt h_step)

  obtain ⟨N, h_ge_N⟩ := h_ge
  let N_u := max N 1 + 1
  use N_u
  intro n hn

  have hn_max : max N 1 + 1 ≤ n := hn
  have hN1 : N ≤ max N 1 := le_max_left N 1
  have h11 : 1 ≤ max N 1 := le_max_right N 1

  have hn_pos : 0 < n := by omega
  have hn_ge_2 : 2 ≤ n := by omega

  obtain ⟨m, hm1⟩ : ∃ m, m + 1 = n := ⟨n - 1, by omega⟩
  have hm_pos : 0 < m := by omega
  have hm_N : N ≤ m := by omega

  have h_n1_le_gm : n + 1 ≤ g m := by
    have h_ge_m : m + 2 ≤ g m := h_ge_N m hm_N
    omega

  have h_g_n_1_le : g (n + 1) ≤ g (g m) := h_inc_le (n + 1) (g m) (by omega) h_n1_le_gm
  have h_g_n_1_le_R : (g (n + 1) : ℝ) ≤ (g (g m) : ℝ) := Nat.cast_le.mpr h_g_n_1_le

  have h_pow_le : (g (n + 1) : ℝ) ^ r ≤ (g (g m) : ℝ) ^ r := by
    apply Real.rpow_le_rpow
    · positivity
    · exact h_g_n_1_le_R
    · exact le_of_lt hr

  have h2_m := h2 m hm_pos
  have h2_m_rw : (g (g m) : ℝ) ^ r ≤ (g n : ℝ) - (g m : ℝ) := by
    have : m + 1 = n := hm1
    rw [this] at h2_m
    exact h2_m

  have h_pow_le2 : (g (n + 1) : ℝ) ^ r ≤ (g n : ℝ) - (g m : ℝ) := le_trans h_pow_le h2_m_rw

  have hgm_pos : (0 : ℝ) < (g m : ℝ) := by
    have : 0 < g m := by
      have : m + 2 ≤ g m := h_ge_N m hm_N
      omega
    exact Nat.cast_pos.mpr this

  have h_bound1 : (g (n + 1) : ℝ) ^ r < (g n : ℝ) := by
    calc
      (g (n + 1) : ℝ) ^ r ≤ (g n : ℝ) - (g m : ℝ) := h_pow_le2
      _ < (g n : ℝ) := by linarith [hgm_pos]

  have h2_n := h2 n hn_pos
  have hgn_pos : (0 : ℝ) < (g n : ℝ) := by
    have : n + 2 ≤ g n := h_ge_N n (by omega)
    have : 0 < g n := by omega
    exact Nat.cast_pos.mpr this

  have h_bound2 : (g (g n) : ℝ) ^ r < (g (n + 1) : ℝ) := by
    calc
      (g (g n) : ℝ) ^ r ≤ (g (n + 1) : ℝ) - (g n : ℝ) := h2_n
      _ < (g (n + 1) : ℝ) := by linarith [hgn_pos]

  have hr_inv_pos : (0 : ℝ) < 1 / r := one_div_pos.mpr hr
  have hr_ne_zero : r ≠ 0 := hr.ne'

  have H_r_cancel : r * (1 / r) = 1 := by
    rw [one_div]
    exact mul_inv_cancel₀ hr_ne_zero

  have hb1 : (g (n + 1) : ℝ) < (g n : ℝ) ^ (1 / r) := by
    have H1 : ((g (n + 1) : ℝ) ^ r) ^ (1 / r) < (g n : ℝ) ^ (1 / r) := by
      apply Real.rpow_lt_rpow
      · positivity
      · exact h_bound1
      · exact hr_inv_pos
    have H2 : (((g (n + 1) : ℝ) ^ r) ^ (1 / r)) = (g (n + 1) : ℝ) := by
      rw [← Real.rpow_mul (by positivity)]
      rw [H_r_cancel, Real.rpow_one]
    rwa [H2] at H1

  have hb2 : (g (g n) : ℝ) < (g (n + 1) : ℝ) ^ (1 / r) := by
    have H1 : ((g (g n) : ℝ) ^ r) ^ (1 / r) < (g (n + 1) : ℝ) ^ (1 / r) := by
      apply Real.rpow_lt_rpow
      · positivity
      · exact h_bound2
      · exact hr_inv_pos
    have H2 : (((g (g n) : ℝ) ^ r) ^ (1 / r)) = (g (g n) : ℝ) := by
      rw [← Real.rpow_mul (by positivity)]
      rw [H_r_cancel, Real.rpow_one]
    rwa [H2] at H1

  have hb3 : (g (n + 1) : ℝ) ^ (1 / r) < ((g n : ℝ) ^ (1 / r)) ^ (1 / r) := by
    apply Real.rpow_lt_rpow
    · positivity
    · exact hb1
    · exact hr_inv_pos

  have hb4 : (g (g n) : ℝ) < ((g n : ℝ) ^ (1 / r)) ^ (1 / r) := lt_trans hb2 hb3

  have H3 : ((g n : ℝ) ^ (1 / r)) ^ (1 / r) = (g n : ℝ) ^ ((1 : ℝ) / (r ^ 2)) := by
    rw [← Real.rpow_mul (by positivity)]
    have : (1 : ℝ) / r * (1 / r) = (1 : ℝ) / (r ^ 2) := by
      calc
        (1 : ℝ) / r * (1 / r) = (1 * 1 : ℝ) / (r * r) := by rw [div_mul_div_comm]
        _ = (1 : ℝ) / (r * r) := by rw [mul_one]
        _ = (1 : ℝ) / (r ^ 2) := by
          have h_r2 : r * r = r ^ 2 := by ring
          rw [h_r2]
    rw [this]

  rwa [H3] at hb4

theorem bounds_conflict (g : ℕ → ℕ) (x : ℝ) (r : ℝ) (hr : (0 : ℝ) < r) (hx : (1 : ℝ) / (r^2) < x)
    (c : ℝ) (hc : (0 : ℝ) < c)
    (h_lower : ∃ N_l : ℕ, ∀ n : ℕ, N_l ≤ n → c * (n : ℝ)^x ≤ (g n : ℝ))
    (h_upper : ∃ N_u : ℕ, ∀ n : ℕ, N_u ≤ n → (g (g n) : ℝ) < ((g n : ℝ))^((1 : ℝ) / (r^2)))
    (h_tendsto : ∀ K : ℕ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → K ≤ g n) : False :=
by
  obtain ⟨N_l, h_lower⟩ := h_lower
  obtain ⟨N_u, h_upper⟩ := h_upper
  have hd : (0 : ℝ) < x - (1 : ℝ) / r^2 := sub_pos.mpr hx
  have hc_inv_pos : (0 : ℝ) < (1 : ℝ) / c := one_div_pos.mpr hc

  have h_pos_rpow : (0 : ℝ) < ((1 : ℝ) / c) ^ ((1 : ℝ) / (x - (1 : ℝ) / r^2)) := by positivity

  let M := max (N_l : ℝ) (((1 : ℝ) / c) ^ ((1 : ℝ) / (x - (1 : ℝ) / r^2)))
  obtain ⟨K, hK⟩ := exists_nat_gt M

  have hK1 : (N_l : ℝ) ≤ K := (le_max_left _ _).trans hK.le
  have hK_Nl : N_l ≤ K := by exact_mod_cast hK1

  have hK2 : ((1 : ℝ) / c) ^ ((1 : ℝ) / (x - (1 : ℝ) / r^2)) < K := (le_max_right _ _).trans_lt hK

  have hK_pos : (0 : ℝ) < (K : ℝ) := lt_trans h_pos_rpow hK2

  have hK3 : (((1 : ℝ) / c) ^ ((1 : ℝ) / (x - (1 : ℝ) / r^2))) ^ (x - (1 : ℝ) / r^2) < (K : ℝ) ^ (x - (1 : ℝ) / r^2) := by
    apply Real.rpow_lt_rpow
    · exact le_of_lt h_pos_rpow
    · exact hK2
    · exact hd

  have h_rpow : (((1 : ℝ) / c) ^ ((1 : ℝ) / (x - (1 : ℝ) / r^2))) ^ (x - (1 : ℝ) / r^2) = (1 : ℝ) / c := by
    rw [← Real.rpow_mul (le_of_lt hc_inv_pos)]
    have h_mul : ((1 : ℝ) / (x - (1 : ℝ) / r^2)) * (x - (1 : ℝ) / r^2) = (1 : ℝ) := div_mul_cancel₀ 1 (ne_of_gt hd)
    rw [h_mul, Real.rpow_one]

  have hK4 : (1 : ℝ) < c * (K : ℝ) ^ (x - (1 : ℝ) / r^2) := by
    rw [h_rpow] at hK3
    by_contra h_not_lt
    have h_le : c * (K : ℝ) ^ (x - (1 : ℝ) / r^2) ≤ (1 : ℝ) := not_lt.mp h_not_lt
    have h_mul : ((1 : ℝ) / c) * (c * (K : ℝ) ^ (x - (1 : ℝ) / r^2)) ≤ ((1 : ℝ) / c) * (1 : ℝ) :=
      mul_le_mul_of_nonneg_left h_le (le_of_lt hc_inv_pos)
    have H_simp : ((1 : ℝ) / c) * (c * (K : ℝ) ^ (x - (1 : ℝ) / r^2)) = (K : ℝ) ^ (x - (1 : ℝ) / r^2) := by
      calc ((1 : ℝ) / c) * (c * (K : ℝ) ^ (x - (1 : ℝ) / r^2))
        _ = (((1 : ℝ) / c) * c) * (K : ℝ) ^ (x - (1 : ℝ) / r^2) := by rw [← mul_assoc]
        _ = (1 : ℝ) * (K : ℝ) ^ (x - (1 : ℝ) / r^2) := by
              have h_inv : ((1 : ℝ) / c) * c = (1 : ℝ) := div_mul_cancel₀ 1 (ne_of_gt hc)
              rw [h_inv]
        _ = (K : ℝ) ^ (x - (1 : ℝ) / r^2) := by rw [one_mul]
    rw [H_simp, mul_one] at h_mul
    exact lt_irrefl _ (lt_of_lt_of_le hK3 h_mul)

  obtain ⟨N_K, h_NK⟩ := h_tendsto K
  let n := max N_u N_K
  have hn_u : N_u ≤ n := le_max_left _ _
  have hn_K : N_K ≤ n := le_max_right _ _

  have h_g_upper : (g (g n) : ℝ) < (g n : ℝ) ^ ((1 : ℝ) / r^2) := h_upper n hn_u

  have h_g_n_ge_K : K ≤ g n := h_NK n hn_K
  have h_g_n_ge_Nl : N_l ≤ g n := le_trans hK_Nl h_g_n_ge_K

  have h_g_lower : c * (g n : ℝ) ^ x ≤ (g (g n) : ℝ) := h_lower (g n) h_g_n_ge_Nl

  have h_g_ineq : c * (g n : ℝ) ^ x < (g n : ℝ) ^ ((1 : ℝ) / r^2) := lt_of_le_of_lt h_g_lower h_g_upper

  have h_gn_pos : (0 : ℝ) < (g n : ℝ) := by
    calc (0 : ℝ) < (K : ℝ) := hK_pos
      _ ≤ (g n : ℝ) := by exact_mod_cast h_g_n_ge_K

  have h_gn_y_pos : (0 : ℝ) < (g n : ℝ) ^ ((1 : ℝ) / r^2) := by positivity

  have h_lt_1 : c * (g n : ℝ) ^ (x - (1 : ℝ) / r^2) < (1 : ℝ) := by
    by_contra h_not_lt
    have h_ge : (1 : ℝ) ≤ c * (g n : ℝ) ^ (x - (1 : ℝ) / r^2) := not_lt.mp h_not_lt
    have H1 : c * (g n : ℝ) ^ (x - (1 : ℝ) / r^2) * (g n : ℝ) ^ ((1 : ℝ) / r^2) = c * (g n : ℝ) ^ x := by
      rw [mul_assoc, ← Real.rpow_add h_gn_pos]
      have h_add : x - (1 : ℝ) / r^2 + (1 : ℝ) / r^2 = x := sub_add_cancel x ((1 : ℝ) / r^2)
      rw [h_add]
    have h_mul_ge : (1 : ℝ) * (g n : ℝ) ^ ((1 : ℝ) / r^2) ≤ c * (g n : ℝ) ^ (x - (1 : ℝ) / r^2) * (g n : ℝ) ^ ((1 : ℝ) / r^2) :=
      mul_le_mul_of_nonneg_right h_ge (le_of_lt h_gn_y_pos)
    rw [one_mul, H1] at h_mul_ge
    exact lt_irrefl _ (lt_of_lt_of_le h_g_ineq h_mul_ge)

  have h_K_le_gn : (K : ℝ) ≤ (g n : ℝ) := by exact_mod_cast h_g_n_ge_K
  have h_rpow_le : (K : ℝ) ^ (x - (1 : ℝ) / r^2) ≤ (g n : ℝ) ^ (x - (1 : ℝ) / r^2) := by
    rcases eq_or_lt_of_le h_K_le_gn with heq | hlt
    · rw [heq]
    · apply le_of_lt
      apply Real.rpow_lt_rpow
      · exact le_of_lt hK_pos
      · exact hlt
      · exact hd

  have h_mul_le : c * (K : ℝ) ^ (x - (1 : ℝ) / r^2) ≤ c * (g n : ℝ) ^ (x - (1 : ℝ) / r^2) :=
    mul_le_mul_of_nonneg_left h_rpow_le (le_of_lt hc)

  have h_contra : (1 : ℝ) < (1 : ℝ) := by
    calc (1 : ℝ) < c * (K : ℝ) ^ (x - (1 : ℝ) / r^2) := hK4
      _ ≤ c * (g n : ℝ) ^ (x - (1 : ℝ) / r^2) := h_mul_le
      _ < (1 : ℝ) := h_lt_1

  exact lt_irrefl (1 : ℝ) h_contra

theorem real_lt_of_not_le (a b : ℝ) (h : ¬ (a ≤ b)) : b < a :=
by
  exact lt_of_not_ge h

theorem r_pos_of_gt_quarter (r : ℝ) (hr : ((1 : ℝ) / (4 : ℝ)) < r) : (0 : ℝ) < r :=
by
  linarith

theorem putnam_2025_b6 : IsGreatest
      {r : ℝ | ∃ g : ℕ → ℕ, (∀ n : ℕ, 0 < n → 0 < g n) ∧
        ∀ n : ℕ, 0 < n → ((g (g n) : ℝ) ^ r) ≤ (g (n + 1) : ℝ) - (g n : ℝ)}
      putnam_2025_b6_solution :=
by
  constructor
  · rw [putnam_solution_eq]
    dsimp only [Set.mem_setOf_eq]
    use fun n => n^2
    constructor
    · intro n hn
      exact putnam_2025_b6_witness_pos n hn
    · intro n hn
      exact putnam_2025_b6_witness_works n hn
  · rintro r ⟨g, h1, h2⟩
    rw [putnam_solution_eq]
    by_contra h_contra
    have hr : ((1 : ℝ) / (4 : ℝ)) < r := real_lt_of_not_le r ((1 : ℝ) / (4 : ℝ)) h_contra
    have hr0 : (0 : ℝ) < r := r_pos_of_gt_quarter r hr
    have h_inc := g_strictly_increasing g r h1 h2
    have h_tendsto := g_tendsto_inf g h_inc
    have h_ge := g_ge_n_plus_two g r hr0 h1 h2
    have h_upper := g_upper_bound_ineq g r hr0 h_inc h_ge h2
    obtain ⟨k, hk⟩ := exponent_seq_unbounded r hr ((1 : ℝ) / (r^2))
    obtain ⟨c, hc_and_lower⟩ := g_lower_bound_iterated g r hr0 h1 h2 k
    have hc := hc_and_lower.1
    have h_lower := hc_and_lower.2
    exact bounds_conflict g (exponent_seq r k) r hr0 hk c hc h_lower h_upper h_tendsto
