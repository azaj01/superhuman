import Mathlib
open Finset
abbrev putnam_2025_b3_solution : Bool := true

theorem one_in_S (S : Set ℕ) (h_nonempty : S.Nonempty) (h_pos : ∀ n ∈ S, 0 < n)
    (h_div : ∀ n ∈ S, ∀ d : ℕ, 0 < d → d ∣ (2025 ^ n - 15 ^ n) → d ∈ S) : 1 ∈ S :=
by
  obtain ⟨n, hn⟩ := h_nonempty
  exact h_div n hn 1 (by decide) (one_dvd _)

theorem extract_3_5 (m : ℕ) (hm : 0 < m) :
    ∃ u v m', m = 3^u * 5^v * m' ∧ Nat.Coprime m' 15 :=
by
  have hm_ne : m ≠ 0 := by omega
  have h3_ne : (3 : ℕ) ≠ 1 := by decide
  obtain ⟨u, m₁, h3, hm1⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm_ne (3 : ℕ) h3_ne
  have hm1_ne : m₁ ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hm1
    omega
  have h5_ne : (5 : ℕ) ≠ 1 := by decide
  obtain ⟨v, m', h5, hm'⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm1_ne (5 : ℕ) h5_ne
  use u, v, m'
  constructor
  · rw [hm1, hm']
    ring
  · have h3_not_dvd_m' : ¬ 3 ∣ m' := by
      intro hdvd
      apply h3
      rw [hm']
      obtain ⟨k, hk⟩ := hdvd
      use 5 ^ v * k
      rw [hk]
      ring
    have hp3 : Nat.Prime 3 := by norm_num
    have hp5 : Nat.Prime 5 := by norm_num
    have hc3 : Nat.Coprime 3 m' := (Nat.Prime.coprime_iff_not_dvd hp3).mpr h3_not_dvd_m'
    have hc5 : Nat.Coprime 5 m' := (Nat.Prime.coprime_iff_not_dvd hp5).mpr h5
    have hc15 : Nat.Coprime (3 * 5) m' := Nat.Coprime.mul hc3 hc5
    have h_eq : (15 : ℕ) = 3 * 5 := by rfl
    rw [h_eq]
    exact hc15.symm

theorem coprime_135_of_coprime_15 {m : ℕ} (h : Nat.Coprime m 15) : Nat.Coprime m 135 :=
by
  apply Nat.coprime_of_dvd'
  intro k _ hk_m hk_135
  have hl : m.Coprime (List.prod [15, 15, 15]) := by
    apply Nat.coprime_list_prod_right_iff.mpr
    intro n hn
    rcases List.mem_cons.mp hn with rfl | hn2
    · exact h
    · rcases List.mem_cons.mp hn2 with rfl | hn3
      · exact h
      · rcases List.mem_cons.mp hn3 with rfl | hn4
        · exact h
        · cases hn4
  have h_prod : List.prod [15, 15, 15] = 3375 := rfl
  rw [h_prod] at hl
  have d_dvd_m : Nat.gcd m 135 ∣ m := Nat.gcd_dvd_left m 135
  have d_dvd_135 : Nat.gcd m 135 ∣ 135 := Nat.gcd_dvd_right m 135
  have h135_3375 : 135 ∣ 3375 := ⟨25, rfl⟩
  have d_dvd_3375 : Nat.gcd m 135 ∣ 3375 := Nat.dvd_trans d_dvd_135 h135_3375
  have d_dvd_gcd : Nat.gcd m 135 ∣ Nat.gcd m 3375 := Nat.dvd_gcd d_dvd_m d_dvd_3375
  have h_gcd_3375 : Nat.gcd m 3375 = 1 := hl
  have d_dvd_1 : Nat.gcd m 135 ∣ 1 := by
    rw [← h_gcd_3375]
    exact d_dvd_gcd
  have hk_gcd : k ∣ Nat.gcd m 135 := Nat.dvd_gcd hk_m hk_135
  exact Nat.dvd_trans hk_gcd d_dvd_1

theorem n_lt_m_unified (u v m' m : ℕ) (hm : m = 3^u * 5^v * m') (hm1 : 1 < m) (hc : Nat.Coprime m' 15) :
    (u + v + 1) * Nat.totient m' < m :=
by
  have cases_m' : m' = 0 ∨ 0 < m' := by omega
  have hm'0 : 0 < m' := by
    rcases cases_m' with rfl | hpos
    · have : m = 0 := by
        calc m = 3^u * 5^v * 0 := hm
          _ = 0 := by ring
      omega
    · exact hpos

  have lt_two_pow : ∀ k, k + 1 ≤ 2^k := by
    intro k
    induction k with
    | zero => decide
    | succ k ih =>
      have h1 : 2^(k+1) = 2^k * 2 := rfl
      rw [h1]
      generalize 2^k = X at *
      have h_pos : 1 ≤ X := by omega
      omega

  have lt_pow : ∀ k, 1 ≤ k → 2^k < 3^k := by
    intro k
    induction k with
    | zero => intro h; omega
    | succ k ih =>
      intro _
      have cases_k : k = 0 ∨ 1 ≤ k := by omega
      rcases cases_k with rfl | hk2
      · decide
      · have ih_lt := ih hk2
        have s1 : 2^k * 2 < 3^k * 2 := by
          generalize 2^k = X at *
          generalize 3^k = Y at *
          omega
        have s2 : 3^k * 2 ≤ 3^k * 3 := by
          generalize 3^k = Y at *
          omega
        calc 2^(k+1) = 2^k * 2 := rfl
          _ < 3^k * 2 := s1
          _ ≤ 3^k * 3 := s2
          _ = 3^(k+1) := rfl

  have le_pow : ∀ k, 3^k ≤ 5^k := by
    intro k
    induction k with
    | zero => decide
    | succ k ih =>
      have s1 : 3^k * 3 ≤ 5^k * 3 := by
        generalize 3^k = X at *
        generalize 5^k = Y at *
        omega
      have s2 : 5^k * 3 ≤ 5^k * 5 := by
        generalize 5^k = Y at *
        omega
      calc 3^(k+1) = 3^k * 3 := rfl
        _ ≤ 5^k * 3 := s1
        _ ≤ 5^k * 5 := s2
        _ = 5^(k+1) := rfl

  have pow_add_lem : ∀ a b c : ℕ, a^(b+c) = a^b * a^c := by
    intro a b c
    induction c with
    | zero =>
      have h : b + 0 = b := rfl
      rw [h]
      have h2 : a^0 = 1 := rfl
      rw [h2, mul_one]
    | succ c ih =>
      have h1 : b + (c + 1) = (b + c) + 1 := by omega
      rw [h1]
      have h2 : a^((b+c)+1) = a^(b+c) * a := rfl
      have h3 : a^(c+1) = a^c * a := rfl
      rw [h2, ih, h3]
      ring

  have cases_uv : u + v = 0 ∨ 1 ≤ u + v := by omega
  rcases cases_uv with huv_zero | huv_pos
  · have hu : u = 0 := by omega
    have hv : v = 0 := by omega
    rw [hu, hv] at hm
    have h_m : m = m' := by
      have h1 : 3^0 = 1 := rfl
      have h2 : 5^0 = 1 := rfl
      rw [h1, h2] at hm
      calc m = 1 * 1 * m' := hm
        _ = m' := by ring
    have hm'_gt_1 : 1 < m' := by omega
    have h_tot_lt : Nat.totient m' < m' := by
      apply Nat.totient_lt
      exact hm'_gt_1
    calc (u + v + 1) * Nat.totient m' = (0 + 0 + 1) * Nat.totient m' := by rw [hu, hv]
      _ = 1 * Nat.totient m' := rfl
      _ = Nat.totient m' := by rw [one_mul]
      _ < m' := h_tot_lt
      _ = m := h_m.symm

  · have step1 : u + v + 1 ≤ 2^(u+v) := lt_two_pow (u+v)
    have step2 : 2^(u+v) < 3^(u+v) := lt_pow (u+v) huv_pos
    have step3 : 3^(u+v) = 3^u * 3^v := pow_add_lem 3 u v
    have step4 : 3^v ≤ 5^v := le_pow v
    have step5 : 3^u * 3^v ≤ 3^u * 5^v := Nat.mul_le_mul_left (3^u) step4
    have step6 : u + v + 1 < 3^u * 5^v := by
      calc u + v + 1 ≤ 2^(u+v) := step1
        _ < 3^(u+v) := step2
        _ = 3^u * 3^v := step3
        _ ≤ 3^u * 5^v := step5
    have step7 : (u + v + 1) * m' < (3^u * 5^v) * m' := Nat.mul_lt_mul_of_pos_right step6 hm'0
    have tot_le : Nat.totient m' ≤ m' := by apply Nat.totient_le
    have step8 : (u + v + 1) * Nat.totient m' ≤ (u + v + 1) * m' := Nat.mul_le_mul_left (u + v + 1) tot_le
    generalize (3^u * 5^v) * m' = RHS at *
    generalize (u + v + 1) * Nat.totient m' = A at *
    generalize (u + v + 1) * m' = B at *
    omega

theorem m_dvd_2025_sub_15 (u v m' n m : ℕ)
    (hm : m = 3^u * 5^v * m')
    (hn : n = (u + v + 1) * Nat.totient m')
    (hm'_pos : 0 < m')
    (hc : Nat.Coprime m' 135) :
    m ∣ (2025 ^ n - 15 ^ n) :=
by
  have h_totient_pos : 1 ≤ m'.totient := Nat.totient_pos.mpr hm'_pos

  have hu_le : u ≤ n := by
    rw [hn]
    calc u ≤ u + v + 1 := by omega
    _ = (u + v + 1) * 1 := by ring
    _ ≤ (u + v + 1) * m'.totient := Nat.mul_le_mul_left _ h_totient_pos

  have hv_le : v ≤ n := by
    rw [hn]
    calc v ≤ u + v + 1 := by omega
    _ = (u + v + 1) * 1 := by ring
    _ ≤ (u + v + 1) * m'.totient := Nat.mul_le_mul_left _ h_totient_pos

  have hm_dvd : m' ∣ 135^n - 1 := by
    have h_cases : m' = 1 ∨ 1 < m' := by omega
    rcases h_cases with rfl | hm1
    · exact one_dvd _
    · have h1 : Nat.Coprime 135 m' := hc.symm
      have h2 : 135 ^ m'.totient ≡ 1 [MOD m'] := Nat.ModEq.pow_totient h1
      have h3 : (135 ^ m'.totient) ^ (u + v + 1) ≡ 1 ^ (u + v + 1) [MOD m'] := Nat.ModEq.pow (u + v + 1) h2
      have h4 : 1 ^ (u + v + 1) = 1 := one_pow _
      rw [h4] at h3

      have h_mod : 135^n ≡ 1 [MOD m'] := by
        have h_pow_mul : 135 ^ n = (135 ^ m'.totient) ^ (u + v + 1) := by
          rw [hn, ← pow_mul]
          congr 1
          ring
        rw [h_pow_mul]
        exact h3

      have h_mod_eq : 135^n % m' = 1 := by
        have h_step : 135^n % m' = 1 % m' := h_mod
        have h_one_mod : 1 % m' = 1 := Nat.mod_eq_of_lt hm1
        rw [h_one_mod] at h_step
        exact h_step

      have h_div_mod : 135^n = m' * (135^n / m') + 135^n % m' := (Nat.div_add_mod (135^n) m').symm
      rw [h_mod_eq] at h_div_mod
      have h_eq : 135^n - 1 = m' * (135^n / m') := by omega
      exact ⟨135^n / m', h_eq⟩

  have h_u_dvd : 3^u ∣ 3^n := pow_dvd_pow 3 hu_le

  have h_v_dvd : 5^v ∣ 5^n := pow_dvd_pow 5 hv_le

  have h_uv_dvd : 3^u * 5^v ∣ 3^n * 5^n := mul_dvd_mul h_u_dvd h_v_dvd
  have h_uvm_dvd : 3^u * 5^v * m' ∣ 3^n * 5^n * (135^n - 1) := mul_dvd_mul h_uv_dvd hm_dvd

  have h_sub : 2025^n - 15^n = 3^n * 5^n * (135^n - 1) := by
    have h1 : 2025^n = 15^n * 135^n := by
      have h_prod : 2025 = 15 * 135 := rfl
      rw [h_prod, mul_pow]
    have h2 : 15^n = 3^n * 5^n := by
      have h_prod : 15 = 3 * 5 := rfl
      rw [h_prod, mul_pow]
    have h3 : 15^n * 135^n - 15^n = 15^n * (135^n - 1) := by
      have h3_eq : 15^n * 135^n - 15^n = 15^n * 135^n - 15^n * 1 := by rw [mul_one]
      rw [h3_eq]
      exact (Nat.mul_sub_left_distrib (15^n) (135^n) 1).symm
    rw [h1, h3, h2]

  rw [hm, h_sub]
  exact h_uvm_dvd

theorem m'_pos_of_m_pos {u v m' m : ℕ} (hm : m = 3^u * 5^v * m') (hm_pos : 0 < m) : 0 < m' :=
by
  cases m'
  · rw [hm] at hm_pos
    simp only [mul_zero] at hm_pos
    omega
  · omega

theorem totient_pos_of_pos {n : ℕ} (hn : 0 < n) : 0 < Nat.totient n :=
Nat.totient_pos.mpr hn

theorem all_pos_in_S (S : Set ℕ) (h_nonempty : S.Nonempty) (h_pos : ∀ n ∈ S, 0 < n)
    (h_div : ∀ n ∈ S, ∀ d : ℕ, 0 < d → d ∣ (2025 ^ n - 15 ^ n) → d ∈ S) :
    ∀ m, 0 < m → m ∈ S :=
by
  intro k
  refine Nat.strong_induction_on k ?_
  intro m IH hm_pos
  obtain rfl | hm_gt_1 : m = 1 ∨ 1 < m := by omega
  · -- Base case (m = 1) cleanly extracted using the Nonempty condition of S
    exact one_in_S S h_nonempty h_pos h_div
  · -- Inductive Step (m > 1) utilizing the strict background graph lemmas
    obtain ⟨u, v, m', hm_eq, h_coprime_15⟩ := extract_3_5 m hm_pos
    have hm'_pos : 0 < m' := m'_pos_of_m_pos hm_eq hm_pos
    have h_coprime_135 : Nat.Coprime m' 135 := coprime_135_of_coprime_15 h_coprime_15

    let n := (u + v + 1) * Nat.totient m'
    have hn_eq : n = (u + v + 1) * Nat.totient m' := rfl

    -- Guarantee n Positivity
    have h_tot_pos : 0 < Nat.totient m' := totient_pos_of_pos hm'_pos
    have h_uv1_pos : 0 < u + v + 1 := by omega
    have hn_pos : 0 < n := by
      first
      | exact Nat.mul_pos h_uv1_pos h_tot_pos
      | exact mul_pos h_uv1_pos h_tot_pos

    -- Applying specific bounds and properties mappings
    have hn_lt_m : n < m := n_lt_m_unified u v m' m hm_eq hm_gt_1 h_coprime_15
    have hn_in_S : n ∈ S := IH n hn_lt_m hn_pos
    have h_m_dvd : m ∣ (2025 ^ n - 15 ^ n) := m_dvd_2025_sub_15 u v m' n m hm_eq hn_eq hm'_pos h_coprime_135

    -- Closing logic strictly driven from the divisor closure property
    exact h_div n hn_in_S m hm_pos h_m_dvd

theorem putnam_2025_b3_lhs : putnam_2025_b3_solution :=
by
  rfl

theorem putnam_2025_b3 : putnam_2025_b3_solution ↔
    ∀ S : Set ℕ,
      S.Nonempty →
      (∀ n ∈ S, 0 < n) →
      (∀ n ∈ S, ∀ d : ℕ, 0 < d → d ∣ (2025 ^ n - 15 ^ n) → d ∈ S) →
      S = {n : ℕ | 0 < n} :=
by
  constructor
  · intro _ S h_nonempty h_pos h_div
    ext m
    constructor
    · intro hm
      exact h_pos m hm
    · intro hm
      exact all_pos_in_S S h_nonempty h_pos h_div m hm
  · intro _
    exact putnam_2025_b3_lhs
