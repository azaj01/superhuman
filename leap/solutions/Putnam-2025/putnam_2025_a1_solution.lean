import Mathlib
def P (m n : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | k + 1 => P m n k * Nat.gcd (2 * m k + 1) (2 * n k + 1)

theorem D_mul_P_eq_aux (m n : ℕ → ℕ) (hm : ∀ k : ℕ, 0 < m k) (hn : ∀ k : ℕ, 0 < n k)
  (h_coprime : ∀ k : ℕ, 0 < k → Nat.Coprime (m k) (n k))
  (h_recurrence : ∀ k : ℕ, ((m (k + 1) : ℚ) / (n (k + 1) : ℚ)) = (2 * (m k : ℚ) + 1) / (2 * (n k : ℚ) + 1))
  (k : ℕ) :
  ((m 0 : ℤ) - (n 0 : ℤ)).natAbs * 2 ^ k = ((m k : ℤ) - (n k : ℤ)).natAbs * P m n k :=
by
  induction k with
  | zero => rfl
  | succ k ih =>
    let A := m (k + 1)
    let B := n (k + 1)
    let X := 2 * m k + 1
    let Y := 2 * n k + 1
    let g := Nat.gcd X Y

    have hn_cross : A * Y = X * B := by
      have h_cross : (A : ℚ) * (Y : ℚ) = (X : ℚ) * (B : ℚ) := by
        have hr := h_recurrence k
        have hX : 2 * (m k : ℚ) + 1 = (X : ℚ) := by
          dsimp [X]
          push_cast
          rfl
        have hY : 2 * (n k : ℚ) + 1 = (Y : ℚ) := by
          dsimp [Y]
          push_cast
          rfl
        have hA : (m (k + 1) : ℚ) = (A : ℚ) := rfl
        have hB : (n (k + 1) : ℚ) = (B : ℚ) := rfl
        rw [hX, hY, hA, hB] at hr

        have hd1 : (B : ℚ) ≠ 0 := by
          have hB_pos : 0 < B := hn (k + 1)
          exact_mod_cast ne_of_gt hB_pos
        have hd2 : (Y : ℚ) ≠ 0 := by
          have hY_pos : 0 < Y := by dsimp [Y]; omega
          exact_mod_cast ne_of_gt hY_pos

        have h1 : (A : ℚ) / (B : ℚ) * ((B : ℚ) * (Y : ℚ)) = (X : ℚ) / (Y : ℚ) * ((B : ℚ) * (Y : ℚ)) := by rw [hr]

        have h2 : (A : ℚ) / (B : ℚ) * ((B : ℚ) * (Y : ℚ)) = (A : ℚ) * (Y : ℚ) := by
          calc (A : ℚ) / (B : ℚ) * ((B : ℚ) * (Y : ℚ))
            _ = ((A : ℚ) / (B : ℚ) * (B : ℚ)) * (Y : ℚ) := by rw [← mul_assoc]
            _ = (A : ℚ) * (Y : ℚ) := by rw [div_mul_cancel₀ _ hd1]

        have h3 : (X : ℚ) / (Y : ℚ) * ((B : ℚ) * (Y : ℚ)) = (X : ℚ) * (B : ℚ) := by
          calc (X : ℚ) / (Y : ℚ) * ((B : ℚ) * (Y : ℚ))
            _ = (X : ℚ) / (Y : ℚ) * ((Y : ℚ) * (B : ℚ)) := by rw [mul_comm (B : ℚ) (Y : ℚ)]
            _ = ((X : ℚ) / (Y : ℚ) * (Y : ℚ)) * (B : ℚ) := by rw [← mul_assoc]
            _ = (X : ℚ) * (B : ℚ) := by rw [div_mul_cancel₀ _ hd2]

        rw [h2, h3] at h1
        exact h1
      exact_mod_cast h_cross

    have h_A_dvd : A ∣ X * B := ⟨Y, hn_cross.symm⟩
    have hAB_coprime : Nat.Coprime A B := h_coprime (k + 1) (by omega)
    have h_A_dvd_X : A ∣ X := hAB_coprime.dvd_of_dvd_mul_right h_A_dvd

    let C := X / A
    have hXC : X = A * C := by
      have h1 : X / A * A = X := Nat.div_mul_cancel h_A_dvd_X
      calc X = X / A * A := h1.symm
           _ = A * (X / A) := Nat.mul_comm _ _

    have hAY : A * Y = A * (C * B) := by
      calc A * Y = X * B := hn_cross
           _ = (A * C) * B := by rw [hXC]
           _ = A * (C * B) := by rw [Nat.mul_assoc]

    have hA_pos : 0 < A := by exact hm (k + 1)
    have hY_eq2 : Y = B * C := by
      have h1 : Y = C * B := Nat.eq_of_mul_eq_mul_left hA_pos hAY
      rw [h1, Nat.mul_comm]

    have hgcd : Nat.gcd A B = 1 := hAB_coprime
    have hg_eq : g = C := by
      calc g = Nat.gcd X Y := rfl
           _ = Nat.gcd (A * C) (B * C) := by rw [hXC, hY_eq2]
           _ = Nat.gcd (C * A) (C * B) := by
             have e1 : A * C = C * A := Nat.mul_comm A C
             have e2 : B * C = C * B := Nat.mul_comm B C
             rw [e1, e2]
           _ = C * Nat.gcd A B := Nat.gcd_mul_left C A B
           _ = C * 1 := by rw [hgcd]
           _ = C := Nat.mul_one C

    have hX_final : 2 * m k + 1 = A * g := by
      calc 2 * m k + 1 = X := rfl
           _ = A * C := hXC
           _ = A * g := by rw [hg_eq]

    have hY_final : 2 * n k + 1 = B * g := by
      calc 2 * n k + 1 = Y := rfl
           _ = B * C := hY_eq2
           _ = B * g := by rw [hg_eq]

    have hX_Z : (2 * (m k : ℤ) + 1) = (A : ℤ) * (g : ℤ) := by
      have h2 : (( (2 * m k + 1 : ℕ) ) : ℤ) = ((A * g : ℕ) : ℤ) := congrArg Nat.cast hX_final
      push_cast at h2
      exact h2

    have hY_Z : (2 * (n k : ℤ) + 1) = (B : ℤ) * (g : ℤ) := by
      have h2 : (( (2 * n k + 1 : ℕ) ) : ℤ) = ((B * g : ℕ) : ℤ) := congrArg Nat.cast hY_final
      push_cast at h2
      exact h2

    have h_sub : (2 * (m k : ℤ) + 1) - (2 * (n k : ℤ) + 1) = (A : ℤ) * (g : ℤ) - (B : ℤ) * (g : ℤ) := by
      rw [hX_Z, hY_Z]

    have h_sub_simp1 : (2 * (m k : ℤ) + 1) - (2 * (n k : ℤ) + 1) = 2 * ((m k : ℤ) - (n k : ℤ)) := by ring
    have h_sub_simp2 : (A : ℤ) * (g : ℤ) - (B : ℤ) * (g : ℤ) = ((A : ℤ) - (B : ℤ)) * (g : ℤ) := by ring
    rw [h_sub_simp1, h_sub_simp2] at h_sub

    have h_abs_eq : (2 * ((m k : ℤ) - (n k : ℤ))).natAbs = (((A : ℤ) - (B : ℤ)) * (g : ℤ)).natAbs := by
      rw [h_sub]

    have h_abs1 : (2 * ((m k : ℤ) - (n k : ℤ))).natAbs = 2 * ((m k : ℤ) - (n k : ℤ)).natAbs := by
      calc (2 * ((m k : ℤ) - (n k : ℤ))).natAbs
        _ = (2 : ℤ).natAbs * ((m k : ℤ) - (n k : ℤ)).natAbs := Int.natAbs_mul 2 _
        _ = 2 * ((m k : ℤ) - (n k : ℤ)).natAbs := rfl

    have h_abs2 : (((A : ℤ) - (B : ℤ)) * (g : ℤ)).natAbs = ((A : ℤ) - (B : ℤ)).natAbs * g := by
      calc (((A : ℤ) - (B : ℤ)) * (g : ℤ)).natAbs
        _ = ((A : ℤ) - (B : ℤ)).natAbs * (g : ℤ).natAbs := Int.natAbs_mul _ _
        _ = ((A : ℤ) - (B : ℤ)).natAbs * g := rfl

    have h_abs : 2 * ((m k : ℤ) - (n k : ℤ)).natAbs = ((A : ℤ) - (B : ℤ)).natAbs * g := by
      rw [← h_abs1, ← h_abs2]
      exact h_abs_eq

    calc ((m 0 : ℤ) - (n 0 : ℤ)).natAbs * 2 ^ (k + 1)
      _ = ((m 0 : ℤ) - (n 0 : ℤ)).natAbs * (2 ^ k * 2) := by rw [pow_add, pow_one]
      _ = ((m 0 : ℤ) - (n 0 : ℤ)).natAbs * 2 ^ k * 2 := by rw [← Nat.mul_assoc]
      _ = (((m k : ℤ) - (n k : ℤ)).natAbs * P m n k) * 2 := by rw [ih]
      _ = (2 * ((m k : ℤ) - (n k : ℤ)).natAbs) * P m n k := by ring
      _ = (((A : ℤ) - (B : ℤ)).natAbs * g) * P m n k := by rw [h_abs]
      _ = ((A : ℤ) - (B : ℤ)).natAbs * (P m n k * g) := by ring
      _ = ((m (k + 1) : ℤ) - (n (k + 1) : ℤ)).natAbs * P m n (k + 1) := rfl

theorem coprime_P_two_aux (m n : ℕ → ℕ) (k : ℕ) :
  Nat.Coprime (P m n k) 2 :=
by
  induction k with
  | zero =>
    change Nat.gcd 1 2 = 1
    rfl
  | succ k ih =>
    have H : Odd (2 * m k + 1) := ⟨m k, rfl⟩
    have H2 : Nat.Coprime (2 * m k + 1) 2 := Odd.coprime_two_right H
    have H3 : Nat.Coprime (Nat.gcd (2 * m k + 1) (2 * n k + 1)) 2 :=
      Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_left _ _) H2
    exact Nat.Coprime.mul ih H3

theorem P_dvd_D0 (m n : ℕ → ℕ) (hm : ∀ k : ℕ, 0 < m k) (hn : ∀ k : ℕ, 0 < n k)
  (h_coprime : ∀ k : ℕ, 0 < k → Nat.Coprime (m k) (n k))
  (h_recurrence : ∀ k : ℕ, ((m (k + 1) : ℚ) / (n (k + 1) : ℚ)) = (2 * (m k : ℚ) + 1) / (2 * (n k : ℚ) + 1))
  (k : ℕ) :
  P m n k ∣ ((m 0 : ℤ) - (n 0 : ℤ)).natAbs :=
by
  -- 1. Instantiate the equality linking D₀, 2^k, Dₖ, and P(k)
  have h1 : ((m 0 : ℤ) - (n 0 : ℤ)).natAbs * 2 ^ k = ((m k : ℤ) - (n k : ℤ)).natAbs * P m n k :=
    D_mul_P_eq_aux m n hm hn h_coprime h_recurrence k

  -- 2. Commute the RHS to match the definition of divisibility exactly
  have h2 : ((m 0 : ℤ) - (n 0 : ℤ)).natAbs * 2 ^ k = P m n k * ((m k : ℤ) - (n k : ℤ)).natAbs :=
    Eq.trans h1 (Nat.mul_comm (((m k : ℤ) - (n k : ℤ)).natAbs) (P m n k))

  -- 3. Extract the Divisibility Fact: P(k) ∣ D₀ * 2^k
  have h3 : P m n k ∣ ((m 0 : ℤ) - (n 0 : ℤ)).natAbs * 2 ^ k :=
    ⟨((m k : ℤ) - (n k : ℤ)).natAbs, h2⟩

  -- 4. Establish coprimality relations using our auxiliary lemma
  have h4 : Nat.Coprime (P m n k) 2 :=
    coprime_P_two_aux m n k

  -- 5. Extend the coprimality property to 2^k
  have h5 : Nat.Coprime (P m n k) (2 ^ k) :=
    Nat.Coprime.pow_right k h4

  -- 6. Final deduction using the theorem: if `a ∣ b * c` and `gcd(a, c) = 1`, then `a ∣ b`
  exact Nat.Coprime.dvd_of_dvd_mul_right h5 h3

theorem lemma7_P_le_diff0 (m n : ℕ → ℕ)
  (hm : ∀ k : ℕ, 0 < m k) (hn : ∀ k : ℕ, 0 < n k)
  (h_distinct : m 0 ≠ n 0)
  (h_coprime : ∀ k : ℕ, 0 < k → Nat.Coprime (m k) (n k))
  (h_recurrence : ∀ k : ℕ, ((m (k + 1) : ℚ) / (n (k + 1) : ℚ)) = (2 * (m k : ℚ) + 1) / (2 * (n k : ℚ) + 1))
  (k : ℕ) :
  P m n k ≤ ((m 0 : ℤ) - (n 0 : ℤ)).natAbs :=
by
  -- Because `m 0` and `n 0` are distinct, the absolute value of their integer difference is strictly greater than 0.
  have h_pos : 0 < ((m 0 : ℤ) - (n 0 : ℤ)).natAbs := by omega
  -- Based on the previously established lemma, `P m n k` divides this absolute difference.
  have h_dvd : P m n k ∣ ((m 0 : ℤ) - (n 0 : ℤ)).natAbs :=
    P_dvd_D0 m n hm hn h_coprime h_recurrence k
  -- Finally, applying the general property of natural numbers that if `a | b` and `b > 0`, then `a ≤ b`.
  exact Nat.le_of_dvd h_pos h_dvd

theorem lemma8_two_pow_le_P (m n : ℕ → ℕ) (k : ℕ) :
  2 ^ (Finset.filter (fun i => ¬Nat.Coprime (2 * m i + 1) (2 * n i + 1)) (Finset.range k)).card ≤ P m n k :=
by
  induction k with
  | zero =>
    have h1 : P m n 0 = 1 := rfl
    have h2 : Finset.range 0 = ∅ := Finset.range_zero
    rw [h1, h2, Finset.filter_empty, Finset.card_empty, pow_zero]
  | succ k ih =>
    have hp : P m n (k + 1) = P m n k * Nat.gcd (2 * m k + 1) (2 * n k + 1) := rfl
    rw [hp]
    have h_succ : Finset.range (k + 1) = insert k (Finset.range k) := Finset.range_succ
    rw [h_succ]
    have h_not_mem : k ∉ Finset.filter (fun i => ¬Nat.Coprime (2 * m i + 1) (2 * n i + 1)) (Finset.range k) := by
      intro h_mem
      rw [Finset.mem_filter] at h_mem
      have h_mem_range := h_mem.1
      rw [Finset.mem_range] at h_mem_range
      omega

    by_cases h : ¬Nat.Coprime (2 * m k + 1) (2 * n k + 1)
    · have h_filter_pos : Finset.filter (fun i => ¬Nat.Coprime (2 * m i + 1) (2 * n i + 1)) (insert k (Finset.range k)) =
        insert k (Finset.filter (fun i => ¬Nat.Coprime (2 * m i + 1) (2 * n i + 1)) (Finset.range k)) := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_insert]
        constructor
        · rintro ⟨h1 | h1, h2⟩
          · left; exact h1
          · right; exact ⟨h1, h2⟩
        · rintro (h1 | ⟨h1, h2⟩)
          · rw [h1]
            exact ⟨Or.inl rfl, h⟩
          · exact ⟨Or.inr h1, h2⟩
      rw [h_filter_pos]
      rw [Finset.card_insert_of_notMem h_not_mem]
      have h_pow : 2 ^ ((Finset.filter (fun i => ¬Nat.Coprime (2 * m i + 1) (2 * n i + 1)) (Finset.range k)).card + 1) =
        2 ^ (Finset.filter (fun i => ¬Nat.Coprime (2 * m i + 1) (2 * n i + 1)) (Finset.range k)).card * 2 := by rw [pow_add, pow_one]
      rw [h_pow]

      have h_gcd_neq_0 : Nat.gcd (2 * m k + 1) (2 * n k + 1) ≠ 0 := by
        intro h0
        have h_zero : 2 * m k + 1 = 0 := (Nat.gcd_eq_zero_iff.mp h0).1
        omega
      have h_gcd_neq_1 : Nat.gcd (2 * m k + 1) (2 * n k + 1) ≠ 1 := h
      have h_gcd : 2 ≤ Nat.gcd (2 * m k + 1) (2 * n k + 1) := by
        revert h_gcd_neq_0 h_gcd_neq_1
        generalize Nat.gcd (2 * m k + 1) (2 * n k + 1) = g
        intro h0 h1
        omega

      have h_P_le : P m n k ≤ P m n k := Nat.le_refl _
      have h1 : P m n k * 2 ≤ P m n k * Nat.gcd (2 * m k + 1) (2 * n k + 1) := Nat.mul_le_mul h_P_le h_gcd
      have h_two_le : 2 ≤ 2 := Nat.le_refl _
      have h2 : 2 ^ (Finset.filter (fun i => ¬Nat.Coprime (2 * m i + 1) (2 * n i + 1)) (Finset.range k)).card * 2 ≤ P m n k * 2 := Nat.mul_le_mul ih h_two_le
      exact Nat.le_trans h2 h1

    · have h_filter_neg : Finset.filter (fun i => ¬Nat.Coprime (2 * m i + 1) (2 * n i + 1)) (insert k (Finset.range k)) =
        Finset.filter (fun i => ¬Nat.Coprime (2 * m i + 1) (2 * n i + 1)) (Finset.range k) := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_insert]
        constructor
        · rintro ⟨h1 | h1, h2⟩
          · rw [h1] at h2
            exact False.elim (h h2)
          · exact ⟨h1, h2⟩
        · rintro ⟨h1, h2⟩
          exact ⟨Or.inr h1, h2⟩
      rw [h_filter_neg]

      have h_gcd_neq_0 : Nat.gcd (2 * m k + 1) (2 * n k + 1) ≠ 0 := by
        intro h0
        have h_zero : 2 * m k + 1 = 0 := (Nat.gcd_eq_zero_iff.mp h0).1
        omega
      have h_gcd : 1 ≤ Nat.gcd (2 * m k + 1) (2 * n k + 1) := by
        revert h_gcd_neq_0
        generalize Nat.gcd (2 * m k + 1) (2 * n k + 1) = g
        intro h0
        omega

      have h_P_le : P m n k ≤ P m n k := Nat.le_refl _
      have h1 : P m n k * 1 ≤ P m n k * Nat.gcd (2 * m k + 1) (2 * n k + 1) := Nat.mul_le_mul h_P_le h_gcd
      rw [mul_one] at h1
      exact Nat.le_trans ih h1

theorem lemma9_infinite_filter (p : ℕ → Prop) [DecidablePred p] (h : ¬ {k | p k}.Finite) (B : ℕ) :
  ∃ K : ℕ, B < (Finset.filter p (Finset.range K)).card :=
by
  classical
  by_contra h_contra
  push_neg at h_contra
  have hQ : ∃ c, ∀ K, (Finset.filter p (Finset.range K)).card ≤ c := ⟨B, h_contra⟩
  let c_min := Nat.find hQ
  have hc_min : ∀ K, (Finset.filter p (Finset.range K)).card ≤ c_min := Nat.find_spec hQ
  have h_exists : ∃ K_0, (Finset.filter p (Finset.range K_0)).card = c_min := by
    by_cases hc : c_min = 0
    · use 0
      have h0 := hc_min 0
      omega
    · have h_lt : c_min - 1 < c_min := by omega
      have h_not : ¬ ∀ K, (Finset.filter p (Finset.range K)).card ≤ c_min - 1 := Nat.find_min hQ h_lt
      push_neg at h_not
      obtain ⟨K, hK⟩ := h_not
      use K
      have := hc_min K
      omega
  obtain ⟨K_0, hK_0⟩ := h_exists
  have h_no_p : ∀ x ≥ K_0, ¬ p x := by
    intro x hx hp
    have h_K0_le : Finset.filter p (Finset.range K_0) ⊆ Finset.filter p (Finset.range x) := by
      intro a ha
      rw [Finset.mem_filter, Finset.mem_range] at ha ⊢
      obtain ⟨ha_lt, ha_p⟩ := ha
      refine ⟨by omega, ha_p⟩
    have h_card1 : c_min ≤ (Finset.filter p (Finset.range x)).card := by
      rw [← hK_0]
      exact Finset.card_le_card h_K0_le
    have h_card_x : (Finset.filter p (Finset.range x)).card = c_min := by
      have := hc_min x
      omega
    have h_x_mem : x ∈ Finset.filter p (Finset.range (x + 1)) := by
      rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, hp⟩
    have h_x_not_mem : x ∉ Finset.filter p (Finset.range x) := by
      rw [Finset.mem_filter, Finset.mem_range]
      push_neg
      intro h_lt
      omega
    have h_sub : insert x (Finset.filter p (Finset.range x)) ⊆ Finset.filter p (Finset.range (x + 1)) := by
      intro a ha
      rw [Finset.mem_insert] at ha
      rcases ha with rfl | ha
      · exact h_x_mem
      · rw [Finset.mem_filter, Finset.mem_range] at ha ⊢
        obtain ⟨ha_lt, ha_p⟩ := ha
        exact ⟨by omega, ha_p⟩
    have h_card3 : (insert x (Finset.filter p (Finset.range x))).card ≤ (Finset.filter p (Finset.range (x + 1))).card := Finset.card_le_card h_sub
    rw [Finset.card_insert_of_notMem h_x_not_mem] at h_card3
    have h_card4 : (Finset.filter p (Finset.range (x + 1))).card ≤ c_min := hc_min (x + 1)
    omega
  have h_eq : {k | p k} = ↑(Finset.filter p (Finset.range K_0)) := by
    ext x
    constructor
    · intro hpx
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
      have hx_lt : x < K_0 := by
        by_contra h_ge
        push_neg at h_ge
        exact h_no_p x h_ge hpx
      exact ⟨hx_lt, hpx⟩
    · intro hx
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hx
      obtain ⟨hx_lt, hpx⟩ := hx
      exact hpx
  have h_fin : {k | p k}.Finite := by
    rw [h_eq]
    exact Finset.finite_toSet (Finset.filter p (Finset.range K_0))
  exact h h_fin

theorem lemma10_two_pow_gt (C : ℕ) : C < 2 ^ C :=
by
  induction C with
  | zero =>
    change 0 < 1
    omega
  | succ k hk =>
    change k + 1 < 2 ^ k * 2
    omega

theorem putnam_2025_a1 (m n : ℕ → ℕ)
  (hm : ∀ k : ℕ, 0 < m k)
  (hn : ∀ k : ℕ, 0 < n k)
  (h_distinct : m 0 ≠ n 0)
  (h_coprime : ∀ k : ℕ, 0 < k → Nat.Coprime (m k) (n k))
  (h_recurrence : ∀ k : ℕ,
    (m (k + 1) : ℚ) / (n (k + 1) : ℚ) = (2 * (m k : ℚ) + 1) / (2 * (n k : ℚ) + 1)) : {k : ℕ | ¬Nat.Coprime (2 * m k + 1) (2 * n k + 1)}.Finite :=
by
  by_contra h_inf

  -- S := {k : ℕ | ¬Nat.Coprime (2 * m k + 1) (2 * n k + 1)}
  -- We assume ¬ S.Finite, meaning the set of such indices is infinite.

  -- Let B = |m_0 - n_0|
  let B := ((m 0 : ℤ) - (n 0 : ℤ)).natAbs

  -- Obtain an index K such that the number of elements in S strictly before K exceeds B
  have h_ex : ∃ K : ℕ, B < (Finset.filter (fun i => ¬Nat.Coprime (2 * m i + 1) (2 * n i + 1)) (Finset.range K)).card :=
    lemma9_infinite_filter (fun i => ¬Nat.Coprime (2 * m i + 1) (2 * n i + 1)) h_inf B

  obtain ⟨K, hK⟩ := h_ex

  -- Map out the mathematical bounds established by the problem's mechanics
  have h1 : 2 ^ (Finset.filter (fun i => ¬Nat.Coprime (2 * m i + 1) (2 * n i + 1)) (Finset.range K)).card ≤ P m n K :=
    lemma8_two_pow_le_P m n K

  have h2 : P m n K ≤ B :=
    lemma7_P_le_diff0 m n hm hn h_distinct h_coprime h_recurrence K

  have h3 : (Finset.filter (fun i => ¬Nat.Coprime (2 * m i + 1) (2 * n i + 1)) (Finset.range K)).card < 2 ^ (Finset.filter (fun i => ¬Nat.Coprime (2 * m i + 1) (2 * n i + 1)) (Finset.range K)).card :=
    lemma10_two_pow_gt _

  -- Given `B < card < 2^card ≤ P ≤ B`, this forms a strict contradictory cycle `B < B`.
  -- `omega` naturally unwinds and resolves integer linear arithmetic of definitions & variable applications like this.
  omega
