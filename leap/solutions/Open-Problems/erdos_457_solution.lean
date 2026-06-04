import Mathlib
open scoped Classical
def t_primes (m : ℕ) : Finset ℕ :=
  (Finset.Ioc (2 * m) (3 * m)).filter Nat.Prime
noncomputable def c_m (m : ℕ) : ℕ :=
  ⌊(3 * (m : ℝ)) / (5 : ℝ)⌋₊
noncomputable def k_m (m : ℕ) : ℕ :=
  if h : ∃ (k : ℕ), k ∈ Finset.Icc 1 (6 ^ (t_primes m).card) ∧ ∀ a ∈ t_primes m, ∃ l : ℤ, |(k : ℝ) * ((Nat.choose (2 * m) m : ℝ) / (a : ℝ)) - (l : ℝ)| ≤ (1 : ℝ) / (6 : ℝ)
  then Classical.choose h
  else 1
noncomputable def n_m (m : ℕ) : ℕ :=
  Int.toNat ((k_m m : ℤ) * (Nat.choose (2 * m) m : ℤ) - (c_m m : ℤ))
noncomputable def L_m (m : ℕ) : ℕ :=
  ⌊Real.log (n_m m)⌋₊

noncomputable def dirichlet_box_idx (x : ℝ) (Q : ℕ) : ℕ := ⌊Int.fract x * (Q : ℝ)⌋₊

theorem m_ge_one_eventually : ∀ᶠ (m : ℕ) in Filter.atTop, 1 ≤ m :=
by
  apply Filter.eventually_atTop.mpr
  exact ⟨1, fun b hb => hb⟩

theorem c_m_val (m : ℕ) : c_m m = ⌊(3 * (m : ℝ)) / (5 : ℝ)⌋₊ :=
rfl

theorem c_m_le_m (m : ℕ) : c_m m ≤ m :=
by
  have h : (c_m m : ℝ) ≤ (m : ℝ) := by
    rw [c_m_val m]
    have h1 : (0 : ℝ) ≤ (3 * (m : ℝ)) / (5 : ℝ) := by positivity
    have h2 : (⌊(3 * (m : ℝ)) / (5 : ℝ)⌋₊ : ℝ) ≤ (3 * (m : ℝ)) / (5 : ℝ) := Nat.floor_le h1
    have hm : (0 : ℝ) ≤ (m : ℝ) := by positivity
    have h3 : (3 * (m : ℝ)) / (5 : ℝ) ≤ (m : ℝ) := by linarith
    exact le_trans h2 h3
  exact_mod_cast h

theorem choose_two_mul_succ (m : ℕ) : Nat.choose (2 * m + 2) (m + 1) = 2 * Nat.choose (2 * m + 1) m :=
by
  -- Rewrite `2 * m + 2` as `2 * m + 1 + 1` to apply Pascal's rule
  have h1 : 2 * m + 2 = 2 * m + 1 + 1 := by omega
  rw [h1]

  -- Apply Pascal's rule: choose(n+1, k+1) = choose(n, k) + choose(n, k+1)
  rw [Nat.choose_succ_succ' (2 * m + 1) m]

  -- Use the symmetry of binomial coefficients to show choose(2m+1, m+1) = choose(2m+1, m)
  have h_symm : Nat.choose (2 * m + 1) (m + 1) = Nat.choose (2 * m + 1) m := by
    have h_le : m + 1 ≤ 2 * m + 1 := by omega
    have h_choose := Nat.choose_symm h_le
    have h_sub : 2 * m + 1 - (m + 1) = m := by omega
    rw [h_sub] at h_choose
    exact h_choose.symm

  -- Substitute the symmetry result back and close the arithmetic goal
  rw [h_symm]
  omega

theorem m_le_choose_two_mul_m (m : ℕ) : m ≤ Nat.choose (2 * m) m :=
by
  induction m with
  | zero => exact Nat.zero_le _
  | succ m ih =>
    by_cases h : m = 0
    · -- Base case inside the induction where m = 0 (so original is m = 1)
      subst h
      -- Shift the goal visually into exact constant integers for `omega` to easily solve
      change 1 ≤ Nat.choose 2 1
      have h_val : Nat.choose 2 1 = 2 := rfl
      omega
    · -- Inductive branch where m > 0 (so original m ≥ 2)
      -- Normalize `Nat.succ m` uniformly into `m + 1` for `omega` and `rw` to parse seamlessly
      change m + 1 ≤ Nat.choose (2 * (m + 1)) (m + 1)
      have h_pos : 0 < m := by omega

      -- Mathlib property: Nat.choose is monotonic over the top coefficient
      have h_le : Nat.choose (2 * m) m ≤ Nat.choose (2 * m + 1) m := Nat.choose_le_succ (2 * m) m

      -- Connecting the binomial structures using our prior lemma
      have h_eq : Nat.choose (2 * (m + 1)) (m + 1) = 2 * Nat.choose (2 * m + 1) m := by
        have h_step : 2 * (m + 1) = 2 * m + 2 := by omega
        rw [h_step, choose_two_mul_succ m]

      -- The Presburger arithmetic core solver automatically handles constants mixed with abstracted variables
      omega

theorem one_le_k_m (m : ℕ) : 1 ≤ k_m m :=
by
  unfold k_m
  split_ifs with h
  · have h_spec := Classical.choose_spec h
    have h_mem := h_spec.1
    rw [Finset.mem_Icc] at h_mem
    exact h_mem.1
  · exact le_rfl

theorem c_m_le_k_m_mul_A_m (m : ℕ) :
  c_m m ≤ k_m m * Nat.choose (2 * m) m :=
by
  have h1 : c_m m ≤ m := c_m_le_m m
  have h2 : m ≤ Nat.choose (2 * m) m := m_le_choose_two_mul_m m
  have h3 : c_m m ≤ Nat.choose (2 * m) m := Nat.le_trans h1 h2
  have h4 : 1 ≤ k_m m := one_le_k_m m
  have h5 : Nat.choose (2 * m) m ≤ k_m m * Nat.choose (2 * m) m := by
    have h_mul := Nat.mul_le_mul_right (Nat.choose (2 * m) m) h4
    rw [Nat.one_mul] at h_mul
    exact h_mul
  exact Nat.le_trans h3 h5

theorem n_m_add_c_m (m : ℕ) : n_m m + c_m m = k_m m * Nat.choose (2 * m) m :=
by
  have h := c_m_le_k_m_mul_A_m m
  unfold n_m
  omega

theorem n_m_real_eq (m : ℕ) :
  (n_m m : ℝ) = (k_m m : ℝ) * (Nat.choose (2 * m) m : ℝ) - (c_m m : ℝ) :=
by
  have h : (n_m m : ℝ) + (c_m m : ℝ) = (k_m m : ℝ) * (Nat.choose (2 * m) m : ℝ) := by
    exact_mod_cast n_m_add_c_m m
  linarith

theorem c_m_le_real (m : ℕ) :
  (c_m m : ℝ) ≤ (3 * (m : ℝ)) / (5 : ℝ) :=
by
  rw [c_m_val]
  exact Nat.floor_le (by positivity)

theorem sum_choose_eq_two_pow_real_aux (m : ℕ) :
  ∑ k ∈ Finset.range (2 * m + 1), (Nat.choose (2 * m) k : ℝ) = (2 : ℝ) ^ (2 * m) :=
by
  have h := add_pow (1 : ℝ) (1 : ℝ) (2 * m)
  simp only [one_pow, mul_one, one_mul] at h
  rw [← h]
  norm_num

theorem four_pow_eq_two_pow_two_mul_aux (m : ℕ) :
  (4 : ℝ) ^ m = (2 : ℝ) ^ (2 * m) :=
by
  have h : (4 : ℝ) = (2 : ℝ) ^ 2 := by norm_num
  rw [h]
  exact (pow_mul (2 : ℝ) 2 m).symm

theorem sum_choose_eq_four_pow_real (m : ℕ) :
  ∑ k ∈ Finset.range (2 * m + 1), (Nat.choose (2 * m) k : ℝ) = (4 : ℝ) ^ m :=
by
  rw [four_pow_eq_two_pow_two_mul_aux m]
  exact sum_choose_eq_two_pow_real_aux m

theorem real_choose_le_central (m k : ℕ) : (Nat.choose (2 * m) k : ℝ) ≤ (Nat.choose (2 * m) m : ℝ) :=
by
  have h := Nat.choose_le_middle k (2 * m)
  have hw : (2 * m) / 2 = m := by omega
  rw [hw] at h
  exact_mod_cast h

theorem sum_const_real (m : ℕ) (x : ℝ) :
  ∑ k ∈ Finset.range (2 * m + 1), x = ((2 : ℝ) * (m : ℝ) + 1) * x :=
by
  -- Evaluate the constant sum, turning it into scalar multiplication.
  -- `simp` handles `Finset.sum_const` and `Finset.card_range`.
  -- We include `nsmul_eq_mul` to ensure the scalar multiplication is converted to real multiplication.
  -- The `simp` tactic will automatically push the type casts internally and close the goal using `rfl`.
  simp [nsmul_eq_mul]

theorem sum_choose_le_mul_choose (m : ℕ) :
  ∑ k ∈ Finset.range (2 * m + 1), (Nat.choose (2 * m) k : ℝ) ≤ ((2 : ℝ) * (m : ℝ) + 1) * (Nat.choose (2 * m) m : ℝ) :=
by
  have h1 : ∑ k ∈ Finset.range (2 * m + 1), (Nat.choose (2 * m) k : ℝ) ≤ ∑ k ∈ Finset.range (2 * m + 1), (Nat.choose (2 * m) m : ℝ) := by
    apply Finset.sum_le_sum
    intro k _
    exact real_choose_le_central m k
  have h2 : ∑ k ∈ Finset.range (2 * m + 1), (Nat.choose (2 * m) m : ℝ) = ((2 : ℝ) * (m : ℝ) + 1) * (Nat.choose (2 * m) m : ℝ) :=
    sum_const_real m (Nat.choose (2 * m) m : ℝ)
  rw [h2] at h1
  exact h1

theorem four_pow_div_le_choose (m : ℕ) :
  (4 : ℝ) ^ m / ((2 : ℝ) * (m : ℝ) + 1) ≤ (Nat.choose (2 * m) m : ℝ) :=
by
  have h_pos : (0 : ℝ) < (2 : ℝ) * (m : ℝ) + 1 := by positivity
  rw [div_le_iff₀ h_pos]
  rw [mul_comm]
  have h_eq := sum_choose_eq_four_pow_real m
  rw [← h_eq]
  exact sum_choose_le_mul_choose m

theorem k_m_mul_choose_ge (m : ℕ) (hm : 1 ≤ m) :
  (4 : ℝ) ^ m / ((2 : ℝ) * (m : ℝ) + 1) ≤ (k_m m : ℝ) * (Nat.choose (2 * m) m : ℝ) :=
by
  -- Obtain the fractional inequality bounded by the central binomial coefficient
  have h1 : (4 : ℝ) ^ m / ((2 : ℝ) * (m : ℝ) + 1) ≤ (Nat.choose (2 * m) m : ℝ) :=
    four_pow_div_le_choose m

  -- Use the lower bound of k_m which ensures k_m m ≥ 1
  have h2 : 1 ≤ k_m m := one_le_k_m m

  -- Push the k_m m ≥ 1 bound to the reals securely
  have h_le : (1 : ℝ) ≤ (k_m m : ℝ) := by exact_mod_cast h2

  -- Central binomial coefficient evaluates to a natural non-negative
  have h_nonneg : (0 : ℝ) ≤ (Nat.choose (2 * m) m : ℝ) := Nat.cast_nonneg _

  -- Multiply the inequalities: (1 : ℝ) * choose (...) ≤ (k_m m : ℝ) * choose (...)
  have h_mul := mul_le_mul_of_nonneg_right h_le h_nonneg

  -- Simplify out the 1 multiplier
  rw [one_mul] at h_mul

  -- Transitively link the fractional lowerbound to complete the proof
  exact le_trans h1 h_mul

theorem n_m_lower_bound (m : ℕ) (hm : 1 ≤ m) :
  (4 : ℝ) ^ m / ((2 : ℝ) * (m : ℝ) + 1) - (3 * (m : ℝ)) / (5 : ℝ) ≤ (n_m m : ℝ) :=
by
  have h1 := n_m_real_eq m
  have h2 := c_m_le_real m
  have h3 := k_m_mul_choose_ge m hm
  linarith

theorem term_lemma_1_algebra (m : ℕ) :
  (6 * (m : ℝ)) / (5 : ℝ) = (m : ℝ) * ((6 : ℝ) / (5 : ℝ)) :=
by
  ring

theorem exp_nat_mul (m : ℕ) (x : ℝ) :
  Real.exp ((m : ℝ) * x) = (Real.exp x) ^ m :=
by
  exact Real.exp_nat_mul x m

theorem term_lemma_1 (m : ℕ) :
  Real.exp ((6 * (m : ℝ)) / (5 : ℝ) + 1) = (Real.exp ((6 : ℝ) / (5 : ℝ))) ^ m * Real.exp (1 : ℝ) :=
by
  rw [term_lemma_1_algebra]
  rw [Real.exp_add]
  rw [exp_nat_mul]

theorem term_lemma_2 (m : ℕ) :
  (Real.exp ((6 : ℝ) / (5 : ℝ)) / (4 : ℝ)) ^ m = (Real.exp ((6 : ℝ) / (5 : ℝ))) ^ m / (4 : ℝ) ^ m :=
by
  exact div_pow (Real.exp ((6 : ℝ) / (5 : ℝ))) (4 : ℝ) m

theorem term_lemma_3_pow_simpl (m : ℕ) :
  (((1 : ℝ) / (2 : ℝ)) ^ m) * (((1 : ℝ) / (2 : ℝ)) ^ m) = (1 : ℝ) / (4 : ℝ) ^ m :=
by
  rw [← mul_pow]
  have h : ((1 : ℝ) / (2 : ℝ)) * ((1 : ℝ) / (2 : ℝ)) = (1 : ℝ) / (4 : ℝ) := by norm_num
  rw [h, div_pow, one_pow]

theorem term_lemma_3 (m : ℕ) :
  ((6 : ℝ) / (5 : ℝ)) * ((m : ℝ) * ((1 : ℝ) / (2 : ℝ)) ^ m) * ((m : ℝ) * ((1 : ℝ) / (2 : ℝ)) ^ m) =
  ((6 : ℝ) / (5 : ℝ)) * (m : ℝ) ^ 2 / (4 : ℝ) ^ m :=
by
  have h : ((6 : ℝ) / (5 : ℝ)) * ((m : ℝ) * ((1 : ℝ) / (2 : ℝ)) ^ m) * ((m : ℝ) * ((1 : ℝ) / (2 : ℝ)) ^ m) =
    (((6 : ℝ) / (5 : ℝ)) * (m : ℝ) ^ 2) * ((((1 : ℝ) / (2 : ℝ)) ^ m) * (((1 : ℝ) / (2 : ℝ)) ^ m)) := by ring
  rw [h]
  rw [term_lemma_3_pow_simpl m]
  ring

theorem term_lemma_4 (m : ℕ) :
  ((3 : ℝ) / (5 : ℝ)) * ((m : ℝ) * ((1 : ℝ) / (4 : ℝ)) ^ m) =
  ((3 : ℝ) / (5 : ℝ)) * (m : ℝ) / (4 : ℝ) ^ m :=
by
  rw [div_pow, one_pow]
  ring

theorem term_decomposition (m : ℕ) :
  ((2 : ℝ) * (m : ℝ) + 1) * Real.exp ((6 * (m : ℝ)) / (5 : ℝ) + 1) / (4 : ℝ) ^ m +
  ((2 : ℝ) * (m : ℝ) + 1) * ((3 * (m : ℝ)) / (5 : ℝ)) / (4 : ℝ) ^ m =
  (2 : ℝ) * Real.exp (1 : ℝ) * ((m : ℝ) * (Real.exp ((6 : ℝ) / (5 : ℝ)) / (4 : ℝ)) ^ m) +
  Real.exp (1 : ℝ) * (Real.exp ((6 : ℝ) / (5 : ℝ)) / (4 : ℝ)) ^ m +
  ((6 : ℝ) / (5 : ℝ)) * ((m : ℝ) * ((1 : ℝ) / (2 : ℝ)) ^ m) * ((m : ℝ) * ((1 : ℝ) / (2 : ℝ)) ^ m) +
  ((3 : ℝ) / (5 : ℝ)) * ((m : ℝ) * ((1 : ℝ) / (4 : ℝ)) ^ m) :=
by
  rw [term_lemma_1 m, term_lemma_2 m, term_lemma_3 m, term_lemma_4 m]
  ring

theorem exp_log_four :
  Real.exp (Real.log (4 : ℝ)) = (4 : ℝ) :=
by
  apply Real.exp_log
  norm_num

theorem five_mul_six_fifths : ((5 : ℕ) : ℝ) * ((6 : ℝ) / (5 : ℝ)) = (6 : ℝ) :=
by
  norm_num

theorem exp_six_fifths_pow_five :
  (Real.exp ((6 : ℝ) / (5 : ℝ))) ^ 5 = Real.exp (6 : ℝ) :=
by
  -- Convert (e^x)^n to e^(n * x)
  rw [← Real.exp_nat_mul ((6 : ℝ) / (5 : ℝ)) 5]
  -- Strip the outer `Real.exp` from both sides
  congr 1
  -- The remaining goal is exactly our helper lemma
  exact five_mul_six_fifths

theorem pow_five_lt_pow_five (x y : ℝ) (h : x ^ 5 < y ^ 5) : x < y :=
by
  -- 5 is an odd number since 5 = 2 * 2 + 1
  have h_odd : Odd 5 := ⟨2, rfl⟩
  -- Apply the left direction of the equivalence for odd powers
  exact (Odd.pow_lt_pow h_odd).mp h

theorem exp_six_eq_pow_six : Real.exp (6 : ℝ) = (Real.exp (1 : ℝ)) ^ 6 :=
by
  -- Rewrite the RHS using Mathlib's exponential exponentiation rule
  -- This replaces (Real.exp 1) ^ 6 with Real.exp (↑6 * 1)
  rw [← Real.exp_nat_mul (1 : ℝ) 6]

  -- The goal is now `Real.exp 6 = Real.exp (↑6 * 1)`.
  -- We strip the `Real.exp` function application from both sides.
  congr 1

  -- The remaining equality `6 = ↑6 * 1` over the reals is handled trivially by norm_num.
  norm_num

theorem exp_one_pos : (0 : ℝ) ≤ Real.exp (1 : ℝ) :=
Real.exp_nonneg (1 : ℝ)

theorem pow_six_lt_pow_six (x y : ℝ) (hx : 0 ≤ x) (h : x < y) : x ^ 6 < y ^ 6 :=
by
  gcongr

theorem three_pow_six_lt_four_pow_five : (3 : ℝ) ^ 6 < (4 : ℝ) ^ 5 :=
by
  norm_num

theorem exp_six_lt_four_pow_five : Real.exp (6 : ℝ) < (4 : ℝ) ^ 5 :=
by
  calc
    Real.exp (6 : ℝ) = (Real.exp (1 : ℝ)) ^ 6 := exp_six_eq_pow_six
    _ < (3 : ℝ) ^ 6 := pow_six_lt_pow_six (Real.exp (1 : ℝ)) (3 : ℝ) exp_one_pos Real.exp_one_lt_three
    _ < (4 : ℝ) ^ 5 := three_pow_six_lt_four_pow_five

theorem six_fifths_lt_log_four : (6 : ℝ) / (5 : ℝ) < Real.log (4 : ℝ) :=
by
  -- Convert `a < b` into `exp a < exp b` using monotonicity of exp
  rw [← Real.exp_lt_exp]

  -- Simplify `exp (log 4)` to `4`
  rw [exp_log_four]

  -- Reduce the problem to comparing their 5th powers
  apply pow_five_lt_pow_five

  -- Simplify `(exp (6/5))^5` to `exp 6`
  rw [exp_six_fifths_pow_five]

  -- Conclude using the fundamental arithmetic inequality `exp 6 < 4^5`
  exact exp_six_lt_four_pow_five

theorem exp_six_fifths_lt_four :
  Real.exp ((6 : ℝ) / (5 : ℝ)) < (4 : ℝ) :=
by
  have h : Real.exp ((6 : ℝ) / (5 : ℝ)) < Real.exp (Real.log (4 : ℝ)) :=
    Real.exp_lt_exp.mpr six_fifths_lt_log_four
  rw [exp_log_four] at h
  exact h

theorem abs_exp_six_fifths_div_four_lt_one : |Real.exp ((6 : ℝ) / (5 : ℝ)) / (4 : ℝ)| < (1 : ℝ) :=
by
  -- Real.exp(x) and 4 are both strictly positive, so the entire fraction is strictly positive.
  have h1 : (0 : ℝ) < Real.exp ((6 : ℝ) / (5 : ℝ)) / (4 : ℝ) := by positivity

  -- The absolute value is redundant because the content is > 0.
  rw [abs_of_pos h1]

  -- Use our upper bound lemma for the exponential term.
  have h2 := exp_six_fifths_lt_four

  -- Linarith can effortlessly solve X / 4 < 1 given that X < 4.
  linarith

theorem limit_part1_core :
  Filter.Tendsto (fun m : ℕ => (m : ℝ) * (Real.exp ((6 : ℝ) / (5 : ℝ)) / (4 : ℝ)) ^ m) Filter.atTop (nhds (0 : ℝ)) :=
by
  exact tendsto_self_mul_const_pow_of_abs_lt_one abs_exp_six_fifths_div_four_lt_one

theorem limit_part1 :
  Filter.Tendsto (fun m : ℕ => (2 : ℝ) * Real.exp (1 : ℝ) * ((m : ℝ) * (Real.exp ((6 : ℝ) / (5 : ℝ)) / (4 : ℝ)) ^ m))
  Filter.atTop (nhds (0 : ℝ)) :=
by
  have h := Filter.Tendsto.const_mul ((2 : ℝ) * Real.exp (1 : ℝ)) limit_part1_core
  simpa only [mul_zero] using h

theorem exp_six_fifths_div_four_pos : (0 : ℝ) < Real.exp ((6 : ℝ) / (5 : ℝ)) / (4 : ℝ) :=
by
  positivity

theorem exp_six_fifths_div_four_lt_one : Real.exp ((6 : ℝ) / (5 : ℝ)) / (4 : ℝ) < (1 : ℝ) :=
by
  have h_exp_1_lt : Real.exp (1 : ℝ) < 2.7182818286 := Real.exp_one_lt_d9
  have h_exp_1_lt_3 : Real.exp (1 : ℝ) < (3 : ℝ) := by linarith
  have h_exp_1_pos : (0 : ℝ) ≤ Real.exp (1 : ℝ) := exp_one_pos
  have h1 : Real.exp (6 : ℝ) = (Real.exp (1 : ℝ)) ^ 6 := exp_six_eq_pow_six
  have h2 : (Real.exp (1 : ℝ)) ^ 6 < (3 : ℝ) ^ 6 := by
    apply pow_six_lt_pow_six
    · exact h_exp_1_pos
    · exact h_exp_1_lt_3
  have h3 : (3 : ℝ) ^ 6 = 729 := by norm_num
  rw [h3] at h2
  have h4 : Real.exp (6 : ℝ) < 729 := by linarith
  have h5 : (729 : ℝ) < (4 : ℝ) ^ 5 := by norm_num
  have h6 : Real.exp (6 : ℝ) < (4 : ℝ) ^ 5 := by linarith
  have h7 : (Real.exp ((6 : ℝ) / (5 : ℝ))) ^ 5 = Real.exp (6 : ℝ) := exp_six_fifths_pow_five
  have h8 : (Real.exp ((6 : ℝ) / (5 : ℝ))) ^ 5 < (4 : ℝ) ^ 5 := by linarith
  have h9 : Real.exp ((6 : ℝ) / (5 : ℝ)) < (4 : ℝ) :=
    pow_five_lt_pow_five (Real.exp ((6 : ℝ) / (5 : ℝ))) (4 : ℝ) h8
  linarith

theorem r_abs_lt_one : |Real.exp ((6 : ℝ) / (5 : ℝ)) / (4 : ℝ)| < 1 :=
by
  have hpos : (0 : ℝ) < Real.exp ((6 : ℝ) / (5 : ℝ)) / (4 : ℝ) := exp_six_fifths_div_four_pos
  have hlt : Real.exp ((6 : ℝ) / (5 : ℝ)) / (4 : ℝ) < (1 : ℝ) := exp_six_fifths_div_four_lt_one
  rw [abs_of_pos hpos]
  exact hlt

theorem limit_part2 :
  Filter.Tendsto (fun m : ℕ => Real.exp (1 : ℝ) * (Real.exp ((6 : ℝ) / (5 : ℝ)) / (4 : ℝ)) ^ m)
  Filter.atTop (nhds (0 : ℝ)) :=
by
  have h1 : Filter.Tendsto (fun m : ℕ => (Real.exp ((6 : ℝ) / (5 : ℝ)) / (4 : ℝ)) ^ m) Filter.atTop (nhds (0 : ℝ)) :=
    tendsto_pow_atTop_nhds_zero_of_abs_lt_one r_abs_lt_one
  have h_const : Filter.Tendsto (fun _ : ℕ => Real.exp (1 : ℝ)) Filter.atTop (nhds (Real.exp (1 : ℝ))) :=
    tendsto_const_nhds
  have h2 := Filter.Tendsto.mul h_const h1
  simp only [mul_zero] at h2
  exact h2

theorem limit_part3_core :
  Filter.Tendsto (fun m : ℕ => (m : ℝ) * ((1 : ℝ) / (2 : ℝ)) ^ m) Filter.atTop (nhds (0 : ℝ)) :=
by
  simpa using tendsto_pow_const_mul_const_pow_of_abs_lt_one 1 (r := (1 : ℝ) / (2 : ℝ)) (by norm_num)

theorem limit_part3 :
  Filter.Tendsto (fun m : ℕ => ((6 : ℝ) / (5 : ℝ)) * ((m : ℝ) * ((1 : ℝ) / (2 : ℝ)) ^ m) * ((m : ℝ) * ((1 : ℝ) / (2 : ℝ)) ^ m))
  Filter.atTop (nhds (0 : ℝ)) :=
by
  have hc : Filter.Tendsto (fun _ : ℕ => ((6 : ℝ) / (5 : ℝ))) Filter.atTop (nhds ((6 : ℝ) / (5 : ℝ))) := tendsto_const_nhds
  have h_core := limit_part3_core
  have h2 := Filter.Tendsto.mul hc h_core
  have h3 := Filter.Tendsto.mul h2 h_core
  have heq : ((6 : ℝ) / (5 : ℝ)) * (0 : ℝ) * (0 : ℝ) = (0 : ℝ) := by norm_num
  exact heq ▸ h3

theorem abs_one_div_four_lt_one : |(1 : ℝ) / (4 : ℝ)| < 1 :=
by
  norm_num

theorem limit_part4_core :
  Filter.Tendsto (fun m : ℕ => (m : ℝ) * ((1 : ℝ) / (4 : ℝ)) ^ m)
  Filter.atTop (nhds (0 : ℝ)) :=
by
  have h := tendsto_pow_const_mul_const_pow_of_abs_lt_one 1 abs_one_div_four_lt_one
  simpa only [pow_one] using h

theorem limit_part4 :
  Filter.Tendsto (fun m : ℕ => ((3 : ℝ) / (5 : ℝ)) * ((m : ℝ) * ((1 : ℝ) / (4 : ℝ)) ^ m))
  Filter.atTop (nhds (0 : ℝ)) :=
by
  -- The limit of a constant is the constant itself
  have hc : Filter.Tendsto (fun _ : ℕ => (3 : ℝ) / (5 : ℝ)) Filter.atTop (nhds ((3 : ℝ) / (5 : ℝ))) :=
    tendsto_const_nhds

  -- The limit of a product of two sequences is the product of their limits
  have h := hc.mul limit_part4_core

  -- The limit point simplifies from ((3/5) * 0) to 0
  have h_zero : ((3 : ℝ) / (5 : ℝ)) * (0 : ℝ) = (0 : ℝ) := mul_zero ((3 : ℝ) / (5 : ℝ))

  -- Rewrite the limit point in our hypothesis to exactly match the target 0
  rw [h_zero] at h
  exact h

theorem limit_sum :
  Filter.Tendsto (fun m : ℕ =>
    (2 : ℝ) * Real.exp (1 : ℝ) * ((m : ℝ) * (Real.exp ((6 : ℝ) / (5 : ℝ)) / (4 : ℝ)) ^ m) +
    Real.exp (1 : ℝ) * (Real.exp ((6 : ℝ) / (5 : ℝ)) / (4 : ℝ)) ^ m +
    ((6 : ℝ) / (5 : ℝ)) * ((m : ℝ) * ((1 : ℝ) / (2 : ℝ)) ^ m) * ((m : ℝ) * ((1 : ℝ) / (2 : ℝ)) ^ m) +
    ((3 : ℝ) / (5 : ℝ)) * ((m : ℝ) * ((1 : ℝ) / (4 : ℝ)) ^ m))
  Filter.atTop (nhds (0 : ℝ)) :=
by
  have h12 := Filter.Tendsto.add limit_part1 limit_part2
  have h123 := Filter.Tendsto.add h12 limit_part3
  have h1234 := Filter.Tendsto.add h123 limit_part4
  -- h1234 tells us the limit goes to ((0 + 0) + 0) + 0, which is exactly 0
  simp only [add_zero] at h1234
  exact h1234

theorem tendsto_A_add_B :
  Filter.Tendsto (fun m : ℕ =>
       ((2 : ℝ) * (m : ℝ) + 1) * Real.exp ((6 * (m : ℝ)) / (5 : ℝ) + 1) / (4 : ℝ) ^ m +
       ((2 : ℝ) * (m : ℝ) + 1) * ((3 * (m : ℝ)) / (5 : ℝ)) / (4 : ℝ) ^ m) Filter.atTop (nhds (0 : ℝ)) :=
by
  have h_eq : (fun m : ℕ =>
       ((2 : ℝ) * (m : ℝ) + 1) * Real.exp ((6 * (m : ℝ)) / (5 : ℝ) + 1) / (4 : ℝ) ^ m +
       ((2 : ℝ) * (m : ℝ) + 1) * ((3 * (m : ℝ)) / (5 : ℝ)) / (4 : ℝ) ^ m) =
       (fun m : ℕ =>
    (2 : ℝ) * Real.exp (1 : ℝ) * ((m : ℝ) * (Real.exp ((6 : ℝ) / (5 : ℝ)) / (4 : ℝ)) ^ m) +
    Real.exp (1 : ℝ) * (Real.exp ((6 : ℝ) / (5 : ℝ)) / (4 : ℝ)) ^ m +
    ((6 : ℝ) / (5 : ℝ)) * ((m : ℝ) * ((1 : ℝ) / (2 : ℝ)) ^ m) * ((m : ℝ) * ((1 : ℝ) / (2 : ℝ)) ^ m) +
    ((3 : ℝ) / (5 : ℝ)) * ((m : ℝ) * ((1 : ℝ) / (4 : ℝ)) ^ m)) := by
    ext m
    exact term_decomposition m
  rw [h_eq]
  exact limit_sum

theorem tendsto_eventually_le_one {f : ℕ → ℝ} (h : Filter.Tendsto f Filter.atTop (nhds (0 : ℝ))) :
  ∀ᶠ m in Filter.atTop, f m ≤ (1 : ℝ) :=
by
  -- Since the sequence converges to 0 and 0 < 1, it must eventually be strictly less than 1
  have h2 : ∀ᶠ m in Filter.atTop, f m < (1 : ℝ) :=
    Filter.Tendsto.eventually_lt_const (zero_lt_one : (0 : ℝ) < (1 : ℝ)) h
  -- Relax the strict inequality (<) to a weak inequality (≤) point-wise
  exact h2.mono fun m hm => le_of_lt hm

theorem eventually_A_add_B_le_one :
  ∀ᶠ (m : ℕ) in Filter.atTop, ((2 : ℝ) * (m : ℝ) + 1) * Real.exp ((6 * (m : ℝ)) / (5 : ℝ) + 1) / (4 : ℝ) ^ m +
       ((2 : ℝ) * (m : ℝ) + 1) * ((3 * (m : ℝ)) / (5 : ℝ)) / (4 : ℝ) ^ m ≤ (1 : ℝ) :=
tendsto_eventually_le_one tendsto_A_add_B

theorem exp_le_of_A_add_B_le_one_algebra (a b c e : ℝ) (ha : (0 : ℝ) < a) (hb : (0 : ℝ) < b)
    (h : a * e / b + a * c / b ≤ (1 : ℝ)) : e ≤ b / a - c :=
by
  -- Step 1: Combine the terms on the left side of `h` into a single fraction.
  have h1 : (a * e + a * c) / b ≤ (1 : ℝ) := by
    have heq : (a * e + a * c) / b = a * e / b + a * c / b := by ring
    rw [heq]
    exact h

  -- Step 2: Clear the denominator `b`. Since `b > 0`, the inequality direction is preserved.
  have h2 : a * e + a * c ≤ b := by
    -- `div_le_iff₀` states: `0 < c → (b / c ≤ a ↔ b ≤ a * c)`
    have h2' : a * e + a * c ≤ (1 : ℝ) * b := (div_le_iff₀ hb).mp h1
    linarith

  -- Step 3: Factor `a` out of the left-hand side.
  have h3 : (e + c) * a ≤ b := by
    have heq2 : (e + c) * a = a * e + a * c := by ring
    rw [heq2]
    exact h2

  -- Step 4: Divide both sides by `a`. Since `a > 0`, the inequality is preserved.
  -- `le_div_iff₀` states: `0 < c → (a ≤ b / c ↔ a * c ≤ b)`
  have h4 : e + c ≤ b / a := (le_div_iff₀ ha).mpr h3

  -- Step 5: Subtract `c` from both sides to finish the proof.
  linarith

theorem exp_le_of_A_add_B_le_one (m : ℕ)
  (h : ((2 : ℝ) * (m : ℝ) + 1) * Real.exp ((6 * (m : ℝ)) / (5 : ℝ) + 1) / (4 : ℝ) ^ m +
       ((2 : ℝ) * (m : ℝ) + 1) * ((3 * (m : ℝ)) / (5 : ℝ)) / (4 : ℝ) ^ m ≤ (1 : ℝ)) :
  Real.exp ((6 * (m : ℝ)) / (5 : ℝ) + 1) ≤ (4 : ℝ) ^ m / ((2 : ℝ) * (m : ℝ) + 1) - (3 * (m : ℝ)) / (5 : ℝ) :=
by
  apply exp_le_of_A_add_B_le_one_algebra
  · positivity
  · positivity
  · exact h

theorem eventually_exp_six_fifths_le :
  ∀ᶠ (m : ℕ) in Filter.atTop,
    Real.exp ((6 * (m : ℝ)) / (5 : ℝ) + 1) ≤
    (4 : ℝ) ^ m / ((2 : ℝ) * (m : ℝ) + 1) - (3 * (m : ℝ)) / (5 : ℝ) :=
Filter.Eventually.mono eventually_A_add_B_le_one exp_le_of_A_add_B_le_one

theorem le_log_of_exp_le {x y : ℝ} (h : Real.exp x ≤ y) : x ≤ Real.log y :=
by
  have h1 : Real.log (Real.exp x) ≤ Real.log y := Real.log_le_log (Real.exp_pos x) h
  rwa [Real.log_exp x] at h1

theorem log_n_m_lower_eventually :
  ∀ᶠ (m : ℕ) in Filter.atTop, (6 * (m : ℝ)) / (5 : ℝ) + 1 ≤ Real.log (n_m m) :=
by
  filter_upwards [m_ge_one_eventually, eventually_exp_six_fifths_le] with m hm he
  exact le_log_of_exp_le (le_trans he (n_m_lower_bound m hm))

theorem L_m_eq_floor_log (m : ℕ) : L_m m = ⌊Real.log (n_m m)⌋₊ :=
rfl

theorem L_m_lower_eventually :
  ∀ᶠ (m : ℕ) in Filter.atTop, ⌊(6 * (m : ℝ)) / (5 : ℝ)⌋₊ ≤ L_m m :=
by
  apply Filter.Eventually.mono log_n_m_lower_eventually
  intro m hm
  rw [L_m_eq_floor_log]
  apply Nat.floor_mono
  linarith

theorem frac_nonneg (m : ℕ) : (0 : ℝ) ≤ (6 * (m : ℝ)) / (5 : ℝ) :=
by
  positivity

theorem m_le_real_frac (m : ℕ) : (m : ℝ) ≤ (6 * (m : ℝ)) / (5 : ℝ) :=
by
  have h : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  linarith

theorem m_le_floor_six_fifths (m : ℕ) : m ≤ ⌊(6 * (m : ℝ)) / (5 : ℝ)⌋₊ :=
by
  by_contra h
  have h1 : ⌊(6 * (m : ℝ)) / (5 : ℝ)⌋₊ < m := not_le.mp h
  have h2 := (Nat.floor_lt (frac_nonneg m)).mp h1
  have h3 := m_le_real_frac m
  linarith

theorem floor_log_le_real_log (n : ℕ) : ((⌊Real.log (n : ℝ)⌋₊ : ℕ) : ℝ) ≤ Real.log (n : ℝ) :=
by
  apply Nat.floor_le
  exact Real.log_natCast_nonneg n

theorem real_log_le_real_nat (n : ℕ) : Real.log (n : ℝ) ≤ (n : ℝ) :=
by
  apply Real.log_le_self
  exact Nat.cast_nonneg n

theorem floor_log_le_self (n : ℕ) : ⌊Real.log (n : ℝ)⌋₊ ≤ n :=
by
  -- Obtain the two intermediate bounds
  have h1 : ((⌊Real.log (n : ℝ)⌋₊ : ℕ) : ℝ) ≤ Real.log (n : ℝ) := floor_log_le_real_log n
  have h2 : Real.log (n : ℝ) ≤ (n : ℝ) := real_log_le_real_nat n

  -- Chain them together using transitivity in ℝ
  have h3 : ((⌊Real.log (n : ℝ)⌋₊ : ℕ) : ℝ) ≤ (n : ℝ) := le_trans h1 h2

  -- Strip the real number coercions to conclude the inequality over ℕ
  exact Nat.cast_le.mp h3

theorem L_m_le_n_m (m : ℕ) : L_m m ≤ n_m m :=
by
  rw [L_m_eq_floor_log m]
  exact floor_log_le_self (n_m m)

theorem m_le_n_m_eventually :
  ∀ᶠ (m : ℕ) in Filter.atTop, m ≤ n_m m :=
by
  filter_upwards [L_m_lower_eventually] with m hm
  calc
    m ≤ ⌊(6 * (m : ℝ)) / (5 : ℝ)⌋₊ := m_le_floor_six_fifths m
    _ ≤ L_m m := hm
    _ ≤ n_m m := L_m_le_n_m m

theorem pos_real_of_ge_one (m : ℕ) (h : 1 ≤ m) : (0 : ℝ) < (m : ℝ) :=
by
  have hm : 0 < m := by omega
  exact_mod_cast hm

theorem log_six_pow_four_pow (c m : ℕ) :
  Real.log ((6 : ℝ) ^ c * (4 : ℝ) ^ m) = (c : ℝ) * Real.log (6 : ℝ) + (m : ℝ) * Real.log (4 : ℝ) :=
by
  have h1 : (6 : ℝ) ^ c ≠ 0 := by positivity
  have h2 : (4 : ℝ) ^ m ≠ 0 := by positivity
  rw [Real.log_mul h1 h2, Real.log_pow, Real.log_pow]

theorem k_m_bound (m : ℕ) :
  k_m m ∈ Finset.Icc 1 (6 ^ (t_primes m).card) :=
by
  unfold k_m
  split_ifs with h
  · exact (Classical.choose_spec h).1
  · rw [Finset.mem_Icc]
    refine ⟨le_rfl, ?_⟩
    have h_pos : 0 < 6 ^ (t_primes m).card := by positivity
    omega

theorem nat_choose_le_four_pow (m : ℕ) :
  Nat.choose (2 * m) m ≤ 4 ^ m :=
by
  calc
    Nat.choose (2 * m) m ≤ 2 ^ (2 * m) := Nat.choose_le_two_pow (2 * m) m
    _ = (2 ^ 2) ^ m := by rw [pow_mul]
    _ = 4 ^ m := by rfl

theorem log_le_log_of_n_m (m : ℕ) (hm : 1 ≤ n_m m) :
  Real.log (n_m m) ≤ Real.log ((6 : ℝ) ^ (t_primes m).card * (4 : ℝ) ^ m) :=
by
  have h2 : k_m m ≤ 6 ^ (t_primes m).card := (Finset.mem_Icc.mp (k_m_bound m)).2
  have h3 : Nat.choose (2 * m) m ≤ 4 ^ m := nat_choose_le_four_pow m

  apply Real.log_le_log
  · -- Prove the strictly positive condition internally in Nat, then easily cast
    have hm_pos : 0 < n_m m := by omega
    exact_mod_cast hm_pos
  · -- Chain the core upper bounds inherently in Nat, utilizing `omega` and `gcongr`
    have h5 : n_m m ≤ 6 ^ (t_primes m).card * 4 ^ m := by
      calc n_m m ≤ n_m m + c_m m := by omega
        _ = k_m m * Nat.choose (2 * m) m := n_m_add_c_m m
        _ ≤ 6 ^ (t_primes m).card * 4 ^ m := by gcongr

    -- Normalizes the inequality seamlessly to ℝ casts
    exact_mod_cast h5

theorem log_n_m_le (m : ℕ) (hm : 1 ≤ n_m m) :
  Real.log (n_m m) ≤ ((t_primes m).card : ℝ) * Real.log (6 : ℝ) + (m : ℝ) * Real.log (4 : ℝ) :=
by
  -- Obtain the combined bound under the logarithm
  have h_log_le := log_le_log_of_n_m m hm

  -- Expand the logarithmic arithmetic properties to directly match the target condition
  rw [log_six_pow_four_pow] at h_log_le

  -- The resulting equality exactly satisfies the goal
  exact h_log_le

theorem mul_le_2_1 {a b : ℝ} (h : a ≤ b) : (2.1 : ℝ) * a ≤ (2.1 : ℝ) * b :=
by
  linarith

theorem algebra_identity (m : ℕ) (hm : (0 : ℝ) < (m : ℝ)) :
  (2.1 : ℝ) * (((t_primes m).card : ℝ) * Real.log (6 : ℝ) + (m : ℝ) * Real.log (4 : ℝ)) =
  (2.1 : ℝ) * (((t_primes m).card : ℝ) / (m : ℝ) * Real.log (6 : ℝ) + Real.log (4 : ℝ)) * (m : ℝ) :=
by
  -- Since m > 0, it follows that m ≠ 0, which ensures division by m is well-defined.
  have hm_ne : (m : ℝ) ≠ 0 := ne_of_gt hm

  -- We establish an explicit identity mapping the variable divided and then multiplied by `m`
  have h1 : ((t_primes m).card : ℝ) / (m : ℝ) * (m : ℝ) = ((t_primes m).card : ℝ) :=
    div_mul_cancel₀ ((t_primes m).card : ℝ) hm_ne

  -- We work symmetrically: expand the right-hand side, then collapse the fraction cleanly.
  symm
  calc
    (2.1 : ℝ) * (((t_primes m).card : ℝ) / (m : ℝ) * Real.log (6 : ℝ) + Real.log (4 : ℝ)) * (m : ℝ)
      = (2.1 : ℝ) * ((((t_primes m).card : ℝ) / (m : ℝ) * (m : ℝ)) * Real.log (6 : ℝ) + (m : ℝ) * Real.log (4 : ℝ)) := by ring
    _ = (2.1 : ℝ) * (((t_primes m).card : ℝ) * Real.log (6 : ℝ) + (m : ℝ) * Real.log (4 : ℝ)) := by rw [h1]

theorem t_primes_subset_range (m : ℕ) :
  t_primes m ⊆ (Finset.range (3 * m + 1)).filter Nat.Prime :=
by
  intro x hx
  unfold t_primes at hx
  rw [Finset.mem_filter] at hx ⊢
  rcases hx with ⟨hx_mem, hx_prime⟩
  refine ⟨?_, hx_prime⟩
  rw [Finset.mem_range]
  simp only [Finset.mem_Ioc, Finset.mem_Icc, Finset.mem_Ico] at hx_mem
  omega

theorem primeCounting_eq_card_range (n : ℕ) :
  Nat.primeCounting n = ((Finset.range (n + 1)).filter Nat.Prime).card :=
by
  exact Nat.count_eq_card_filter_range Nat.Prime (n + 1)

theorem t_primes_card_le_primeCounting (m : ℕ) :
  (t_primes m).card ≤ Nat.primeCounting (3 * m) :=
by
  -- Rewrite the prime counting function into its equivalent Finset cardinality form
  rw [primeCounting_eq_card_range (3 * m)]
  -- Apply the monotonicity of cardinality over subsets
  exact Finset.card_le_card (t_primes_subset_range m)

theorem t_primes_card_le_primeCounting_real (m : ℕ) :
  ((t_primes m).card : ℝ) ≤ (Nat.primeCounting (3 * m) : ℝ) :=
by
  have h1 : (t_primes m).card ≤ ((Finset.range (3 * m + 1)).filter Nat.Prime).card :=
    Finset.card_le_card (t_primes_subset_range m)
  have h2 : Nat.primeCounting (3 * m) = ((Finset.range (3 * m + 1)).filter Nat.Prime).card :=
    primeCounting_eq_card_range (3 * m)
  have h3 : (t_primes m).card ≤ Nat.primeCounting (3 * m) := by
    rw [h2]
    exact h1
  exact_mod_cast h3

theorem right_hand_side_eq (m : ℕ) :
  (3 : ℝ) * ((Nat.primeCounting (3 * m) : ℝ) / ((3 * m : ℕ) : ℝ)) = (Nat.primeCounting (3 * m) : ℝ) / (m : ℝ) :=
by
  have h_denom : ((3 * m : ℕ) : ℝ) = (3 : ℝ) * (m : ℝ) := by push_cast; rfl
  rw [h_denom]
  by_cases hm : (m : ℝ) = 0
  · simp [hm]
  · have h3 : (3 : ℝ) ≠ 0 := by norm_num
    have hm3 : (3 : ℝ) * (m : ℝ) ≠ 0 := mul_ne_zero h3 hm
    field_simp [hm, h3, hm3] <;> ring

theorem div_le_div_of_nonneg_right_real {a b c : ℝ} (hab : a ≤ b) (hc : 0 ≤ c) : a / c ≤ b / c :=
div_le_div_of_nonneg_right hab hc

theorem m_cast_nonneg (m : ℕ) : (0 : ℝ) ≤ (m : ℝ) :=
Nat.cast_nonneg m

theorem t_primes_card_div_m_le (m : ℕ) :
  ((t_primes m).card : ℝ) / (m : ℝ) ≤ (3 : ℝ) * ((Nat.primeCounting (3 * m) : ℝ) / ((3 * m : ℕ) : ℝ)) :=
by
  rw [right_hand_side_eq m]
  exact div_le_div_of_nonneg_right_real (t_primes_card_le_primeCounting_real m) (m_cast_nonneg m)

theorem t_primes_card_div_m_nonneg (m : ℕ) :
  (0 : ℝ) ≤ ((t_primes m).card : ℝ) / (m : ℝ) :=
by
  positivity

theorem m_le_three_mul (m : ℕ) : m ≤ 3 * m :=
by
  omega

theorem tendsto_three_mul_atTop :
  Filter.Tendsto (fun m : ℕ => 3 * m) Filter.atTop Filter.atTop :=
-- Use the comparison principle: if `m ≤ 3 * m` for all `m`, and `id` goes to `atTop`,
  -- then `3 * m` also goes to `atTop`. `Filter.tendsto_id` proves that `fun m => m` goes to `atTop`.
  Filter.tendsto_atTop_mono m_le_three_mul Filter.tendsto_id

theorem eq_mul_div_of_div_mul (b c d : ℝ) : (b / d) * c = b * c / d :=
by
  exact div_mul_eq_mul_div b d c

theorem ineq_helper (a b c d : ℝ) (h1 : a ≤ b * c / d) (h2 : 0 < c) : a / c ≤ b / d :=
by
  rw [div_le_iff₀ h2]
  rw [eq_mul_div_of_div_mul]
  exact h1

theorem eventually_primeCounting_le_nat_one :
  ∀ᶠ (n : ℕ) in Filter.atTop, (Nat.primeCounting n : ℝ) ≤ (Real.log (4 : ℝ) + (1 : ℝ)) * (n : ℝ) / Real.log (n : ℝ) :=
by
  have h := Chebyshev.eventually_primeCounting_le (zero_lt_one : (0 : ℝ) < 1)
  refine (tendsto_natCast_atTop_atTop.eventually h).mono fun n hn => ?_
  rw [Nat.floor_natCast] at hn
  exact hn

theorem eventually_pos_nat : ∀ᶠ (n : ℕ) in Filter.atTop, (0 : ℝ) < (n : ℝ) :=
by
  rw [Filter.eventually_atTop]
  exact ⟨1, fun b hb => pos_real_of_ge_one b hb⟩

theorem primeCounting_div_bound_eventually :
  ∀ᶠ (n : ℕ) in Filter.atTop, (Nat.primeCounting n : ℝ) / (n : ℝ) ≤ (Real.log (4 : ℝ) + (1 : ℝ)) / Real.log (n : ℝ) :=
by
  filter_upwards [eventually_primeCounting_le_nat_one, eventually_pos_nat] with n hn1 hn2
  exact ineq_helper (Nat.primeCounting n : ℝ) (Real.log (4 : ℝ) + (1 : ℝ)) (n : ℝ) (Real.log (n : ℝ)) hn1 hn2

theorem tendsto_bound_zero :
  Filter.Tendsto (fun n : ℕ => (Real.log (4 : ℝ) + (1 : ℝ)) / Real.log (n : ℝ)) Filter.atTop (nhds (0 : ℝ)) :=
by
  -- Rewrite division as multiplication by the inverse
  have heq : (fun n : ℕ => (Real.log (4 : ℝ) + (1 : ℝ)) / Real.log (n : ℝ)) =
             (fun n : ℕ => (Real.log (4 : ℝ) + (1 : ℝ)) * (Real.log (n : ℝ))⁻¹) := by
    funext n
    exact div_eq_mul_inv (Real.log (4 : ℝ) + (1 : ℝ)) (Real.log (n : ℝ))
  rw [heq]

  -- The real cast of natural numbers tends to infinity
  have h_cast : Filter.Tendsto (fun n : ℕ => (n : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_iff.mpr Filter.tendsto_id

  -- Composing with the real logarithm also tends to infinity
  have h_log : Filter.Tendsto (fun n : ℕ => Real.log (n : ℝ)) Filter.atTop Filter.atTop :=
    Filter.Tendsto.comp Real.tendsto_log_atTop h_cast

  -- The inverse of a function tending to infinity tends to zero
  have h1 : Filter.Tendsto (fun n : ℕ => (Real.log (n : ℝ))⁻¹) Filter.atTop (nhds (0 : ℝ)) :=
    Filter.Tendsto.comp tendsto_inv_atTop_zero h_log

  -- A constant function trivially tends to itself
  have hc : Filter.Tendsto (fun _ : ℕ => Real.log (4 : ℝ) + (1 : ℝ)) Filter.atTop (nhds (Real.log (4 : ℝ) + (1 : ℝ))) :=
    tendsto_const_nhds

  -- Multiplying a function tending to 0 by a function tending to a constant `c` gives a function tending to `c * 0`
  have h2 : Filter.Tendsto (fun n : ℕ => (Real.log (4 : ℝ) + (1 : ℝ)) * (Real.log (n : ℝ))⁻¹) Filter.atTop (nhds ((Real.log (4 : ℝ) + (1 : ℝ)) * (0 : ℝ))) :=
    Filter.Tendsto.mul hc h1

  -- Simplify the limit point `c * 0 = 0` to close the goal perfectly
  rw [mul_zero] at h2

  exact h2

theorem primeCounting_div_nonneg_eventually :
  ∀ᶠ (n : ℕ) in Filter.atTop, (0 : ℝ) ≤ (Nat.primeCounting n : ℝ) / (n : ℝ) :=
by
  apply Filter.Eventually.of_forall
  intro n
  positivity

theorem tendsto_zero_nhds_zero :
  Filter.Tendsto (fun _ : ℕ => (0 : ℝ)) Filter.atTop (nhds (0 : ℝ)) :=
tendsto_const_nhds

theorem custom_squeeze (f g h : ℕ → ℝ) (a : ℝ)
  (h_fg : ∀ᶠ n in Filter.atTop, f n ≤ g n)
  (h_gh : ∀ᶠ n in Filter.atTop, g n ≤ h n)
  (hf : Filter.Tendsto f Filter.atTop (nhds a))
  (hh : Filter.Tendsto h Filter.atTop (nhds a)) :
  Filter.Tendsto g Filter.atTop (nhds a) :=
by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
  · exact hf
  · exact hh
  · exact h_fg
  · exact h_gh

theorem tendsto_primeCounting_div_atTop_nhds_zero :
  Filter.Tendsto (fun n : ℕ => (Nat.primeCounting n : ℝ) / (n : ℝ)) Filter.atTop (nhds (0 : ℝ)) :=
by
  exact custom_squeeze
    (fun _ => (0 : ℝ))
    (fun n => (Nat.primeCounting n : ℝ) / (n : ℝ))
    (fun n => (Real.log (4 : ℝ) + (1 : ℝ)) / Real.log (n : ℝ))
    (0 : ℝ)
    primeCounting_div_nonneg_eventually
    primeCounting_div_bound_eventually
    tendsto_zero_nhds_zero
    tendsto_bound_zero

theorem tendsto_primeCounting_comp :
  Filter.Tendsto (fun m : ℕ => (Nat.primeCounting (3 * m) : ℝ) / ((3 * m : ℕ) : ℝ)) Filter.atTop (nhds (0 : ℝ)) :=
Filter.Tendsto.comp tendsto_primeCounting_div_atTop_nhds_zero tendsto_three_mul_atTop

theorem t_primes_card_div_m_tendsto_zero :
  Filter.Tendsto (fun m : ℕ => ((t_primes m).card : ℝ) / (m : ℝ)) Filter.atTop (nhds (0 : ℝ)) :=
by
  have hg : Filter.Tendsto (fun _ : ℕ => (0 : ℝ)) Filter.atTop (nhds 0) := tendsto_const_nhds
  have hh : Filter.Tendsto (fun m : ℕ => (3 : ℝ) * ((Nat.primeCounting (3 * m) : ℝ) / ((3 * m : ℕ) : ℝ))) Filter.atTop (nhds 0) := by
    have h_const : Filter.Tendsto (fun _ : ℕ => (3 : ℝ)) Filter.atTop (nhds (3 : ℝ)) := tendsto_const_nhds
    have h_mul := h_const.mul tendsto_primeCounting_comp
    have h_zero : (3 : ℝ) * 0 = 0 := mul_zero (3 : ℝ)
    rw [h_zero] at h_mul
    exact h_mul
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hg hh t_primes_card_div_m_nonneg t_primes_card_div_m_le

theorem limit_expr :
  Filter.Tendsto (fun m : ℕ => (2.1 : ℝ) * (((t_primes m).card : ℝ) / (m : ℝ) * Real.log (6 : ℝ) + Real.log (4 : ℝ)))
  Filter.atTop (nhds ((2.1 : ℝ) * Real.log (4 : ℝ))) :=
by
  have h1 : Filter.Tendsto (fun m : ℕ => ((t_primes m).card : ℝ) / (m : ℝ)) Filter.atTop (nhds (0 : ℝ)) := t_primes_card_div_m_tendsto_zero
  have h2 := Filter.Tendsto.mul_const (Real.log (6 : ℝ)) h1
  have h3 := Filter.Tendsto.add_const (Real.log (4 : ℝ)) h2
  have h4 := Filter.Tendsto.const_mul (2.1 : ℝ) h3
  have heq : (2.1 : ℝ) * ((0 : ℝ) * Real.log (6 : ℝ) + Real.log (4 : ℝ)) = (2.1 : ℝ) * Real.log (4 : ℝ) := by
    rw [zero_mul, zero_add]
  rw [heq] at h4
  exact h4

theorem exp_mul_eq_pow_thirty_two (x : ℝ) : Real.exp ((32 : ℝ) * x) = (Real.exp x) ^ 32 :=
by
  exact Real.exp_nat_mul x 32

theorem my_pow_le_pow_of_le_left {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (n : ℕ) : a ^ n ≤ b ^ n :=
by
  gcongr

theorem four_le_pow_thirty_two : (4 : ℝ) ≤ (((357 : ℝ) / (8000 : ℝ)) + 1) ^ 32 :=
by
  norm_num

theorem log_four_le : Real.log (4 : ℝ) ≤ ((357 : ℝ) / (250 : ℝ)) :=
by
  have h_pos : (0 : ℝ) < (4 : ℝ) := by norm_num
  rw [Real.log_le_iff_le_exp h_pos]
  have h1 : (32 : ℝ) * ((357 : ℝ) / (8000 : ℝ)) = (357 : ℝ) / (250 : ℝ) := by norm_num
  have h2 : ((357 : ℝ) / (8000 : ℝ)) + 1 ≤ Real.exp ((357 : ℝ) / (8000 : ℝ)) := Real.add_one_le_exp ((357 : ℝ) / (8000 : ℝ))
  have h3 : (0 : ℝ) ≤ ((357 : ℝ) / (8000 : ℝ)) + 1 := by norm_num
  have h4 : (((357 : ℝ) / (8000 : ℝ)) + 1) ^ 32 ≤ (Real.exp ((357 : ℝ) / (8000 : ℝ))) ^ 32 := my_pow_le_pow_of_le_left h3 h2 32
  calc
    (4 : ℝ) ≤ (((357 : ℝ) / (8000 : ℝ)) + 1) ^ 32 := four_le_pow_thirty_two
    _ ≤ (Real.exp ((357 : ℝ) / (8000 : ℝ))) ^ 32 := h4
    _ = Real.exp ((32 : ℝ) * ((357 : ℝ) / (8000 : ℝ))) := (exp_mul_eq_pow_thirty_two ((357 : ℝ) / (8000 : ℝ))).symm
    _ = Real.exp ((357 : ℝ) / (250 : ℝ)) := by rw [h1]

theorem val_lt_three : (2.1 : ℝ) * Real.log (4 : ℝ) < 3 :=
by
  have h1 : (2.1 : ℝ) * Real.log (4 : ℝ) ≤ (2.1 : ℝ) * ((357 : ℝ) / (250 : ℝ)) := mul_le_2_1 log_four_le
  have h2 : (2.1 : ℝ) * ((357 : ℝ) / (250 : ℝ)) < (3 : ℝ) := by norm_num
  exact lt_of_le_of_lt h1 h2

theorem eventually_lt_three :
  ∀ᶠ (m : ℕ) in Filter.atTop, (2.1 : ℝ) * (((t_primes m).card : ℝ) / (m : ℝ) * Real.log (6 : ℝ) + Real.log (4 : ℝ)) < 3 :=
by
  exact Filter.Tendsto.eventually_lt_const val_lt_three limit_expr

theorem mul_lt_mul_m {a m : ℝ} (hab : a < 3) (hm : 0 < m) : a * m < 3 * m :=
by
  exact mul_lt_mul_of_pos_right hab hm

theorem log_n_m_upper_eventually :
  ∀ᶠ (m : ℕ) in Filter.atTop, (2.1 : ℝ) * Real.log (n_m m) < 3 * (m : ℝ) :=
by
  have h1 : ∀ᶠ (m : ℕ) in Filter.atTop, 1 ≤ m := m_ge_one_eventually
  have h2 : ∀ᶠ (m : ℕ) in Filter.atTop, m ≤ n_m m := m_le_n_m_eventually
  have h3 : ∀ᶠ (m : ℕ) in Filter.atTop, (2.1 : ℝ) * (((t_primes m).card : ℝ) / (m : ℝ) * Real.log (6 : ℝ) + Real.log (4 : ℝ)) < 3 := eventually_lt_three

  filter_upwards [h1, h2, h3] with m hm1 hm2 hm3

  have hm_pos : (0 : ℝ) < (m : ℝ) := pos_real_of_ge_one m hm1
  have hn_pos : 1 ≤ n_m m := le_trans hm1 hm2

  have h_log : Real.log (n_m m) ≤ ((t_primes m).card : ℝ) * Real.log (6 : ℝ) + (m : ℝ) * Real.log (4 : ℝ) :=
    log_n_m_le m hn_pos

  have h_mul : (2.1 : ℝ) * Real.log (n_m m) ≤ (2.1 : ℝ) * (((t_primes m).card : ℝ) * Real.log (6 : ℝ) + (m : ℝ) * Real.log (4 : ℝ)) :=
    mul_le_2_1 h_log

  rw [algebra_identity m hm_pos] at h_mul

  have h_lt : (2.1 : ℝ) * (((t_primes m).card : ℝ) / (m : ℝ) * Real.log (6 : ℝ) + Real.log (4 : ℝ)) * (m : ℝ) < 3 * (m : ℝ) :=
    mul_lt_mul_m hm3 hm_pos

  exact lt_of_le_of_lt h_mul h_lt

theorem p_sub_mod_mem_Icc (n p L : ℕ) (hp : 0 < p) (hL : p ≤ L) :
  p - n % p ∈ Finset.Icc 1 L :=
by
  rw [Finset.mem_Icc]
  have := Nat.mod_lt n hp
  omega

theorem dvd_n_add_p_sub_mod (n p : ℕ) (hp : 0 < p) :
  p ∣ n + (p - n % p) :=
by
  -- Provide `omega` with the upper bound of the modulo to safely handle Nat subtraction
  have h1 : n % p < p := Nat.mod_lt n hp
  -- Expose the Euclidean division relation so `omega` sees it as linear components
  have h2 : p * (n / p) + n % p = n := Nat.div_add_mod n p

  -- Re-arrange the goal expression algebraically using the hypotheses
  have h3 : n + (p - n % p) = p * (n / p) + p := by omega
  rw [h3]

  -- By definition, p ∣ A means there exists some k such that A = p * k.
  -- We provide (n / p + 1) and use `ring` to prove equivalence.
  exact ⟨n / p + 1, by ring⟩

theorem exists_index_dvd (n p L : ℕ) (hp : 0 < p) (hL : p ≤ L) :
  ∃ i ∈ Finset.Icc 1 L, p ∣ n + i :=
by
  use p - n % p
  exact ⟨p_sub_mod_mem_Icc n p L hp hL, dvd_n_add_p_sub_mod n p hp⟩

theorem dvd_prod_of_length_ge (n p L : ℕ) (hp : 0 < p) (hL : p ≤ L) :
  p ∣ ∏ i ∈ Finset.Icc 1 L, (n + i) :=
by
  -- Obtain the explicit index `i` that ensures `p ∣ n + i` within the interval `[1, L]`.
  obtain ⟨i, hi_mem, h_dvd⟩ := exists_index_dvd n p L hp hL

  -- Show that `n + i` itself trivially divides the product of consecutive elements.
  have h_prod : (n + i) ∣ ∏ j ∈ Finset.Icc 1 L, (n + j) :=
    Finset.dvd_prod_of_mem (fun j => n + j) hi_mem

  -- Conclude the proof by transitivity: if `p ∣ n + i` and `n + i ∣ ∏ (...)`, then `p ∣ ∏ (...)`.
  exact dvd_trans h_dvd h_prod

theorem case1_div (m : ℕ) (p : ℕ) (hp1 : p.Prime) (hp2 : p ≤ m) (hL : m ≤ L_m m) :
  p ∣ ∏ i ∈ Finset.Icc 1 (L_m m), (n_m m + i) :=
by
  apply dvd_prod_of_length_ge
  · exact hp1.pos
  · exact le_trans hp2 hL

theorem prime_dvd_choose (m : ℕ) (p : ℕ) (hp1 : p.Prime) (hp2 : m < p) (hp3 : p ≤ 2 * m) :
  p ∣ Nat.choose (2 * m) m :=
by
  exact Nat.Prime.dvd_choose hp1 hp2 (by omega) hp3

theorem case2_div (m : ℕ) (p : ℕ) (hp1 : p.Prime) (hp2 : m < p) (hp3 : p ≤ 2 * m)
    (hc : c_m m ≤ L_m m) (hc_pos : 1 ≤ c_m m) :
  p ∣ ∏ i ∈ Finset.Icc 1 (L_m m), (n_m m + i) :=
by
  -- Show that our target offset `c_m m` is inside the product range.
  have h_mem : c_m m ∈ Finset.Icc 1 (L_m m) := by
    rw [Finset.mem_Icc]
    exact ⟨hc_pos, hc⟩

  -- From the given prime bounds, we know p divides the central binomial coefficient.
  have h_div_choose : p ∣ Nat.choose (2 * m) m := prime_dvd_choose m p hp1 hp2 hp3

  -- Show that p divides the chosen term of the product.
  have h_div_term : p ∣ (n_m m + c_m m) := by
    rw [n_m_add_c_m m]
    obtain ⟨d, hd⟩ := h_div_choose
    use k_m m * d
    -- Reorder terms to show: k_m m * (p * d) = p * (k_m m * d)
    rw [hd, ← mul_assoc, mul_comm (k_m m) p, mul_assoc]

  -- Since `n_m m + c_m m` is a factor of the product, it divides the entire product.
  have h_prod_div : n_m m + c_m m ∣ ∏ i ∈ Finset.Icc 1 (L_m m), (n_m m + i) :=
    Finset.dvd_prod_of_mem (fun i => n_m m + i) h_mem

  -- Finally, applying transitivity concludes the proof.
  exact dvd_trans h_div_term h_prod_div

theorem dirichlet_box_idx_eq (x : ℝ) (Q : ℕ) :
  dirichlet_box_idx x Q = ⌊Int.fract x * (Q : ℝ)⌋₊ :=
rfl

theorem fract_mul_nat_cast_nonneg (x : ℝ) (Q : ℕ) :
  (0 : ℝ) ≤ Int.fract x * (Q : ℝ) :=
by
  apply mul_nonneg
  · exact Int.fract_nonneg x
  · exact Nat.cast_nonneg Q

theorem fract_mul_lt_cast (x : ℝ) (Q : ℕ) (hQ : 0 < Q) :
  Int.fract x * (Q : ℝ) < (Q : ℝ) :=
by
  -- Obtain the base inequality for the fractional part
  have h1 : Int.fract x < 1 := Int.fract_lt_one x
  -- Cast the strict positivity of Q to the real numbers
  have h2 : (0 : ℝ) < (Q : ℝ) := Nat.cast_pos.mpr hQ
  -- Multiply the strict inequality h1 by the positive quantity (Q : ℝ)
  have h3 := mul_lt_mul_of_pos_right h1 h2
  -- Simplify the resulting 1 * (Q : ℝ) down to (Q : ℝ)
  rw [one_mul] at h3
  exact h3

theorem nat_floor_lt_of_lt_cast (a : ℝ) (Q : ℕ) (ha : (0 : ℝ) ≤ a) (h : a < (Q : ℝ)) :
  ⌊a⌋₊ < Q :=
by
  exact (Nat.floor_lt ha).mpr h

theorem dirichlet_box_idx_lt (x : ℝ) (Q : ℕ) (hQ : 0 < Q) :
  dirichlet_box_idx x Q < Q :=
by
  rw [dirichlet_box_idx_eq]
  apply nat_floor_lt_of_lt_cast
  · apply fract_mul_nat_cast_nonneg
  · apply fract_mul_lt_cast _ _ hQ

theorem dirichlet_card_ineq (s : Finset ℕ) (Q : ℕ) :
  Fintype.card (s → Fin Q) < Fintype.card (Fin (Q ^ s.card + 1)) :=
by
  simp

theorem fin_to_Icc {M : ℕ} (k : Fin (M + 1)) : (k : ℕ) ∈ Finset.Icc 0 M :=
by
  rw [Finset.mem_Icc]
  have h := k.isLt
  omega

theorem fin_val_ne {n : ℕ} {a b : Fin n} (h : a ≠ b) : (a : ℕ) ≠ (b : ℕ) :=
by
  intro h_eq
  apply h
  exact Fin.ext h_eq

theorem extract_box_eq (s : Finset ℕ) (ξ : ℕ → ℝ) (Q : ℕ) (hQ : 0 < Q)
    (k₁ k₂ : Fin (Q ^ s.card + 1))
    (f : Fin (Q ^ s.card + 1) → (s → Fin Q))
    (hf : ∀ k a, f k a = ⟨dirichlet_box_idx (((k : ℕ) : ℝ) * ξ (a : ℕ)) Q, dirichlet_box_idx_lt (((k : ℕ) : ℝ) * ξ (a : ℕ)) Q hQ⟩)
    (heq : f k₁ = f k₂) :
    ∀ a ∈ s, dirichlet_box_idx (((k₁ : ℕ) : ℝ) * ξ a) Q = dirichlet_box_idx (((k₂ : ℕ) : ℝ) * ξ a) Q :=
by
  -- Introduce an arbitrary element `a` and the assumption that it belongs to `s`
  intro a ha

  -- Step 1: Prove that functions applied to point `⟨a, ha⟩` are equivalent
  have h_eq : f k₁ ⟨a, ha⟩ = f k₂ ⟨a, ha⟩ := by rw [heq]

  -- Step 2: Push the equality to the underlying natural number bounds (the `.val` field of `Fin`)
  have h_val : (f k₁ ⟨a, ha⟩).val = (f k₂ ⟨a, ha⟩).val :=
    congrArg (fun x : Fin Q => x.val) h_eq

  -- Step 3: Expand the definition of the function for `k₁` and isolate its `.val`
  -- The expression `(⟨X, hX⟩ : Fin Q).val` is definitionally equivalent to `X`.
  have hk1_val : (f k₁ ⟨a, ha⟩).val = dirichlet_box_idx (((k₁ : ℕ) : ℝ) * ξ a) Q :=
    congrArg (fun x : Fin Q => x.val) (hf k₁ ⟨a, ha⟩)

  -- Step 4: Expand the definition of the function for `k₂` and isolate its `.val`
  have hk2_val : (f k₂ ⟨a, ha⟩).val = dirichlet_box_idx (((k₂ : ℕ) : ℝ) * ξ a) Q :=
    congrArg (fun x : Fin Q => x.val) (hf k₂ ⟨a, ha⟩)

  -- Step 5: Rewrite our foundational point-wise equality `h_val` using the extracted `.val` identities
  rw [hk1_val, hk2_val] at h_val

  -- Step 6: The rewritten statement now matches our exact goal
  exact h_val

theorem dirichlet_tuple_collision (s : Finset ℕ) (ξ : ℕ → ℝ) (Q : ℕ) (hQ : 0 < Q) :
  ∃ k₁ k₂, k₁ ∈ Finset.Icc 0 (Q ^ s.card) ∧ k₂ ∈ Finset.Icc 0 (Q ^ s.card) ∧ k₁ < k₂ ∧
  ∀ a ∈ s, dirichlet_box_idx ((k₁ : ℝ) * ξ a) Q = dirichlet_box_idx ((k₂ : ℝ) * ξ a) Q :=
by
  let f : Fin (Q ^ s.card + 1) → (s → Fin Q) := fun k a =>
    ⟨dirichlet_box_idx (((k : ℕ) : ℝ) * ξ (a : ℕ)) Q, dirichlet_box_idx_lt (((k : ℕ) : ℝ) * ξ (a : ℕ)) Q hQ⟩

  have hf : ∀ k a, f k a = ⟨dirichlet_box_idx (((k : ℕ) : ℝ) * ξ (a : ℕ)) Q, dirichlet_box_idx_lt (((k : ℕ) : ℝ) * ξ (a : ℕ)) Q hQ⟩ := fun k a => rfl

  obtain ⟨k₁_fin, k₂_fin, hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt f (dirichlet_card_ineq s Q)

  have heq_eval := extract_box_eq s ξ Q hQ k₁_fin k₂_fin f hf heq
  have hne_val := fin_val_ne hne

  by_cases hlt : (k₁_fin : ℕ) < (k₂_fin : ℕ)
  · exact ⟨(k₁_fin : ℕ), (k₂_fin : ℕ), fin_to_Icc k₁_fin, fin_to_Icc k₂_fin, hlt, heq_eval⟩
  · have hgt : (k₂_fin : ℕ) < (k₁_fin : ℕ) := by omega
    have heq_eval_symm : ∀ a ∈ s, dirichlet_box_idx (((k₂_fin : ℕ) : ℝ) * ξ a) Q = dirichlet_box_idx (((k₁_fin : ℕ) : ℝ) * ξ a) Q :=
      fun a ha => (heq_eval a ha).symm
    exact ⟨(k₂_fin : ℕ), (k₁_fin : ℕ), fin_to_Icc k₂_fin, fin_to_Icc k₁_fin, hgt, heq_eval_symm⟩

theorem real_nat_floor_le (x : ℝ) (hx : (0 : ℝ) ≤ x) : (⌊x⌋₊ : ℝ) ≤ x :=
Nat.floor_le hx

theorem real_lt_nat_floor_add_one_of_neg (x : ℝ) (hx : x < 0) : x < (⌊x⌋₊ : ℝ) + (1 : ℝ) :=
by
  have h : (0 : ℝ) ≤ (⌊x⌋₊ : ℝ) := Nat.cast_nonneg ⌊x⌋₊
  linarith

theorem real_lt_nat_floor_add_one_of_nonneg (x : ℝ) (hx : 0 ≤ x) : x < (⌊x⌋₊ : ℝ) + (1 : ℝ) :=
by
  exact Nat.lt_floor_add_one x

theorem real_lt_nat_floor_add_one (x : ℝ) : x < (⌊x⌋₊ : ℝ) + (1 : ℝ) :=
by
  by_cases h : x < 0
  · exact real_lt_nat_floor_add_one_of_neg x h
  · exact real_lt_nat_floor_add_one_of_nonneg x (not_lt.mp h)

theorem real_abs_lt_of_lt_of_neg_lt {x y : ℝ} (h1 : -y < x) (h2 : x < y) : |x| < y :=
abs_lt.mpr ⟨h1, h2⟩

theorem abs_sub_lt_one_of_nat_floor_eq {a b : ℝ} (ha : (0 : ℝ) ≤ a) (hb : (0 : ℝ) ≤ b) (h : ⌊a⌋₊ = ⌊b⌋₊) :
  |a - b| < (1 : ℝ) :=
by
  -- Obtain the lower bounds for a and b based on their non-negative floors
  have ha1 := real_nat_floor_le a ha
  have hb1 := real_nat_floor_le b hb

  -- Obtain the strict upper bounds for a and b relative to their non-negative floors
  have ha2 := real_lt_nat_floor_add_one a
  have hb2 := real_lt_nat_floor_add_one b

  -- Project the equality of their floor functions onto real numbers
  have hc : (⌊a⌋₊ : ℝ) = (⌊b⌋₊ : ℝ) := by rw [h]

  -- Reduce |a - b| < 1 to showing -1 < a - b and a - b < 1
  apply real_abs_lt_of_lt_of_neg_lt
  · -- Prove -1 < a - b (equivalent to b - a < 1)
    linarith
  · -- Prove a - b < 1
    linarith

theorem abs_sub_lt_one_of_box_eq (x y : ℝ) (Q : ℕ)
  (h : dirichlet_box_idx x Q = dirichlet_box_idx y Q) :
  |Int.fract y * (Q : ℝ) - Int.fract x * (Q : ℝ)| < (1 : ℝ) :=
by
  have hx := dirichlet_box_idx_eq x Q
  have hy := dirichlet_box_idx_eq y Q
  rw [hx, hy] at h
  exact abs_sub_lt_one_of_nat_floor_eq (fract_mul_nat_cast_nonneg y Q) (fract_mul_nat_cast_nonneg x Q) h.symm

theorem fract_diff_mul_eq (x y Q : ℝ) (l : ℤ) (hl : l = (⌊y⌋ : ℤ) - (⌊x⌋ : ℤ)) :
  Int.fract y * Q - Int.fract x * Q = (y - x - (l : ℝ)) * Q :=
by
  rw [hl]
  have hy : Int.fract y = y - (⌊y⌋ : ℝ) := rfl
  have hx : Int.fract x = x - (⌊x⌋ : ℝ) := rfl
  rw [hy, hx]
  push_cast
  ring

theorem abs_mul_pos (A Q : ℝ) (hQ : (0 : ℝ) < Q) : |A * Q| = |A| * Q :=
by
  rw [abs_mul, abs_of_pos hQ]

theorem le_div_of_mul_lt_pos (x y z : ℝ) (hy : (0 : ℝ) < y) (h : x * y < z) : x ≤ z / y :=
(le_div_iff₀ hy).mpr (le_of_lt h)

theorem abs_mul_lt_one_implies_le (A Q : ℝ) (hQ : (0 : ℝ) < Q) (h : |A * Q| < (1 : ℝ)) :
  |A| ≤ (1 : ℝ) / Q :=
by
  rw [abs_mul_pos A Q hQ] at h
  exact le_div_of_mul_lt_pos |A| Q (1 : ℝ) hQ h

theorem nat_cast_pos_of_pos {Q : ℕ} (h : 0 < Q) : (0 : ℝ) < (Q : ℝ) :=
by
  exact_mod_cast h

theorem dirichlet_box_diff (x y : ℝ) (Q : ℕ) (hQ : 0 < Q)
  (h_eq : dirichlet_box_idx x Q = dirichlet_box_idx y Q) :
  ∃ l : ℤ, |y - x - (l : ℝ)| ≤ (1 : ℝ) / (Q : ℝ) :=
by
  let l : ℤ := (⌊y⌋ : ℤ) - (⌊x⌋ : ℤ)
  refine ⟨l, ?_⟩
  have h1 : |Int.fract y * (Q : ℝ) - Int.fract x * (Q : ℝ)| < (1 : ℝ) := abs_sub_lt_one_of_box_eq x y Q h_eq
  have h2 : Int.fract y * (Q : ℝ) - Int.fract x * (Q : ℝ) = (y - x - (l : ℝ)) * (Q : ℝ) := fract_diff_mul_eq x y (Q : ℝ) l rfl
  rw [h2] at h1
  have hQ_pos : (0 : ℝ) < (Q : ℝ) := nat_cast_pos_of_pos hQ
  exact abs_mul_lt_one_implies_le (y - x - (l : ℝ)) (Q : ℝ) hQ_pos h1

theorem dirichlet_witness_bounds (k₁ k₂ k M : ℕ)
  (h1 : k₁ ∈ Finset.Icc 0 M) (h2 : k₂ ∈ Finset.Icc 0 M) (hlt : k₁ < k₂) (h : k + k₁ = k₂) :
  k ∈ Finset.Icc 1 M :=
by
  simp only [Finset.mem_Icc] at *
  omega

theorem dirichlet_witness_real_eq (k₁ k₂ k : ℕ) (h : k + k₁ = k₂) :
  (k : ℝ) = (k₂ : ℝ) - (k₁ : ℝ) :=
by
  rw [← h]
  push_cast
  ring

theorem dirichlet_witness_exists_helper (k₁ k₂ : ℕ) (hlt : k₁ < k₂) :
  ∃ k : ℕ, k + k₁ = k₂ :=
by
  -- strict inequality implies non-strict inequality
  have hle : k₁ ≤ k₂ := Nat.le_of_lt hlt
  -- By canonical order property, a ≤ b ↔ ∃ c, b = c + a
  have hex : ∃ c, k₂ = c + k₁ := le_iff_exists_add'.mp hle
  -- Eliminate the existential and supply the required symmetric equality to the goal
  exact hex.elim (fun c hc => ⟨c, hc.symm⟩)

theorem dirichlet_witness_exists (k₁ k₂ : ℕ) (s_card Q : ℕ)
  (h1 : k₁ ∈ Finset.Icc 0 (Q ^ s_card)) (h2 : k₂ ∈ Finset.Icc 0 (Q ^ s_card)) (hlt : k₁ < k₂) :
  ∃ k : ℕ, k ∈ Finset.Icc 1 (Q ^ s_card) ∧ (k : ℝ) = (k₂ : ℝ) - (k₁ : ℝ) :=
by
  have ⟨k, hk⟩ := dirichlet_witness_exists_helper k₁ k₂ hlt
  use k
  constructor
  · exact dirichlet_witness_bounds k₁ k₂ k (Q ^ s_card) h1 h2 hlt hk
  · exact dirichlet_witness_real_eq k₁ k₂ k hk

theorem dirichlet_simultaneous (s : Finset ℕ) (ξ : ℕ → ℝ) (Q : ℕ) (hQ : 0 < Q) :
  ∃ k ∈ Finset.Icc 1 (Q ^ s.card), ∀ a ∈ s, ∃ l : ℤ, |(k : ℝ) * ξ a - (l : ℝ)| ≤ (1 : ℝ) / (Q : ℝ) :=
by
  obtain ⟨k₁, k₂, hk1, hk2, hlt, heq⟩ := dirichlet_tuple_collision s ξ Q hQ
  obtain ⟨k, hk_Icc, hk_eq⟩ := dirichlet_witness_exists k₁ k₂ s.card Q hk1 hk2 hlt
  refine ⟨k, hk_Icc, ?_⟩
  intro a ha
  have heq_idx : dirichlet_box_idx ((k₁ : ℝ) * ξ a) Q = dirichlet_box_idx ((k₂ : ℝ) * ξ a) Q := heq a ha
  obtain ⟨l, hl⟩ := dirichlet_box_diff ((k₁ : ℝ) * ξ a) ((k₂ : ℝ) * ξ a) Q hQ heq_idx
  use l
  have hrw : (k : ℝ) * ξ a = (k₂ : ℝ) * ξ a - (k₁ : ℝ) * ξ a := by
    rw [hk_eq, sub_mul]
  rw [hrw]
  exact hl

theorem k_m_exists (m : ℕ) :
  ∃ (k : ℕ), k ∈ Finset.Icc 1 (6 ^ (t_primes m).card) ∧ ∀ a ∈ t_primes m, ∃ l : ℤ, |(k : ℝ) * ((Nat.choose (2 * m) m : ℝ) / (a : ℝ)) - (l : ℝ)| ≤ (1 : ℝ) / (6 : ℝ) :=
by
  exact dirichlet_simultaneous (t_primes m) (fun a => (Nat.choose (2 * m) m : ℝ) / (a : ℝ)) 6 (by norm_num)

theorem k_m_eq (m : ℕ) :
  k_m m = Classical.choose (k_m_exists m) :=
by
  unfold k_m
  exact dif_pos (k_m_exists m)

theorem k_m_spec_lemma (m : ℕ) (a : ℕ) (ha : a ∈ t_primes m) :
  ∃ l : ℤ, |(k_m m : ℝ) * ((Nat.choose (2 * m) m : ℝ) / (a : ℝ)) - (l : ℝ)| ≤ (1 : ℝ) / (6 : ℝ) :=
by
  rw [k_m_eq m]
  exact (Classical.choose_spec (k_m_exists m)).right a ha

theorem t_primes_prime (m p : ℕ) (hp : p ∈ t_primes m) : p.Prime :=
by
  simp only [t_primes, Finset.mem_filter] at hp
  exact hp.2

theorem t_primes_pos (m p : ℕ) (hp : p ∈ t_primes m) : (0 : ℝ) < (p : ℝ) :=
by
  -- Obtain the primality of p
  have h_prime : p.Prime := t_primes_prime m p hp
  -- A prime number is strictly greater than 0
  have h_pos : 0 < p := h_prime.pos
  -- Lift the positivity to the real numbers
  exact Nat.cast_pos.mpr h_pos

theorem approx_mul_p_algebra (k_val C p_val l_val : ℝ) (hp_pos : (0 : ℝ) < p_val) :
  k_val * C - l_val * p_val = (k_val * (C / p_val) - l_val) * p_val :=
by
  have : p_val ≠ 0 := ne_of_gt hp_pos
  field_simp

theorem approx_mul_p (k_val : ℝ) (C : ℝ) (p_val : ℝ) (l_val : ℝ) (hp_pos : (0 : ℝ) < p_val)
  (h_approx : |k_val * (C / p_val) - l_val| ≤ (1 : ℝ) / (6 : ℝ)) :
  |k_val * C - l_val * p_val| ≤ p_val / (6 : ℝ) :=
by
  calc
    |k_val * C - l_val * p_val| = |(k_val * (C / p_val) - l_val) * p_val| := by rw [approx_mul_p_algebra k_val C p_val l_val hp_pos]
    _ = |k_val * (C / p_val) - l_val| * |p_val| := abs_mul (k_val * (C / p_val) - l_val) p_val
    _ = |k_val * (C / p_val) - l_val| * p_val := by rw [abs_of_pos hp_pos]
    _ ≤ ((1 : ℝ) / (6 : ℝ)) * p_val := mul_le_mul_of_nonneg_right h_approx (le_of_lt hp_pos)
    _ = p_val / (6 : ℝ) := by ring

theorem cast_k_m_choose (m : ℕ) :
  (((k_m m : ℤ) * (Nat.choose (2 * m) m : ℤ) : ℝ)) = (k_m m : ℝ) * (Nat.choose (2 * m) m : ℝ) :=
by
  push_cast
  ring

theorem k_m_approx (m : ℕ) (p : ℕ) (hp : p ∈ t_primes m) :
  ∃ l : ℤ, |((k_m m : ℤ) * (Nat.choose (2 * m) m : ℤ) : ℝ) - (l : ℝ) * (p : ℝ)| ≤ (p : ℝ) / (6 : ℝ) :=
by
  have ⟨l, hl⟩ := k_m_spec_lemma m p hp
  refine ⟨l, ?_⟩
  rw [cast_k_m_choose m]
  exact approx_mul_p (k_m m : ℝ) (Nat.choose (2 * m) m : ℝ) (p : ℝ) (l : ℝ) (t_primes_pos m p hp) hl

theorem case3_p_in_t_primes (m p : ℕ) (hp1 : p.Prime) (hp2 : 2 * m < p) (hp3 : p ≤ 3 * m) :
    p ∈ t_primes m :=
by
  simp only [t_primes, Finset.mem_filter, Finset.mem_Ioc]
  exact ⟨⟨hp2, hp3⟩, hp1⟩

theorem real_cast_ge_10 (m : ℕ) (hm : 10 ≤ m) :
    (10 : ℝ) ≤ (m : ℝ) :=
by
  exact_mod_cast hm

theorem m_div_2_le_c_m_real (m : ℝ) (hm : (10 : ℝ) ≤ m) :
    m / (2 : ℝ) ≤ (3 * m) / (5 : ℝ) - (1 : ℝ) :=
by
  linarith

theorem real_sub_one_lt_nat_floor (x : ℝ) :
    x - (1 : ℝ) < (⌊x⌋₊ : ℝ) :=
by
  have h := Nat.lt_succ_floor x
  push_cast at h
  linarith

theorem case3_c_m_lower_bound (m : ℕ) (hm : 10 ≤ m) :
    (m : ℝ) / (2 : ℝ) < (c_m m : ℝ) :=
by
  -- 1. Replace c_m with its explicit mathematical floor function formulation
  rw [c_m_val m]

  -- 2. Obtain our required bounds via the extracted lemmas
  have hm_real := real_cast_ge_10 m hm
  have h1 := m_div_2_le_c_m_real (m : ℝ) hm_real
  have h2 := real_sub_one_lt_nat_floor ((3 * (m : ℝ)) / (5 : ℝ))

  -- 3. Solve the trivial resulting linear inequality system automatically
  linarith

theorem cast_ineq_helper (m p : ℕ) (hp : p ≤ 3 * m) : (p : ℝ) ≤ (3 : ℝ) * (m : ℝ) :=
by
  exact_mod_cast hp

theorem real_ineq_helper (X p m : ℝ) (h1 : |X| ≤ p / (6 : ℝ)) (h2 : p ≤ (3 : ℝ) * m) :
    X ≤ m / (2 : ℝ) :=
by
  have h3 : X ≤ p / (6 : ℝ) := le_of_abs_le h1
  linarith

theorem case3_X_le_m_div_2 (m p : ℕ) (l : ℤ) (hp : p ≤ 3 * m)
    (h_approx : |((k_m m : ℤ) * (Nat.choose (2 * m) m : ℤ) : ℝ) - (l : ℝ) * (p : ℝ)| ≤ (p : ℝ) / (6 : ℝ)) :
    ((k_m m : ℤ) * (Nat.choose (2 * m) m : ℤ) : ℝ) - (l : ℝ) * (p : ℝ) ≤ (m : ℝ) / (2 : ℝ) :=
real_ineq_helper (((k_m m : ℤ) * (Nat.choose (2 * m) m : ℤ) : ℝ) - (l : ℝ) * (p : ℝ)) (p : ℝ) (m : ℝ) h_approx (cast_ineq_helper m p hp)

theorem case3_i0_bounds_lower (m p : ℕ) (l : ℤ) (hm : 10 ≤ m) (hp : p ≤ 3 * m)
    (h_approx : |((k_m m : ℤ) * (Nat.choose (2 * m) m : ℤ) : ℝ) - (l : ℝ) * (p : ℝ)| ≤ (p : ℝ) / (6 : ℝ)) :
    (1 : ℤ) ≤ l * (p : ℤ) - ((k_m m : ℤ) * (Nat.choose (2 * m) m : ℤ)) + (c_m m : ℤ) :=
by
  have h1 := case3_X_le_m_div_2 m p l hp h_approx
  have h2 := case3_c_m_lower_bound m hm

  -- Combine sub-lemma bounds in ℝ
  have h3 : ((k_m m : ℤ) * (Nat.choose (2 * m) m : ℤ) : ℝ) - (l : ℝ) * (p : ℝ) < (c_m m : ℝ) := by
    linarith

  -- Setup an explicit casting identity to ensure robust typing
  have h4 : (((k_m m : ℤ) * (Nat.choose (2 * m) m : ℤ) - l * (p : ℤ)) : ℝ) < ((c_m m : ℤ) : ℝ) := by
    have eq1 : (((k_m m : ℤ) * (Nat.choose (2 * m) m : ℤ) - l * (p : ℤ)) : ℝ) = ((k_m m : ℤ) * (Nat.choose (2 * m) m : ℤ) : ℝ) - (l : ℝ) * (p : ℝ) := by push_cast; ring
    have eq2 : ((c_m m : ℤ) : ℝ) = (c_m m : ℝ) := by push_cast; ring
    linarith

  -- Push the strict bound strictly into ℤ natively
  have h5 : (k_m m : ℤ) * (Nat.choose (2 * m) m : ℤ) - l * (p : ℤ) < (c_m m : ℤ) := by
    exact_mod_cast h4

  -- Solve the pure integer arithmetic consequence logically identical to the strict inequality
  omega

theorem case3_i0_bounds_upper_X_lt_c_m (m p : ℕ) (l : ℤ) (hm : 10 ≤ m) (hp : p ≤ 3 * m)
    (h_approx : |((k_m m : ℤ) * (Nat.choose (2 * m) m : ℤ) : ℝ) - (l : ℝ) * (p : ℝ)| ≤ (p : ℝ) / (6 : ℝ)) :
    (l : ℝ) * (p : ℝ) - ((k_m m : ℤ) * (Nat.choose (2 * m) m : ℤ) : ℝ) < (c_m m : ℝ) :=
by

  -- Step 1: Cast the bound p ≤ 3 * m to real numbers
  have hp_real : (p : ℝ) ≤ 3 * (m : ℝ) := by exact_mod_cast hp

  -- Step 2: Use `abs_sub_le_iff` to extract the upper bound directly from the absolute value inequality
  -- |A - B| ≤ C ↔ A - B ≤ C ∧ B - A ≤ C
  -- taking `.right` yields `B - A ≤ C`, where `B = l * p` and `A = k_m * choose (2m) m`
  have h_abs_right := (abs_sub_le_iff.mp h_approx).right

  -- Step 3: Call the explicit lemma for the lower bound on c_m over ℝ
  have h_cm := case3_c_m_lower_bound m hm

  -- Step 4: Let `linarith` handle the transitivity chaining over ℝ
  -- h_abs_right : L - K ≤ p / 6
  -- hp_real     : p ≤ 3m   (hence p / 6 ≤ 3m / 6 = m / 2)
  -- h_cm        : m / 2 < c_m
  -- conclusion  : L - K < c_m
  linarith

theorem case3_i0_bounds_upper (m p : ℕ) (l : ℤ) (hm : 10 ≤ m) (hp : p ≤ 3 * m)
    (h_approx : |((k_m m : ℤ) * (Nat.choose (2 * m) m : ℤ) : ℝ) - (l : ℝ) * (p : ℝ)| ≤ (p : ℝ) / (6 : ℝ)) :
    l * (p : ℤ) - ((k_m m : ℤ) * (Nat.choose (2 * m) m : ℤ)) + (c_m m : ℤ) ≤ (2 : ℤ) * (c_m m : ℤ) - (1 : ℤ) :=
by
  have h1 := case3_i0_bounds_upper_X_lt_c_m m p l hm hp h_approx

  -- Lift the structure up into Reals ensuring that casting applies appropriately to map terms identical to `h1`.
  have h2 : ((l * (p : ℤ) - (k_m m : ℤ) * (Nat.choose (2 * m) m : ℤ) : ℤ) : ℝ) < ((c_m m : ℤ) : ℝ) := by
    push_cast at h1 ⊢
    exact h1

  -- Mod-cast simplifies out the outer real cast wrapping ensuring the expression translates strictly to Int.
  have h3 : l * (p : ℤ) - (k_m m : ℤ) * (Nat.choose (2 * m) m : ℤ) < (c_m m : ℤ) := by
    exact_mod_cast h2

  -- Now operating strictly over Integers, `omega` solves `A < B → A + B ≤ 2*B - 1`.
  omega

theorem case3_i0_bounds (m p : ℕ) (l : ℤ) (hm : 10 ≤ m) (hp : p ≤ 3 * m)
    (h_approx : |((k_m m : ℤ) * (Nat.choose (2 * m) m : ℤ) : ℝ) - (l : ℝ) * (p : ℝ)| ≤ (p : ℝ) / (6 : ℝ)) :
    (1 : ℤ) ≤ l * (p : ℤ) - ((k_m m : ℤ) * (Nat.choose (2 * m) m : ℤ)) + (c_m m : ℤ) ∧
    l * (p : ℤ) - ((k_m m : ℤ) * (Nat.choose (2 * m) m : ℤ)) + (c_m m : ℤ) ≤ (2 : ℤ) * (c_m m : ℤ) - (1 : ℤ) :=
by
  constructor
  · exact case3_i0_bounds_lower m p l hm hp h_approx
  · exact case3_i0_bounds_upper m p l hm hp h_approx

theorem case3_i0_to_nat (m p : ℕ) (l : ℤ) (hL : 2 * c_m m ≤ L_m m + 1)
    (h_bounds : (1 : ℤ) ≤ l * (p : ℤ) - ((k_m m : ℤ) * (Nat.choose (2 * m) m : ℤ)) + (c_m m : ℤ) ∧
                l * (p : ℤ) - ((k_m m : ℤ) * (Nat.choose (2 * m) m : ℤ)) + (c_m m : ℤ) ≤ (2 : ℤ) * (c_m m : ℤ) - (1 : ℤ)) :
    ∃ i_nat : ℕ, (i_nat : ℤ) = l * (p : ℤ) - ((k_m m : ℤ) * (Nat.choose (2 * m) m : ℤ)) + (c_m m : ℤ) ∧
                 i_nat ∈ Finset.Icc 1 (L_m m) :=
by
  use (l * (p : ℤ) - ((k_m m : ℤ) * (Nat.choose (2 * m) m : ℤ)) + (c_m m : ℤ)).toNat
  have hi_nat : ((l * (p : ℤ) - ((k_m m : ℤ) * (Nat.choose (2 * m) m : ℤ)) + (c_m m : ℤ)).toNat : ℤ) = l * (p : ℤ) - ((k_m m : ℤ) * (Nat.choose (2 * m) m : ℤ)) + (c_m m : ℤ) := by omega
  refine ⟨hi_nat, ?_⟩
  rw [Finset.mem_Icc]
  constructor <;> omega

theorem case3_n_m_eq_int (m : ℕ) :
  (n_m m : ℤ) = (k_m m : ℤ) * (Nat.choose (2 * m) m : ℤ) - (c_m m : ℤ) :=
by
  have h : (n_m m : ℤ) + (c_m m : ℤ) = (k_m m : ℤ) * (Nat.choose (2 * m) m : ℤ) := by
    exact_mod_cast n_m_add_c_m m
  omega

theorem case3_n_m_add_i_nat_eq (m p i_nat : ℕ) (l : ℤ)
    (hi : (i_nat : ℤ) = l * (p : ℤ) - ((k_m m : ℤ) * (Nat.choose (2 * m) m : ℤ)) + (c_m m : ℤ)) :
    (n_m m + i_nat : ℤ) = l * (p : ℤ) :=
by
  push_cast
  rw [case3_n_m_eq_int m]
  rw [hi]
  ring

theorem case3_p_dvd_n_m_add_i (m p i_nat : ℕ) (l : ℤ)
    (hi : (i_nat : ℤ) = l * (p : ℤ) - ((k_m m : ℤ) * (Nat.choose (2 * m) m : ℤ)) + (c_m m : ℤ)) :
    p ∣ n_m m + i_nat :=
by
  have h_eq := case3_n_m_add_i_nat_eq m p i_nat l hi
  -- We provide l as the witness for integer divisibility and match terms.
  have hdvd : (p : ℤ) ∣ (n_m m + i_nat : ℤ) := ⟨l, by rw [h_eq, mul_comm]⟩
  -- Automatically cast the structural divisibility back down to Natural Numbers.
  exact_mod_cast hdvd

theorem case3_dvd_prod (m p L i_nat : ℕ) (hi : i_nat ∈ Finset.Icc 1 L) (hdiv : p ∣ n_m m + i_nat) :
    p ∣ ∏ i ∈ Finset.Icc 1 L, (n_m m + i) :=
dvd_trans hdiv (Finset.dvd_prod_of_mem (fun i => n_m m + i) hi)

theorem case3_div (m : ℕ) (p : ℕ) (hp1 : p.Prime) (hp2 : 2 * m < p) (hp3 : p ≤ 3 * m)
    (hc1 : 10 ≤ m) (hL : 2 * c_m m ≤ L_m m + 1) :
  p ∣ ∏ i ∈ Finset.Icc 1 (L_m m), (n_m m + i) :=
by
  -- Step 1: Prove membership in t_primes
  have hp_t : p ∈ t_primes m := case3_p_in_t_primes m p hp1 hp2 hp3

  -- Step 2: Use Dirichlet's approximation to obtain multiplier l : ℤ
  have hex : ∃ l : ℤ, |((k_m m : ℤ) * (Nat.choose (2 * m) m : ℤ) : ℝ) - (l : ℝ) * (p : ℝ)| ≤ (p : ℝ) / (6 : ℝ) :=
    k_m_approx m p hp_t
  obtain ⟨l, hl⟩ := hex

  -- Step 3: Establish bounds for our target bounded integer index
  have h_bounds := case3_i0_bounds m p l hc1 hp3 hl

  -- Step 4: Cast valid integer bounds down to Natural bounds and confirm member length in 1..L_m
  have hi_ex := case3_i0_to_nat m p l hL h_bounds
  obtain ⟨i_nat, hi_eq, hi_mem⟩ := hi_ex

  -- Step 5: Validate division p ∣ (n_m m + i_nat)
  have hdiv : p ∣ n_m m + i_nat := case3_p_dvd_n_m_add_i m p i_nat l hi_eq

  -- Step 6: Expand property to division among bounded set elements over Finset sequence product
  exact case3_dvd_prod m p (L_m m) i_nat hi_mem hdiv

theorem c_m_real_bound (m : ℕ) (hm : 10 ≤ m) : (1 : ℝ) ≤ (3 * (m : ℝ)) / (5 : ℝ) :=
by
  have hm_R : (10 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  linarith

theorem one_le_floor_of_one_le_real (x : ℝ) (hx : (1 : ℝ) ≤ x) : 1 ≤ ⌊x⌋₊ :=
by
  exact Nat.floor_pos.mpr hx

theorem c_m_bound1 (m : ℕ) (hm : 10 ≤ m) : 1 ≤ c_m m :=
by
  rw [c_m_val m]
  exact one_le_floor_of_one_le_real ((3 * (m : ℝ)) / (5 : ℝ)) (c_m_real_bound m hm)

theorem c_m_le_floor_six_fifths (m : ℕ) : c_m m ≤ ⌊(6 * (m : ℝ)) / (5 : ℝ)⌋₊ :=
by
  unfold c_m
  apply Nat.floor_mono
  have : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  linarith

theorem two_mul_floor_le_floor_two_mul (x : ℝ) (hx : 0 ≤ x) : 2 * ⌊x⌋₊ ≤ ⌊2 * x⌋₊ :=
by
  have h_pos : (0 : ℝ) ≤ 2 * x := by linarith
  rw [Nat.le_floor_iff h_pos]
  push_cast
  have h1 : (⌊x⌋₊ : ℝ) ≤ x := (Nat.le_floor_iff hx).mp (le_refl ⌊x⌋₊)
  linarith

theorem c_m_val_eq (m : ℕ) : c_m m = ⌊(3 * (m : ℝ)) / (5 : ℝ)⌋₊ :=
by
  rfl

theorem two_mul_c_m_le_floor_six_fifths (m : ℕ) : 2 * c_m m ≤ ⌊(6 * (m : ℝ)) / (5 : ℝ)⌋₊ :=
by
  -- Apply the assumed definition of c_m
  rw [c_m_val_eq]

  -- The interior fraction is naturally non-negative
  have hx : 0 ≤ (3 * (m : ℝ)) / (5 : ℝ) := by positivity

  -- Use our rigorous helper lemma
  have h := two_mul_floor_le_floor_two_mul ((3 * (m : ℝ)) / (5 : ℝ)) hx

  -- Equate real arithmetic to perfectly match the right hand side
  have h_eq : (2 : ℝ) * ((3 * (m : ℝ)) / (5 : ℝ)) = (6 * (m : ℝ)) / (5 : ℝ) := by ring

  -- Finish the proof by substituting this equivalence
  rw [h_eq] at h
  exact h

theorem p_le_three_m {p m : ℕ} (hp : p ≤ (2.1 : ℝ) * Real.log (n_m m)) (h_log : (2.1 : ℝ) * Real.log (n_m m) < 3 * (m : ℝ)) : p ≤ 3 * m :=
by
  have h : (p : ℝ) < 3 * (m : ℝ) := by linarith
  have h2 : (p : ℝ) ≤ ((3 * m : ℕ) : ℝ) := by
    push_cast
    exact h.le
  exact_mod_cast h2

theorem all_primes_div_eventually :
  ∀ᶠ (m : ℕ) in Filter.atTop, ∀ (p : ℕ), p ≤ (2.1 : ℝ) * Real.log (n_m m) → p.Prime →
    p ∣ ∏ i ∈ Finset.Icc 1 ⌊Real.log (n_m m)⌋₊, (n_m m + i) :=
by
  -- Intersect the eventually true filters
  filter_upwards [log_n_m_upper_eventually, L_m_lower_eventually, Filter.eventually_ge_atTop 10] with m h_log h_L hm

  -- Introduce variables and adjust the goal format to use L_m
  intro p hp h_prime
  rw [← L_m_eq_floor_log m]

  -- Deduce universal upper limit for p
  have hp_3m : p ≤ 3 * m := p_le_three_m hp h_log

  -- Branch out into the 3 Cases
  by_cases hp1 : p ≤ m
  · have H1 : m ≤ ⌊(6 * (m : ℝ)) / (5 : ℝ)⌋₊ := m_le_floor_six_fifths m
    have hL_m : m ≤ L_m m := le_trans H1 h_L
    exact case1_div m p h_prime hp1 hL_m
  · have hp1_lt : m < p := by omega
    by_cases hp2 : p ≤ 2 * m
    · have H1 : c_m m ≤ ⌊(6 * (m : ℝ)) / (5 : ℝ)⌋₊ := c_m_le_floor_six_fifths m
      have hc_L : c_m m ≤ L_m m := le_trans H1 h_L
      have hc_pos : 1 ≤ c_m m := c_m_bound1 m hm
      exact case2_div m p h_prime hp1_lt hp2 hc_L hc_pos
    · have hp2_lt : 2 * m < p := by omega
      have H1 : 2 * c_m m ≤ ⌊(6 * (m : ℝ)) / (5 : ℝ)⌋₊ := two_mul_c_m_le_floor_six_fifths m
      have H2 : 2 * c_m m ≤ L_m m := le_trans H1 h_L
      have h2c_L : 2 * c_m m ≤ L_m m + 1 := by omega
      exact case3_div m p h_prime hp2_lt hp_3m hm h2c_L

theorem n_m_tendsto :
  Filter.Tendsto n_m Filter.atTop Filter.atTop :=
by
  apply Filter.tendsto_atTop_mono' Filter.atTop m_le_n_m_eventually
  exact Filter.tendsto_id

theorem finite_eventually_not {P : ℕ → Prop} (h : {n | P n}.Finite) : ∀ᶠ n in Filter.atTop, ¬ P n :=
by
  by_contra h_contra
  -- h_contra : ¬ ∀ᶠ n in Filter.atTop, ¬ P n
  -- This is definitionally equivalent to: ∃ᶠ n in Filter.atTop, P n
  have h_inf : {n | P n}.Infinite := Nat.frequently_atTop_iff_infinite.mp h_contra
  -- Set.Infinite is defined as ¬ Set.Finite, so we can directly apply it to h to get a contradiction.
  exact h_inf h

theorem infinite_of_tendsto (f : ℕ → ℕ) (hf : Filter.Tendsto f Filter.atTop Filter.atTop)
    (P : ℕ → Prop) (hP : ∀ᶠ (m : ℕ) in Filter.atTop, P (f m)) :
  {n | P n}.Infinite :=
by
  -- Assume the set is finite for the sake of contradiction
  -- Set.Infinite is definitionally `¬ Set.Finite`, so `intro` gives us the finite hypothesis directly.
  intro h_fin

  -- 1. Because the set is finite, its complement eventually holds for all elements as we approach atTop.
  have h1 : ∀ᶠ n in Filter.atTop, ¬ P n := finite_eventually_not h_fin

  -- 2. By the limit definition `Tendsto f atTop atTop`, preimages map eventually back to `atTop`.
  have h2 : ∀ᶠ m in Filter.atTop, ¬ P (f m) := hf.eventually h1

  -- 3. We intersect our new eventual condition with the one provided in the hypothesis.
  have h3 : ∀ᶠ m in Filter.atTop, ¬ P (f m) ∧ P (f m) := h2.and hP

  -- 4. An intersection of `¬ P (f m)` and `P (f m)` monotonically implies `False`.
  have h4 : ∀ᶠ m in Filter.atTop, False := h3.mono (fun _ hm => hm.1 hm.2)

  -- 5. The filter `atTop` on `ℕ` is non-degenerate (`NeBot`), so an eventual `False` must actually instantiate a contradiction.
  have ⟨_, hm⟩ := Filter.Eventually.exists h4

  -- 6. Goal is fully resolved
  exact hm

theorem erdos_457 : ∃ ε > (0 : ℝ),
    { (n : ℕ) | ∀ (p : ℕ), p ≤ (2 + ε) * Real.log n → p.Prime →
      p ∣ ∏ i ∈ Finset.Icc 1 ⌊Real.log n⌋₊, (n + i) }.Infinite :=
by
  use (0.1 : ℝ)
  refine ⟨by norm_num, ?_⟩
  have H : (2 : ℝ) + 0.1 = 2.1 := by norm_num
  simp_rw [H]
  exact infinite_of_tendsto n_m n_m_tendsto _ all_primes_div_eventually
