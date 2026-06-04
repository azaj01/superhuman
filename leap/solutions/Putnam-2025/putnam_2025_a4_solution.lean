import Mathlib
abbrev putnam_2025_a4_solution : ℕ := 3

open scoped BigOperators
def u (i : Fin 2025) : Fin 3 → ℝ :=
  ![1, (i.val : ℝ), (i.val : ℝ)^2]
def v (i : Fin 2025) : Fin 3 → ℝ :=
  ![((i - 1).val : ℝ) * ((i + 1).val : ℝ)^2 - ((i - 1).val : ℝ)^2 * ((i + 1).val : ℝ),
    ((i - 1).val : ℝ)^2 - ((i + 1).val : ℝ)^2,
    ((i + 1).val : ℝ) - ((i - 1).val : ℝ)]
def A (i : Fin 2025) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun r c ↦ u i r * v i c

def D (i j : Fin 2025) : ℝ :=
  (((i + 1).val : ℝ) - ((i - 1).val : ℝ)) * (((j.val : ℝ) - ((i - 1).val : ℝ)) * ((j.val : ℝ) - ((i + 1).val : ℝ)))

theorem sol_eq : putnam_2025_a4_solution = 3 :=
rfl

theorem sum_fin_3_expand (f : Fin 3 → ℝ) :
  ∑ k : Fin 3, f k = f 0 + f 1 + f 2 :=
by
  exact Fin.sum_univ_three f

theorem u_eval_0 (i : Fin 2025) : u i 0 = 1 :=
by
  rfl

theorem u_eval_1 (i : Fin 2025) : u i 1 = (i.val : ℝ) :=
rfl

theorem u_eval_2 (i : Fin 2025) : u i 2 = (i.val : ℝ)^2 :=
by
  rfl

theorem v_eval_0 (i : Fin 2025) :
  v i 0 = ((i - 1).val : ℝ) * ((i + 1).val : ℝ)^2 - ((i - 1).val : ℝ)^2 * ((i + 1).val : ℝ) :=
rfl

theorem v_eval_1 (i : Fin 2025) :
  v i 1 = ((i - 1).val : ℝ)^2 - ((i + 1).val : ℝ)^2 :=
by
  rfl

theorem v_eval_2 (i : Fin 2025) :
  v i 2 = ((i + 1).val : ℝ) - ((i - 1).val : ℝ) :=
by
  rfl

theorem v_dot_u_eq_D (i j : Fin 2025) : ∑ k : Fin 3, v i k * u j k = D i j :=
by
  -- 1. Expand the sum over Fin 3 explicitly into three additions.
  rw [sum_fin_3_expand]

  -- 2. Substitute the values of vector `u` evaluated at indexes 0, 1, and 2.
  rw [u_eval_0, u_eval_1, u_eval_2]

  -- 3. Substitute the values of vector `v` evaluated at indexes 0, 1, and 2.
  rw [v_eval_0, v_eval_1, v_eval_2]

  -- 4. Unfold the exact mathematical definition of the scalar polynomial D.
  unfold D

  -- 5. Complete the proof through direct real algebraic resolution.
  ring

theorem A_mul_A_apply (i j : Fin 2025) (r c : Fin 3) : (A i * A j) r c = u i r * D i j * v j c :=
by
  rw [Matrix.mul_apply]
  calc
    (∑ k : Fin 3, A i r k * A j k c)
      = ∑ k : Fin 3, u i r * (v i k * u j k) * v j c := by
        apply Finset.sum_congr rfl
        intro k _
        change (u i r * v i k) * (u j k * v j c) = u i r * (v i k * u j k) * v j c
        ring
    _ = (∑ k : Fin 3, u i r * (v i k * u j k)) * v j c := by rw [← Finset.sum_mul]
    _ = u i r * (∑ k : Fin 3, v i k * u j k) * v j c := by rw [← Finset.mul_sum]
    _ = u i r * D i j * v j c := by rw [v_dot_u_eq_D i j]

theorem i_add_one_val_of_j_val_eq (i j : Fin 2025) (h : j.val = i.val + 1) : (i + 1).val = j.val :=
by
  omega

theorem D_eq_zero_of_j_val_eq_i_add_one (i j : Fin 2025) (h : (i + 1).val = j.val) : D i j = 0 :=
by
  unfold D
  rw [← h]
  ring

theorem A_mul_A_eq_zero_of_j_eq_i_add_one (i j : Fin 2025) (h : j.val = i.val + 1) :
  A i * A j = 0 :=
by
  ext r c
  have h1 : (i + 1).val = j.val := i_add_one_val_of_j_val_eq i j h
  have h2 : D i j = 0 := D_eq_zero_of_j_val_eq_i_add_one i j h1
  rw [A_mul_A_apply i j r c, h2]
  simp

theorem j_minus_one_val_of_j_val_eq (i j : Fin 2025) (h : j.val = i.val + 1) :
  (j - 1).val = i.val :=
by
  omega

theorem fin_2_sum (f : Fin 2 → ℝ) : ∑ k : Fin 2, f k = f 0 + f 1 :=
by
  rw [Fin.sum_univ_two]

theorem fin_3_sum_eq (f : Fin 3 → ℝ) : ∑ k : Fin 3, f k = f 0 + f 1 + f 2 :=
by
  -- Peel off the 0th index term. The remaining summation evaluates over `Fin 2`.
  rw [Fin.sum_univ_succ]

  -- Apply our defined lemma to strictly evaluate the nested `Fin 2` sum.
  rw [fin_2_sum]

  -- Now our goal takes the definitionally equal form `f 0 + (f 1 + f 2) = (f 0 + f 1) + f 2`.
  -- We isolate the algebraic proof that simply re-associates the additions to match definitions.
  have H : f 0 + (f 1 + f 2) = f 0 + f 1 + f 2 := by rw [← add_assoc]

  -- Because `Fin.succ 0` is exactly `1 : Fin 3` and `Fin.succ 1` is exactly `2 : Fin 3`,
  -- `H` perfectly resolves the remaining equivalence.
  exact H

theorem sum_v_mul_u_eq_zero (i j : Fin 2025) (h : (j - 1).val = i.val) :
  ∑ k : Fin 3, v j k * u i k = 0 :=
by
  rw [fin_3_sum_eq]
  simp only [u_eval_0, u_eval_1, u_eval_2, v_eval_0, v_eval_1, v_eval_2]
  have h_val : (i.val : ℝ) = ((j - 1).val : ℝ) := by rw [← h]
  rw [h_val]
  ring

theorem term_rearrange (a b c d : ℝ) : (a * b) * (c * d) = a * (b * c) * d :=
by
  ring

theorem A_mul_A_apply_alt (i j : Fin 2025) (r c : Fin 3) :
  (A j * A i) r c = u j r * (∑ k : Fin 3, v j k * u i k) * v i c :=
by
  -- 1. Unpack matrix multiplication definition and unfold the definition of A
  simp only [Matrix.mul_apply, A]

  -- 2. Rearrange the multiplicands inside the summation
  simp_rw [term_rearrange]

  -- 3. Factor out the variables that are independent of the summation index 'k'
  rw [← Finset.sum_mul, ← Finset.mul_sum]

theorem A_mul_A_eq_zero_of_j_eq_i_add_one_rev (i j : Fin 2025) (h : j.val = i.val + 1) :
  A j * A i = 0 :=
by
  ext r c
  change (A j * A i) r c = 0
  have h1 : (j - 1).val = i.val := j_minus_one_val_of_j_val_eq i j h
  have h2 : ∑ k : Fin 3, v j k * u i k = 0 := sum_v_mul_u_eq_zero i j h1
  rw [A_mul_A_apply_alt i j r c, h2]
  ring

theorem i_sub_one_val_eq_2024 (i : Fin 2025) (hi : i.val = 0) : (i - 1).val = 2024 :=
by
  omega

theorem D_eq_zero_of_j_val_eq_i_sub_one_val (i j : Fin 2025) (h : j.val = (i - 1).val) : D i j = 0 :=
by
  unfold D
  rw [h]
  ring

theorem D_eq_zero_of_j_last_i_zero (i j : Fin 2025) (hi : i.val = 0) (hj : j.val = 2024) : D i j = 0 :=
D_eq_zero_of_j_val_eq_i_sub_one_val i j (hj.trans (i_sub_one_val_eq_2024 i hi).symm)

theorem A_mul_A_eq_zero_of_j_last_i_zero (i j : Fin 2025) (hi : i.val = 0) (hj : j.val = 2024) :
  A i * A j = 0 :=
by
  ext r c
  simp [A_mul_A_apply, D_eq_zero_of_j_last_i_zero i j hi hj]

theorem j_add_one_val_eq_zero (j : Fin 2025) (hj : j.val = 2024) : (j + 1).val = 0 :=
by
  omega

theorem D_j_i_eq_zero (i j : Fin 2025) (hi : i.val = 0) (hj : j.val = 2024) : D j i = 0 :=
by
  unfold D
  have hj' : (j + 1).val = 0 := j_add_one_val_eq_zero j hj
  rw [hi, hj']
  ring

theorem A_mul_A_eq_zero_of_D_eq_zero (a b : Fin 2025) (h : D a b = 0) : A a * A b = 0 :=
by
  ext r c
  rw [A_mul_A_apply, h]
  simp

theorem A_mul_A_eq_zero_of_j_last_i_zero_rev (i j : Fin 2025) (hi : i.val = 0) (hj : j.val = 2024) :
  A j * A i = 0 :=
by
  have h_D : D j i = 0 := D_j_i_eq_zero i j hi hj
  exact A_mul_A_eq_zero_of_D_eq_zero j i h_D

theorem A_comm_of_mem (i j : Fin 2025) (h : j.val - i.val ∈ ({0, 1, 2024} : Set ℕ)) (hij : i ≤ j) :
  A i * A j = A j * A i :=
by
  -- Expand the set membership into explicitly testable logical Ors
  simp_rw [Set.mem_insert_iff, Set.mem_singleton_iff] at h

  -- Bring bounded properties of `Fin` into context for the `omega` tactic
  have h_le : i.val ≤ j.val := hij
  have hi_lt : i.val < 2025 := i.isLt
  have hj_lt : j.val < 2025 := j.isLt

  rcases h with h0 | h1 | h2024
  · -- Case 0: j.val - i.val = 0
    have h_eq : i = j := Fin.ext (by omega)
    rw [h_eq]

  · -- Case 1: j.val - i.val = 1
    have hj : j.val = i.val + 1 := by omega

    -- Matrix multiplication yields the zero matrix commutatively
    rw [A_mul_A_eq_zero_of_j_eq_i_add_one i j hj, A_mul_A_eq_zero_of_j_eq_i_add_one_rev i j hj]

  · -- Case 2024: j.val - i.val = 2024
    -- Considering i <= j and max domain sizes, the only solution to this index difference is i = 0 and j = 2024
    have hi : i.val = 0 := by omega
    have hj : j.val = 2024 := by omega

    -- Similarly, evaluating to the zero matrix commutatively finishes the sub-case
    rw [A_mul_A_eq_zero_of_j_last_i_zero i j hi hj, A_mul_A_eq_zero_of_j_last_i_zero_rev i j hi hj]

theorem val_add_one_neq_val_sub_one (i : Fin 2025) : (i + 1).val ≠ (i - 1).val :=
by
  omega

theorem neighbor_diff_neq_zero (i : Fin 2025) : ((i + 1).val : ℝ) - ((i - 1).val : ℝ) ≠ (0 : ℝ) :=
by
  intro h
  -- If the difference is zero, the two real values must be equal.
  have h1 : ((i + 1).val : ℝ) = ((i - 1).val : ℝ) := sub_eq_zero.mp h

  -- Since the real casts are equal, their underlying natural values must also be equal.
  have h2 : (i + 1).val = (i - 1).val := by exact_mod_cast h1

  -- Use our helper lemma which establishes this is impossible in Fin 2025.
  exact val_add_one_neq_val_sub_one i h2

theorem fin_2025_sub_one_val_zero (i : Fin 2025) (h : i.val = 0) :
  (i - 1).val = 2024 :=
by
  have hi : i = 0 := by
    ext
    exact h
  rw [hi]
  rfl

theorem fin_2025_sub_one_val_pos (i : Fin 2025) (h : i.val > 0) :
  i.val = (i - 1).val + 1 :=
by
  omega

theorem j_neq_i_sub_one (i j : Fin 2025) (hij : i ≤ j) (h : j.val - i.val ∉ ({0, 1, 2024} : Set ℕ)) : j.val ≠ (i - 1).val :=
by
  intro heq
  have hij' : i.val ≤ j.val := hij
  have h_cases : i.val = 0 ∨ i.val > 0 := by omega
  rcases h_cases with h0 | hp
  · have h1 := fin_2025_sub_one_val_zero i h0
    have h2 : j.val - i.val ≠ 2024 := by
      intro hc
      apply h
      rw [hc]
      simp
    omega
  · have h1 := fin_2025_sub_one_val_pos i hp
    omega

theorem fin_2025_add_one_val_of_lt (i : Fin 2025) (h : i.val < 2024) :
  (i + 1).val = i.val + 1 :=
by
  omega

theorem fin_2025_add_one_val_eq_zero (i : Fin 2025) (h : i.val = 2024) :
  (i + 1).val = 0 :=
by
  omega

theorem j_neq_i_add_one (i j : Fin 2025) (hij : i ≤ j) (h : j.val - i.val ∉ ({0, 1, 2024} : Set ℕ)) : j.val ≠ (i + 1).val :=
by
  intro heq
  -- Expand the set membership representation to a logical disjunction
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h

  -- Expose hypotheses properties clearly to the context for `omega` to utilize
  have ij_le : i.val ≤ j.val := hij
  have i_lt := i.isLt

  -- Case split on whether `i.val` is at its maximal threshold before wrap-around
  have ival_cases : i.val = 2024 ∨ i.val < 2024 := by omega
  rcases ival_cases with hieq | hil
  · -- Case 1: `i.val = 2024`
    -- Under this case, (i + 1) wraps around to 0
    have hi1 : (i + 1).val = 0 := fin_2025_add_one_val_eq_zero i hieq
    -- The derived hypothesis `j.val = 0` cleanly contradicts `2024 ≤ j.val`
    omega
  · -- Case 2: `i.val < 2024`
    -- Under this case, (i + 1).val steps up by 1 like standard natural number addition
    have hi1 : (i + 1).val = i.val + 1 := fin_2025_add_one_val_of_lt i hil
    -- The derived hypothesis `j.val = i.val + 1` mathematically contradicts `j.val - i.val ≠ 1` evaluated natively
    omega

theorem j_neq_neighbors (i j : Fin 2025) (hij : i ≤ j) (h : j.val - i.val ∉ ({0, 1, 2024} : Set ℕ)) :
  (j.val : ℝ) - ((i - 1).val : ℝ) ≠ (0 : ℝ) ∧ (j.val : ℝ) - ((i + 1).val : ℝ) ≠ (0 : ℝ) :=
by
  constructor
  · intro h1
    apply j_neq_i_sub_one i j hij h
    exact_mod_cast sub_eq_zero.mp h1
  · intro h1
    apply j_neq_i_add_one i j hij h
    exact_mod_cast sub_eq_zero.mp h1

theorem real_system_step1 (vi vj I J Dij Dji : ℝ)
  (eq0 : Dij * vj = Dji * vi)
  (eq1 : I * Dij * vj = J * Dji * vi) :
  (I - J) * Dij * vj = (0 : ℝ) :=
by
  calc
    (I - J) * Dij * vj = I * Dij * vj - J * (Dij * vj) := by ring
    _ = J * Dji * vi - J * (Dji * vi) := by rw [eq1, eq0]
    _ = 0 := by ring

theorem real_system_step2 (vj I J Dij : ℝ)
  (hI_neq_J : I - J ≠ (0 : ℝ))
  (hvj_neq : vj ≠ (0 : ℝ))
  (h_prod : (I - J) * Dij * vj = (0 : ℝ)) :
  Dij = (0 : ℝ) :=
by
  -- In Lean, multiplication is left-associative, so `(I - J) * Dij * vj`
  -- is equivalent to `((I - J) * Dij) * vj`.
  have h1 : (I - J) * Dij = 0 ∨ vj = 0 := mul_eq_zero.mp h_prod
  cases h1 with
  | inl h2 =>
    -- Case where `(I - J) * Dij = 0`
    have h3 : I - J = 0 ∨ Dij = 0 := mul_eq_zero.mp h2
    cases h3 with
    | inl h4 =>
      -- `I - J = 0` contradicts `hI_neq_J`
      exact False.elim (hI_neq_J h4)
    | inr h5 =>
      -- `Dij = 0`, which is our target goal
      exact h5
  | inr h6 =>
    -- Case where `vj = 0`, which contradicts `hvj_neq`
    exact False.elim (hvj_neq h6)

theorem real_system_eq_zero (vi vj I J Dij Dji : ℝ)
  (hI_neq_J : I - J ≠ (0 : ℝ))
  (hvj_neq : vj ≠ (0 : ℝ))
  (eq0 : Dij * vj = Dji * vi)
  (eq1 : I * Dij * vj = J * Dji * vi) :
  Dij = (0 : ℝ) :=
by
  have h1 : (I - J) * Dij * vj = (0 : ℝ) := real_system_step1 vi vj I J Dij Dji eq0 eq1
  have h2 : Dij = (0 : ℝ) := real_system_step2 vj I J Dij hI_neq_J hvj_neq h1
  exact h2

theorem fin_three_sum (f : Fin 3 → ℝ) :
  ∑ k : Fin 3, f k = f (0 : Fin 3) + f (1 : Fin 3) + f (2 : Fin 3) :=
by
  exact Fin.sum_univ_three f

theorem A_mul_A_0_2 (i j : Fin 2025) :
  (A i * A j) (0 : Fin 3) (2 : Fin 3) = D i j * v j (2 : Fin 3) :=
by
  simp only [Matrix.mul_apply]
  rw [fin_three_sum]
  simp [A, u, v, D]
  ring

theorem get_eq0 (i j : Fin 2025) (h : A i * A j = A j * A i) :
  D i j * v j (2 : Fin 3) = D j i * v i (2 : Fin 3) :=
by
  rw [← A_mul_A_0_2 i j, ← A_mul_A_0_2 j i, h]

theorem my_A_def (i : Fin 2025) (r c : Fin 3) : A i r c = u i r * v i c :=
rfl

theorem my_fin_three_sum (f : Fin 3 → ℝ) :
  Finset.sum Finset.univ f = f (0 : Fin 3) + f (1 : Fin 3) + f (2 : Fin 3) :=
by
  rw [Fin.sum_univ_three]

theorem my_u_eval_one (i : Fin 2025) :
  u i (1 : Fin 3) = (i.val : ℝ) :=
rfl

theorem lemma_u_eval_zero (i : Fin 2025) :
  u i (0 : Fin 3) = (1 : ℝ) :=
rfl

theorem my_lemma_u_eval_one (i : Fin 2025) :
  u i (1 : Fin 3) = (i.val : ℝ) :=
rfl

theorem lemma_u_eval_two (i : Fin 2025) :
  u i (2 : Fin 3) = (i.val : ℝ)^2 :=
rfl

theorem lemma_v_eval_zero (i : Fin 2025) :
  v i (0 : Fin 3) = ((i - 1).val : ℝ) * ((i + 1).val : ℝ)^2 - ((i - 1).val : ℝ)^2 * ((i + 1).val : ℝ) :=
rfl

theorem lemma_v_eval_one (i : Fin 2025) :
  v i (1 : Fin 3) = ((i - 1).val : ℝ)^2 - ((i + 1).val : ℝ)^2 :=
by
  rfl

theorem lemma_v_eval_two (i : Fin 2025) :
  v i (2 : Fin 3) = ((i + 1).val : ℝ) - ((i - 1).val : ℝ) :=
by
  rfl

theorem lemma_D_eval (i j : Fin 2025) :
  D i j = (((i + 1).val : ℝ) - ((i - 1).val : ℝ)) *
          ((j.val : ℝ) - ((i - 1).val : ℝ)) *
          ((j.val : ℝ) - ((i + 1).val : ℝ)) :=
by
  unfold D
  ring

theorem my_v_u_inner_eq_D (i j : Fin 2025) :
  v i (0 : Fin 3) * u j (0 : Fin 3) +
  v i (1 : Fin 3) * u j (1 : Fin 3) +
  v i (2 : Fin 3) * u j (2 : Fin 3) = D i j :=
by
  simp only [
    lemma_v_eval_zero, lemma_u_eval_zero,
    lemma_v_eval_one, my_lemma_u_eval_one,
    lemma_v_eval_two, lemma_u_eval_two,
    lemma_D_eval
  ]
  ring

theorem A_mul_A_1_2 (i j : Fin 2025) :
  (A i * A j) (1 : Fin 3) (2 : Fin 3) = (i.val : ℝ) * D i j * v j (2 : Fin 3) :=
by
  have h_D := my_v_u_inner_eq_D i j

  -- Step 1: Unfold matrix multiplication formula which introduces the summation over Fin 3
  rw [Matrix.mul_apply]

  -- Step 2: Unfold the matrix `A` components into functions `u` and `v`
  simp only [my_A_def]

  -- Step 3: Explicitly evaluate the Fin 3 summation into three concrete real expressions
  simp only [my_fin_three_sum]

  -- Step 4: Substitute `u i (1 : Fin 3)` with exactly `(i.val : ℝ)`
  -- (We explicitly bind `i` to avoid rewriting `u j 1`)
  simp only [my_u_eval_one i]

  -- Step 5: Inject the encapsulated expansion of `D i j` into the right-hand side
  rw [← h_D]

  -- Step 6: With all constants cleanly laid out in ℝ, close the exact polynomial equivalence
  ring

theorem get_eq1 (i j : Fin 2025) (h : A i * A j = A j * A i) :
  (i.val : ℝ) * D i j * v j (2 : Fin 3) = (j.val : ℝ) * D j i * v i (2 : Fin 3) :=
by
  have h1 : (A i * A j) (1 : Fin 3) (2 : Fin 3) = (i.val : ℝ) * D i j * v j (2 : Fin 3) := A_mul_A_1_2 i j
  have h2 : (A j * A i) (1 : Fin 3) (2 : Fin 3) = (j.val : ℝ) * D j i * v i (2 : Fin 3) := A_mul_A_1_2 j i
  rw [← h1, h, h2]

theorem real_val_sub_neq_zero (i j : Fin 2025) (hij : i.val ≠ j.val) :
  (i.val : ℝ) - (j.val : ℝ) ≠ (0 : ℝ) :=
by
  intro h
  have h1 : (i.val : ℝ) = (j.val : ℝ) := sub_eq_zero.mp h
  have h2 : i.val = j.val := by exact_mod_cast h1
  exact hij h2

theorem v_two_neq_zero (j : Fin 2025) : v j (2 : Fin 3) ≠ (0 : ℝ) :=
by
  change ((j + 1).val : ℝ) - ((j - 1).val : ℝ) ≠ (0 : ℝ)
  intro h
  have h1 : ((j + 1).val : ℝ) = ((j - 1).val : ℝ) := sub_eq_zero.mp h
  have h2 : (j + 1).val = (j - 1).val := by exact_mod_cast h1
  have h3 : j + 1 = j - 1 := by
    ext
    exact h2
  have h4 : j + 1 + 1 = j - 1 + 1 := congrArg (· + 1) h3
  have h5 : j - 1 + 1 = j := by
    calc j - 1 + 1 = j + -1 + 1 := by rw [sub_eq_add_neg]
      _ = j + (-1 + 1) := by rw [add_assoc]
      _ = j + (1 + -1) := by rw [add_comm (-1 : Fin 2025) 1]
      _ = j + (1 - 1) := by rw [← sub_eq_add_neg]
      _ = j + 0 := by rw [sub_self]
      _ = j := by rw [add_zero]
  rw [h5] at h4
  have h6 : j + 1 + 1 = j + 2 := by
    rw [add_assoc]
    have h_two : (1 : Fin 2025) + 1 = 2 := rfl
    rw [h_two]
  rw [h6] at h4
  have h7 : j + 2 - j = j - j := congrArg (· - j) h4
  have h8 : j + 2 - j = 2 := by
    calc j + 2 - j = j + 2 + -j := by rw [sub_eq_add_neg]
      _ = 2 + j + -j := by rw [add_comm j 2]
      _ = 2 + (j + -j) := by rw [add_assoc]
      _ = 2 + (j - j) := by rw [← sub_eq_add_neg]
      _ = 2 + 0 := by rw [sub_self]
      _ = 2 := by rw [add_zero]
  have h9 : j - j = 0 := by rw [sub_self]
  rw [h8, h9] at h7
  have h10 : (2 : Fin 2025).val = (0 : Fin 2025).val := congrArg Fin.val h7
  omega

theorem dot_zero_of_comm (i j : Fin 2025) (hij : i.val ≠ j.val) (h : A i * A j = A j * A i) :
  (((i + 1).val : ℝ) - ((i - 1).val : ℝ)) * (((j.val : ℝ) - ((i - 1).val : ℝ)) * ((j.val : ℝ) - ((i + 1).val : ℝ))) = (0 : ℝ) :=
by
  change D i j = (0 : ℝ)
  exact real_system_eq_zero (v i (2 : Fin 3)) (v j (2 : Fin 3)) (i.val : ℝ) (j.val : ℝ) (D i j) (D j i)
    (real_val_sub_neq_zero i j hij) (v_two_neq_zero j) (get_eq0 i j h) (get_eq1 i j h)

theorem A_not_comm_of_not_mem (i j : Fin 2025) (h : j.val - i.val ∉ ({0, 1, 2024} : Set ℕ)) (hij : i ≤ j) :
  A i * A j ≠ A j * A i :=
by
  intro h_comm
  have h_neq : i.val ≠ j.val := by
    intro heq
    apply h
    have hsub : j.val - i.val = (0 : ℕ) := by omega
    rw [hsub]
    exact Or.inl rfl
  have h_dot := dot_zero_of_comm i j h_neq h_comm
  have h_neighbor_diff := neighbor_diff_neq_zero i
  have h_j_neighbors := j_neq_neighbors i j hij h
  have h_or1 := mul_eq_zero.mp h_dot
  cases h_or1 with
  | inl h1 => exact h_neighbor_diff h1
  | inr h23 =>
    have h_or2 := mul_eq_zero.mp h23
    cases h_or2 with
    | inl h2 => exact h_j_neighbors.1 h2
    | inr h3 => exact h_j_neighbors.2 h3

theorem matrix_zero_eq (X Y : Matrix (Fin 0) (Fin 0) ℝ) : X = Y :=
Subsingleton.elim X Y

theorem matrix_zero_comm (B : Fin 2025 → Matrix (Fin 0) (Fin 0) ℝ) (i j : Fin 2025) :
  B i * B j = B j * B i :=
matrix_zero_eq (B i * B j) (B j * B i)

theorem counterexample_indices_valid : (0 : Fin 2025) ≤ (2 : Fin 2025) :=
by
  decide

theorem counterexample_not_mem :
  (2 : Fin 2025).val - (0 : Fin 2025).val ∉ ({0, 1, 2024} : Set ℕ) :=
by
  -- Evaluate the `Fin` definitions and finite set notation definitionally
  change ¬((2 : ℕ) = 0 ∨ (2 : ℕ) = 1 ∨ (2 : ℕ) = 2024)
  -- The logical combination of distinct natural number equalities is decidable
  decide

theorem k_neq_0 (B : Fin 2025 → Matrix (Fin 0) (Fin 0) ℝ) :
  ¬ (∀ i j : Fin 2025, i ≤ j →
      (B i * B j = B j * B i ↔ j.val - i.val ∈ ({0, 1, 2024} : Set ℕ))) :=
by
  intro H
  -- Apply the assumption for i = 0 and j = 2
  have h_le := counterexample_indices_valid
  have h_iff := H 0 2 h_le

  -- The left-hand side of the biconditional is true since 0x0 matrices commute
  have h_comm := matrix_zero_comm B 0 2

  -- The biconditional then implies the right-hand side is also true
  have h_mem := h_iff.mp h_comm

  -- But our counterexample lemma establishes this is false, leading to a contradiction
  exact counterexample_not_mem h_mem

theorem fin_one_eq_zero_aux (i : Fin 1) : i = (0 : Fin 1) :=
by
  ext
  omega

theorem matrix_one_ext (X Y : Matrix (Fin 1) (Fin 1) ℝ)
  (h : X (0 : Fin 1) (0 : Fin 1) = Y (0 : Fin 1) (0 : Fin 1)) : X = Y :=
by
  -- Matrix equality is just pointwise equality, so we can apply function extensionality
  ext i j
  -- Any element in `Fin 1` is strictly equal to 0, which we can rewrite
  rw [fin_one_eq_zero_aux i, fin_one_eq_zero_aux j]
  -- The transformed goal now exactly matches our given hypothesis
  exact h

theorem matrix_one_mul_zero_zero (X Y : Matrix (Fin 1) (Fin 1) ℝ) :
  (X * Y) (0 : Fin 1) (0 : Fin 1) = X (0 : Fin 1) (0 : Fin 1) * Y (0 : Fin 1) (0 : Fin 1) :=
by
  simp [Matrix.mul_apply]

theorem matrix_one_comm (B : Fin 2025 → Matrix (Fin 1) (Fin 1) ℝ) (i j : Fin 2025) :
  B i * B j = B j * B i :=
by
  -- Apply our extension lemma to reduce the equality of matrices to their (0,0) entries
  apply matrix_one_ext
  -- Unfold the definition of multiplication at the (0,0) entry for both sides
  rw [matrix_one_mul_zero_zero, matrix_one_mul_zero_zero]
  -- The remaining goal is just an equality of real numbers, which commutes
  exact mul_comm _ _

theorem counterexample_not_mem_aux : (2 : Fin 2025).val - (0 : Fin 2025).val ∉ ({0, 1, 2024} : Set ℕ) :=
by
  -- Unfold the definition of the explicit Set insertion and singleton membership.
  -- This transforms `x ∉ {0, 1, 2024}` into `¬(x = 0 ∨ x = 1 ∨ x = 2024)`.
  simp_rw [Set.mem_insert_iff, Set.mem_singleton_iff]
  -- Evaluate the decidable finite arithmetic and logic using the kernel/compiler.
  decide

theorem counterexample_indices_valid_aux : (0 : Fin 2025) ≤ (2 : Fin 2025) :=
by
  decide

theorem k_neq_1 (B : Fin 2025 → Matrix (Fin 1) (Fin 1) ℝ) :
  ¬ (∀ i j : Fin 2025, i ≤ j →
      (B i * B j = B j * B i ↔ j.val - i.val ∈ ({0, 1, 2024} : Set ℕ))) :=
by
  intro h
  -- Specialize the universal condition to indices i = 0 and j = 2
  have h1 := h 0 2 counterexample_indices_valid_aux
  -- Extract the right side of the equivalence by providing the commutativity proof
  have h2 := h1.mp (matrix_one_comm B 0 2)
  -- Deduce the contradiction since 2 - 0 = 2 is undeniably not in {0, 1, 2024}
  exact counterexample_not_mem_aux h2

theorem mul_apply_fin2 (A B : Matrix (Fin 2) (Fin 2) ℝ) (i j : Fin 2) :
  (A * B) i j = A i 0 * B 0 j + A i 1 * B 1 j :=
by
  simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem commute_eqs (X Y : Matrix (Fin 2) (Fin 2) ℝ) (h : X * Y = Y * X) :
  X 0 1 * Y 1 0 = Y 0 1 * X 1 0 ∧
  Y 0 1 * (X 1 1 - X 0 0) = X 0 1 * (Y 1 1 - Y 0 0) ∧
  Y 1 0 * (X 1 1 - X 0 0) = X 1 0 * (Y 1 1 - Y 0 0) :=
by

  -- Step 1: Extract corresponding components from the hypothesis `h`
  have h00 : (X * Y) 0 0 = (Y * X) 0 0 := by rw [h]
  have h01 : (X * Y) 0 1 = (Y * X) 0 1 := by rw [h]
  have h10 : (X * Y) 1 0 = (Y * X) 1 0 := by rw [h]

  -- Step 2: Expand the matrix multiplications algebraically for these components
  rw [mul_apply_fin2 X Y 0 0, mul_apply_fin2 Y X 0 0] at h00
  rw [mul_apply_fin2 X Y 0 1, mul_apply_fin2 Y X 0 1] at h01
  rw [mul_apply_fin2 X Y 1 0, mul_apply_fin2 Y X 1 0] at h10

  -- Step 3 & 4: Split goal and close via algebraic equivalent differences substituting the matrices parts
  refine ⟨?_, ?_, ?_⟩
  · calc
      X 0 1 * Y 1 0 = X 0 0 * Y 0 0 + X 0 1 * Y 1 0 - X 0 0 * Y 0 0 := by ring
      _ = Y 0 0 * X 0 0 + Y 0 1 * X 1 0 - X 0 0 * Y 0 0 := by rw [h00]
      _ = Y 0 1 * X 1 0 := by ring
  · calc
      Y 0 1 * (X 1 1 - X 0 0) = Y 0 0 * X 0 1 + Y 0 1 * X 1 1 - Y 0 1 * X 0 0 - Y 0 0 * X 0 1 := by ring
      _ = X 0 0 * Y 0 1 + X 0 1 * Y 1 1 - Y 0 1 * X 0 0 - Y 0 0 * X 0 1 := by rw [←h01]
      _ = X 0 1 * (Y 1 1 - Y 0 0) := by ring
  · calc
      Y 1 0 * (X 1 1 - X 0 0) = X 1 0 * Y 0 0 + X 1 1 * Y 1 0 - Y 1 0 * X 0 0 - X 1 0 * Y 0 0 := by ring
      _ = Y 1 0 * X 0 0 + Y 1 1 * X 1 0 - Y 1 0 * X 0 0 - X 1 0 * Y 0 0 := by rw [h10]
      _ = X 1 0 * (Y 1 1 - Y 0 0) := by ring

theorem is_scalar_imp (Y : Matrix (Fin 2) (Fin 2) ℝ)
  (h : ∃ c : ℝ, Y = c • (1 : Matrix (Fin 2) (Fin 2) ℝ)) :
  Y 0 1 = 0 ∧ Y 1 0 = 0 ∧ Y 0 0 = Y 1 1 :=
by
  -- Extract the scalar `c` and the equality `Y = c • 1`, substituting `Y` in the goal.
  rcases h with ⟨c, rfl⟩
  -- Split the conjunction into three separate goals
  refine ⟨?_, ?_, ?_⟩
  · -- Subgoal 1: Y 0 1 = 0
    -- simp unfolds scalar multiplication pointwise and evaluates the identity matrix entries
    simp [Matrix.one_apply]
  · -- Subgoal 2: Y 1 0 = 0
    simp [Matrix.one_apply]
  · -- Subgoal 3: Y 0 0 = Y 1 1
    simp [Matrix.one_apply]

theorem imp_is_scalar (Y : Matrix (Fin 2) (Fin 2) ℝ)
  (h : Y 0 1 = 0 ∧ Y 1 0 = 0 ∧ Y 0 0 = Y 1 1) :
  ∃ c : ℝ, Y = c • (1 : Matrix (Fin 2) (Fin 2) ℝ) :=
by
  use Y 0 0
  ext i j
  -- We exhaust all 4 combinations of indices (i, j) for a 2x2 matrix
  -- and use the simplified rules along with the given hypothesis h to close them.
  fin_cases i <;> fin_cases j <;> simp [h]

theorem is_scalar_iff (Y : Matrix (Fin 2) (Fin 2) ℝ) :
  (∃ c : ℝ, Y = c • (1 : Matrix (Fin 2) (Fin 2) ℝ)) ↔
  (Y 0 1 = 0 ∧ Y 1 0 = 0 ∧ Y 0 0 = Y 1 1) :=
by
  exact ⟨is_scalar_imp Y, imp_is_scalar Y⟩

theorem matrix_eq (A B : Matrix (Fin 2) (Fin 2) ℝ)
  (h00 : A 0 0 = B 0 0)
  (h01 : A 0 1 = B 0 1)
  (h10 : A 1 0 = B 1 0)
  (h11 : A 1 1 = B 1 1) : A = B :=
by
  ext i j
  fin_cases i
  · fin_cases j
    · exact h00
    · exact h01
  · fin_cases j
    · exact h10
    · exact h11

theorem mat_eval_00 (α β : ℝ) (Y : Matrix (Fin 2) (Fin 2) ℝ) :
  (α • (1 : Matrix (Fin 2) (Fin 2) ℝ) + β • Y) 0 0 = α + β * Y 0 0 :=
by
  -- `simp` effortlessly applies point-wise matrix addition, scalar multiplication,
  -- and reduces the identity matrix diagonal value to 1.
  -- `<;> ring` ensures that if any polynomial arithmetic is left over, it's automatically equated.
  simp <;> ring

theorem mat_eval_01 (α β : ℝ) (Y : Matrix (Fin 2) (Fin 2) ℝ) :
  (α • (1 : Matrix (Fin 2) (Fin 2) ℝ) + β • Y) 0 1 = β * Y 0 1 :=
by
  simp [Matrix.one_apply]

theorem mat_eval_10 (α β : ℝ) (Y : Matrix (Fin 2) (Fin 2) ℝ) :
  (α • (1 : Matrix (Fin 2) (Fin 2) ℝ) + β • Y) 1 0 = β * Y 1 0 :=
by
  -- 1 and 0 are distinct indices in Fin 2.
  have h : (1 : Fin 2) ≠ (0 : Fin 2) := by decide
  -- Unfold the definition of the identity matrix entry,
  -- simplify the point-wise additions/smul, and resolve scalar multiplication to normal multiplication.
  simp [Matrix.one_apply, h, smul_eq_mul]

theorem mat_eval_11 (α β : ℝ) (Y : Matrix (Fin 2) (Fin 2) ℝ) :
  (α • (1 : Matrix (Fin 2) (Fin 2) ℝ) + β • Y) 1 1 = α + β * Y 1 1 :=
by
  simp [Matrix.one_apply]

theorem exists_scalars_of_commute (X Y : Matrix (Fin 2) (Fin 2) ℝ)
  (hXY : X * Y = Y * X)
  (hY_not_scalar : ¬ ∃ c : ℝ, Y = c • (1 : Matrix (Fin 2) (Fin 2) ℝ)) :
  ∃ α β : ℝ, X = α • (1 : Matrix (Fin 2) (Fin 2) ℝ) + β • Y :=
by
  rw [is_scalar_iff] at hY_not_scalar

  -- Force a disjunction out of the negation of a conjunction
  have h_or : Y 0 1 ≠ 0 ∨ Y 1 0 ≠ 0 ∨ Y 0 0 ≠ Y 1 1 := by
    by_contra h
    push_neg at h
    exact hY_not_scalar h

  have heqs := commute_eqs X Y hXY
  rcases heqs with ⟨heq1, heq2, heq3⟩

  rcases h_or with h01 | h10 | h00
  · -- Case 1: Y 0 1 ≠ 0
    have h10_eq : (X 0 1 / Y 0 1) * Y 1 0 = X 1 0 := by
      calc (X 0 1 / Y 0 1) * Y 1 0 = (X 0 1 * Y 1 0) / Y 0 1 := by ring
        _ = (Y 0 1 * X 1 0) / Y 0 1 := by rw [heq1]
        _ = X 1 0 * Y 0 1 / Y 0 1 := by ring
        _ = X 1 0 := by rw [mul_div_cancel_right₀ _ h01]

    have h11_eq : X 0 0 - (X 0 1 / Y 0 1) * Y 0 0 + (X 0 1 / Y 0 1) * Y 1 1 = X 1 1 := by
      calc X 0 0 - (X 0 1 / Y 0 1) * Y 0 0 + (X 0 1 / Y 0 1) * Y 1 1
          = X 0 0 + (X 0 1 * (Y 1 1 - Y 0 0)) / Y 0 1 := by ring
        _ = X 0 0 + (Y 0 1 * (X 1 1 - X 0 0)) / Y 0 1 := by rw [← heq2]
        _ = X 0 0 + (X 1 1 - X 0 0) * Y 0 1 / Y 0 1 := by ring
        _ = X 0 0 + (X 1 1 - X 0 0) := by rw [mul_div_cancel_right₀ _ h01]
        _ = X 1 1 := by ring

    use X 0 0 - (X 0 1 / Y 0 1) * Y 0 0, X 0 1 / Y 0 1
    apply matrix_eq
    · rw [mat_eval_00]; ring
    · rw [mat_eval_01]; exact (div_mul_cancel₀ _ h01).symm
    · rw [mat_eval_10]; exact h10_eq.symm
    · rw [mat_eval_11]; exact h11_eq.symm

  · -- Case 2: Y 1 0 ≠ 0
    have h01_eq : (X 1 0 / Y 1 0) * Y 0 1 = X 0 1 := by
      calc (X 1 0 / Y 1 0) * Y 0 1 = (X 1 0 * Y 0 1) / Y 1 0 := by ring
        _ = (Y 0 1 * X 1 0) / Y 1 0 := by ring
        _ = (X 0 1 * Y 1 0) / Y 1 0 := by rw [← heq1]
        _ = X 0 1 * Y 1 0 / Y 1 0 := by ring
        _ = X 0 1 := by rw [mul_div_cancel_right₀ _ h10]

    have h11_eq : X 0 0 - (X 1 0 / Y 1 0) * Y 0 0 + (X 1 0 / Y 1 0) * Y 1 1 = X 1 1 := by
      calc X 0 0 - (X 1 0 / Y 1 0) * Y 0 0 + (X 1 0 / Y 1 0) * Y 1 1
          = X 0 0 + (X 1 0 * (Y 1 1 - Y 0 0)) / Y 1 0 := by ring
        _ = X 0 0 + (Y 1 0 * (X 1 1 - X 0 0)) / Y 1 0 := by rw [← heq3]
        _ = X 0 0 + (X 1 1 - X 0 0) * Y 1 0 / Y 1 0 := by ring
        _ = X 0 0 + (X 1 1 - X 0 0) := by rw [mul_div_cancel_right₀ _ h10]
        _ = X 1 1 := by ring

    use X 0 0 - (X 1 0 / Y 1 0) * Y 0 0, X 1 0 / Y 1 0
    apply matrix_eq
    · rw [mat_eval_00]; ring
    · rw [mat_eval_01]; exact h01_eq.symm
    · rw [mat_eval_10]; exact (div_mul_cancel₀ _ h10).symm
    · rw [mat_eval_11]; exact h11_eq.symm

  · -- Case 3: Y 0 0 ≠ Y 1 1
    have h00' : Y 1 1 - Y 0 0 ≠ 0 := by intro contra; apply h00; linarith
    have h01_eq : ((X 1 1 - X 0 0) / (Y 1 1 - Y 0 0)) * Y 0 1 = X 0 1 := by
      calc ((X 1 1 - X 0 0) / (Y 1 1 - Y 0 0)) * Y 0 1
          = (Y 0 1 * (X 1 1 - X 0 0)) / (Y 1 1 - Y 0 0) := by ring
        _ = (X 0 1 * (Y 1 1 - Y 0 0)) / (Y 1 1 - Y 0 0) := by rw [heq2]
        _ = X 0 1 * (Y 1 1 - Y 0 0) / (Y 1 1 - Y 0 0) := by ring
        _ = X 0 1 := by rw [mul_div_cancel_right₀ _ h00']

    have h10_eq : ((X 1 1 - X 0 0) / (Y 1 1 - Y 0 0)) * Y 1 0 = X 1 0 := by
      calc ((X 1 1 - X 0 0) / (Y 1 1 - Y 0 0)) * Y 1 0
          = (Y 1 0 * (X 1 1 - X 0 0)) / (Y 1 1 - Y 0 0) := by ring
        _ = (X 1 0 * (Y 1 1 - Y 0 0)) / (Y 1 1 - Y 0 0) := by rw [heq3]
        _ = X 1 0 * (Y 1 1 - Y 0 0) / (Y 1 1 - Y 0 0) := by ring
        _ = X 1 0 := by rw [mul_div_cancel_right₀ _ h00']

    have h11_eq : X 0 0 - ((X 1 1 - X 0 0) / (Y 1 1 - Y 0 0)) * Y 0 0 + ((X 1 1 - X 0 0) / (Y 1 1 - Y 0 0)) * Y 1 1 = X 1 1 := by
      calc X 0 0 - ((X 1 1 - X 0 0) / (Y 1 1 - Y 0 0)) * Y 0 0 + ((X 1 1 - X 0 0) / (Y 1 1 - Y 0 0)) * Y 1 1
          = X 0 0 + ((X 1 1 - X 0 0) / (Y 1 1 - Y 0 0)) * (Y 1 1 - Y 0 0) := by ring
        _ = X 0 0 + (X 1 1 - X 0 0) := by rw [div_mul_cancel₀ _ h00']
        _ = X 1 1 := by ring

    use X 0 0 - ((X 1 1 - X 0 0) / (Y 1 1 - Y 0 0)) * Y 0 0, (X 1 1 - X 0 0) / (Y 1 1 - Y 0 0)
    apply matrix_eq
    · rw [mat_eval_00]; ring
    · rw [mat_eval_01]; exact h01_eq.symm
    · rw [mat_eval_10]; exact h10_eq.symm
    · rw [mat_eval_11]; exact h11_eq.symm

theorem lemma1_smul_id_mul_smul_id (α γ : ℝ) :
  (α • (1 : Matrix (Fin 2) (Fin 2) ℝ)) * (γ • (1 : Matrix (Fin 2) (Fin 2) ℝ)) = (α * γ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) :=
by
  simp [smul_mul_assoc, mul_smul_comm, smul_smul]
  ring

theorem lemma2_smul_id_mul_smul_mat (α δ : ℝ) (Y : Matrix (Fin 2) (Fin 2) ℝ) :
  (α • (1 : Matrix (Fin 2) (Fin 2) ℝ)) * (δ • Y) = (α * δ) • Y :=
by
  -- Factor out the scalar α from the matrix multiplication
  rw [smul_mul_assoc]
  -- Multiply the identity matrix by (δ • Y), which simply leaves (δ • Y)
  rw [one_mul]
  -- Combine the nested scalar multiplications α • (δ • Y) into (α * δ) • Y
  rw [← mul_smul]

theorem lemma3_smul_mat_mul_smul_id (β γ : ℝ) (Y : Matrix (Fin 2) (Fin 2) ℝ) :
  (β • Y) * (γ • (1 : Matrix (Fin 2) (Fin 2) ℝ)) = (β * γ) • Y :=
by
  rw [Matrix.smul_mul, Matrix.mul_smul, mul_one, ← mul_smul]

theorem lemma4_smul_mat_mul_smul_mat (β δ : ℝ) (Y : Matrix (Fin 2) (Fin 2) ℝ) :
  (β • Y) * (δ • Y) = (β * δ) • (Y * Y) :=
by
  rw [Matrix.smul_mul, Matrix.mul_smul, ← mul_smul]

theorem lemma5_add_smul_rearrange (α β γ δ : ℝ) (Y : Matrix (Fin 2) (Fin 2) ℝ) :
  (α * γ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) + (β * γ) • Y + ((α * δ) • Y + (β * δ) • (Y * Y)) =
  (α * γ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) + (α * δ + β * γ) • Y + (β * δ) • (Y * Y) :=
by
  rw [add_smul]
  abel

theorem linear_combination_commute_expansion (Y : Matrix (Fin 2) (Fin 2) ℝ) (α β γ δ : ℝ) :
  (α • (1 : Matrix (Fin 2) (Fin 2) ℝ) + β • Y) * (γ • (1 : Matrix (Fin 2) (Fin 2) ℝ) + δ • Y) =
  (α * γ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) + (α * δ + β * γ) • Y + (β * δ) • (Y * Y) :=
by
  rw [mul_add, add_mul, add_mul]
  rw [lemma1_smul_id_mul_smul_id, lemma2_smul_id_mul_smul_mat, lemma3_smul_mat_mul_smul_id, lemma4_smul_mat_mul_smul_mat]
  rw [lemma5_add_smul_rearrange]

theorem linear_combination_commute (Y : Matrix (Fin 2) (Fin 2) ℝ) (α β γ δ : ℝ) :
  (α • (1 : Matrix (Fin 2) (Fin 2) ℝ) + β • Y) * (γ • (1 : Matrix (Fin 2) (Fin 2) ℝ) + δ • Y) =
  (γ • (1 : Matrix (Fin 2) (Fin 2) ℝ) + δ • Y) * (α • (1 : Matrix (Fin 2) (Fin 2) ℝ) + β • Y) :=
by
  -- Expand the Left-Hand Side
  rw [linear_combination_commute_expansion Y α β γ δ]
  -- Expand the Right-Hand Side
  rw [linear_combination_commute_expansion Y γ δ α β]

  -- The real coefficients inherently commute. We declare these commutativity properties.
  have h1 : α * γ = γ * α := by ring
  have h2 : α * δ + β * γ = γ * β + δ * α := by ring
  have h3 : β * δ = δ * β := by ring

  -- Rewrite the expanded Left-Hand Side elements to exactly match the expanded Right-Hand Side
  rw [h1, h2, h3]

theorem m2_comm_trans (X Y Z : Matrix (Fin 2) (Fin 2) ℝ)
  (hXY : X * Y = Y * X)
  (hYZ : Y * Z = Z * Y)
  (hY_not_scalar : ¬ ∃ c : ℝ, Y = c • (1 : Matrix (Fin 2) (Fin 2) ℝ)) :
  X * Z = Z * X :=
by
  -- Y commutes with Z, therefore Z commutes with Y
  have hZY : Z * Y = Y * Z := hYZ.symm

  -- Obtain scalars for X and Z as linear combinations of 1 and Y
  obtain ⟨α, β, hX⟩ := exists_scalars_of_commute X Y hXY hY_not_scalar
  obtain ⟨γ, δ, hZ⟩ := exists_scalars_of_commute Z Y hZY hY_not_scalar

  -- Substitute the linearly dependent forms of X and Z into the goal
  rw [hX, hZ]

  -- Applying our lemma resolving the commutative properties of two linearly scaled copies of the same matrix
  exact linear_combination_commute Y α β γ δ

theorem scalar_mul_id_left (c : ℝ) (Z : Matrix (Fin 2) (Fin 2) ℝ) :
  (c • (1 : Matrix (Fin 2) (Fin 2) ℝ)) * Z = c • Z :=
by
  rw [smul_mul_assoc, one_mul]

theorem scalar_mul_id_right (c : ℝ) (Z : Matrix (Fin 2) (Fin 2) ℝ) :
  Z * (c • (1 : Matrix (Fin 2) (Fin 2) ℝ)) = c • Z :=
by
  simp

theorem scalar_matrix_comm (c : ℝ) (Z : Matrix (Fin 2) (Fin 2) ℝ) :
  (c • (1 : Matrix (Fin 2) (Fin 2) ℝ)) * Z = Z * (c • (1 : Matrix (Fin 2) (Fin 2) ℝ)) :=
by
  rw [scalar_mul_id_left, scalar_mul_id_right]

theorem diff_0_1 : (1 : Fin 2025).val - (0 : Fin 2025).val ∈ ({0, 1, 2024} : Set ℕ) :=
by
  simp

theorem diff_1_2 : (2 : Fin 2025).val - (1 : Fin 2025).val ∈ ({0, 1, 2024} : Set ℕ) :=
by
  -- Prove the arithmetic reduction by definitional equality.
  have h : (2 : Fin 2025).val - (1 : Fin 2025).val = 1 := rfl

  -- Substitute the result into the goal.
  rw [h]

  -- `simp` automatically unfolds the Set membership to `1 = 0 ∨ 1 = 1 ∨ 1 = 2024`,
  -- identifies the true disjunct `1 = 1`, and discharges the proof.
  simp

theorem diff_0_2 : (2 : Fin 2025).val - (0 : Fin 2025).val ∉ ({0, 1, 2024} : Set ℕ) :=
by
  -- Introduce the assumption that the expression belongs to the set to derive a contradiction.
  intro h
  -- Expand the finite set membership into a sequence of disjunctions (ORs).
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
  -- Revert the hypothesis so `decide` can evaluate the entire logic explicitly.
  revert h
  -- `decide` evaluates the arithmetic: 2 - 0 = 2.
  -- It then evaluates the propositions 2 = 0 ∨ 2 = 1 ∨ 2 = 2024 to False, completing the proof.
  decide

theorem diff_1_3 : (3 : Fin 2025).val - (1 : Fin 2025).val ∉ ({0, 1, 2024} : Set ℕ) :=
by
  intro h
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
  revert h
  decide

theorem le_0_1 : (0 : Fin 2025) ≤ (1 : Fin 2025) :=
by
 decide

theorem le_1_2 : (1 : Fin 2025) ≤ (2 : Fin 2025) :=
by
  decide

theorem le_0_2 : (0 : Fin 2025) ≤ (2 : Fin 2025) :=
by
  decide

theorem le_1_3 : (1 : Fin 2025) ≤ (3 : Fin 2025) :=
by
  decide

theorem k_neq_2 (B : Fin 2025 → Matrix (Fin 2) (Fin 2) ℝ) :
  ¬ (∀ i j : Fin 2025, i ≤ j →
      (B i * B j = B j * B i ↔ j.val - i.val ∈ ({0, 1, 2024} : Set ℕ))) :=
by
  intro h

  -- Deduce specific commutativities and non-commutativities from the theorem hypothesis
  have h01 : B 0 * B 1 = B 1 * B 0 := (h 0 1 le_0_1).mpr diff_0_1
  have h12 : B 1 * B 2 = B 2 * B 1 := (h 1 2 le_1_2).mpr diff_1_2
  have h02_not : B 0 * B 2 ≠ B 2 * B 0 := fun heq => diff_0_2 ((h 0 2 le_0_2).mp heq)
  have h13_not : B 1 * B 3 ≠ B 3 * B 1 := fun heq => diff_1_3 ((h 1 3 le_1_3).mp heq)

  -- Split by cases depending on whether B 1 is a scalar matrix or not
  by_cases hY : ∃ c : ℝ, B 1 = c • (1 : Matrix (Fin 2) (Fin 2) ℝ)
  · -- Case 1: B 1 is a scalar matrix. Therefore, it commutes with all matrices.
    have ⟨c, hc⟩ := hY
    have h13 : B 1 * B 3 = B 3 * B 1 := by
      rw [hc]
      exact scalar_matrix_comm c (B 3)
    -- This creates a direct contradiction with our earlier deduction that B 1 and B 3 do not commute
    exact h13_not h13
  · -- Case 2: B 1 is NOT a scalar matrix.
    -- Thus, transitivity applies over its commutativity connections to B 0 and B 2.
    have h02 : B 0 * B 2 = B 2 * B 0 := m2_comm_trans (B 0) (B 1) (B 2) h01 h12 hY
    -- This creates a direct contradiction with our earlier deduction that B 0 and B 2 do not commute
    exact h02_not h02

theorem putnam_2025_a4 : IsLeast {k : ℕ | ∃ A : Fin 2025 → Matrix (Fin k) (Fin k) ℝ,
    ∀ i j : Fin 2025, i ≤ j →
      (A i * A j = A j * A i ↔ j.val - i.val ∈ ({0, 1, 2024} : Set ℕ))}
  putnam_2025_a4_solution :=
by
  rw [sol_eq]
  constructor
  · simp only [Set.mem_setOf_eq]
    use A
    intro i j hij
    constructor
    · intro h
      by_contra hnot
      have h_neq := A_not_comm_of_not_mem i j hnot hij
      exact h_neq h
    · intro h
      exact A_comm_of_mem i j h hij
  · rintro k ⟨B, hB⟩
    by_contra hlt
    obtain (rfl | rfl | rfl) : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    · exact k_neq_0 B hB
    · exact k_neq_1 B hB
    · exact k_neq_2 B hB
