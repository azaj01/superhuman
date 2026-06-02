import Mathlib
abbrev b : ℕ → ℤ
| 0 => 0
| n + 1 => 2 * (b n) ^ 2 + b n + 1

noncomputable def F : ℕ → Polynomial ℤ
| 0 => Polynomial.X
| n + 1 => 2 * (F n) ^ 2 + F n + 1
def d : ℕ → ℤ
| 0 => 1
| n + 1 => d n * (4 * b n + 1)
def e : ℕ → ℤ
| 0 => 0
| n + 1 => e n * (4 * b n + 1) + 2 * (d n) ^ 2

def Y_val (P y z w Z_1 : ℤ) : ℤ :=
  y + P * (1 + 2 * z) * (1 + 2 * y) + P * 2 * w * (1 + 2 * y) ^ 2 + P ^ 2 * 4 * (1 + 2 * y) ^ 3 * Z_1
def Z_val (P y z w Z_2 : ℤ) : ℤ :=
  z + P * (1 + 2 * z) ^ 2 + P * w * (1 + 2 * y) + P * 4 * w * (1 + 2 * y) * (1 + 2 * z) +
  P * (1 + 2 * y) ^ 2 * Z_2 + P ^ 2 * 4 * (1 + 2 * y) ^ 2 * (1 + 2 * z) * Z_2

noncomputable def my_R_new (B D E R : Polynomial ℤ) : Polynomial ℤ :=
  (4 : Polynomial ℤ) * B * R + (4 : Polynomial ℤ) * D * E + (4 : Polynomial ℤ) * D * R * Polynomial.X + (2 : Polynomial ℤ) * E ^ 2 * Polynomial.X + (4 : Polynomial ℤ) * E * R * Polynomial.X ^ 2 + (2 : Polynomial ℤ) * R ^ 2 * Polynomial.X ^ 3 + R

noncomputable def R_new (B D E R : Polynomial ℤ) : Polynomial ℤ :=
  4 * B * R + 4 * D * E + R + (2 * E ^ 2 + 4 * D * R) * Polynomial.X + 4 * E * R * Polynomial.X ^ 2 + 2 * R ^ 2 * Polynomial.X ^ 3

theorem AD_prop_nat_base :
  (∃ y : ℤ, b (2 ^ 1) = (2 : ℤ) ^ 1 * 2 * (1 + 2 * y)) ∧
  (∃ z : ℤ, d (2 ^ 1) = 1 + (2 : ℤ) ^ 1 * 2 * (1 + 2 * z)) :=
by
  constructor
  · exact ⟨0, rfl⟩
  · exact ⟨0, rfl⟩

theorem two_pow_succ_eq_add (k : ℕ) : 2 ^ (k + 1) = 2 ^ k + 2 ^ k :=
by
  rw [pow_add, pow_one]
  ring

theorem my_F_mod_X3_zero : F 0 = Polynomial.C (b 0) + Polynomial.C (d 0) * Polynomial.X + Polynomial.C (e 0) * Polynomial.X ^ 2 + Polynomial.X ^ 3 * 0 :=
by
  simp [F, b, d, e]

theorem my_F_succ_eq (n : ℕ) : F (n + 1) = (2 : Polynomial ℤ) * (F n) ^ 2 + F n + (1 : Polynomial ℤ) :=
rfl

theorem b_recurrence (n : ℕ) : b (n + 1) = (2 : ℤ) * (b n) ^ 2 + b n + (1 : ℤ) :=
rfl

theorem C_two : Polynomial.C (2 : ℤ) = (2 : Polynomial ℤ) :=
by
  simp

theorem C_one : Polynomial.C (1 : ℤ) = (1 : Polynomial ℤ) :=
map_one Polynomial.C

theorem my_C_b_succ (n : ℕ) : Polynomial.C (b (n + 1)) = (2 : Polynomial ℤ) * (Polynomial.C (b n)) ^ 2 + Polynomial.C (b n) + (1 : Polynomial ℤ) :=
by
  -- Unfold the sequence recurrence using our helper lemma
  rw [b_recurrence]
  -- Distribute the RingHom over addition, multiplication, and exponentiation,
  -- then evaluate the mapped integer constants 2 and 1.
  simp only [map_add, map_mul, map_pow, C_two, C_one]

theorem my_C_d_succ (n : ℕ) : Polynomial.C (d (n + 1)) = (4 : Polynomial ℤ) * Polynomial.C (b n) * Polynomial.C (d n) + Polynomial.C (d n) :=
by
  -- Unfold the definition of d(n+1) and push the ring homomorphism Polynomial.C
  -- over all multiplications, additions, and explicit numeric constants.
  simp [d, map_mul, map_add]
  -- Resolve the resulting polynomial algebra equality
  ring

theorem my_e_succ_eq (n : ℕ) : e (n + 1) = e n * (4 * b n + 1) + 2 * (d n) ^ 2 :=
rfl

theorem my_C_one : Polynomial.C (1 : ℤ) = (1 : Polynomial ℤ) :=
by
  exact Polynomial.C_1

theorem my_C_two : Polynomial.C (2 : ℤ) = (2 : Polynomial ℤ) :=
by
  simp

theorem my_C_four : Polynomial.C (4 : ℤ) = (4 : Polynomial ℤ) :=
by
  simp

theorem my_C_e_succ (n : ℕ) : Polynomial.C (e (n + 1)) = (4 : Polynomial ℤ) * Polynomial.C (b n) * Polynomial.C (e n) + Polynomial.C (e n) + (2 : Polynomial ℤ) * (Polynomial.C (d n)) ^ 2 :=
by
  -- 1. Unfold the definition of the e (n + 1) sequence mathematically.
  rw [my_e_succ_eq n]

  -- 2. Push the Polynomial.C RingHom down to the sequence atoms and constants.
  -- We apply ring homomorphism identities and rewrite our constants.
  simp only [map_add, map_mul, map_pow, my_C_one, my_C_two, my_C_four]

  -- 3. The equation is now purely algebraic in the commutative ring `Polynomial ℤ`.
  ring

theorem my_F_mod_X3_algebra (B D E R : Polynomial ℤ) :
  (2 : Polynomial ℤ) * (B + D * Polynomial.X + E * Polynomial.X ^ 2 + Polynomial.X ^ 3 * R) ^ 2 +
  (B + D * Polynomial.X + E * Polynomial.X ^ 2 + Polynomial.X ^ 3 * R) + (1 : Polynomial ℤ) =
  ((2 : Polynomial ℤ) * B ^ 2 + B + (1 : Polynomial ℤ)) +
  ((4 : Polynomial ℤ) * B * D + D) * Polynomial.X +
  ((4 : Polynomial ℤ) * B * E + E + (2 : Polynomial ℤ) * D ^ 2) * Polynomial.X ^ 2 +
  Polynomial.X ^ 3 * my_R_new B D E R :=
by
  unfold my_R_new
  ring

theorem F_mod_X3 (n : ℕ) : ∃ R : Polynomial ℤ, F n = Polynomial.C (b n) + Polynomial.C (d n) * Polynomial.X + Polynomial.C (e n) * Polynomial.X ^ 2 + Polynomial.X ^ 3 * R :=
by
  induction n with
  | zero =>
    use 0
    exact my_F_mod_X3_zero
  | succ n ih =>
    rcases ih with ⟨Rn, hRn⟩
    use my_R_new (Polynomial.C (b n)) (Polynomial.C (d n)) (Polynomial.C (e n)) Rn
    rw [my_F_succ_eq, hRn, my_F_mod_X3_algebra, ← my_C_b_succ, ← my_C_d_succ, ← my_C_e_succ]

theorem b_add_eq_F_eval_base (n : ℕ) : b (n + 0) = (F 0).eval (b n) :=
by
  simp [F]

theorem b_succ (k : ℕ) : b (k + 1) = 2 * (b k) ^ 2 + b k + 1 :=
rfl

theorem F_succ (k : ℕ) : F (k + 1) = 2 * (F k) ^ 2 + F k + 1 :=
rfl

theorem b_add_eq_F_eval_step (n m : ℕ) (ih : b (n + m) = (F m).eval (b n)) : b (n + (m + 1)) = (F (m + 1)).eval (b n) :=
by
  rw [← add_assoc]
  rw [b_succ]
  rw [ih]
  rw [F_succ]
  simp
  try ring

theorem b_add_eq_F_eval (n m : ℕ) : b (n + m) = (F m).eval (b n) :=
by
  induction m with
  | zero =>
    exact b_add_eq_F_eval_base n
  | succ m ih =>
    exact b_add_eq_F_eval_step n m ih

theorem b_add_expansion (n m : ℕ) : ∃ Z : ℤ, b (n + m) = b m + d m * b n + e m * (b n) ^ 2 + (b n) ^ 3 * Z :=
by
  -- Rewrite the sequence addition into polynomial evaluation using our helper lemma
  rw [b_add_eq_F_eval n m]

  -- Obtain the structural representation of F_m via the F_mod_X3 lemma
  rcases F_mod_X3 m with ⟨R, hR⟩

  -- Provide the remainder polynomial evaluated at b(n) as the witness for the existential variable Z
  use R.eval (b n)

  -- Substitute F_m with its structural form
  rw [hR]

  -- Distribute the evaluation operation over polynomial addition, multiplication, constants, X, and powers.
  -- This accurately simplifies the left hand side to identically match the right hand side, closing the goal.
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow]

theorem b_pow_succ_expansion (k : ℕ) :
  ∃ Z : ℤ, b (2 ^ (k + 1)) = b (2 ^ k) + d (2 ^ k) * b (2 ^ k) + e (2 ^ k) * (b (2 ^ k)) ^ 2 + (b (2 ^ k)) ^ 3 * Z :=
by
  have h : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := two_pow_succ_eq_add k
  rw [h]
  exact b_add_expansion (2 ^ k) (2 ^ k)

theorem e_zero_even : ∃ y : ℤ, e 0 = 2 * y :=
by
  use 0
  rfl

theorem e_succ_even (n : ℕ) (hn : ∃ y : ℤ, e n = 2 * y) : ∃ y : ℤ, e (n + 1) = 2 * y :=
by
  rcases hn with ⟨y, hy⟩
  use y * (4 * b n + 1) + (d n) ^ 2
  have h : e (n + 1) = e n * (4 * b n + 1) + 2 * (d n) ^ 2 := rfl
  rw [h, hy]
  ring

theorem e_is_even (n : ℕ) : ∃ y : ℤ, e n = 2 * y :=
by
  induction n with
  | zero => exact e_zero_even
  | succ n ih => exact e_succ_even n ih

theorem e_is_even_k (k : ℕ) : ∃ w : ℤ, e (2 ^ k) = 2 * w :=
by
  exact e_is_even (2 ^ k)

theorem AD_prop_nat_step_b_algebra (P y z w Z_1 : ℤ) :
  (P * 2 * 2 * (1 + 2 * y)) +
  (1 + P * 2 * 2 * (1 + 2 * z)) * (P * 2 * 2 * (1 + 2 * y)) +
  (2 * w) * (P * 2 * 2 * (1 + 2 * y)) ^ 2 +
  (P * 2 * 2 * (1 + 2 * y)) ^ 3 * Z_1 =
  P * 2 * 2 * 2 * (1 + 2 * (y + P * (1 + 2 * z) * (1 + 2 * y) + P * 2 * w * (1 + 2 * y) ^ 2 + P ^ 2 * 4 * (1 + 2 * y) ^ 3 * Z_1)) :=
by
  ring

theorem AD_prop_nat_step_b (m : ℕ)
  (ih : (∃ y : ℤ, b (2 ^ (m + 1)) = (2 : ℤ) ^ (m + 1) * 2 * (1 + 2 * y)) ∧
        (∃ z : ℤ, d (2 ^ (m + 1)) = 1 + (2 : ℤ) ^ (m + 1) * 2 * (1 + 2 * z))) :
  ∃ y : ℤ, b (2 ^ (m + 2)) = (2 : ℤ) ^ (m + 2) * 2 * (1 + 2 * y) :=
by
  -- Destructure the inductive hypotheses
  rcases ih with ⟨⟨y, hy⟩, ⟨z, hz⟩⟩

  -- Obtain the required expansions at k = m + 1
  have hZ := b_pow_succ_expansion (m + 1)
  rcases hZ with ⟨Z_1, hZ_1⟩

  have he := e_is_even_k (m + 1)
  rcases he with ⟨w, hw⟩

  -- Shift the exponent target from m + 2 to the form m + 1 + 1
  have h_m2 : m + 2 = m + 1 + 1 := by omega
  rw [h_m2]

  -- Provide the witness for the main goal explicitly to decouple from potentially undefined auxiliary functions
  use y + ((2 : ℤ) ^ m) * (1 + 2 * z) * (1 + 2 * y) + ((2 : ℤ) ^ m) * 2 * w * (1 + 2 * y) ^ 2 + ((2 : ℤ) ^ m) ^ 2 * 4 * (1 + 2 * y) ^ 3 * Z_1

  -- Establish clean algebraic forms for b(2^{m+1}) and d(2^{m+1}) dropping the (m+1) power down to m
  have hb : b (2 ^ (m + 1)) = (2 : ℤ) ^ m * 2 * 2 * (1 + 2 * y) := by
    rw [hy, pow_succ]
  have hd : d (2 ^ (m + 1)) = 1 + (2 : ℤ) ^ m * 2 * 2 * (1 + 2 * z) := by
    rw [hz, pow_succ]

  -- Substitute the known inductive equations directly into the expansion step
  rw [hb, hd, hw] at hZ_1

  -- Condense the massive expansion through the purely algebraic lemma
  have halg := AD_prop_nat_step_b_algebra ((2 : ℤ) ^ m) y z w Z_1
  rw [halg] at hZ_1

  -- Finally map the substituted result strictly against the goal via pure exponent reduction and ring operations
  rw [hZ_1]

  -- Reduce the target exponent in a separate have-block to precisely target the necessary transformations
  have h_pow : (2 : ℤ) ^ (m + 1 + 1) = (2 : ℤ) ^ m * 2 * 2 := by
    rw [pow_succ, pow_succ]
  rw [h_pow]

theorem zpow_m_plus_1 (m : ℕ) : (2 : ℤ) ^ (m + 1) = (2 : ℤ) ^ m * 2 :=
by
  ring

theorem zpow_m_plus_2 (m : ℕ) : (2 : ℤ) ^ (m + 2) = (2 : ℤ) ^ m * 4 :=
by
  ring

theorem d_add_zero_helper (n : ℕ) : d (n + 0) = d n :=
by
  rfl

theorem eval_F_zero_deriv_helper : ∀ x, (Polynomial.derivative (F 0)).eval x = 1 :=
by
  intro x
  simp [F]

theorem d_add_succ_helper (n k : ℕ) : d (n + (k + 1)) = d (n + k) * (4 * b (n + k) + 1) :=
by
  rw [← add_assoc]
  rfl

theorem b_add_eq_F_eval_helper (n k : ℕ) : b (n + k) = (F k).eval (b n) :=
by
  induction k with
  | zero =>
    -- Base case: k = 0
    -- b (n + 0) simplifies to b n
    -- F 0 is Polynomial.X, and Polynomial.X.eval (b n) simplifies to b n
    simp [F]
  | succ k ih =>
    -- Inductive step: k + 1
    -- n + (k + 1) is definitionally (n + k) + 1
    -- So b (n + k + 1) unfolds to 2 * b (n + k)^2 + b (n + k) + 1 by the definition of b
    -- F (k + 1) unfolds to 2 * (F k)^2 + F k + 1 by the definition of F
    -- Polynomial.eval acts as a ring homomorphism, so simp automatically pushes it inside
    -- Applying `ih` rewrites `b (n + k)` to `(F k).eval (b n)`, matching both sides
    simp [F, b, ih]

theorem F_succ_eq_poly (m : ℕ) :
  F (m + 1) = 2 * (F m) ^ 2 + F m + 1 :=
rfl

theorem derivative_quadratic_comp {R : Type*} [CommSemiring R] (P : Polynomial R) :
  Polynomial.derivative (2 * P ^ 2 + P + 1) = (4 * P + 1) * Polynomial.derivative P :=
by
  -- Explicitly rewrite the power as a multiplication so the product rule can be applied trivially
  have h : P ^ 2 = P * P := by ring
  rw [h]
  -- Expand the formal derivative using standard rules (linearity and the product rule)
  simp [Polynomial.derivative_mul]
  -- Resolve the remaining polynomial algebraic equality
  ring

theorem derivative_F_succ_poly (m : ℕ) :
  Polynomial.derivative (F (m + 1)) = (4 * F m + 1) * Polynomial.derivative (F m) :=
by
  rw [F_succ_eq_poly m]
  exact derivative_quadratic_comp (F m)

theorem eval_derivative_F_succ_helper (m : ℕ) :
  ∀ x, (Polynomial.derivative (F (m + 1))).eval x = (4 * (F m).eval x + 1) * (Polynomial.derivative (F m)).eval x :=
by
  intro x
  rw [derivative_F_succ_poly m]
  simp <;> try ring

theorem d_add_eq (n m : ℕ) :
  d (n + m) = (Polynomial.derivative (F m)).eval (b n) * d n :=
by
  induction m with
  | zero =>
    -- Base case: Reduce (n + 0) and evaluate the derivative of F_0
    rw [d_add_zero_helper n]
    rw [eval_F_zero_deriv_helper (b n)]
    ring
  | succ k ih =>
    -- Inductive step: Expand the definition of d for the successor
    rw [d_add_succ_helper n k]

    -- Apply the induction hypothesis for d(n + k)
    rw [ih]

    -- Bridge the integer sequence b(n + k) with its polynomial representation
    rw [b_add_eq_F_eval_helper n k]

    -- Evaluate the formal derivative of F_{k+1}
    rw [eval_derivative_F_succ_helper k (b n)]

    -- Finally, the equality follows purely by ring axioms
    ring

theorem F_poly_step (B D E R : Polynomial ℤ) :
  2 * (B + D * Polynomial.X + E * Polynomial.X ^ 2 + Polynomial.X ^ 3 * R) ^ 2 +
  (B + D * Polynomial.X + E * Polynomial.X ^ 2 + Polynomial.X ^ 3 * R) + 1 =
  (2 * B ^ 2 + B + 1) +
  (4 * B * D + D) * Polynomial.X +
  (4 * B * E + 2 * D ^ 2 + E) * Polynomial.X ^ 2 +
  Polynomial.X ^ 3 * R_new B D E R :=
by
  unfold R_new
  ring

theorem base_case_eq :
  F 0 = Polynomial.C (b 0) + Polynomial.C (d 0) * Polynomial.X + Polynomial.C (e 0) * Polynomial.X ^ 2 + Polynomial.X ^ 3 * (0 : Polynomial ℤ) :=
by
  simp [F, b, d, e]

theorem my_F_succ (n : ℕ) :
  F (n + 1) = 2 * (F n) ^ 2 + F n + 1 :=
rfl

theorem b_succ_def_helper (n : ℕ) : b (n + 1) = 2 * (b n) ^ 2 + b n + 1 :=
rfl

theorem C_2 : Polynomial.C (2 : ℤ) = 2 :=
by
  simp

theorem C_b_succ (n : ℕ) :
  Polynomial.C (b (n + 1)) = 2 * (Polynomial.C (b n)) ^ 2 + Polynomial.C (b n) + 1 :=
by
  -- Unfold the recursive equation for the next step of the sequence `b`
  rw [b_succ_def_helper]
  -- `Polynomial.C` is a bundled RingHom, meaning we can apply standard simplification mappings
  -- exhaustively over addition, multiplication, powers, and evaluate its constants.
  simp only [map_add, map_mul, map_pow, map_one, C_2]

theorem C_d_succ (n : ℕ) :
  Polynomial.C (d (n + 1)) = 4 * Polynomial.C (b n) * Polynomial.C (d n) + Polynomial.C (d n) :=
by
  have hd : d (n + 1) = d n * (4 * b n + 1) := rfl
  rw [hd]
  simp only [map_mul, map_add, map_one, Polynomial.C_ofNat]
  ring

theorem e_succ_def (n : ℕ) : e (n + 1) = e n * (4 * b n + 1) + 2 * (d n) ^ 2 :=
rfl

theorem C_e_succ (n : ℕ) :
  Polynomial.C (e (n + 1)) = 4 * Polynomial.C (b n) * Polynomial.C (e n) + 2 * (Polynomial.C (d n)) ^ 2 + Polynomial.C (e n) :=
by
  rw [e_succ_def]
  have h2 : Polynomial.C (2 : ℤ) = 2 := Polynomial.C_ofNat 2
  have h4 : Polynomial.C (4 : ℤ) = 4 := Polynomial.C_ofNat 4
  simp only [map_add, map_mul, map_pow, map_one, h2, h4]
  ring

theorem F_eq_poly_expansion (n : ℕ) :
  ∃ R : Polynomial ℤ, F n = Polynomial.C (b n) + Polynomial.C (d n) * Polynomial.X + Polynomial.C (e n) * Polynomial.X ^ 2 + Polynomial.X ^ 3 * R :=
by
  induction n with
  | zero =>
    use 0
    exact base_case_eq
  | succ n ih =>
    obtain ⟨R, hR⟩ := ih
    use R_new (Polynomial.C (b n)) (Polynomial.C (d n)) (Polynomial.C (e n)) R

    -- Unfold F for n + 1
    rw [my_F_succ n]
    -- Substitute the induction hypothesis
    rw [hR]
    -- Rearrange algebraically precisely matching the mapped structures
    rw [F_poly_step]
    -- Reconstruct the mapped sequence representations backwards for n + 1
    rw [← C_b_succ n, ← C_d_succ n, ← C_e_succ n]

theorem eval_derivative_poly_expansion (b_val d_val e_val : ℤ) (R : Polynomial ℤ) (x : ℤ) :
  (Polynomial.derivative (Polynomial.C b_val + Polynomial.C d_val * Polynomial.X + Polynomial.C e_val * Polynomial.X ^ 2 + Polynomial.X ^ 3 * R)).eval x =
  d_val + 2 * e_val * x + x ^ 2 * (3 * R.eval x + x * (Polynomial.derivative R).eval x) :=
by
  simp
  ring

theorem deriv_F_eval_b (n : ℕ) :
  ∃ Z : ℤ, (Polynomial.derivative (F n)).eval (b n) = d n + 2 * e n * b n + (b n) ^ 2 * Z :=
by
  -- Obtain the polynomial R such that F_n(X) = b_n + d_n X + e_n X^2 + X^3 R_n(X)
  have ⟨R, hR⟩ := F_eq_poly_expansion n

  -- Provide the exact integer witness required to complete the algebraic identity
  exact ⟨3 * R.eval (b n) + b n * (Polynomial.derivative R).eval (b n), by
    -- Substitute the expanded polynomial definition of F n
    -- Then automatically apply our derived algebraic expansion evaluated at (b n)
    rw [hR, eval_derivative_poly_expansion]
  ⟩

theorem d_expansion_helper (m : ℕ) :
  ∃ (w : ℤ) (Z_2 : ℤ), d (2 ^ (m + 2)) =
    d (2 ^ (m + 1)) * (d (2 ^ (m + 1)) + 4 * w * b (2 ^ (m + 1)) + (b (2 ^ (m + 1))) ^ 2 * Z_2) :=
by
  -- 1. Note that 2^(m+2) = 2^(m+1) + 2^(m+1)
  have h1 : 2 ^ (m + 2) = 2 ^ (m + 1) + 2 ^ (m + 1) := by
    have : m + 2 = m + 1 + 1 := by omega
    rw [this, pow_add, pow_one]
    ring
  rw [h1]

  -- 2. Use the addition formula for sequence d
  rw [d_add_eq]

  -- 3. Obtain Z from evaluating the derivative of F
  rcases deriv_F_eval_b (2 ^ (m + 1)) with ⟨Z, hZ⟩

  -- 4. Obtain the witness that e is even
  rcases e_is_even (2 ^ (m + 1)) with ⟨w, hw⟩

  -- 5. Provide exact witnesses to the existential statement
  use w, Z

  -- 6. Substitute equations algebraically
  rw [hZ]
  rw [hw]

  -- 7. Solve and close with `ring`
  ring

theorem AD_prop_nat_step_d (m : ℕ)
  (ih : (∃ y : ℤ, b (2 ^ (m + 1)) = (2 : ℤ) ^ (m + 1) * 2 * (1 + 2 * y)) ∧
        (∃ z : ℤ, d (2 ^ (m + 1)) = 1 + (2 : ℤ) ^ (m + 1) * 2 * (1 + 2 * z))) :
  ∃ z : ℤ, d (2 ^ (m + 2)) = 1 + (2 : ℤ) ^ (m + 2) * 2 * (1 + 2 * z) :=
by
  obtain ⟨y, hy⟩ := ih.1
  obtain ⟨z_ih, hz⟩ := ih.2
  obtain ⟨w, Z_2, h_exp⟩ := d_expansion_helper m

  have hP1 : (2 : ℤ) ^ (m + 1) = (2 : ℤ) ^ m * 2 := zpow_m_plus_1 m
  have hP2 : (2 : ℤ) ^ (m + 2) = (2 : ℤ) ^ m * 4 := zpow_m_plus_2 m

  use z_ih + w * (1 + 2 * y) + ((2 : ℤ) ^ m) * (1 + 2 * z_ih) ^ 2 + ((2 : ℤ) ^ m) * 4 * w * (1 + 2 * y) * (1 + 2 * z_ih) + ((2 : ℤ) ^ m) * (1 + 2 * y) ^ 2 * Z_2 + ((2 : ℤ) ^ m) ^ 2 * 4 * (1 + 2 * y) ^ 2 * (1 + 2 * z_ih) * Z_2
  rw [h_exp, hy, hz, hP1, hP2]
  ring

theorem AD_prop_nat_step (m : ℕ)
  (ih : (∃ y : ℤ, b (2 ^ (m + 1)) = (2 : ℤ) ^ (m + 1) * 2 * (1 + 2 * y)) ∧
        (∃ z : ℤ, d (2 ^ (m + 1)) = 1 + (2 : ℤ) ^ (m + 1) * 2 * (1 + 2 * z))) :
  (∃ y : ℤ, b (2 ^ (m + 2)) = (2 : ℤ) ^ (m + 2) * 2 * (1 + 2 * y)) ∧
  (∃ z : ℤ, d (2 ^ (m + 2)) = 1 + (2 : ℤ) ^ (m + 2) * 2 * (1 + 2 * z)) :=
⟨AD_prop_nat_step_b m ih, AD_prop_nat_step_d m ih⟩

theorem AD_prop_nat_k (k : ℕ) (hk : 1 ≤ k) :
  (∃ y : ℤ, b (2 ^ k) = (2 : ℤ) ^ k * 2 * (1 + 2 * y)) ∧
  (∃ z : ℤ, d (2 ^ k) = 1 + (2 : ℤ) ^ k * 2 * (1 + 2 * z)) :=
by
  cases k with
  | zero => omega
  | succ m =>
    -- We clear hk because it depends on m and would otherwise be automatically generalized
    -- by the `induction` tactic, thereby altering the type of our induction hypothesis (`ih`).
    clear hk
    induction m with
    | zero =>
      exact AD_prop_nat_base
    | succ n ih =>
      exact AD_prop_nat_step n ih

theorem b_diff_val_helper (k : ℕ) (hk : 1 ≤ k) :
  ∃ y z w Z : ℤ,
    b (2 ^ (k + 1)) = b (2 ^ k) + d (2 ^ k) * b (2 ^ k) + e (2 ^ k) * (b (2 ^ k)) ^ 2 + (b (2 ^ k)) ^ 3 * Z ∧
    b (2 ^ k) = (2 : ℤ) ^ k * 2 * (1 + 2 * y) ∧
    d (2 ^ k) = 1 + (2 : ℤ) ^ k * 2 * (1 + 2 * z) ∧
    e (2 ^ k) = 2 * w :=
by
  have ⟨h_y, h_z⟩ := AD_prop_nat_k k hk
  have ⟨y, hy⟩ := h_y
  have ⟨z, hz⟩ := h_z
  have ⟨w, hw⟩ := e_is_even_k k
  have ⟨Z, hZ⟩ := b_pow_succ_expansion k
  exact ⟨y, z, w, Z, hZ, hy, hz, hw⟩

theorem pow_two_identity_one (k : ℕ) : (2 ^ (2 * k + 2) : ℤ) = ((2 : ℤ) ^ k) ^ 2 * 4 :=
by
  -- Push the integer coercion inwards so the LHS becomes `(2 : ℤ) ^ (2 * k + 2)`
  push_cast

  -- Split the addition in the exponent: `a^(m + n) = a^m * a^n`
  rw [pow_add]

  -- Commute `2 * k` to `k * 2` to prepare for multiplicative splitting
  rw [mul_comm 2 k]

  -- Split the multiplication in the exponent: `a^(m * n) = (a^m)^n`
  rw [pow_mul]

  -- The LHS is now exactly `((2 : ℤ) ^ k) ^ 2 * (2 : ℤ) ^ 2`.
  -- We rely on the `ring` tactic to automatically evaluate `(2 : ℤ) ^ 2` to `4` and solve the equality.
  ring

theorem pow_two_identity_two (k : ℕ) : (2 ^ (2 * k + 3) : ℤ) = ((2 : ℤ) ^ k) ^ 2 * 8 :=
by
  push_cast
  rw [pow_add, mul_comm 2 k, pow_mul]
  ring

theorem pow_two_identities (k : ℕ) :
  (2 ^ (2 * k + 2) : ℤ) = ((2 : ℤ) ^ k) ^ 2 * 4 ∧
  (2 ^ (2 * k + 3) : ℤ) = ((2 : ℤ) ^ k) ^ 2 * 8 :=
by
  -- Split the conjunction into two separate identities
  constructor
  · exact pow_two_identity_one k
  · exact pow_two_identity_two k

theorem b_diff_val (k : ℕ) (hk : 1 ≤ k) :
  ∃ z : ℤ, b (2 ^ (k + 1)) - 2 * b (2 ^ k) = (2 ^ (2 * k + 2) : ℤ) + (2 ^ (2 * k + 3) : ℤ) * z :=
by
  rcases b_diff_val_helper k hk with ⟨y, z, w, Z, h1, h2, h3, h4⟩
  have h_pow := pow_two_identities k
  use y + z + 2 * y * z + w + 4 * w * y + 4 * w * y ^ 2 + (2:ℤ) ^ k * Z * (1 + 2 * y) ^ 3
  rw [h1, h2, h3, h4, h_pow.1, h_pow.2]
  ring

theorem putnam_2025_a6 (k : ℕ) (hk : 1 ≤ k) : (2 ^ (2 * k + 2) : ℤ) ∣ (b (2 ^ (k + 1)) - 2 * b (2 ^ k)) ∧
    ¬((2 ^ (2 * k + 3) : ℤ) ∣ (b (2 ^ (k + 1)) - 2 * b (2 ^ k))) :=
by
  have ⟨z, hz⟩ := b_diff_val k hk
  have hpow : (2 ^ (2 * k + 3) : ℤ) = (2 ^ (2 * k + 2) : ℤ) * 2 := by
    have h_eq : 2 * k + 3 = 2 * k + 2 + 1 := by omega
    rw [h_eq, pow_add, pow_one]
  constructor
  · exact ⟨1 + 2 * z, by rw [hz, hpow]; ring⟩
  · rintro ⟨w, hw⟩
    rw [hz, hpow] at hw
    have h1 : (2 ^ (2 * k + 2) : ℤ) * (1 + 2 * z) = (2 ^ (2 * k + 2) : ℤ) * (2 * w) := by
      calc (2 ^ (2 * k + 2) : ℤ) * (1 + 2 * z)
        _ = (2 ^ (2 * k + 2) : ℤ) + (2 ^ (2 * k + 2) : ℤ) * 2 * z := by ring
        _ = (2 ^ (2 * k + 2) : ℤ) * 2 * w := hw
        _ = (2 ^ (2 * k + 2) : ℤ) * (2 * w) := by ring
    have h_pos : (0 : ℤ) < (2 ^ (2 * k + 2) : ℤ) := by positivity
    have h_ne : (2 ^ (2 * k + 2) : ℤ) ≠ 0 := ne_of_gt h_pos
    have h2 : 1 + 2 * z = 2 * w := mul_left_cancel₀ h_ne h1
    omega
