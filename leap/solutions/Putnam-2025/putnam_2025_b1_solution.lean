import Mathlib
open Affine
open EuclideanGeometry

theorem affineIndependent_of_dist_eq_of_distinct (B : EuclideanSpace ℝ (Fin 2)) (r : ℝ)
  (X_1 X_2 X_3 : EuclideanSpace ℝ (Fin 2))
  (hd12 : X_1 ≠ X_2) (hd23 : X_2 ≠ X_3) (hd13 : X_1 ≠ X_3)
  (hr1 : dist X_1 B = r) (hr2 : dist X_2 B = r) (hr3 : dist X_3 B = r) :
  AffineIndependent ℝ ![X_1, X_2, X_3] :=
by
  by_contra h_not_indep

  -- Use the core definition: affine independence is linear independence of the displacement vectors
  have h_not_indep2 : ¬ LinearIndependent ℝ (fun j : {x : Fin 3 // x ≠ 0} => ![X_1, X_2, X_3] j.val -ᵥ ![X_1, X_2, X_3] 0) := by
    intro h
    exact h_not_indep ((affineIndependent_iff_linearIndependent_vsub ℝ ![X_1, X_2, X_3] 0).mpr h)

  obtain ⟨w, hw_zero, hw_not_zero⟩ := Fintype.not_linearIndependent_iff.mp h_not_indep2
  let j1 : {x : Fin 3 // x ≠ 0} := ⟨1, by decide⟩
  let j2 : {x : Fin 3 // x ≠ 0} := ⟨2, by decide⟩

  -- Subtraction definitionally evaluates
  have h_eval1 : ![X_1, X_2, X_3] j1.val -ᵥ ![X_1, X_2, X_3] 0 = X_2 - X_1 := by change X_2 - X_1 = X_2 - X_1; rfl
  have h_eval2 : ![X_1, X_2, X_3] j2.val -ᵥ ![X_1, X_2, X_3] 0 = X_3 - X_1 := by change X_3 - X_1 = X_3 - X_1; rfl

  have h_univ : (Finset.univ : Finset {x : Fin 3 // x ≠ 0}) = {j1, j2} := by
    ext ⟨val, hval⟩
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff, j1, j2, Subtype.mk.injEq]
    revert hval
    fin_cases val <;> simp

  -- Rephrase the affine combination equality
  have h_sum : ∑ j, w j • (![X_1, X_2, X_3] j.val -ᵥ ![X_1, X_2, X_3] 0) = w j1 • (X_2 - X_1) + w j2 • (X_3 - X_1) := by
    calc ∑ j, w j • (![X_1, X_2, X_3] j.val -ᵥ ![X_1, X_2, X_3] 0)
      _ = ∑ j ∈ ({j1, j2} : Finset _), w j • (![X_1, X_2, X_3] j.val -ᵥ ![X_1, X_2, X_3] 0) := by rw [h_univ]
      _ = w j1 • (![X_1, X_2, X_3] j1.val -ᵥ ![X_1, X_2, X_3] 0) + w j2 • (![X_1, X_2, X_3] j2.val -ᵥ ![X_1, X_2, X_3] 0) := by
        apply Finset.sum_pair
        intro h
        have h12 : (1 : Fin 3) = 2 := congr_arg Subtype.val h
        revert h12
        decide
      _ = w j1 • (X_2 - X_1) + w j2 • (X_3 - X_1) := by rw [h_eval1, h_eval2]

  -- Isolate the logical scenarios for finding secant representation coefficient c
  have h_cases : w j2 = 0 ∨ w j2 ≠ 0 := eq_or_ne (w j2) 0
  rcases h_cases with h2_zero | h2_nz
  · have h1_nz : w j1 ≠ 0 := by
      obtain ⟨j, hj⟩ := hw_not_zero
      have hj_cases : j = j1 ∨ j = j2 := by
        have h_mem : j ∈ ({j1, j2} : Finset _) := by rw [← h_univ]; exact Finset.mem_univ j
        simp only [Finset.mem_insert, Finset.mem_singleton] at h_mem
        exact h_mem
      rcases hj_cases with rfl | rfl
      · exact hj
      · exact False.elim (hj h2_zero)
    have hw1_eq : w j1 • (X_2 - X_1) = 0 := by
      calc w j1 • (X_2 - X_1) = w j1 • (X_2 - X_1) + w j2 • (X_3 - X_1) := by simp [h2_zero]
        _ = 0 := by rw [← h_sum, hw_zero]
    have h_x21 : X_2 - X_1 = 0 := by
      cases smul_eq_zero.mp hw1_eq with
      | inl h => exact False.elim (h1_nz h)
      | inr h => exact h
    have h_x2_eq_x1 : X_2 = X_1 := sub_eq_zero.mp h_x21
    exact hd12 h_x2_eq_x1.symm

  · let c := - w j1 / w j2
    have hc_sub : X_3 - X_1 = c • (X_2 - X_1) := by
      have h_eq : w j2 • (X_3 - X_1) = (- w j1) • (X_2 - X_1) := by
        have h_sum2 : w j1 • (X_2 - X_1) + w j2 • (X_3 - X_1) = 0 := by
          rw [← h_sum, hw_zero]
        calc w j2 • (X_3 - X_1) = 0 + w j2 • (X_3 - X_1) := by rw [zero_add]
          _ = (-(w j1 • (X_2 - X_1)) + w j1 • (X_2 - X_1)) + w j2 • (X_3 - X_1) := by rw [neg_add_cancel]
          _ = -(w j1 • (X_2 - X_1)) + (w j1 • (X_2 - X_1) + w j2 • (X_3 - X_1)) := by rw [add_assoc]
          _ = -(w j1 • (X_2 - X_1)) + 0 := by rw [h_sum2]
          _ = -(w j1 • (X_2 - X_1)) := by rw [add_zero]
          _ = (- w j1) • (X_2 - X_1) := by rw [neg_smul]
      calc X_3 - X_1 = (1 : ℝ) • (X_3 - X_1) := by rw [one_smul]
        _ = ((w j2)⁻¹ * w j2) • (X_3 - X_1) := by
          congr 1
          exact (inv_mul_cancel₀ h2_nz).symm
        _ = (w j2)⁻¹ • (w j2 • (X_3 - X_1)) := by rw [mul_smul]
        _ = (w j2)⁻¹ • ((- w j1) • (X_2 - X_1)) := by rw [h_eq]
        _ = ((w j2)⁻¹ * - w j1) • (X_2 - X_1) := by rw [← mul_smul]
        _ = c • (X_2 - X_1) := by
          congr 1
          dsimp [c]
          ring

    -- Translate distances from metric formulation to norm representations
    have hN1 : ‖X_1 - B‖ = r := by have h := hr1; rw [dist_eq_norm] at h; exact h
    have hN2 : ‖X_2 - B‖ = r := by have h := hr2; rw [dist_eq_norm] at h; exact h
    have hN3 : ‖X_3 - B‖ = r := by have h := hr3; rw [dist_eq_norm] at h; exact h

    have hI1 : inner ℝ (X_1 - B) (X_1 - B) = r ^ 2 := by rw [real_inner_self_eq_norm_sq (X_1 - B), hN1]
    have hI2 : inner ℝ (X_2 - B) (X_2 - B) = r ^ 2 := by rw [real_inner_self_eq_norm_sq (X_2 - B), hN2]
    have hI3 : inner ℝ (X_3 - B) (X_3 - B) = r ^ 2 := by rw [real_inner_self_eq_norm_sq (X_3 - B), hN3]

    -- Expand inner product for point 2
    have h_exp2 : inner ℝ (X_2 - B) (X_2 - B) = inner ℝ (X_1 - B) (X_1 - B) + 2 * inner ℝ (X_1 - B) (X_2 - X_1) + inner ℝ (X_2 - X_1) (X_2 - X_1) := by
      have hY2 : X_2 - B = (X_1 - B) + (X_2 - X_1) := by abel
      calc inner ℝ (X_2 - B) (X_2 - B)
        _ = inner ℝ ((X_1 - B) + (X_2 - X_1)) ((X_1 - B) + (X_2 - X_1)) := by rw [hY2]
        _ = inner ℝ (X_1 - B) ((X_1 - B) + (X_2 - X_1)) + inner ℝ (X_2 - X_1) ((X_1 - B) + (X_2 - X_1)) := by rw [inner_add_left]
        _ = inner ℝ (X_1 - B) (X_1 - B) + inner ℝ (X_1 - B) (X_2 - X_1) + (inner ℝ (X_2 - X_1) (X_1 - B) + inner ℝ (X_2 - X_1) (X_2 - X_1)) := by rw [inner_add_right, inner_add_right]
        _ = inner ℝ (X_1 - B) (X_1 - B) + inner ℝ (X_1 - B) (X_2 - X_1) + inner ℝ (X_2 - X_1) (X_1 - B) + inner ℝ (X_2 - X_1) (X_2 - X_1) := by abel
        _ = inner ℝ (X_1 - B) (X_1 - B) + 2 * inner ℝ (X_1 - B) (X_2 - X_1) + inner ℝ (X_2 - X_1) (X_2 - X_1) := by
          rw [real_inner_comm (X_2 - X_1) (X_1 - B)]
          ring

    have h_eq2 : 2 * inner ℝ (X_1 - B) (X_2 - X_1) + inner ℝ (X_2 - X_1) (X_2 - X_1) = 0 := by
      linarith [hI2, hI1, h_exp2]

    -- Expand inner product for point 3 parameterized by coefficient c
    have h_exp3 : inner ℝ (X_3 - B) (X_3 - B) = inner ℝ (X_1 - B) (X_1 - B) + 2 * c * inner ℝ (X_1 - B) (X_2 - X_1) + c ^ 2 * inner ℝ (X_2 - X_1) (X_2 - X_1) := by
      have hY3 : X_3 - B = (X_1 - B) + c • (X_2 - X_1) := by
        calc X_3 - B = (X_3 - X_1) + (X_1 - B) := by abel
          _ = c • (X_2 - X_1) + (X_1 - B) := by rw [hc_sub]
          _ = (X_1 - B) + c • (X_2 - X_1) := by abel
      calc inner ℝ (X_3 - B) (X_3 - B)
        _ = inner ℝ ((X_1 - B) + c • (X_2 - X_1)) ((X_1 - B) + c • (X_2 - X_1)) := by rw [hY3]
        _ = inner ℝ (X_1 - B) ((X_1 - B) + c • (X_2 - X_1)) + inner ℝ (c • (X_2 - X_1)) ((X_1 - B) + c • (X_2 - X_1)) := by rw [inner_add_left]
        _ = inner ℝ (X_1 - B) (X_1 - B) + inner ℝ (X_1 - B) (c • (X_2 - X_1)) + (inner ℝ (c • (X_2 - X_1)) (X_1 - B) + inner ℝ (c • (X_2 - X_1)) (c • (X_2 - X_1))) := by rw [inner_add_right, inner_add_right]
        _ = inner ℝ (X_1 - B) (X_1 - B) + inner ℝ (X_1 - B) (c • (X_2 - X_1)) + inner ℝ (c • (X_2 - X_1)) (X_1 - B) + inner ℝ (c • (X_2 - X_1)) (c • (X_2 - X_1)) := by abel
        _ = inner ℝ (X_1 - B) (X_1 - B) + c * inner ℝ (X_1 - B) (X_2 - X_1) + c * inner ℝ (X_2 - X_1) (X_1 - B) + c * c * inner ℝ (X_2 - X_1) (X_2 - X_1) := by
          have h1 : inner ℝ (X_1 - B) (c • (X_2 - X_1)) = c * inner ℝ (X_1 - B) (X_2 - X_1) := by rw [real_inner_smul_right]
          have h2 : inner ℝ (c • (X_2 - X_1)) (X_1 - B) = c * inner ℝ (X_2 - X_1) (X_1 - B) := by rw [real_inner_smul_left]
          have h3 : inner ℝ (c • (X_2 - X_1)) (c • (X_2 - X_1)) = c * c * inner ℝ (X_2 - X_1) (X_2 - X_1) := by
            calc inner ℝ (c • (X_2 - X_1)) (c • (X_2 - X_1))
              _ = c * inner ℝ (X_2 - X_1) (c • (X_2 - X_1)) := by rw [real_inner_smul_left]
              _ = c * (c * inner ℝ (X_2 - X_1) (X_2 - X_1)) := by rw [real_inner_smul_right]
              _ = c * c * inner ℝ (X_2 - X_1) (X_2 - X_1) := by ring
          rw [h1, h2, h3]
        _ = inner ℝ (X_1 - B) (X_1 - B) + 2 * c * inner ℝ (X_1 - B) (X_2 - X_1) + c ^ 2 * inner ℝ (X_2 - X_1) (X_2 - X_1) := by
          rw [real_inner_comm (X_2 - X_1) (X_1 - B)]
          ring

    have h_eq3 : 2 * c * inner ℝ (X_1 - B) (X_2 - X_1) + c ^ 2 * inner ℝ (X_2 - X_1) (X_2 - X_1) = 0 := by
      linarith [hI3, hI1, h_exp3]

    -- Form the intersection constraint contradiction: A line crosses a circle in max 2 points algebraically
    have h_comb : (c ^ 2 - c) * inner ℝ (X_2 - X_1) (X_2 - X_1) = 0 := by
      calc (c ^ 2 - c) * inner ℝ (X_2 - X_1) (X_2 - X_1)
        _ = (2 * c * inner ℝ (X_1 - B) (X_2 - X_1) + c ^ 2 * inner ℝ (X_2 - X_1) (X_2 - X_1)) - c * (2 * inner ℝ (X_1 - B) (X_2 - X_1) + inner ℝ (X_2 - X_1) (X_2 - X_1)) := by ring
        _ = 0 - c * 0 := by rw [h_eq3, h_eq2]
        _ = 0 := by ring

    -- Isolate the logical scenarios
    cases mul_eq_zero.mp h_comb with
    | inl hc1 =>
      have h_quad : c * (c - 1) = 0 := by
        calc c * (c - 1) = c ^ 2 - c := by ring
          _ = 0 := hc1
      cases mul_eq_zero.mp h_quad with
      | inl h0 =>
        have hX3 : X_3 = X_1 := by
          calc X_3 = (X_3 - X_1) + X_1 := by abel
            _ = c • (X_2 - X_1) + X_1 := by rw [hc_sub]
            _ = (0 : ℝ) • (X_2 - X_1) + X_1 := by rw [h0]
            _ = 0 + X_1 := by rw [zero_smul]
            _ = X_1 := by abel
        exact hd13 hX3.symm
      | inr h1 =>
        have hc_one : c = 1 := sub_eq_zero.mp h1
        have hX3 : X_3 = X_2 := by
          calc X_3 = (X_3 - X_1) + X_1 := by abel
            _ = c • (X_2 - X_1) + X_1 := by rw [hc_sub]
            _ = (1 : ℝ) • (X_2 - X_1) + X_1 := by rw [hc_one]
            _ = (X_2 - X_1) + X_1 := by rw [one_smul]
            _ = X_2 := by abel
        exact hd23 hX3.symm
    | inr hc2 =>
      have h_norm : ‖X_2 - X_1‖^2 = 0 := by
        rw [← real_inner_self_eq_norm_sq (X_2 - X_1)]
        exact hc2
      have h_norm2 : ‖X_2 - X_1‖ = 0 := sq_eq_zero_iff.mp h_norm
      have hX21 : X_2 - X_1 = 0 := norm_eq_zero.mp h_norm2
      have hX2 : X_2 = X_1 := sub_eq_zero.mp hX21
      exact hd12 hX2.symm

theorem circumcenter_eq_of_dist_eq (s : Simplex ℝ (EuclideanSpace ℝ (Fin 2)) 2)
  (B : EuclideanSpace ℝ (Fin 2)) (r : ℝ)
  (h0 : dist (s.points 0) B = r)
  (h1 : dist (s.points 1) B = r)
  (h2 : dist (s.points 2) B = r) :
  s.circumcenter = B :=
by
  have h_dist : ∀ i : Fin 3, dist (s.points i) B = r := by
    intro i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  have h_proj := Affine.Simplex.orthogonalProjection_eq_circumcenter_of_dist_eq s h_dist
  have h_in : B ∈ affineSpan ℝ (Set.range s.points) := by
    have h_dim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2 := by simp
    have h_top : affineSpan ℝ (Set.range s.points) = ⊤ := Affine.Simplex.span_eq_top s h_dim
    rw [h_top]
    simp
  have h_self : (s.orthogonalProjectionSpan B : EuclideanSpace ℝ (Fin 2)) = B := by
    change (orthogonalProjection (affineSpan ℝ (Set.range s.points)) B : EuclideanSpace ℝ (Fin 2)) = B
    exact orthogonalProjection_eq_self_iff.mpr h_in
  rw [h_self] at h_proj
  exact h_proj.symm

theorem monochromatic_of_three_points {α : Type*} (color : α → Bool) (X_1 X_2 X_3 : α)
  (hc12 : color X_1 = color X_2) (hc23 : color X_2 = color X_3) :
  ∀ i j : Fin 3, color (![X_1, X_2, X_3] i) = color (![X_1, X_2, X_3] j) :=
by
  intros i j
  have h : ∀ k : Fin 3, color (![X_1, X_2, X_3] k) = color X_1 := by
    intro k
    fin_cases k
    · rfl
    · exact hc12.symm
    · exact Eq.trans hc23.symm hc12.symm
  rw [h i, h j]

theorem color_center_of_three_points (color : EuclideanSpace ℝ (Fin 2) → Bool)
  (h : ∀ (s : Simplex ℝ (EuclideanSpace ℝ (Fin 2)) 2),
    (∀ i j : Fin 3, color (s.points i) = color (s.points j)) →
    color s.circumcenter = color (s.points 0))
  (B : EuclideanSpace ℝ (Fin 2)) (r : ℝ) (X_1 X_2 X_3 : EuclideanSpace ℝ (Fin 2))
  (hd12 : X_1 ≠ X_2) (hd23 : X_2 ≠ X_3) (hd13 : X_1 ≠ X_3)
  (hr1 : dist X_1 B = r) (hr2 : dist X_2 B = r) (hr3 : dist X_3 B = r)
  (hc12 : color X_1 = color X_2) (hc23 : color X_2 = color X_3) :
  color B = color X_1 :=
by
  have ha : AffineIndependent ℝ ![X_1, X_2, X_3] :=
    affineIndependent_of_dist_eq_of_distinct B r X_1 X_2 X_3 hd12 hd23 hd13 hr1 hr2 hr3
  let s : Simplex ℝ (EuclideanSpace ℝ (Fin 2)) 2 := ⟨![X_1, X_2, X_3], ha⟩

  have hr1' : dist (s.points 0) B = r := by
    change dist X_1 B = r
    exact hr1
  have hr2' : dist (s.points 1) B = r := by
    change dist X_2 B = r
    exact hr2
  have hr3' : dist (s.points 2) B = r := by
    change dist X_3 B = r
    exact hr3

  have h_circ : s.circumcenter = B := circumcenter_eq_of_dist_eq s B r hr1' hr2' hr3'

  have h_mono : ∀ i j : Fin 3, color (s.points i) = color (s.points j) := by
    intros i j
    change color (![X_1, X_2, X_3] i) = color (![X_1, X_2, X_3] j)
    exact monochromatic_of_three_points color X_1 X_2 X_3 hc12 hc23 i j

  have h_s : color s.circumcenter = color (s.points 0) := h s h_mono
  rw [h_circ] at h_s
  change color B = color X_1 at h_s
  exact h_s

theorem at_most_two_exceptions (P : ℝ → Prop)
  (h_not_three : ¬ ∃ r1 r2 r3 : ℝ, r1 ≠ r2 ∧ r2 ≠ r3 ∧ r1 ≠ r3 ∧ P r1 ∧ P r2 ∧ P r3) :
  ∃ b1 b2 : ℝ, ∀ r, P r → r = b1 ∨ r = b2 :=
by
  by_contra h
  push_neg at h
  obtain ⟨r1, hr1, _, _⟩ := h (0 : ℝ) 0
  obtain ⟨r2, hr2, hr21, _⟩ := h r1 r1
  obtain ⟨r3, hr3, hr31, hr32⟩ := h r1 r2
  exact h_not_three ⟨r1, r2, r3, hr21.symm, hr32.symm, hr31.symm, hr1, hr2, hr3⟩

theorem exists_point_on_circle_with_dist (A B : EuclideanSpace ℝ (Fin 2)) (R r : ℝ)
  (hr_min : |R - dist A B| ≤ r) (hr_max : r ≤ R + dist A B) :
  ∃ X : EuclideanSpace ℝ (Fin 2), dist X A = R ∧ dist X B = r :=
by
  have h_d_nonneg : (0 : ℝ) ≤ dist A B := dist_nonneg
  have hr_nonneg : (0 : ℝ) ≤ r := by
    calc
      (0 : ℝ) ≤ |R - dist A B| := abs_nonneg _
      _ ≤ r := hr_min
  have hR_nonneg : (0 : ℝ) ≤ R := by
    have h1 : R - dist A B ≤ r := le_trans (le_abs_self _) hr_min
    have h2 : -(R - dist A B) ≤ r := le_trans (neg_le_abs _) hr_min
    have h3 : r ≤ R + dist A B := hr_max
    linarith

  let A0 : ℝ := A.ofLp (0 : Fin 2)
  let A1 : ℝ := A.ofLp (1 : Fin 2)
  let B0 : ℝ := B.ofLp (0 : Fin 2)
  let B1 : ℝ := B.ofLp (1 : Fin 2)
  let d := dist A B

  have hd_sq : d ^ 2 = (B0 - A0) ^ 2 + (B1 - A1) ^ 2 := by
    have h_sq := EuclideanSpace.dist_sq_eq B A
    have h_sum : (∑ i : Fin 2, dist (B.ofLp i) (A.ofLp i) ^ 2) = dist (B.ofLp (0 : Fin 2)) (A.ofLp (0 : Fin 2)) ^ 2 + dist (B.ofLp (1 : Fin 2)) (A.ofLp (1 : Fin 2)) ^ 2 := by
      rw [Fin.sum_univ_two]
    rw [h_sum] at h_sq
    have h0 : dist (B.ofLp (0 : Fin 2)) (A.ofLp (0 : Fin 2)) ^ 2 = (B0 - A0) ^ 2 := by
      have h_eq : dist (B.ofLp (0 : Fin 2)) (A.ofLp (0 : Fin 2)) = |B0 - A0| := rfl
      rw [h_eq, sq_abs]
    have h1 : dist (B.ofLp (1 : Fin 2)) (A.ofLp (1 : Fin 2)) ^ 2 = (B1 - A1) ^ 2 := by
      have h_eq : dist (B.ofLp (1 : Fin 2)) (A.ofLp (1 : Fin 2)) = |B1 - A1| := rfl
      rw [h_eq, sq_abs]
    rw [h0, h1] at h_sq
    calc d ^ 2 = dist A B ^ 2 := rfl
      _ = dist B A ^ 2 := by rw [dist_comm]
      _ = (B0 - A0) ^ 2 + (B1 - A1) ^ 2 := h_sq

  by_cases hd : d = (0 : ℝ)
  · -- Case d = 0
    have hAB : A = B := dist_eq_zero.mp hd
    have hRr : R = r := by
      have h1 : R - (0 : ℝ) ≤ r := by
        have hd_zero : dist A B = (0 : ℝ) := hd
        rw [hd_zero] at hr_min
        exact le_trans (le_abs_self _) hr_min
      have h2 : r ≤ R + (0 : ℝ) := by
        have hd_zero : dist A B = (0 : ℝ) := hd
        rw [hd_zero] at hr_max
        exact hr_max
      linarith

    let X0 : ℝ := A0 + R
    let X1 : ℝ := A1
    let X : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 (fun i : Fin 2 => if i = (0 : Fin 2) then X0 else X1)
    use X

    have h_X0 : X.ofLp (0 : Fin 2) = X0 := by
      change (if (0 : Fin 2) = (0 : Fin 2) then X0 else X1) = X0
      exact if_pos rfl
    have h_X1 : X.ofLp (1 : Fin 2) = X1 := by
      change (if (1 : Fin 2) = (0 : Fin 2) then X0 else X1) = X1
      have h_neq : (1 : Fin 2) ≠ (0 : Fin 2) := by decide
      exact if_neg h_neq

    have hdA : dist X A ^ 2 = R ^ 2 := by
      have h_sq := EuclideanSpace.dist_sq_eq X A
      have h_sum : (∑ i : Fin 2, dist (X.ofLp i) (A.ofLp i) ^ 2) = dist (X.ofLp (0 : Fin 2)) (A.ofLp (0 : Fin 2)) ^ 2 + dist (X.ofLp (1 : Fin 2)) (A.ofLp (1 : Fin 2)) ^ 2 := by
        rw [Fin.sum_univ_two]
      rw [h_sum] at h_sq
      have h0 : dist (X.ofLp (0 : Fin 2)) (A.ofLp (0 : Fin 2)) ^ 2 = R ^ 2 := by
        rw [h_X0]
        change dist X0 A0 ^ 2 = R ^ 2
        have h_eq : dist X0 A0 = |X0 - A0| := rfl
        rw [h_eq]
        have h_in : X0 - A0 = R := by
          calc X0 - A0 = (A0 + R) - A0 := rfl
            _ = R := by ring
        rw [h_in, sq_abs]
      have h1 : dist (X.ofLp (1 : Fin 2)) (A.ofLp (1 : Fin 2)) ^ 2 = (0 : ℝ) := by
        rw [h_X1]
        change dist X1 A1 ^ 2 = (0 : ℝ)
        have h_eq : dist X1 A1 = |X1 - A1| := rfl
        rw [h_eq]
        have h_in : X1 - A1 = (0 : ℝ) := by
          calc X1 - A1 = A1 - A1 := rfl
            _ = 0 := by ring
        rw [h_in, abs_zero, zero_pow (by decide)]
      rw [h0, h1, add_zero] at h_sq
      exact h_sq

    have h_dist_A : dist X A = R := by
      have H1 : Real.sqrt (dist X A ^ 2) = dist X A := Real.sqrt_sq dist_nonneg
      have H2 : Real.sqrt (R ^ 2) = R := Real.sqrt_sq hR_nonneg
      calc
        dist X A = Real.sqrt (dist X A ^ 2) := H1.symm
        _ = Real.sqrt (R ^ 2) := by rw [hdA]
        _ = R := H2

    have h_dist_B : dist X B = r := by
      rw [← hAB, h_dist_A, hRr]

    exact ⟨h_dist_A, h_dist_B⟩

  · -- Case d > 0
    have hd_pos : (0 : ℝ) < d := lt_of_le_of_ne dist_nonneg (Ne.symm hd)
    let num := ((R + d) ^ 2 - r ^ 2) * (r ^ 2 - (R - d) ^ 2)
    have h1 : (0 : ℝ) ≤ (R + d) ^ 2 - r ^ 2 := by
      calc
        (0 : ℝ) ≤ (R + d - r) * (R + d + r) := by
          have hA : (0 : ℝ) ≤ R + d - r := by linarith
          have hB : (0 : ℝ) ≤ R + d + r := by linarith
          positivity
        _ = (R + d) ^ 2 - r ^ 2 := by ring
    have h2 : (0 : ℝ) ≤ r ^ 2 - (R - d) ^ 2 := by
      have h_le1 : R - d ≤ r := le_trans (le_abs_self _) hr_min
      have h_le2 : -(R - d) ≤ r := le_trans (neg_le_abs _) hr_min
      calc
        (0 : ℝ) ≤ (r - (R - d)) * (r + (R - d)) := by
          have hA : (0 : ℝ) ≤ r - (R - d) := by linarith
          have hB : (0 : ℝ) ≤ r + (R - d) := by linarith
          positivity
        _ = r ^ 2 - (R - d) ^ 2 := by ring
    have hnum_nonneg : (0 : ℝ) ≤ num := mul_nonneg h1 h2

    let α := (d ^ 2 + R ^ 2 - r ^ 2) / ((2 : ℝ) * d ^ 2)
    let β := Real.sqrt num / ((2 : ℝ) * d ^ 2)
    let X0 : ℝ := A0 + α * (B0 - A0) - β * (B1 - A1)
    let X1 : ℝ := A1 + α * (B1 - A1) + β * (B0 - A0)
    let X : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 (fun i : Fin 2 => if i = (0 : Fin 2) then X0 else X1)
    use X

    have h_X0 : X.ofLp (0 : Fin 2) = X0 := by
      change (if (0 : Fin 2) = (0 : Fin 2) then X0 else X1) = X0
      exact if_pos rfl
    have h_X1 : X.ofLp (1 : Fin 2) = X1 := by
      change (if (1 : Fin 2) = (0 : Fin 2) then X0 else X1) = X1
      have h_neq : (1 : Fin 2) ≠ (0 : Fin 2) := by decide
      exact if_neg h_neq

    have h_β_sq : β ^ 2 = num / ((4 : ℝ) * d ^ 4) := by
      calc
        β ^ 2 = (Real.sqrt num / ((2 : ℝ) * d ^ 2)) ^ 2 := rfl
        _ = (Real.sqrt num) ^ 2 / ((2 : ℝ) * d ^ 2) ^ 2 := by rw [div_pow]
        _ = num / ((4 : ℝ) * d ^ 4) := by
          rw [Real.sq_sqrt hnum_nonneg]
          congr 1
          ring
    have h_α_sq : α ^ 2 = (d ^ 2 + R ^ 2 - r ^ 2) ^ 2 / ((4 : ℝ) * d ^ 4) := by
      calc
        α ^ 2 = ((d ^ 2 + R ^ 2 - r ^ 2) / ((2 : ℝ) * d ^ 2)) ^ 2 := rfl
        _ = (d ^ 2 + R ^ 2 - r ^ 2) ^ 2 / ((2 : ℝ) * d ^ 2) ^ 2 := by rw [div_pow]
        _ = (d ^ 2 + R ^ 2 - r ^ 2) ^ 2 / ((4 : ℝ) * d ^ 4) := by
          congr 1
          ring

    have hdA : dist X A ^ 2 = R ^ 2 := by
      have h_sq := EuclideanSpace.dist_sq_eq X A
      have h_sum : (∑ i : Fin 2, dist (X.ofLp i) (A.ofLp i) ^ 2) = dist (X.ofLp (0 : Fin 2)) (A.ofLp (0 : Fin 2)) ^ 2 + dist (X.ofLp (1 : Fin 2)) (A.ofLp (1 : Fin 2)) ^ 2 := by
        rw [Fin.sum_univ_two]
      rw [h_sum] at h_sq
      have h0 : dist (X.ofLp (0 : Fin 2)) (A.ofLp (0 : Fin 2)) ^ 2 = (X0 - A0) ^ 2 := by
        rw [h_X0]
        change dist X0 A0 ^ 2 = (X0 - A0) ^ 2
        have h_eq : dist X0 A0 = |X0 - A0| := rfl
        rw [h_eq, sq_abs]
      have h1 : dist (X.ofLp (1 : Fin 2)) (A.ofLp (1 : Fin 2)) ^ 2 = (X1 - A1) ^ 2 := by
        rw [h_X1]
        change dist X1 A1 ^ 2 = (X1 - A1) ^ 2
        have h_eq : dist X1 A1 = |X1 - A1| := rfl
        rw [h_eq, sq_abs]
      rw [h0, h1] at h_sq
      have hX0_sub : X0 - A0 = α * (B0 - A0) - β * (B1 - A1) := by
        calc X0 - A0 = (A0 + α * (B0 - A0) - β * (B1 - A1)) - A0 := rfl
          _ = α * (B0 - A0) - β * (B1 - A1) := by ring
      have hX1_sub : X1 - A1 = α * (B1 - A1) + β * (B0 - A0) := by
        calc X1 - A1 = (A1 + α * (B1 - A1) + β * (B0 - A0)) - A1 := rfl
          _ = α * (B1 - A1) + β * (B0 - A0) := by ring
      rw [hX0_sub, hX1_sub] at h_sq
      have h_expand : (α * (B0 - A0) - β * (B1 - A1)) ^ 2 + (α * (B1 - A1) + β * (B0 - A0)) ^ 2 = (α ^ 2 + β ^ 2) * ((B0 - A0) ^ 2 + (B1 - A1) ^ 2) := by ring
      rw [h_expand] at h_sq
      have h_d_sq : (B0 - A0) ^ 2 + (B1 - A1) ^ 2 = d ^ 2 := by exact hd_sq.symm
      rw [h_d_sq] at h_sq
      have h_alg : (α ^ 2 + β ^ 2) * d ^ 2 = R ^ 2 := by
        rw [h_α_sq, h_β_sq]
        have hd2_ne_zero : d ^ 2 ≠ (0 : ℝ) := by positivity
        have h_num_add : (d ^ 2 + R ^ 2 - r ^ 2) ^ 2 + num = (4 : ℝ) * R ^ 2 * d ^ 2 := by
          calc (d ^ 2 + R ^ 2 - r ^ 2) ^ 2 + num = (d ^ 2 + R ^ 2 - r ^ 2) ^ 2 + ((R + d) ^ 2 - r ^ 2) * (r ^ 2 - (R - d) ^ 2) := rfl
            _ = (4 : ℝ) * R ^ 2 * d ^ 2 := by ring
        calc
          ((d ^ 2 + R ^ 2 - r ^ 2) ^ 2 / ((4 : ℝ) * d ^ 4) + num / ((4 : ℝ) * d ^ 4)) * d ^ 2 = ((d ^ 2 + R ^ 2 - r ^ 2) ^ 2 + num) / ((4 : ℝ) * d ^ 4) * d ^ 2 := by ring
          _ = ((4 : ℝ) * R ^ 2 * d ^ 2) / ((4 : ℝ) * d ^ 4) * d ^ 2 := by rw [h_num_add]
          _ = (R ^ 2 / d ^ 2) * d ^ 2 := by
             have H : ((4 : ℝ) * R ^ 2 * d ^ 2) / ((4 : ℝ) * d ^ 4) = R ^ 2 / d ^ 2 := by
               have h_num : (4 : ℝ) * R ^ 2 * d ^ 2 = R ^ 2 * ((4 : ℝ) * d ^ 2) := by ring
               have h_den : (4 : ℝ) * d ^ 4 = d ^ 2 * ((4 : ℝ) * d ^ 2) := by ring
               rw [h_num, h_den]
               rw [mul_div_mul_right (R ^ 2) (d ^ 2) (by positivity)]
             rw [H]
          _ = R ^ 2 := div_mul_cancel₀ _ hd2_ne_zero
      rw [h_alg] at h_sq
      exact h_sq

    have hdB : dist X B ^ 2 = r ^ 2 := by
      have h_sq := EuclideanSpace.dist_sq_eq X B
      have h_sum : (∑ i : Fin 2, dist (X.ofLp i) (B.ofLp i) ^ 2) = dist (X.ofLp (0 : Fin 2)) (B.ofLp (0 : Fin 2)) ^ 2 + dist (X.ofLp (1 : Fin 2)) (B.ofLp (1 : Fin 2)) ^ 2 := by
        rw [Fin.sum_univ_two]
      rw [h_sum] at h_sq
      have h0 : dist (X.ofLp (0 : Fin 2)) (B.ofLp (0 : Fin 2)) ^ 2 = (X0 - B0) ^ 2 := by
        rw [h_X0]
        change dist X0 B0 ^ 2 = (X0 - B0) ^ 2
        have h_eq : dist X0 B0 = |X0 - B0| := rfl
        rw [h_eq, sq_abs]
      have h1 : dist (X.ofLp (1 : Fin 2)) (B.ofLp (1 : Fin 2)) ^ 2 = (X1 - B1) ^ 2 := by
        rw [h_X1]
        change dist X1 B1 ^ 2 = (X1 - B1) ^ 2
        have h_eq : dist X1 B1 = |X1 - B1| := rfl
        rw [h_eq, sq_abs]
      rw [h0, h1] at h_sq
      have hX0_sub : X0 - B0 = (α - (1 : ℝ)) * (B0 - A0) - β * (B1 - A1) := by
        calc X0 - B0 = (A0 + α * (B0 - A0) - β * (B1 - A1)) - B0 := rfl
          _ = (α - (1 : ℝ)) * (B0 - A0) - β * (B1 - A1) := by ring
      have hX1_sub : X1 - B1 = (α - (1 : ℝ)) * (B1 - A1) + β * (B0 - A0) := by
        calc X1 - B1 = (A1 + α * (B1 - A1) + β * (B0 - A0)) - B1 := rfl
          _ = (α - (1 : ℝ)) * (B1 - A1) + β * (B0 - A0) := by ring
      rw [hX0_sub, hX1_sub] at h_sq
      have h_expand : ((α - (1 : ℝ)) * (B0 - A0) - β * (B1 - A1)) ^ 2 + ((α - (1 : ℝ)) * (B1 - A1) + β * (B0 - A0)) ^ 2 = ((α - (1 : ℝ)) ^ 2 + β ^ 2) * ((B0 - A0) ^ 2 + (B1 - A1) ^ 2) := by ring
      rw [h_expand] at h_sq
      have h_d_sq : (B0 - A0) ^ 2 + (B1 - A1) ^ 2 = d ^ 2 := by exact hd_sq.symm
      rw [h_d_sq] at h_sq
      have h_α_minus_one_sq : (α - (1 : ℝ)) ^ 2 = (R ^ 2 - d ^ 2 - r ^ 2) ^ 2 / ((4 : ℝ) * d ^ 4) := by
        have hd2_ne_zero : (2 : ℝ) * d ^ 2 ≠ (0 : ℝ) := by positivity
        calc
          (α - (1 : ℝ)) ^ 2 = (α - ((2 : ℝ) * d ^ 2) / ((2 : ℝ) * d ^ 2)) ^ 2 := by
            have h1 : (1 : ℝ) = ((2 : ℝ) * d ^ 2) / ((2 : ℝ) * d ^ 2) := (div_self hd2_ne_zero).symm
            rw [h1]
          _ = ((d ^ 2 + R ^ 2 - r ^ 2) / ((2 : ℝ) * d ^ 2) - ((2 : ℝ) * d ^ 2) / ((2 : ℝ) * d ^ 2)) ^ 2 := rfl
          _ = ((d ^ 2 + R ^ 2 - r ^ 2 - (2 : ℝ) * d ^ 2) / ((2 : ℝ) * d ^ 2)) ^ 2 := by rw [← sub_div]
          _ = (R ^ 2 - d ^ 2 - r ^ 2) ^ 2 / ((4 : ℝ) * d ^ 4) := by
            rw [div_pow]
            congr 1
            · ring
            · ring
      have h_alg : ((α - (1 : ℝ)) ^ 2 + β ^ 2) * d ^ 2 = r ^ 2 := by
        rw [h_α_minus_one_sq, h_β_sq]
        have hd2_ne_zero : d ^ 2 ≠ (0 : ℝ) := by positivity
        have h_num_add : (R ^ 2 - d ^ 2 - r ^ 2) ^ 2 + num = (4 : ℝ) * r ^ 2 * d ^ 2 := by
          calc (R ^ 2 - d ^ 2 - r ^ 2) ^ 2 + num = (R ^ 2 - d ^ 2 - r ^ 2) ^ 2 + ((R + d) ^ 2 - r ^ 2) * (r ^ 2 - (R - d) ^ 2) := rfl
            _ = (4 : ℝ) * r ^ 2 * d ^ 2 := by ring
        calc
          ((R ^ 2 - d ^ 2 - r ^ 2) ^ 2 / ((4 : ℝ) * d ^ 4) + num / ((4 : ℝ) * d ^ 4)) * d ^ 2 = ((R ^ 2 - d ^ 2 - r ^ 2) ^ 2 + num) / ((4 : ℝ) * d ^ 4) * d ^ 2 := by ring
          _ = ((4 : ℝ) * r ^ 2 * d ^ 2) / ((4 : ℝ) * d ^ 4) * d ^ 2 := by rw [h_num_add]
          _ = (r ^ 2 / d ^ 2) * d ^ 2 := by
             have H : ((4 : ℝ) * r ^ 2 * d ^ 2) / ((4 : ℝ) * d ^ 4) = r ^ 2 / d ^ 2 := by
               have h_num : (4 : ℝ) * r ^ 2 * d ^ 2 = r ^ 2 * ((4 : ℝ) * d ^ 2) := by ring
               have h_den : (4 : ℝ) * d ^ 4 = d ^ 2 * ((4 : ℝ) * d ^ 2) := by ring
               rw [h_num, h_den]
               rw [mul_div_mul_right (r ^ 2) (d ^ 2) (by positivity)]
             rw [H]
          _ = r ^ 2 := div_mul_cancel₀ _ hd2_ne_zero
      rw [h_alg] at h_sq
      exact h_sq

    have h_dist_A : dist X A = R := by
      have H1 : Real.sqrt (dist X A ^ 2) = dist X A := Real.sqrt_sq dist_nonneg
      have H2 : Real.sqrt (R ^ 2) = R := Real.sqrt_sq hR_nonneg
      calc
        dist X A = Real.sqrt (dist X A ^ 2) := H1.symm
        _ = Real.sqrt (R ^ 2) := by rw [hdA]
        _ = R := H2

    have h_dist_B : dist X B = r := by
      have H1 : Real.sqrt (dist X B ^ 2) = dist X B := Real.sqrt_sq dist_nonneg
      have H2 : Real.sqrt (r ^ 2) = r := Real.sqrt_sq hr_nonneg
      calc
        dist X B = Real.sqrt (dist X B ^ 2) := H1.symm
        _ = Real.sqrt (r ^ 2) := by rw [hdB]
        _ = r := H2

    exact ⟨h_dist_A, h_dist_B⟩

theorem bool_eq_of_ne_of_ne {a b c : Bool} (h1 : b ≠ a) (h2 : c ≠ a) : b = c :=
by
  cases a <;> cases b <;> cases c <;> simp_all

theorem not_three_opposite_color (color : EuclideanSpace ℝ (Fin 2) → Bool)
  (h : ∀ s : Simplex ℝ (EuclideanSpace ℝ (Fin 2)) 2,
    (∀ i j : Fin 3, color (s.points i) = color (s.points j)) →
    color s.circumcenter = color (s.points 0))
  (A : EuclideanSpace ℝ (Fin 2)) (R : ℝ)
  (Y_1 Y_2 Y_3 : EuclideanSpace ℝ (Fin 2))
  (hd12 : Y_1 ≠ Y_2) (hd23 : Y_2 ≠ Y_3) (hd13 : Y_1 ≠ Y_3)
  (hr1 : dist Y_1 A = R) (hr2 : dist Y_2 A = R) (hr3 : dist Y_3 A = R) :
  ¬ (color Y_1 ≠ color A ∧ color Y_2 ≠ color A ∧ color Y_3 ≠ color A) :=
by
  intro ⟨h1, h2, h3⟩
  have hc12 : color Y_1 = color Y_2 := bool_eq_of_ne_of_ne h1 h2
  have hc23 : color Y_2 = color Y_3 := bool_eq_of_ne_of_ne h2 h3
  have h_center : color A = color Y_1 :=
    color_center_of_three_points color h A R Y_1 Y_2 Y_3 hd12 hd23 hd13 hr1 hr2 hr3 hc12 hc23
  exact h1 h_center.symm

theorem not_three_exceptions_for_color (color : EuclideanSpace ℝ (Fin 2) → Bool)
  (h : ∀ s : Simplex ℝ (EuclideanSpace ℝ (Fin 2)) 2,
    (∀ i j : Fin 3, color (s.points i) = color (s.points j)) →
    color s.circumcenter = color (s.points 0))
  (A B : EuclideanSpace ℝ (Fin 2)) (R : ℝ) :
  ¬ ∃ r1 r2 r3 : ℝ, r1 ≠ r2 ∧ r2 ≠ r3 ∧ r1 ≠ r3 ∧
    (|R - dist A B| ≤ r1 ∧ r1 ≤ R + dist A B ∧ ∀ X : EuclideanSpace ℝ (Fin 2), dist X A = R → dist X B = r1 → color X ≠ color A) ∧
    (|R - dist A B| ≤ r2 ∧ r2 ≤ R + dist A B ∧ ∀ X : EuclideanSpace ℝ (Fin 2), dist X A = R → dist X B = r2 → color X ≠ color A) ∧
    (|R - dist A B| ≤ r3 ∧ r3 ≤ R + dist A B ∧ ∀ X : EuclideanSpace ℝ (Fin 2), dist X A = R → dist X B = r3 → color X ≠ color A) :=
by
  intro h_ex
  -- Extract variables and conditions
  rcases h_ex with ⟨r1, r2, r3, h12, h23, h13, h1, h2, h3⟩
  rcases h1 with ⟨h1_min, h1_max, h1_color⟩
  rcases h2 with ⟨h2_min, h2_max, h2_color⟩
  rcases h3 with ⟨h3_min, h3_max, h3_color⟩

  -- Obtain X1, X2, X3 from the bounded radii
  have ⟨X1, hX1A, hX1B⟩ := exists_point_on_circle_with_dist A B R r1 h1_min h1_max
  have ⟨X2, hX2A, hX2B⟩ := exists_point_on_circle_with_dist A B R r2 h2_min h2_max
  have ⟨X3, hX3A, hX3B⟩ := exists_point_on_circle_with_dist A B R r3 h3_min h3_max

  -- Prove that the distinct lengths to B imply distinct points
  have h_ne12 : X1 ≠ X2 := by
    intro heq
    apply h12
    rw [← hX1B, ← hX2B, heq]

  have h_ne23 : X2 ≠ X3 := by
    intro heq
    apply h23
    rw [← hX2B, ← hX3B, heq]

  have h_ne13 : X1 ≠ X3 := by
    intro heq
    apply h13
    rw [← hX1B, ← hX3B, heq]

  -- Establish that all distinct points hold opposite coloring to A
  have hc1 := h1_color X1 hX1A hX1B
  have hc2 := h2_color X2 hX2A hX2B
  have hc3 := h3_color X3 hX3A hX3B

  -- Final contradiction based on previously stated lemma constraints
  exact not_three_opposite_color color h A R X1 X2 X3 h_ne12 h_ne23 h_ne13 hX1A hX2A hX3A ⟨hc1, hc2, hc3⟩

theorem exists_same_color_with_dist (color : EuclideanSpace ℝ (Fin 2) → Bool)
  (h : ∀ s : Simplex ℝ (EuclideanSpace ℝ (Fin 2)) 2,
    (∀ i j : Fin 3, color (s.points i) = color (s.points j)) →
    color s.circumcenter = color (s.points 0))
  (A B : EuclideanSpace ℝ (Fin 2)) (R : ℝ) :
  ∃ b1 b2 : ℝ, ∀ r : ℝ,
    |R - dist A B| ≤ r → r ≤ R + dist A B → r ≠ b1 → r ≠ b2 →
    ∃ X : EuclideanSpace ℝ (Fin 2), dist X A = R ∧ dist X B = r ∧ color X = color A :=
by
  let P : ℝ → Prop := fun r => |R - dist A B| ≤ r ∧ r ≤ R + dist A B ∧ ∀ X : EuclideanSpace ℝ (Fin 2), dist X A = R → dist X B = r → color X ≠ color A
  have h_not_three : ¬ ∃ r1 r2 r3 : ℝ, r1 ≠ r2 ∧ r2 ≠ r3 ∧ r1 ≠ r3 ∧ P r1 ∧ P r2 ∧ P r3 :=
    not_three_exceptions_for_color color h A B R
  rcases at_most_two_exceptions P h_not_three with ⟨b1, b2, hb⟩
  use b1, b2
  intro r hr_min hr_max h_neq1 h_neq2
  by_contra h_none
  have hPr : P r := by
    refine ⟨hr_min, hr_max, ?_⟩
    intro X hXA hXB hColor
    apply h_none
    exact ⟨X, hXA, hXB, hColor⟩
  have h_eq : r = b1 ∨ r = b2 := hb r hPr
  rcases h_eq with r_eq_b1 | r_eq_b2
  · exact h_neq1 r_eq_b1
  · exact h_neq2 r_eq_b2

theorem exists_good_r (d : ℝ) (hd : d > 0) (b1 b2 b3 b4 b5 b6 : ℝ) :
  ∃ r : ℝ, (2 : ℝ) * d ≤ r ∧ r ≤ (3 : ℝ) * d ∧
    r ≠ b1 ∧ r ≠ b2 ∧ r ≠ b3 ∧ r ≠ b4 ∧ r ≠ b5 ∧ r ≠ b6 :=
by
  classical
  have h_lt : (2 : ℝ) * d < (3 : ℝ) * d := by linarith
  have h_inf := Set.Icc_infinite h_lt
  have h_ex := h_inf.exists_notMem_finset ({b1, b2, b3, b4, b5, b6} : Finset ℝ)
  obtain ⟨r, hr_mem, hr_not⟩ := h_ex
  use r
  refine ⟨hr_mem.1, hr_mem.2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h; apply hr_not; rw [h]; simp [Finset.mem_insert, Finset.mem_singleton]
  · intro h; apply hr_not; rw [h]; simp [Finset.mem_insert, Finset.mem_singleton]
  · intro h; apply hr_not; rw [h]; simp [Finset.mem_insert, Finset.mem_singleton]
  · intro h; apply hr_not; rw [h]; simp [Finset.mem_insert, Finset.mem_singleton]
  · intro h; apply hr_not; rw [h]; simp [Finset.mem_insert, Finset.mem_singleton]
  · intro h; apply hr_not; rw [h]; simp [Finset.mem_insert, Finset.mem_singleton]

theorem putnam_2025_b1 (color : EuclideanSpace ℝ (Fin 2) → Bool)
    (h : ∀ (s : Simplex ℝ (EuclideanSpace ℝ (Fin 2)) 2),
      (∀ i j : Fin 3, color (s.points i) = color (s.points j)) →
      color s.circumcenter = color (s.points 0)) : ∃ c : Bool, ∀ P : EuclideanSpace ℝ (Fin 2), color P = c :=
by
  by_contra h_neg
  push_neg at h_neg
  have hA := h_neg true
  rcases hA with ⟨A, hA'⟩
  have hB := h_neg false
  rcases hB with ⟨B, hB'⟩

  have hcA : color A = false := by
    cases h_color : color A
    · rfl
    · exfalso; exact hA' h_color
  have hcB : color B = true := by
    cases h_color : color B
    · exfalso; exact hB' h_color
    · rfl

  have hAB : color A ≠ color B := by
    rw [hcA, hcB]
    decide

  have hAB_neq : A ≠ B := fun h_eq => hAB (by rw [h_eq])
  have hd : dist A B > 0 := dist_pos.mpr hAB_neq

  have h_ex1 := exists_same_color_with_dist color h A B ((2 : ℝ) * dist A B)
  rcases h_ex1 with ⟨b1, b2, H1⟩

  have h_ex2 := exists_same_color_with_dist color h A B (((5 : ℝ) / (2 : ℝ)) * dist A B)
  rcases h_ex2 with ⟨b3, b4, H2⟩

  have h_ex3 := exists_same_color_with_dist color h A B ((3 : ℝ) * dist A B)
  rcases h_ex3 with ⟨b5, b6, H3⟩

  have h_r := exists_good_r (dist A B) hd b1 b2 b3 b4 b5 b6
  rcases h_r with ⟨r, hr23, hr33, hr_b1, hr_b2, hr_b3, hr_b4, hr_b5, hr_b6⟩

  have H1_min : |(2 : ℝ) * dist A B - dist A B| ≤ r := by
    have h_sub : (2 : ℝ) * dist A B - dist A B = dist A B := by ring
    rw [h_sub, abs_of_pos hd]
    linarith
  have H1_max : r ≤ (2 : ℝ) * dist A B + dist A B := by
    have h_add : (2 : ℝ) * dist A B + dist A B = (3 : ℝ) * dist A B := by ring
    rw [h_add]
    exact hr33

  rcases H1 r H1_min H1_max hr_b1 hr_b2 with ⟨X1, hX1A, hX1B, hX1c⟩

  have H2_min : |((5 : ℝ) / (2 : ℝ)) * dist A B - dist A B| ≤ r := by
    have h_sub : ((5 : ℝ) / (2 : ℝ)) * dist A B - dist A B = ((3 : ℝ) / (2 : ℝ)) * dist A B := by ring
    rw [h_sub, abs_of_pos (by linarith)]
    linarith
  have H2_max : r ≤ ((5 : ℝ) / (2 : ℝ)) * dist A B + dist A B := by
    have h_add : ((5 : ℝ) / (2 : ℝ)) * dist A B + dist A B = ((7 : ℝ) / (2 : ℝ)) * dist A B := by ring
    rw [h_add]
    linarith

  rcases H2 r H2_min H2_max hr_b3 hr_b4 with ⟨X2, hX2A, hX2B, hX2c⟩

  have H3_min : |(3 : ℝ) * dist A B - dist A B| ≤ r := by
    have h_sub : (3 : ℝ) * dist A B - dist A B = (2 : ℝ) * dist A B := by ring
    rw [h_sub, abs_of_pos (by linarith)]
    linarith
  have H3_max : r ≤ (3 : ℝ) * dist A B + dist A B := by
    have h_add : (3 : ℝ) * dist A B + dist A B = (4 : ℝ) * dist A B := by ring
    rw [h_add]
    linarith

  rcases H3 r H3_min H3_max hr_b5 hr_b6 with ⟨X3, hX3A, hX3B, hX3c⟩

  -- Establish distinction of identified vertices
  have hX12 : X1 ≠ X2 := by
    intro h_eq
    have h_dist : dist X1 A = dist X2 A := by rw [h_eq]
    rw [hX1A, hX2A] at h_dist
    linarith
  have hX23 : X2 ≠ X3 := by
    intro h_eq
    have h_dist : dist X2 A = dist X3 A := by rw [h_eq]
    rw [hX2A, hX3A] at h_dist
    linarith
  have hX13 : X1 ≠ X3 := by
    intro h_eq
    have h_dist : dist X1 A = dist X3 A := by rw [h_eq]
    rw [hX1A, hX3A] at h_dist
    linarith

  -- Match monochromatic vertices
  have hc12 : color X1 = color X2 := by rw [hX1c, hX2c]
  have hc23 : color X2 = color X3 := by rw [hX2c, hX3c]

  -- Resolve contradiction
  have hB_color := color_center_of_three_points color h B r X1 X2 X3 hX12 hX23 hX13 hX1B hX2B hX3B hc12 hc23
  rw [hX1c] at hB_color
  exact hAB hB_color.symm
