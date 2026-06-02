import Mathlib
open Real
noncomputable abbrev putnam_2025_a2_solution : ℝ × ℝ := (1 / π, 4 / π ^ 2)

noncomputable def f_a2 (x : ℝ) : ℝ := (1 : ℝ) - cos x - ((2 : ℝ) / π) * x
noncomputable def f'_a2 (x : ℝ) : ℝ := sin x - ((2 : ℝ) / π)
noncomputable def h_a2 (x : ℝ) : ℝ := sin x - x + x ^ 2 / π
noncomputable def h'_a2 (x : ℝ) : ℝ := cos x - (1 : ℝ) + ((2 : ℝ) / π) * x

theorem v_bounds {x : ℝ} (hx1 : (0 : ℝ) ≤ x) (hx2 : x ≤ π) :
  (0 : ℝ) ≤ |x - π / (2 : ℝ)| / (2 : ℝ) ∧ |x - π / (2 : ℝ)| / (2 : ℝ) ≤ π / (4 : ℝ) :=
by
  constructor
  · positivity
  · have h3 : x - π / (2 : ℝ) ≤ π / (2 : ℝ) := by linarith
    have h4 : -(π / (2 : ℝ)) ≤ x - π / (2 : ℝ) := by linarith
    have h5 : |x - π / (2 : ℝ)| ≤ π / (2 : ℝ) := abs_le.mpr ⟨h4, h3⟩
    linarith

theorem sin_ge_mul_x {x : ℝ} (hx1 : (0 : ℝ) ≤ x) (hx2 : x ≤ π / (4 : ℝ)) :
  ((2 : ℝ) * Real.sqrt (2 : ℝ) / π) * x ≤ sin x :=
by
  have hp : 0 < π := Real.pi_pos
  let b := x * 4 / π
  let a := 1 - b

  have hb0 : 0 ≤ b := div_nonneg (mul_nonneg hx1 (by norm_num)) hp.le
  have hb1 : b ≤ 1 := by
    rw [div_le_one hp]
    calc x * 4 ≤ (π / 4) * 4 := mul_le_mul_of_nonneg_right hx2 (by norm_num)
      _ = π := div_mul_cancel₀ π (by norm_num)
  have ha0 : 0 ≤ a := sub_nonneg.mpr hb1
  have hab : a + b = 1 := sub_add_cancel 1 b

  have h_comb : a * 0 + b * (π / 4) = x := by
    dsimp [a, b]
    have hp_ne : π ≠ 0 := hp.ne'
    have h4_ne : (4 : ℝ) ≠ 0 := by norm_num
    field_simp
    ring

  have h_concave : ConcaveOn ℝ (Set.Icc 0 π) sin := strictConcaveOn_sin_Icc.concaveOn
  have h0 : (0 : ℝ) ∈ Set.Icc 0 π := ⟨le_refl 0, hp.le⟩
  have hpi4 : π / 4 ∈ Set.Icc 0 π := by
    refine ⟨by positivity, ?_⟩
    calc π / 4 = π * (1 / 4) := by ring
      _ ≤ π * 1 := mul_le_mul_of_nonneg_left (by norm_num) hp.le
      _ = π := mul_one π

  have h_ineq := h_concave.2 h0 hpi4 ha0 hb0 hab

  have h_smul_eq : a • (0 : ℝ) + b • (π / 4) = x := by
    change a * 0 + b * (π / 4) = x
    exact h_comb
  rw [h_smul_eq] at h_ineq

  have h_lhs : a • sin 0 + b • sin (π / 4) = ((2 : ℝ) * Real.sqrt (2 : ℝ) / π) * x := by
    change a * sin 0 + b * sin (π / 4) = _
    rw [Real.sin_zero, Real.sin_pi_div_four]
    dsimp [b]
    ring

  rw [h_lhs] at h_ineq
  exact h_ineq

theorem square_ineq {v : ℝ} (hv_nonneg : (0 : ℝ) ≤ v) (h : ((2 : ℝ) * Real.sqrt (2 : ℝ) / π) * v ≤ sin v) :
  ((8 : ℝ) / π ^ 2) * v ^ 2 ≤ sin v ^ 2 :=
by
  have h1 : (0 : ℝ) ≤ ((2 : ℝ) * Real.sqrt (2 : ℝ) / π) * v := by positivity
  have h2 : (0 : ℝ) ≤ sin v := le_trans h1 h
  have h_sq : (((2 : ℝ) * Real.sqrt (2 : ℝ) / π) * v) ^ 2 ≤ sin v ^ 2 := by
    calc (((2 : ℝ) * Real.sqrt (2 : ℝ) / π) * v) ^ 2
      _ = (((2 : ℝ) * Real.sqrt (2 : ℝ) / π) * v) * (((2 : ℝ) * Real.sqrt (2 : ℝ) / π) * v) := by ring
      _ ≤ sin v * sin v := mul_le_mul h h h1 h2
      _ = sin v ^ 2 := by ring
  have h3 : (((2 : ℝ) * Real.sqrt (2 : ℝ) / π) * v) ^ 2 = ((8 : ℝ) / π ^ 2) * v ^ 2 := by
    have hs : (Real.sqrt (2 : ℝ)) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
    calc (((2 : ℝ) * Real.sqrt (2 : ℝ) / π) * v) ^ 2
      _ = ((2 : ℝ) ^ 2 * (Real.sqrt (2 : ℝ)) ^ 2 / π ^ 2) * v ^ 2 := by ring
      _ = ((2 : ℝ) ^ 2 * (2 : ℝ) / π ^ 2) * v ^ 2 := by rw [hs]
      _ = ((8 : ℝ) / π ^ 2) * v ^ 2 := by ring
  rwa [h3] at h_sq

theorem lin_arith_step {v : ℝ} (h : ((8 : ℝ) / π ^ 2) * v ^ 2 ≤ sin v ^ 2) :
  (1 : ℝ) - (2 : ℝ) * sin v ^ 2 ≤ (1 : ℝ) - ((16 : ℝ) / π ^ 2) * v ^ 2 :=
by
  calc
    (1 : ℝ) - (2 : ℝ) * sin v ^ 2 ≤ (1 : ℝ) - (2 : ℝ) * (((8 : ℝ) / π ^ 2) * v ^ 2) := by linarith
    _ = (1 : ℝ) - ((16 : ℝ) / π ^ 2) * v ^ 2 := by ring

theorem sin_eq_one_minus_two_sin_sq (x : ℝ) :
  sin x = (1 : ℝ) - (2 : ℝ) * sin (|x - π / (2 : ℝ)| / (2 : ℝ)) ^ 2 :=
by
  have h1 : (2 : ℝ) * sin (|x - π / (2 : ℝ)| / (2 : ℝ)) ^ 2 = 2 * sin (|x - π / (2 : ℝ)| / (2 : ℝ)) * sin (|x - π / (2 : ℝ)| / (2 : ℝ)) := by ring
  have h2 : 2 * sin (|x - π / (2 : ℝ)| / (2 : ℝ)) * sin (|x - π / (2 : ℝ)| / (2 : ℝ)) = cos (|x - π / (2 : ℝ)| / (2 : ℝ) - |x - π / (2 : ℝ)| / (2 : ℝ)) - cos (|x - π / (2 : ℝ)| / (2 : ℝ) + |x - π / (2 : ℝ)| / (2 : ℝ)) := Real.two_mul_sin_mul_sin (|x - π / (2 : ℝ)| / (2 : ℝ)) (|x - π / (2 : ℝ)| / (2 : ℝ))
  have h3 : |x - π / (2 : ℝ)| / (2 : ℝ) - |x - π / (2 : ℝ)| / (2 : ℝ) = 0 := by ring
  have h4 : |x - π / (2 : ℝ)| / (2 : ℝ) + |x - π / (2 : ℝ)| / (2 : ℝ) = |x - π / (2 : ℝ)| := by ring
  have h5 : (1 : ℝ) - (2 : ℝ) * sin (|x - π / (2 : ℝ)| / (2 : ℝ)) ^ 2 = cos (|x - π / (2 : ℝ)|) := by
    calc (1 : ℝ) - (2 : ℝ) * sin (|x - π / (2 : ℝ)| / (2 : ℝ)) ^ 2
      _ = (1 : ℝ) - (2 * sin (|x - π / (2 : ℝ)| / (2 : ℝ)) * sin (|x - π / (2 : ℝ)| / (2 : ℝ))) := by rw [h1]
      _ = (1 : ℝ) - (cos (|x - π / (2 : ℝ)| / (2 : ℝ) - |x - π / (2 : ℝ)| / (2 : ℝ)) - cos (|x - π / (2 : ℝ)| / (2 : ℝ) + |x - π / (2 : ℝ)| / (2 : ℝ))) := by rw [h2]
      _ = (1 : ℝ) - (cos 0 - cos (|x - π / (2 : ℝ)|)) := by rw [h3, h4]
      _ = (1 : ℝ) - (1 - cos (|x - π / (2 : ℝ)|)) := by rw [Real.cos_zero]
      _ = cos (|x - π / (2 : ℝ)|) := by ring
  rw [h5, Real.cos_abs, Real.cos_sub_pi_div_two]

theorem poly_eq_one_minus_sq (x : ℝ) :
  putnam_2025_a2_solution.2 * x * (π - x) =
  (1 : ℝ) - ((16 : ℝ) / π ^ 2) * (|x - π / (2 : ℝ)| / (2 : ℝ)) ^ 2 :=
by
  change (4 : ℝ) / π ^ 2 * x * (π - x) = (1 : ℝ) - ((16 : ℝ) / π ^ 2) * (|x - π / (2 : ℝ)| / (2 : ℝ)) ^ 2
  have h_sq : (|x - π / (2 : ℝ)| / (2 : ℝ)) ^ 2 = (|x - π / (2 : ℝ)| * |x - π / (2 : ℝ)|) / (4 : ℝ) := by ring
  have h_abs : |x - π / (2 : ℝ)| * |x - π / (2 : ℝ)| = (x - π / (2 : ℝ)) * (x - π / (2 : ℝ)) := abs_mul_abs_self (x - π / (2 : ℝ))
  rw [h_sq, h_abs]
  have h_pi : (π : ℝ) ≠ 0 := by positivity
  field_simp
  ring

theorem putnam_2025_a2_upper_bound : ∀ x ∈ Set.Icc 0 π, sin x ≤ putnam_2025_a2_solution.2 * x * (π - x) :=
by
  intro x hx

  -- Extract domain bounds on x
  have hx1 : (0 : ℝ) ≤ x := hx.1
  have hx2 : x ≤ π := hx.2

  -- Validate the bounds of v = |x - π/2| / 2
  have hv := v_bounds hx1 hx2

  -- Fetch the core lower bound and process it algebraically
  have h1 := sin_ge_mul_x hv.1 hv.2
  have h2 := square_ineq hv.1 h1
  have h3 := lin_arith_step h2

  -- Instantiate shift equalities to finalize the shape of both sides
  have h4 := sin_eq_one_minus_two_sin_sq x
  have h5 := poly_eq_one_minus_sq x

  -- Rewrite LHS and RHS, reducing the goal exactly into the shape of h3
  rw [h4, h5]
  exact h3

theorem putnam_2025_a2_lower_bound_left {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) (π / (2 : ℝ))) :
  putnam_2025_a2_solution.1 * x * (π - x) ≤ sin x :=
by
  let f : ℝ → ℝ := fun t => Real.sin t - t + ((1 : ℝ) / π) * (t * t)

  have hf_eq : ∀ t, Real.sin t - ((1 : ℝ) / π) * t * (π - t) = f t := by
    intro t
    dsimp [f]
    have hpi : π ≠ 0 := Real.pi_ne_zero
    have h_div : π / π = 1 := div_self hpi
    calc
      Real.sin t - ((1 : ℝ) / π) * t * (π - t) = Real.sin t - t * (π / π) + ((1 : ℝ) / π) * (t * t) := by ring
      _ = Real.sin t - t * 1 + ((1 : ℝ) / π) * (t * t) := by rw [h_div]
      _ = Real.sin t - t + ((1 : ℝ) / π) * (t * t) := by ring

  have hf_diff : Differentiable ℝ f := by
    apply Differentiable.add
    · apply Differentiable.sub
      · exact differentiable_sin
      · exact differentiable_id
    · apply Differentiable.mul
      · exact differentiable_const _
      · apply Differentiable.mul
        · exact differentiable_id
        · exact differentiable_id

  have h_has_deriv : ∀ c, HasDerivAt f (Real.cos c - (1 : ℝ) + (2 : ℝ) * c / π) c := by
    intro c
    have h1 := hasDerivAt_sin c
    have h2 := hasDerivAt_id c
    have h3 := HasDerivAt.sub h1 h2
    have h5 := HasDerivAt.mul h2 h2
    have h6 := HasDerivAt.const_mul ((1 : ℝ) / π) h5
    have h7 := HasDerivAt.add h3 h6
    apply HasDerivAt.congr_deriv h7
    dsimp only [id]
    ring

  have hf_deriv : ∀ c, deriv f c = Real.cos c - (1 : ℝ) + (2 : ℝ) * c / π := by
    intro c
    exact (h_has_deriv c).deriv

  have h_deriv_nonneg : ∀ c ∈ Set.Icc (0 : ℝ) (π / (2 : ℝ)), (0 : ℝ) ≤ deriv f c := by
    intro c hc
    rw [hf_deriv c]
    have hx1 : (0 : ℝ) ∈ Set.Icc (-(π / (2 : ℝ))) (π / (2 : ℝ)) := by
      constructor
      · linarith [Real.pi_pos]
      · linarith [Real.pi_pos]
    have hx2 : π / (2 : ℝ) ∈ Set.Icc (-(π / (2 : ℝ))) (π / (2 : ℝ)) := by
      constructor
      · linarith [Real.pi_pos]
      · exact le_refl _
    have ha : (0 : ℝ) ≤ (1 : ℝ) - (2 : ℝ) * c / π := by
      have hpi : (0 : ℝ) < π := Real.pi_pos
      have hc2 : c ≤ π / (2 : ℝ) := hc.2
      have h1 : (2 : ℝ) * c ≤ π := by linarith
      have h2 : (0 : ℝ) ≤ π⁻¹ := inv_nonneg.mpr (le_of_lt hpi)
      have h_mul : (2 : ℝ) * c * π⁻¹ ≤ π * π⁻¹ := mul_le_mul_of_nonneg_right h1 h2
      change (2 : ℝ) * c / π ≤ π / π at h_mul
      rw [div_self (ne_of_gt hpi)] at h_mul
      linarith
    have hb : (0 : ℝ) ≤ (2 : ℝ) * c / π := by
      have : (0 : ℝ) ≤ c := hc.1
      have hpi : (0 : ℝ) < π := Real.pi_pos
      positivity
    have hab : (1 : ℝ) - (2 : ℝ) * c / π + (2 : ℝ) * c / π = (1 : ℝ) := by ring
    have h_comb : ((1 : ℝ) - (2 : ℝ) * c / π) • (0 : ℝ) + ((2 : ℝ) * c / π) • (π / (2 : ℝ)) = c := by
      have hpi : π ≠ 0 := Real.pi_ne_zero
      have h_div : π / π = 1 := div_self hpi
      rw [smul_eq_mul, smul_eq_mul]
      calc
        ((1 : ℝ) - (2 : ℝ) * c / π) * (0 : ℝ) + ((2 : ℝ) * c / π) * (π / (2 : ℝ)) = c * (π / π) := by ring
        _ = c * 1 := by rw [h_div]
        _ = c := by ring
    have h_conc : ConcaveOn ℝ (Set.Icc (-(π / (2 : ℝ))) (π / (2 : ℝ))) Real.cos := strictConcaveOn_cos_Icc.concaveOn
    have h_eval := h_conc.2 hx1 hx2 ha hb hab
    rw [h_comb] at h_eval
    have h_cos_bnd : (1 : ℝ) - (2 : ℝ) * c / π ≤ Real.cos c := by
      have h_step : (1 : ℝ) - (2 : ℝ) * c / π = ((1 : ℝ) - (2 : ℝ) * c / π) • Real.cos (0 : ℝ) + ((2 : ℝ) * c / π) • Real.cos (π / (2 : ℝ)) := by
        rw [smul_eq_mul, smul_eq_mul, Real.cos_zero, Real.cos_pi_div_two]
        ring
      rw [h_step]
      exact h_eval
    linarith

  have h_f0 : f (0 : ℝ) = (0 : ℝ) := by
    dsimp [f]
    rw [Real.sin_zero]
    ring

  have h_fx_nonneg : (0 : ℝ) ≤ f x := by
    rcases eq_or_lt_of_le hx.1 with hx0 | hx0
    · rw [← hx0, h_f0]
    · have hab : (0 : ℝ) < x := hx0
      have hf_cont : ContinuousOn f (Set.Icc (0 : ℝ) x) := hf_diff.continuous.continuousOn
      have hd : DifferentiableOn ℝ f (Set.Ioo (0 : ℝ) x) := hf_diff.differentiableOn
      obtain ⟨c, hc_oo, hc_eq⟩ := exists_deriv_eq_slope f hab hf_cont hd
      have hc_cc : c ∈ Set.Icc (0 : ℝ) (π / (2 : ℝ)) := by
        constructor
        · exact le_of_lt hc_oo.1
        · exact le_trans (le_of_lt hc_oo.2) hx.2
      have hc_nonneg := h_deriv_nonneg c hc_cc
      rw [hc_eq] at hc_nonneg
      have hx_pos : (0 : ℝ) < x - (0 : ℝ) := by linarith
      have h_mul : (0 : ℝ) ≤ (f x - f (0 : ℝ)) / (x - (0 : ℝ)) * (x - (0 : ℝ)) := mul_nonneg hc_nonneg (le_of_lt hx_pos)
      have h_cancel : (f x - f (0 : ℝ)) / (x - (0 : ℝ)) * (x - (0 : ℝ)) = f x - f (0 : ℝ) := div_mul_cancel₀ (f x - f (0 : ℝ)) (ne_of_gt hx_pos)
      rw [h_cancel] at h_mul
      rw [h_f0] at h_mul
      linarith

  have h_final : (0 : ℝ) ≤ Real.sin x - ((1 : ℝ) / π) * x * (π - x) := by
    rw [hf_eq]
    exact h_fx_nonneg

  have h_sol : putnam_2025_a2_solution.1 = (1 : ℝ) / π := rfl
  rw [h_sol]
  linarith [h_final]

theorem putnam_2025_a2_lower_bound_right_interval_map {x : ℝ} (hx : x ∈ Set.Icc (π / (2 : ℝ)) π) :
  π - x ∈ Set.Icc (0 : ℝ) (π / (2 : ℝ)) :=
by
  rw [Set.mem_Icc] at hx ⊢
  obtain ⟨hx_left, hx_right⟩ := hx
  constructor
  · linarith
  · linarith

theorem putnam_2025_a2_poly_symm (x : ℝ) :
  putnam_2025_a2_solution.1 * (π - x) * (π - (π - x)) = putnam_2025_a2_solution.1 * x * (π - x) :=
by
  ring

theorem h_a2_zero : h_a2 (0 : ℝ) = (0 : ℝ) :=
by
  simp [h_a2]

theorem h'_a2_ge_zero {x : ℝ} (hx0 : (0 : ℝ) ≤ x) (hx1 : x ≤ π / (2 : ℝ)) :
  (0 : ℝ) ≤ h'_a2 x :=
by
  unfold h'_a2
  have h := Real.one_sub_mul_le_cos hx0 hx1
  linarith

theorem hasDerivAt_sin_minus_x (x : ℝ) :
  HasDerivAt (fun x => Real.sin x - x) (Real.cos x - (1 : ℝ)) x :=
by
  exact HasDerivAt.sub (Real.hasDerivAt_sin x) (hasDerivAt_id x)

theorem hasDerivAt_sq_real (x : ℝ) : HasDerivAt (fun x => x ^ 2) ((2 : ℝ) * x) x :=
by
  simpa using hasDerivAt_pow 2 x

theorem hasDerivAt_x_sq_div_pi (x : ℝ) :
  HasDerivAt (fun x => x ^ 2 / Real.pi) (((2 : ℝ) / Real.pi) * x) x :=
by
  -- Divide the derivative of the helper lemma by the constant Real.pi
  have h := HasDerivAt.div_const (hasDerivAt_sq_real x) Real.pi

  -- Assert the algebraic equality bridging our constructed derivative and the target expression
  have h_deriv : (((2 : ℝ) / Real.pi) * x) = ((2 : ℝ) * x) / Real.pi := by
    ring

  -- Rewrite the main goal using the equality and apply the hypothesis
  rw [h_deriv]
  exact h

theorem hasDerivAt_h_a2 (x : ℝ) : HasDerivAt h_a2 (h'_a2 x) x :=
(hasDerivAt_sin_minus_x x).add (hasDerivAt_x_sq_div_pi x)

theorem continuous_h_a2 : Continuous h_a2 :=
by
  unfold h_a2
  continuity

theorem h_a2_eq_derivative_mul {x : ℝ} (hx_pos : (0 : ℝ) < x) :
  ∃ c : ℝ, (0 : ℝ) ≤ c ∧ c ≤ x ∧ h_a2 x = h'_a2 c * x :=
by
  -- Provide continuity on the closed interval using the global derivative
  have h_cont : ContinuousOn h_a2 (Set.Icc (0 : ℝ) x) := continuous_h_a2.continuousOn

  -- Provide differentiability on the open interval using the global derivative
  have h_diff : ∀ y ∈ Set.Ioo (0 : ℝ) x, HasDerivAt h_a2 (h'_a2 y) y :=
    fun y _ => hasDerivAt_h_a2 y

  -- Apply the Mean Value Theorem using Mathlib's exists_hasDerivAt_eq_slope
  obtain ⟨c, hc_mem, hc_eq⟩ := exists_hasDerivAt_eq_slope h_a2 h'_a2 hx_pos h_cont h_diff

  -- Provide c as the witness and extract the required inclusive bounds directly from the strictly bounded ones
  use c
  refine ⟨le_of_lt hc_mem.1, le_of_lt hc_mem.2, ?_⟩

  have hx_sub_ne : x - (0 : ℝ) ≠ 0 := by linarith

  -- We use calc to algebraically rearrange hc_eq into the desired equality
  calc
    h_a2 x = h_a2 x - h_a2 (0 : ℝ) + h_a2 (0 : ℝ) := by ring
    _ = h'_a2 c * (x - (0 : ℝ)) + h_a2 (0 : ℝ) := by
      rw [hc_eq, div_mul_cancel₀ _ hx_sub_ne]
    _ = h'_a2 c * x := by
      rw [h_a2_zero]
      ring

theorem h_a2_nonneg_of_pos {x : ℝ} (hx_pos : (0 : ℝ) < x) (hx_le : x ≤ π / (2 : ℝ)) :
  (0 : ℝ) ≤ h_a2 x :=
by
  -- Obtain the point 'c' guaranteed by our MVT helper lemma
  obtain ⟨c, hc0, hcx, h_eq⟩ := h_a2_eq_derivative_mul hx_pos
  -- Rewrite the main goal using the algebraic equivalence
  rw [h_eq]
  -- Prove that both factors of the multiplication are non-negative
  exact mul_nonneg (h'_a2_ge_zero hc0 (le_trans hcx hx_le)) (le_of_lt hx_pos)

theorem h_a2_nonneg {x : ℝ} (hx_ge : (0 : ℝ) ≤ x) (hx_le : x ≤ π / (2 : ℝ)) :
  (0 : ℝ) ≤ h_a2 x :=
by
  rcases lt_or_eq_of_le hx_ge with hx_pos | rfl
  · -- Case: 0 < x
    exact h_a2_nonneg_of_pos hx_pos hx_le
  · -- Case: 0 = x (meaning x is exactly 0)
    -- We can solve this explicitly using the lemma without relying on tactic auto-closing behavior
    exact le_of_eq h_a2_zero.symm

theorem putnam_2025_a2_lower_bound_left_helper {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) (π / (2 : ℝ))) :
  putnam_2025_a2_solution.1 * x * (π - x) ≤ sin x :=
by
  -- Extract bounds on x from the set membership hypothesis
  have hx_ge : (0 : ℝ) ≤ x := hx.1
  have hx_le : x ≤ π / (2 : ℝ) := hx.2

  -- Establish the polynomial identity safely without relying on unconditional fraction inversions
  have h_eq : putnam_2025_a2_solution.1 * x * (π - x) = x - x ^ 2 / π := by
    change ((1 : ℝ) / π) * x * (π - x) = x - x ^ 2 / π
    have hpi : π ≠ 0 := Real.pi_ne_zero
    calc
      ((1 : ℝ) / π) * x * (π - x)
        = x * (π / π) - x ^ 2 / π := by ring
      _ = x * 1 - x ^ 2 / π := by rw [div_self hpi]
      _ = x - x ^ 2 / π := by ring

  -- Retrieve bounding from the proven lemmas (h_a2 x >= 0) and evaluate the target inequality
  have h1 : (0 : ℝ) ≤ sin x - x + x ^ 2 / π := h_a2_nonneg hx_ge hx_le

  calc
    putnam_2025_a2_solution.1 * x * (π - x)
      = x - x ^ 2 / π := h_eq
    _ ≤ x - x ^ 2 / π + (sin x - x + x ^ 2 / π) := by linarith [h1]
    _ = sin x := by ring

theorem putnam_2025_a2_lower_bound_right {x : ℝ} (hx : x ∈ Set.Icc (π / (2 : ℝ)) π) :
  putnam_2025_a2_solution.1 * x * (π - x) ≤ sin x :=
by
  -- 1. Map the right-interval domain of x to the left-interval domain of (π - x)
  have h_map := putnam_2025_a2_lower_bound_right_interval_map hx

  -- 2. Apply the bound inequality from the left interval to the reflected value (π - x)
  have h_left := putnam_2025_a2_lower_bound_left_helper h_map

  -- 3. Expose the symmetry in the quadratic form and sine function respectively
  have h_symm := putnam_2025_a2_poly_symm x
  have h_sin : sin (π - x) = sin x := Real.sin_pi_sub x

  -- 4. Rewrite the expression to prove the lower bound inequality on the right interval
  rw [h_symm, h_sin] at h_left
  exact h_left

theorem putnam_2025_a2_lower_bound : ∀ x ∈ Set.Icc 0 π, putnam_2025_a2_solution.1 * x * (π - x) ≤ sin x :=
by
  intro x hx
  -- Split the interval [0, π] at π / 2
  have h_or : x ≤ π / (2 : ℝ) ∨ π / (2 : ℝ) ≤ x := le_total x (π / (2 : ℝ))
  cases h_or with
  | inl h1 =>
    -- Case 1: x is in the left half, [0, π / 2]
    exact putnam_2025_a2_lower_bound_left ⟨hx.1, h1⟩
  | inr h2 =>
    -- Case 2: x is in the right half, [π / 2, π]
    exact putnam_2025_a2_lower_bound_right ⟨h2, hx.2⟩

theorem putnam_2025_a2_greatest (a' : ℝ) (h : ∀ x ∈ Set.Icc 0 π, a' * x * (π - x) ≤ sin x) : a' ≤ putnam_2025_a2_solution.1 :=
by
  have h_bound : ∀ x ∈ Set.Ioo 0 π, a' * x ≤ (1 : ℝ) := by
    intro x hx
    have y_pos : 0 < π - x := sub_pos.mpr hx.2
    have eq1 : sin x = sin (π - x) := by
      rw [Real.sin_sub, Real.sin_pi, Real.cos_pi]
      ring
    have sin_y_le_y : sin (π - x) ≤ π - x := by
      first
      | exact Real.sin_le (le_of_lt y_pos)
      | exact Real.sin_le_id (le_of_lt y_pos)
      | exact sin_le (le_of_lt y_pos)
      | exact sin_le_id (le_of_lt y_pos)
      | have h1 : ContinuousOn sin (Set.Icc 0 (π - x)) := Real.continuous_sin.continuousOn
        have h2 : ∀ y ∈ Set.Ioo 0 (π - x), DifferentiableAt ℝ sin y := fun y _ => Real.differentiable_sin.differentiableAt
        have ⟨c, hc, hc_eq⟩ := exists_deriv_eq_slope y_pos h1 h2
        have hc_eq2 : sin (π - x) = deriv sin c * (π - x) := by
          calc sin (π - x) = sin (π - x) - sin 0 := by rw [Real.sin_zero, sub_zero]
            _ = deriv sin c * (π - x - 0) := hc_eq
            _ = deriv sin c * (π - x) := by rw [sub_zero]
        have hc_deriv : deriv sin c = cos c := by
          first
          | exact congr_fun Real.deriv_sin c
          | exact Real.deriv_sin c
          | exact congr_fun deriv_sin c
          | exact deriv_sin c
          | simp
        have hc_eq3 : sin (π - x) = cos c * (π - x) := by
          rw [hc_eq2, hc_deriv]
        calc sin (π - x) = cos c * (π - x) := hc_eq3
          _ ≤ (1 : ℝ) * (π - x) := mul_le_mul_of_nonneg_right (Real.cos_le_one c) (le_of_lt y_pos)
          _ = π - x := one_mul (π - x)
    have h_sin : sin x ≤ π - x := by
      rw [eq1]
      exact sin_y_le_y
    have h_hyp := h x (by
      constructor
      · exact le_of_lt hx.1
      · exact le_of_lt hx.2
    )
    have h_inv_pos : 0 ≤ (π - x)⁻¹ := inv_nonneg.mpr (le_of_lt y_pos)
    have h_mul : a' * x * (π - x) * (π - x)⁻¹ ≤ (π - x) * (π - x)⁻¹ := by
      refine mul_le_mul_of_nonneg_right ?_ h_inv_pos
      calc a' * x * (π - x) ≤ sin x := h_hyp
        _ ≤ π - x := h_sin
    have h_cancel : (π - x) * (π - x)⁻¹ = (1 : ℝ) := mul_inv_cancel₀ (ne_of_gt y_pos)
    have h_lhs : a' * x * (π - x) * (π - x)⁻¹ = a' * x := by
      calc a' * x * (π - x) * (π - x)⁻¹ = a' * x * ((π - x) * (π - x)⁻¹) := mul_assoc (a' * x) (π - x) ((π - x)⁻¹)
        _ = a' * x * (1 : ℝ) := by rw [h_cancel]
        _ = a' * x := mul_one (a' * x)
    have h_rhs : (π - x) * (π - x)⁻¹ = (1 : ℝ) := h_cancel
    rw [h_lhs, h_rhs] at h_mul
    exact h_mul

  have h_a_pi : a' * π ≤ (1 : ℝ) := by
    by_contra h_contra
    push_neg at h_contra
    have h_a_pos : 0 < a' := by
      by_contra h_a_neg
      push_neg at h_a_neg
      have h_a_pi_le_zero : a' * π ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h_a_neg (le_of_lt Real.pi_pos)
      linarith
    have h_diff_pos : 0 < a' * π - (1 : ℝ) := sub_pos.mpr h_contra
    have h_two_a_pos : 0 < (2 : ℝ) * a' := mul_pos (by linarith) h_a_pos
    set ϵ := (a' * π - (1 : ℝ)) / ((2 : ℝ) * a')
    have eq_eps : ϵ * ((2 : ℝ) * a') = a' * π - (1 : ℝ) := div_mul_cancel₀ _ (ne_of_gt h_two_a_pos)
    have h_ϵ_pos : 0 < ϵ := by
      by_contra h_le
      push_neg at h_le
      have h_mul_le : ϵ * ((2 : ℝ) * a') ≤ 0 * ((2 : ℝ) * a') := mul_le_mul_of_nonneg_right h_le (le_of_lt h_two_a_pos)
      rw [zero_mul, eq_eps] at h_mul_le
      linarith
    have h_ϵ_lt_pi : ϵ < π := by
      by_contra h_ge
      push_neg at h_ge
      have h_mul_ge : π * ((2 : ℝ) * a') ≤ ϵ * ((2 : ℝ) * a') := mul_le_mul_of_nonneg_right h_ge (le_of_lt h_two_a_pos)
      rw [eq_eps] at h_mul_ge
      have h_strict : a' * π - (1 : ℝ) < π * ((2 : ℝ) * a') := by
        have h_pos_prod : 0 < a' * π := mul_pos h_a_pos Real.pi_pos
        calc a' * π - (1 : ℝ) < a' * π * (2 : ℝ) := by linarith
          _ = π * ((2 : ℝ) * a') := by ring
      linarith
    set x := π - ϵ
    have hx_pos : 0 < x := sub_pos.mpr h_ϵ_lt_pi
    have hx_lt_pi : x < π := sub_lt_self π h_ϵ_pos
    have hx_in : x ∈ Set.Ioo 0 π := ⟨hx_pos, hx_lt_pi⟩
    have h_ax_le_1 := h_bound x hx_in
    have eq2 : a' * ϵ * (2 : ℝ) = a' * π - (1 : ℝ) := by
      calc a' * ϵ * (2 : ℝ) = ϵ * ((2 : ℝ) * a') := by ring
        _ = a' * π - (1 : ℝ) := eq_eps
    have eq3 : a' * x * (2 : ℝ) = a' * π + (1 : ℝ) := by
      calc a' * x * (2 : ℝ) = a' * (π - ϵ) * (2 : ℝ) := rfl
        _ = a' * π * (2 : ℝ) - a' * ϵ * (2 : ℝ) := by ring
        _ = a' * π * (2 : ℝ) - (a' * π - (1 : ℝ)) := by rw [eq2]
        _ = a' * π + (1 : ℝ) := by ring
    have h_ax_gt_1 : (1 : ℝ) < a' * x := by
      have : (2 : ℝ) < a' * x * (2 : ℝ) := by
        calc (2 : ℝ) = (1 : ℝ) + (1 : ℝ) := by ring
          _ < a' * π + (1 : ℝ) := by linarith
          _ = a' * x * (2 : ℝ) := eq3.symm
      linarith
    linarith

  have h_pi_pos : 0 < π := Real.pi_pos
  change a' ≤ (1 : ℝ) / π
  by_contra h_gt
  push_neg at h_gt
  have h_gt2 : ((1 : ℝ) / π) * π < a' * π := mul_lt_mul_of_pos_right h_gt h_pi_pos
  rw [div_mul_cancel₀ (1 : ℝ) (ne_of_gt h_pi_pos)] at h_gt2
  linarith

theorem putnam_2025_a2_least (b' : ℝ) (h : ∀ x ∈ Set.Icc 0 π, sin x ≤ b' * x * (π - x)) : putnam_2025_a2_solution.2 ≤ b' :=
by
  have h_pi_div_2 : (π / (2 : ℝ)) ∈ Set.Icc 0 π := by
    constructor
    · positivity
    · linarith [Real.pi_pos]
  have h_spec := h (π / (2 : ℝ)) h_pi_div_2
  have h_sin : sin (π / (2 : ℝ)) = 1 := Real.sin_pi_div_two
  rw [h_sin] at h_spec
  have h_spec2 : (1 : ℝ) ≤ b' * (π ^ 2 / (4 : ℝ)) := by
    calc (1 : ℝ) ≤ b' * (π / (2 : ℝ)) * (π - (π / (2 : ℝ))) := h_spec
         _ = b' * (π ^ 2 / (4 : ℝ)) := by ring
  have h1 : (4 : ℝ) / π ^ 2 * (1 : ℝ) ≤ (4 : ℝ) / π ^ 2 * (b' * (π ^ 2 / (4 : ℝ))) :=
    mul_le_mul_of_nonneg_left h_spec2 (by positivity)
  have h2 : (4 : ℝ) / π ^ 2 * (b' * (π ^ 2 / (4 : ℝ))) = b' := by
    calc (4 : ℝ) / π ^ 2 * (b' * (π ^ 2 / (4 : ℝ))) = b' * (π ^ 2 / π ^ 2) := by ring
         _ = b' * (1 : ℝ) := by
           congr 1
           exact div_self (ne_of_gt (by positivity))
         _ = b' := mul_one b'
  rw [h2, mul_one] at h1
  change (4 : ℝ) / π ^ 2 ≤ b'
  exact h1

theorem putnam_2025_a2 (a b : ℝ) : ((a, b) = putnam_2025_a2_solution) ↔
  (IsGreatest {a' : ℝ | ∀ x ∈ Set.Icc 0 π, a' * x * (π - x) ≤ sin x} a ∧
   IsLeast {b' : ℝ | ∀ x ∈ Set.Icc 0 π, sin x ≤ b' * x * (π - x)} b) :=
by
  constructor
  · intro h
    -- Extract coordinate identities from the solution tuple equality
    have ha : a = putnam_2025_a2_solution.1 := congrArg Prod.fst h
    have hb : b = putnam_2025_a2_solution.2 := congrArg Prod.snd h
    rw [ha, hb]
    -- Construct the IsGreatest and IsLeast bounds properties
    constructor
    · constructor
      · exact putnam_2025_a2_lower_bound
      · intro x hx
        exact putnam_2025_a2_greatest x hx
    · constructor
      · exact putnam_2025_a2_upper_bound
      · intro x hx
        exact putnam_2025_a2_least x hx
  · rintro ⟨⟨ha_mem, ha_upper⟩, ⟨hb_mem, hb_lower⟩⟩
    -- Constrain a through mutual lower/upper bounds (antisymmetry)
    have ha_eq : a = putnam_2025_a2_solution.1 := by
      apply le_antisymm
      · exact putnam_2025_a2_greatest a ha_mem
      · exact ha_upper putnam_2025_a2_lower_bound
    -- Constrain b through mutual lower/upper bounds (antisymmetry)
    have hb_eq : b = putnam_2025_a2_solution.2 := by
      apply le_antisymm
      · exact hb_lower putnam_2025_a2_upper_bound
      · exact putnam_2025_a2_least b hb_mem
    -- Reconstruct equality for the product tuple
    apply Prod.ext
    · exact ha_eq
    · exact hb_eq
