import Mathlib
open Set
open Real
open MeasureTheory
open Interval

theorem I_f_pos (f : ℝ → ℝ) (hf_cont : ContinuousOn f (Icc 0 1)) (hf_mono : StrictMonoOn f (Icc 0 1)) (hf_nonneg : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ f x) :
    0 < ∫ x in (0:ℝ)..1, f x :=
by
  apply intervalIntegral.integral_pos
  · exact zero_lt_one
  · exact hf_cont
  · intro x hx
    apply hf_nonneg
    exact ⟨le_of_lt hx.1, hx.2⟩
  · use (1 : ℝ)
    constructor
    · exact ⟨zero_le_one, le_refl (1 : ℝ)⟩
    · have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_refl (0 : ℝ), zero_le_one⟩
      have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_refl (1 : ℝ)⟩
      have hf0 : 0 ≤ f 0 := hf_nonneg 0 h0
      have hf01 : f 0 < f 1 := hf_mono h0 h1 zero_lt_one
      exact lt_of_le_of_lt hf0 hf01

theorem I_f_sq_pos (f : ℝ → ℝ) (hf_cont : ContinuousOn f (Icc 0 1)) (hf_mono : StrictMonoOn f (Icc 0 1)) (hf_nonneg : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ f x) :
    0 < ∫ x in (0:ℝ)..1, (f x) ^ 2 :=
by
  apply intervalIntegral.integral_pos (by norm_num)
  · exact hf_cont.pow 2
  · intro x _
    positivity
  · use 1
    have h1 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by
      rw [Set.mem_Icc]
      constructor
      · norm_num
      · norm_num
    have h2 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by
      rw [Set.mem_Icc]
      constructor
      · norm_num
      · norm_num
    refine ⟨h2, ?_⟩
    have h3 : (0 : ℝ) < 1 := by norm_num
    have h4 : f 0 < f 1 := hf_mono h1 h2 h3
    have h5 : 0 ≤ f 0 := hf_nonneg 0 h1
    have h6 : 0 < f 1 := lt_of_le_of_lt h5 h4
    positivity

theorem A_nonneg (f : ℝ → ℝ) (hf_cont : ContinuousOn f (Icc 0 1)) (hf_mono : StrictMonoOn f (Icc 0 1)) (hf_nonneg : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ f x) :
    0 ≤ (∫ x in (0:ℝ)..1, x * f x) / (∫ x in (0:ℝ)..1, f x) :=
by
  have h_num : 0 ≤ ∫ x in (0:ℝ)..1, x * f x := by
    apply intervalIntegral.integral_nonneg
    · norm_num
    · intro x hx
      exact mul_nonneg hx.1 (hf_nonneg x hx)
  have h_den : 0 ≤ ∫ x in (0:ℝ)..1, f x := by
    apply intervalIntegral.integral_nonneg
    · norm_num
    · exact hf_nonneg
  exact div_nonneg h_num h_den

theorem A_lt_one (f : ℝ → ℝ) (hf_cont : ContinuousOn f (Icc 0 1)) (hf_mono : StrictMonoOn f (Icc 0 1)) (hf_nonneg : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ f x) :
    (∫ x in (0:ℝ)..1, x * f x) / (∫ x in (0:ℝ)..1, f x) < 1 :=
by
  have h_le : (0:ℝ) ≤ (1:ℝ) := by norm_num
  have h_uIcc : uIcc (0:ℝ) 1 = Icc (0:ℝ) 1 := uIcc_of_le h_le

  have hint1 : IntervalIntegrable f volume (0:ℝ) (1:ℝ) := by
    apply ContinuousOn.intervalIntegrable
    rw [h_uIcc]
    exact hf_cont

  have hint2 : IntervalIntegrable (fun x ↦ x * f x) volume (0:ℝ) (1:ℝ) := by
    apply ContinuousOn.intervalIntegrable
    rw [h_uIcc]
    apply ContinuousOn.mul
    · exact Continuous.continuousOn continuous_id
    · exact hf_cont

  have H_pos : (0:ℝ) < ∫ x in (0:ℝ)..1, f x - x * f x := by
    apply intervalIntegral.integral_pos
    · norm_num
    · apply ContinuousOn.sub
      · exact hf_cont
      · apply ContinuousOn.mul
        · exact Continuous.continuousOn continuous_id
        · exact hf_cont
    · intro x hx
      have h1 : (0:ℝ) ≤ (1:ℝ) - x := by linarith [hx.2]
      have h2 : (0:ℝ) ≤ f x := hf_nonneg x ⟨hx.1.le, hx.2⟩
      have heq : f x - x * f x = ((1:ℝ) - x) * f x := by ring
      rw [heq]
      exact mul_nonneg h1 h2
    · use (1 / 2 : ℝ)
      refine ⟨by norm_num, ?_⟩
      have heq : f (1 / 2 : ℝ) - (1 / 2 : ℝ) * f (1 / 2 : ℝ) = (1 / 2 : ℝ) * f (1 / 2 : ℝ) := by ring
      rw [heq]
      have h1 : (0:ℝ) < (1 / 2 : ℝ) := by norm_num
      have h2 : (0:ℝ) < f (1 / 2 : ℝ) := by
        have hx : (0:ℝ) ∈ Icc (0:ℝ) 1 := by norm_num
        have hy : (1 / 2 : ℝ) ∈ Icc (0:ℝ) 1 := by norm_num
        have hxy : (0:ℝ) < (1 / 2 : ℝ) := by norm_num
        have h_strict : f (0:ℝ) < f (1 / 2 : ℝ) := hf_mono hx hy hxy
        have h0 : (0:ℝ) ≤ f (0:ℝ) := hf_nonneg (0:ℝ) (by norm_num)
        linarith
      exact mul_pos h1 h2

  -- Wrapping the integrals in explicit parentheses fixes the Type mismatch parse issue
  have H_sub : ∫ x in (0:ℝ)..1, f x - x * f x = (∫ x in (0:ℝ)..1, f x) - (∫ x in (0:ℝ)..1, x * f x) := by
    exact intervalIntegral.integral_sub hint1 hint2

  rw [H_sub] at H_pos
  have H_lt : ∫ x in (0:ℝ)..1, x * f x < ∫ x in (0:ℝ)..1, f x := by linarith

  have H_f_pos : (0:ℝ) < ∫ x in (0:ℝ)..1, f x := by
    apply intervalIntegral.integral_pos
    · norm_num
    · exact hf_cont
    · intro x hx
      exact hf_nonneg x ⟨hx.1.le, hx.2⟩
    · use (1 : ℝ)
      refine ⟨by norm_num, ?_⟩
      have hx : (0:ℝ) ∈ Icc (0:ℝ) 1 := by norm_num
      have hy : (1 : ℝ) ∈ Icc (0:ℝ) 1 := by norm_num
      have hxy : (0:ℝ) < (1 : ℝ) := by norm_num
      have h_strict : f (0:ℝ) < f (1 : ℝ) := hf_mono hx hy hxy
      have h0 : (0:ℝ) ≤ f (0:ℝ) := hf_nonneg (0:ℝ) (by norm_num)
      linarith

  have H_lt_mul : ∫ x in (0:ℝ)..1, x * f x < (1 : ℝ) * ∫ x in (0:ℝ)..1, f x := by
    calc
      ∫ x in (0:ℝ)..1, x * f x < ∫ x in (0:ℝ)..1, f x := H_lt
      _ = (1 : ℝ) * ∫ x in (0:ℝ)..1, f x := by ring

  exact (div_lt_iff₀ H_f_pos).mpr H_lt_mul

theorem I_H_pos (f : ℝ → ℝ) (hf_cont : ContinuousOn f (Icc 0 1)) (hf_mono : StrictMonoOn f (Icc 0 1)) (hf_nonneg : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ f x) (A : ℝ) (hA_nonneg : 0 ≤ A) (hA_lt : A < 1) :
    0 < ∫ x in (0:ℝ)..1, (x - A) * f x * (f x - f A) :=
by
  have hab : (0:ℝ) < 1 := by norm_num
  have hg_cont : ContinuousOn (fun x ↦ (x - A) * f x * (f x - f A)) (Icc (0:ℝ) 1) := by
    have h1 : ContinuousOn (fun x : ℝ ↦ x - A) (Icc (0:ℝ) 1) :=
      continuous_id.continuousOn.sub continuous_const.continuousOn
    have h2 : ContinuousOn (fun x : ℝ ↦ f x - f A) (Icc (0:ℝ) 1) :=
      hf_cont.sub continuous_const.continuousOn
    exact (h1.mul hf_cont).mul h2

  have hg_nonneg : ∀ x ∈ Ioc (0:ℝ) 1, 0 ≤ (x - A) * f x * (f x - f A) := by
    intro x hx
    have hx_icc : x ∈ Icc (0:ℝ) 1 := ⟨hx.1.le, hx.2⟩
    have fx_nonneg : 0 ≤ f x := hf_nonneg x hx_icc
    have hA_icc : A ∈ Icc (0:ℝ) 1 := ⟨hA_nonneg, hA_lt.le⟩
    rcases lt_trichotomy x A with h_lt | h_eq | h_gt
    · have h1 : x - A ≤ 0 := by linarith
      have h2 : f x < f A := hf_mono hx_icc hA_icc h_lt
      have h3 : f x - f A ≤ 0 := by linarith
      have step1 : 0 ≤ -(x - A) := by linarith
      have step2 : 0 ≤ -(f x - f A) := by linarith
      have step3 : 0 ≤ -(x - A) * -(f x - f A) := mul_nonneg step1 step2
      have step4 : 0 ≤ (x - A) * (f x - f A) := by
        calc 0 ≤ -(x - A) * -(f x - f A) := step3
             _ = (x - A) * (f x - f A) := by ring
      have step5 : 0 ≤ (x - A) * (f x - f A) * f x := mul_nonneg step4 fx_nonneg
      calc 0 ≤ (x - A) * (f x - f A) * f x := step5
           _ = (x - A) * f x * (f x - f A) := by ring
    · have heq : (x - A) * f x * (f x - f A) = 0 := by
        calc (x - A) * f x * (f x - f A) = (A - A) * f A * (f A - f A) := by rw [h_eq]
             _ = 0 := by ring
      exact heq.symm.le
    · have h1 : 0 ≤ x - A := by linarith
      have h2 : f A < f x := hf_mono hA_icc hx_icc h_gt
      have h3 : 0 ≤ f x - f A := by linarith
      have step4 : 0 ≤ (x - A) * (f x - f A) := mul_nonneg h1 h3
      have step5 : 0 ≤ (x - A) * (f x - f A) * f x := mul_nonneg step4 fx_nonneg
      calc 0 ≤ (x - A) * (f x - f A) * f x := step5
           _ = (x - A) * f x * (f x - f A) := by ring

  have hg_pos : ∃ c ∈ Icc (0:ℝ) 1, 0 < (c - A) * f c * (f c - f A) := by
    use (1:ℝ)
    have h1_icc : (1:ℝ) ∈ Icc (0:ℝ) 1 := ⟨zero_le_one, le_refl (1:ℝ)⟩
    refine ⟨h1_icc, ?_⟩
    have hA_icc : A ∈ Icc (0:ℝ) 1 := ⟨hA_nonneg, hA_lt.le⟩
    have h1 : (0:ℝ) < (1:ℝ) - A := sub_pos.mpr hA_lt
    have h2 : f A < f (1:ℝ) := hf_mono hA_icc h1_icc hA_lt
    have h3 : (0:ℝ) < f (1:ℝ) - f A := sub_pos.mpr h2
    have h4 : (0:ℝ) ≤ f A := hf_nonneg A hA_icc
    have h5 : (0:ℝ) < f (1:ℝ) := lt_of_le_of_lt h4 h2
    have h6 : (0:ℝ) < ((1:ℝ) - A) * f (1:ℝ) := mul_pos h1 h5
    exact mul_pos h6 h3

  apply intervalIntegral.integral_pos hab hg_cont hg_nonneg hg_pos

theorem I_H_eq_diff (f : ℝ → ℝ) (hf_cont : ContinuousOn f (Icc 0 1)) (A : ℝ) (hA : A = (∫ x in (0:ℝ)..1, x * f x) / (∫ x in (0:ℝ)..1, f x))
    (h_pos : 0 < ∫ x in (0:ℝ)..1, f x) :
    (∫ x in (0:ℝ)..1, (x - A) * f x * (f x - f A)) =
    (∫ x in (0:ℝ)..1, x * (f x)^2) - A * (∫ x in (0:ℝ)..1, (f x)^2) :=
by

  -- Relate unordered intervals to standard intervals
  have h_uIcc : uIcc (0:ℝ) 1 = Icc (0:ℝ) 1 := uIcc_of_le zero_le_one

  -- Basic continuity facts
  have cont_id : ContinuousOn (fun x : ℝ ↦ x) (uIcc (0:ℝ) 1) := continuous_id.continuousOn
  have cont_f : ContinuousOn f (uIcc (0:ℝ) 1) := by
    rw [h_uIcc]
    exact hf_cont

  -- Integrability of terms
  have h1a_c : ContinuousOn (fun x ↦ x * (f x)^2) (uIcc (0:ℝ) 1) :=
    ContinuousOn.mul cont_id (ContinuousOn.pow cont_f 2)
  have h1a : IntervalIntegrable (fun x ↦ x * (f x)^2) volume (0:ℝ) 1 := ContinuousOn.intervalIntegrable h1a_c

  have h1b_c : ContinuousOn (fun x ↦ A * (f x)^2) (uIcc (0:ℝ) 1) :=
    ContinuousOn.mul continuous_const.continuousOn (ContinuousOn.pow cont_f 2)
  have h1b : IntervalIntegrable (fun x ↦ A * (f x)^2) volume (0:ℝ) 1 := ContinuousOn.intervalIntegrable h1b_c

  have h1_c : ContinuousOn (fun x ↦ x * (f x)^2 - A * (f x)^2) (uIcc (0:ℝ) 1) :=
    ContinuousOn.sub h1a_c h1b_c
  have h1 : IntervalIntegrable (fun x ↦ x * (f x)^2 - A * (f x)^2) volume (0:ℝ) 1 := ContinuousOn.intervalIntegrable h1_c

  have h2a_c : ContinuousOn (fun x ↦ x * f x) (uIcc (0:ℝ) 1) :=
    ContinuousOn.mul cont_id cont_f
  have h2a : IntervalIntegrable (fun x ↦ x * f x) volume (0:ℝ) 1 := ContinuousOn.intervalIntegrable h2a_c

  have h2b_c : ContinuousOn (fun x ↦ A * f x) (uIcc (0:ℝ) 1) :=
    ContinuousOn.mul continuous_const.continuousOn cont_f
  have h2b : IntervalIntegrable (fun x ↦ A * f x) volume (0:ℝ) 1 := ContinuousOn.intervalIntegrable h2b_c

  have h2_sub_c : ContinuousOn (fun x ↦ x * f x - A * f x) (uIcc (0:ℝ) 1) :=
    ContinuousOn.sub h2a_c h2b_c

  have h2_c : ContinuousOn (fun x ↦ f A * (x * f x - A * f x)) (uIcc (0:ℝ) 1) :=
    ContinuousOn.mul continuous_const.continuousOn h2_sub_c
  have h2 : IntervalIntegrable (fun x ↦ f A * (x * f x - A * f x)) volume (0:ℝ) 1 := ContinuousOn.intervalIntegrable h2_c

  -- Equivalence between standard multiplication and scalar multiplication to use integral_smul
  have H_smul1 : (fun x ↦ A * (f x)^2) = (fun x ↦ A • (f x)^2) := by ext x; rw [smul_eq_mul]
  have H_smul2 : (fun x ↦ f A * (x * f x - A * f x)) = (fun x ↦ f A • (x * f x - A * f x)) := by ext x; rw [smul_eq_mul]
  have H_smul3 : (fun x ↦ A * f x) = (fun x ↦ A • f x) := by ext x; rw [smul_eq_mul]

  -- Useful relation derived from A's definition
  have h_A_mul : A * (∫ x in (0:ℝ)..1, f x) = ∫ x in (0:ℝ)..1, x * f x := by
    calc A * (∫ x in (0:ℝ)..1, f x)
      _ = ((∫ x in (0:ℝ)..1, x * f x) / (∫ x in (0:ℝ)..1, f x)) * (∫ x in (0:ℝ)..1, f x) := by rw [hA]
      _ = ∫ x in (0:ℝ)..1, x * f x := div_mul_cancel₀ _ (ne_of_gt h_pos)

  -- Core step-by-step equivalence chain for integration
  calc
    ∫ x in (0:ℝ)..1, (x - A) * f x * (f x - f A)
    _ = ∫ x in (0:ℝ)..1, ((x * (f x)^2 - A * (f x)^2) - f A * (x * f x - A * f x)) := by
      congr 1; ext x; ring
    _ = (∫ x in (0:ℝ)..1, (x * (f x)^2 - A * (f x)^2)) - (∫ x in (0:ℝ)..1, f A * (x * f x - A * f x)) := by
      rw [intervalIntegral.integral_sub h1 h2]
    _ = (∫ x in (0:ℝ)..1, x * (f x)^2) - (∫ x in (0:ℝ)..1, A * (f x)^2) - (∫ x in (0:ℝ)..1, f A * (x * f x - A * f x)) := by
      rw [intervalIntegral.integral_sub h1a h1b]
    _ = (∫ x in (0:ℝ)..1, x * (f x)^2) - (∫ x in (0:ℝ)..1, A • (f x)^2) - (∫ x in (0:ℝ)..1, f A • (x * f x - A * f x)) := by
      rw [H_smul1, H_smul2]
    _ = (∫ x in (0:ℝ)..1, x * (f x)^2) - A • (∫ x in (0:ℝ)..1, (f x)^2) - f A • (∫ x in (0:ℝ)..1, (x * f x - A * f x)) := by
      rw [intervalIntegral.integral_smul, intervalIntegral.integral_smul]
    _ = (∫ x in (0:ℝ)..1, x * (f x)^2) - A * (∫ x in (0:ℝ)..1, (f x)^2) - f A * (∫ x in (0:ℝ)..1, (x * f x - A * f x)) := by
      rw [smul_eq_mul, smul_eq_mul]
    _ = (∫ x in (0:ℝ)..1, x * (f x)^2) - A * (∫ x in (0:ℝ)..1, (f x)^2) - f A * ((∫ x in (0:ℝ)..1, x * f x) - (∫ x in (0:ℝ)..1, A * f x)) := by
      rw [intervalIntegral.integral_sub h2a h2b]
    _ = (∫ x in (0:ℝ)..1, x * (f x)^2) - A * (∫ x in (0:ℝ)..1, (f x)^2) - f A * ((∫ x in (0:ℝ)..1, x * f x) - (∫ x in (0:ℝ)..1, A • f x)) := by
      rw [H_smul3]
    _ = (∫ x in (0:ℝ)..1, x * (f x)^2) - A * (∫ x in (0:ℝ)..1, (f x)^2) - f A * ((∫ x in (0:ℝ)..1, x * f x) - A • (∫ x in (0:ℝ)..1, f x)) := by
      rw [intervalIntegral.integral_smul]
    _ = (∫ x in (0:ℝ)..1, x * (f x)^2) - A * (∫ x in (0:ℝ)..1, (f x)^2) - f A * ((∫ x in (0:ℝ)..1, x * f x) - A * (∫ x in (0:ℝ)..1, f x)) := by
      rw [smul_eq_mul]
    _ = (∫ x in (0:ℝ)..1, x * (f x)^2) - A * (∫ x in (0:ℝ)..1, (f x)^2) - f A * ((∫ x in (0:ℝ)..1, x * f x) - (∫ x in (0:ℝ)..1, x * f x)) := by
      rw [h_A_mul]
    _ = (∫ x in (0:ℝ)..1, x * (f x)^2) - A * (∫ x in (0:ℝ)..1, (f x)^2) - f A * 0 := by
      rw [sub_self]
    _ = (∫ x in (0:ℝ)..1, x * (f x)^2) - A * (∫ x in (0:ℝ)..1, (f x)^2) := by
      ring

theorem A_lt_I3_div_I2 (A I2 I3 : ℝ) (hI2_pos : 0 < I2) (h_diff : 0 < I3 - A * I2) :
    A < I3 / I2 :=
by
  rw [lt_div_iff₀ hI2_pos]
  linarith

theorem putnam_2025_b2 (f : ℝ → ℝ)
    (hf_cont : ContinuousOn f (Icc 0 1))
    (hf_mono : StrictMonoOn f (Icc 0 1))
    (hf_nonneg : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ f x) : (∫ x in (0:ℝ)..1, x * f x) / (∫ x in (0:ℝ)..1, f x) <
    (∫ x in (0:ℝ)..1, x * (f x) ^ 2) / (∫ x in (0:ℝ)..1, (f x) ^ 2) :=
by
  let A := (∫ x in (0:ℝ)..1, x * f x) / (∫ x in (0:ℝ)..1, f x)
  have h_I0_pos := I_f_pos f hf_cont hf_mono hf_nonneg
  have hA_nonneg := A_nonneg f hf_cont hf_mono hf_nonneg
  have hA_lt_one := A_lt_one f hf_cont hf_mono hf_nonneg
  have h_IH_pos := I_H_pos f hf_cont hf_mono hf_nonneg A hA_nonneg hA_lt_one
  have h_IH_eq := I_H_eq_diff f hf_cont A rfl h_I0_pos
  have h_diff_pos : 0 < (∫ x in (0:ℝ)..1, x * (f x)^2) - A * (∫ x in (0:ℝ)..1, (f x)^2) := by
    rw [← h_IH_eq]
    exact h_IH_pos
  have h_I2_pos := I_f_sq_pos f hf_cont hf_mono hf_nonneg
  exact A_lt_I3_div_I2 A (∫ x in (0:ℝ)..1, (f x)^2) (∫ x in (0:ℝ)..1, x * (f x)^2) h_I2_pos h_diff_pos
