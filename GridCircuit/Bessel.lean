module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

import GridCircuit.Misc
import Mathlib.Analysis.Real.Pi.Bounds

public section

open Real MeasureTheory Asymptotics Filter Set

/-- Integrability related to Bessel function. -/
theorem integrable_bessel (x1 x2 : ℝ) :
    IntegrableOn (fun p ↦ (1 - cos (x1 * p.1 * cos (p.2 - x2))) / p.1)
    (Set.Ioc 0 1 ×ˢ Set.Ioo (-π) π) (volume.prod volume) := by
  apply IntegrableOn.of_bound (by simp) ?_ (x1 ^ 2 / 2) ?_
  · apply AEStronglyMeasurable.restrict
    apply StronglyMeasurable.aestronglyMeasurable
    fun_prop
  · refine ae_restrict_of_forall_mem (by measurability) fun p hp ↦ ?_
    rw [Set.mem_prod] at hp
    rw [norm_eq_abs, abs_div, div_le_iff₀ (by simpa using hp.1.1.ne')]
    rw [abs_of_nonneg (by simpa using cos_le_one _)]
    rw [abs_of_nonneg hp.1.1.le]
    apply (one_sub_cos_le _).trans
    rw [← mul_div_right_comm, div_le_div_iff_of_pos_right (by simp)]
    rw [mul_pow, mul_pow, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    trans p.1 ^ 2
    · apply mul_le_of_le_one_right (sq_nonneg _)
      simpa using abs_cos_le_one _
    exact _root_.sq_le hp.1.1.le hp.1.2

theorem integrable_bessel_slice (x1 x2 : ℝ) :
    IntegrableOn (fun r ↦ ∫ θ in Set.Ioo (-π) π,
      (1 - cos (x1 * r * cos (θ - x2))) / r) (Set.Ioc 0 1) := by
  obtain h := integrable_bessel x1 x2
  rw [IntegrableOn, ← Measure.prod_restrict] at h
  exact h.integral_prod_left

theorem intervalIntegrable_bessel_slice {x : ℝ} (hx : 0 < x) :
    IntervalIntegrable (fun r ↦ ∫ θ in Set.Ioo (-π) π, (1 - cos (r * cos θ)) / r) volume 0 x := by
  suffices IntervalIntegrable
      (fun r ↦ ∫ θ in Set.Ioo (-π) π, x⁻¹ * (1 - cos (x * (x⁻¹ * r) * cos θ)) / (x⁻¹ * r))
      volume (0 / x⁻¹) (1 / x⁻¹) by
   simpa [hx.ne.symm, ← div_div, mul_right_comm _ _ (x)] using this
  apply IntervalIntegrable.comp_mul_left
    (f := fun r ↦ ∫ θ in Set.Ioo (-π) π, x⁻¹ * (1 - cos (x * r * cos θ)) / r)
  simp_rw [mul_div_assoc, integral_const_mul]
  apply IntervalIntegrable.const_mul
  apply IntegrableOn.intervalIntegrable
  rw [Set.uIcc_of_le (by simp), integrableOn_Icc_iff_integrableOn_Ioc]
  simpa using integrable_bessel_slice x 0

theorem intervalIntegrable_bessel_slice' {x : ℝ} (hx : 0 < x) :
    IntervalIntegrable (fun r ↦ ∫ θ in -π..π, (1 - cos (r * cos θ)) / r) volume 0 x := by
  convert intervalIntegrable_bessel_slice hx
  rw [intervalIntegral.integral_of_le (by simpa using pi_nonneg)]
  rw [MeasureTheory.integral_Ioc_eq_integral_Ioo]

theorem besselJ_bound {r : ℝ} (hr : 1 ≤ r) :
    |∫ θ in (-π)..π, cos (r * cos θ)| ≤ (4 + 4 * π) / √r := by
  have hr0 : r ≠ 0 := fun h ↦ by norm_num [h] at hr
  have hrpos : 0 < r := lt_of_lt_of_le (by simp) hr
  have hrb : 1 / √r ≤ π / 2 := by
    grw [← Real.pi_gt_three, ← hr]
    norm_num
  have hrr : √r * r⁻¹ = 1 / √r := by
    rw [one_div]
    apply eq_inv_of_mul_eq_one_left
    rw [mul_right_comm, ← sq, sq_sqrt hrpos.le]
    exact mul_inv_cancel₀ hr0
  suffices |∫ θ in (-π)..π, cos (r * cos θ)| ≤
      2 * (2 * (1 * |1 / √r - 0| + ((π / 2 / √r) + (π / 2) * √r * r⁻¹))) by
    convert this
    rw [sub_zero, abs_of_nonneg (by simp), mul_assoc, hrr]
    ring
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0)
    (Continuous.intervalIntegrable (by fun_prop) _ _)
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  rw [show ∫ θ in -π..0, cos (r * cos θ) = ∫ x in -π..-0, cos (r * cos x) by simp]
  rw [← intervalIntegral.integral_comp_neg]
  simp_rw [cos_neg]
  rw [← two_mul, abs_mul, Nat.abs_ofNat]
  refine mul_le_mul_of_nonneg_left ?_ (by simp)
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := π / 2)
    (Continuous.intervalIntegrable (by fun_prop) _ _)
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  rw [show ∫ θ in π / 2..π, cos (r * cos θ) = ∫ x in (π - π / 2)..(π - 0), cos (r * cos x) by
    congr <;> ring]
  rw [← intervalIntegral.integral_comp_sub_left]
  simp_rw [cos_pi_sub, mul_neg, cos_neg]
  rw [← two_mul, abs_mul, Nat.abs_ofNat]
  refine mul_le_mul_of_nonneg_left ?_ (by simp)
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 1 / √r)
    (Continuous.intervalIntegrable (by fun_prop) _ _)
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  apply (abs_add_le _ _).trans
  apply add_le_add
  · rw [← norm_eq_abs]
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro _ _
    rw [norm_eq_abs]
    apply abs_cos_le_one
  have hsin {θ : ℝ} (hθ : θ ∈ uIcc (1 / √r) (π / 2)) : sin θ ≠ 0 := by
    rw [Set.uIcc_of_le hrb] at hθ
    refine (Real.sin_pos_of_mem_Ioo ?_).ne.symm
    apply Set.mem_of_mem_of_subset hθ
    apply Icc_subset_Ioo
    · simpa using hrpos
    · simpa using pi_pos
  have hcongr : ∫ θ in 1 / √r..(π / 2), cos (r * cos θ)
      = ∫ θ in 1 / √r..(π / 2), (r * -sin θ)⁻¹ * (cos (r * cos θ) * (r * -sin θ)) := by
    apply intervalIntegral.integral_congr
    intro θ hθ
    simp only
    rw [mul_left_comm (_⁻¹), inv_mul_cancel₀ (mul_ne_zero hr0 (by simpa using hsin hθ))]
    rw [mul_one]
  rw [hcongr]
  have hu : ∀ θ ∈ uIcc (1 / √r) (π / 2), HasDerivAt (fun θ ↦ (r * -sin θ)⁻¹)
      (cos θ / (sin θ) ^ 2 * r⁻¹) θ := by
    intro θ hθ
    convert_to HasDerivAt (fun θ ↦ (r * -sin θ)⁻¹) (-(r * (-cos θ)) / (r * -sin θ) ^ 2) θ
    · field
    apply HasDerivAt.inv ?_ (by simp [hr0, hsin hθ])
    apply HasDerivAt.const_mul
    apply HasDerivAt.neg
    apply hasDerivAt_sin
  have hv : ∀ θ ∈ uIcc (1 / √r) (π / 2), HasDerivAt (fun θ ↦ sin (r * cos θ))
      (cos (r * cos θ) * (r * -sin θ)) θ := by
    intro θ hθ
    apply HasDerivAt.sin
    apply HasDerivAt.const_mul
    apply hasDerivAt_cos
  rw [intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv (by
    apply ContinuousOn.intervalIntegrable
    intro θ hθ
    obtain h := hsin hθ
    fun_prop (disch := grind)
  ) (Continuous.intervalIntegrable (by fun_prop) _ _)]
  rw [cos_pi_div_two, mul_zero, sin_zero, mul_zero, zero_sub]
  apply (abs_add_le _ _).trans
  apply add_le_add
  · rw [abs_neg, abs_mul]
    rw [abs_inv, mul_neg, abs_neg]
    have hsin : 0 < sin (1 / √r) := sin_pos_of_mem_Ioo
      (by
        rw [mem_Ioo]
        constructor
        · simpa using hrpos
        · apply lt_of_le_of_lt hrb
          simpa using pi_pos
      )
    rw [inv_mul_le_iff₀ (abs_pos.mpr (mul_ne_zero hr0 (ne_of_gt hsin)))]
    apply (abs_sin_le_one _).trans
    rw [abs_mul, abs_of_nonneg (hrpos.le), abs_of_nonneg hsin.le]
    grw [← Real.mul_le_sin (by simp) (by grw [← Real.pi_gt_three, ← hr]; norm_num)]
    convert_to! 1 ≤ r / (√r) ^ 2
    · field
    rw [sq_sqrt (by simpa using hrpos.le), div_self hr0]
  rw [abs_neg]
  trans ∫ x in 1 / √r..π / 2, cos x / sin x ^ 2 * r⁻¹
  · rw [← norm_eq_abs]
    apply intervalIntegral.norm_integral_le_of_norm_le hrb ?_ (ContinuousOn.intervalIntegrable (by
      intro t ht
      fun_prop (disch := grind)
    ))
    apply Eventually.of_forall
    intro θ hθ
    rw [norm_eq_abs, abs_mul]
    grw [abs_sin_le_one (r * cos θ)]
    rw [mul_one, abs_of_nonneg]
    refine mul_nonneg ?_ (by simpa using hrpos.le)
    refine div_nonneg ?_ (sq_nonneg _)
    apply Real.cos_nonneg_of_mem_Icc
    apply Set.mem_of_mem_of_subset hθ
    apply Ioc_subset_Icc_self.trans
    apply Icc_subset_Icc_left
    trans 0
    · linarith [pi_nonneg]
    · simp
  rw [intervalIntegral.integral_mul_const]
  have hderiv : ∀ θ ∈ Set.uIcc (1 / √r) (π / 2),
      HasDerivAt (fun θ ↦ -(sin θ)⁻¹) (cos θ / sin θ ^ 2) θ := by
    intro θ hθ
    convert_to HasDerivAt (fun θ ↦ -(sin θ)⁻¹) (-(-cos θ / sin θ ^ 2)) θ
    · ring
    apply HasDerivAt.neg
    refine HasDerivAt.inv ?_ (hsin hθ)
    apply hasDerivAt_sin
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (by
    apply ContinuousOn.intervalIntegrable
    intro θ hθ
    obtain h := hsin hθ
    fun_prop (disch := grind)
  )]
  simp only [sin_pi_div_two, inv_one, one_div, sub_neg_eq_add]
  refine mul_le_mul_of_nonneg_right ?_ (by simpa using hrpos.le)
  trans (sin (√r)⁻¹)⁻¹
  · simp
  rw [inv_le_comm₀ (by
    apply sin_pos_of_mem_Ioo
    rw [mem_Ioo]
    constructor
    · simpa using hrpos
    · rw [← one_div]
      apply lt_of_le_of_lt hrb
      simpa using pi_pos
    ) (mul_pos (by simpa using pi_pos) (by simpa using hrpos))]
  rw [mul_inv, inv_div]
  apply mul_le_sin (by simp)
  simpa using hrb

theorem asymptotic_bessel :
    (fun x ↦ ((2 * π)⁻¹ * ∫ r in 0..x, ∫ θ in -π..π, (1 - cos (r * cos θ)) / r) - log x)
    =O[atTop] (1 : ℝ → ℝ) := by
  simp_rw [IsBigO_def, IsBigOWith_def]
  use |(2 * π)⁻¹ * ∫ (x : ℝ) in 0..1, ∫ (θ : ℝ) in -π..π, (1 - cos (x * cos θ)) / x| +
    (|(2 * π)⁻¹| * ∫ (x : ℝ) in Ioi 1, (4 + 4 * π) / x ^ (3 / 2 : ℝ))
  simp_rw [Pi.one_apply, norm_one, mul_one, norm_eq_abs]
  filter_upwards [Filter.eventually_ge_atTop 1] with x hx
  have hintegrableleft :
      IntervalIntegrable (fun r ↦ ∫ θ in -π..π, (1 - cos (r * cos θ)) / r) volume 0 1 :=
    intervalIntegrable_bessel_slice' (by simp)
  have integrableright :
      IntervalIntegrable (fun r ↦ ∫ θ in -π..π, (1 - cos (r * cos θ)) / r) volume 1 x := by
    suffices IntervalIntegrable (fun r ↦ ∫ θ in -π..π, (1 - cos (r * cos θ)) / r)
        volume 0 x by
      apply this.mono_set
      apply Set.uIcc_subset_uIcc
      · rw [uIcc_of_le (le_trans (by simp) hx)]
        simpa using hx
      · simp
    exact intervalIntegrable_bessel_slice' (lt_of_lt_of_le (by simp) hx)
  rw [← intervalIntegral.integral_add_adjacent_intervals hintegrableleft integrableright]
  rw [mul_add, add_sub_assoc]
  apply (abs_add_le _ _).trans
  rw [add_le_add_iff_left]
  conv in fun x ↦ _ =>
    ext x
    simp only [sub_div]
    rw [intervalIntegral.integral_sub (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _)]
    rw [intervalIntegral.integral_const, sub_neg_eq_add, ← two_mul, smul_eq_mul]
  have hintegrable : IntervalIntegrable
      (fun r ↦ ∫ θ in -π..π, cos (r * cos θ) / r) volume 1 x := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hx]
    simp_rw [intervalIntegral.integral_of_le (show -π ≤ π by simpa using pi_nonneg)]
    apply continuousOn_of_dominated (bound := fun _ ↦ 1)
    · intro r hr
      fun_prop
    · intro r hr
      apply Eventually.of_forall
      intro θ
      rw [norm_eq_abs, abs_div]
      rw [div_le_one₀ (abs_pos.mpr fun h ↦ by norm_num [h] at hr)]
      apply (abs_cos_le_one _).trans
      grind
    · fun_prop
    · apply Eventually.of_forall
      intro θ
      fun_prop (disch := grind)
  rw [intervalIntegral.integral_sub (ContinuousOn.intervalIntegrable_of_Icc hx
    (by fun_prop (disch := grind))) hintegrable]
  have hintinv : ∫ (x : ℝ) in 1..x, 1 / x = log x := by
    simp_rw [one_div]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y hy ↦ hasDerivAt_log (fun h ↦ by
        simp only [uIcc_of_le hx, h, mem_Icc] at hy
        norm_num at hy
      ))
      (ContinuousOn.intervalIntegrable_of_Icc hx (by fun_prop (disch := grind)))]
    rw [log_one, sub_zero]
  rw [intervalIntegral.integral_const_mul, hintinv, mul_sub, inv_mul_cancel_left₀ (by simp),
    sub_sub_cancel_left, abs_neg, abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (by simp)
  trans ∫ r in 1..x, (4 + 4 * π) / r ^ (3 / 2 : ℝ)
  · rw [← norm_eq_abs]
    apply intervalIntegral.norm_integral_le_of_norm_le hx
    · apply Eventually.of_forall
      intro r hr
      rw [norm_eq_abs, intervalIntegral.integral_div, abs_div]
      grw [besselJ_bound hr.1.le]
      apply le_of_eq
      rw [abs_of_nonneg (le_trans (by simp) hr.1.le), div_div]
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add_one (ne_of_gt (lt_trans (by simp) (hr.1)))]
      norm_num
    · apply ContinuousOn.intervalIntegrable_of_Icc hx
      apply ContinuousOn.div (by fun_prop) ?_ (fun r hr ↦ (rpow_pos_of_pos (by grind) _).ne.symm)
      apply ContinuousOn.rpow_const (by fun_prop) (by grind)
  rw [intervalIntegral.integral_of_le hx]
  refine setIntegral_mono_set ?_ ?_ (Eventually.of_forall (by simpa using! Set.Ioc_subset_Ioi_self))
  · simp_rw [div_eq_mul_inv (4 + 4 * π)]
    apply Integrable.const_mul
    suffices IntegrableOn (fun (x : ℝ) ↦ (x ^ (-(3 / 2) : ℝ))) (Set.Ioi 1) by
      refine this.congr_fun (fun x hx ↦ ?_) measurableSet_Ioi
      simp only
      rw [rpow_neg (le_trans (by simp) hx.le)]
    apply integrableOn_Ioi_rpow_of_lt (by norm_num) (by simp)
  · apply ae_restrict_of_forall_mem (measurableSet_Ioi)
    intro r hr
    simp only [Pi.zero_apply]
    apply div_nonneg (add_nonneg (by simp) (by simpa using pi_nonneg))
    apply rpow_nonneg
    exact le_trans (by simp) hr.le
