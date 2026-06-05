import Mathlib
open Real MeasureTheory Asymptotics Filter intervalIntegral
open scoped Real

-- Aristotle for the whole file

noncomputable def innerIntegrand (r θ : ℝ) : ℝ := (1 - cos (r * cos θ)) / r
noncomputable def innerIntegral (r : ℝ) : ℝ := ∫ θ in -π..π, innerIntegrand r θ
/-
Pointwise bound 1: for r > 0, innerIntegrand r θ ≤ r / 2
-/
lemma innerIntegrand_le_half_r {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    innerIntegrand r θ ≤ r / 2 := by
      unfold innerIntegrand;
      rw [ div_le_iff₀ hr ];
      -- By Real.one_sub_sq_div_two_le_cos, we have 1 - cos t ≤ t^2/2.
      have h_cos_bound : ∀ t : ℝ, 1 - Real.cos t ≤ t^2 / 2 := by
        intro t;
        -- Use the trigonometric identity $1 - \cos t = 2 \sin^2 (t/2)$ and the fact that $\sin^2 (t/2) \leq (t/2)^2$.
        have h_sin_sq : Real.sin (t / 2) ^ 2 ≤ (t / 2) ^ 2 := by
          exact sin_sq_le_sq;
        rw [ Real.sin_sq, Real.cos_sq ] at h_sin_sq ; ring_nf at * ; nlinarith;
      exact le_trans ( h_cos_bound _ ) ( by nlinarith [ Real.cos_sq' θ ] )
/-
Pointwise bound 2: for r > 0, innerIntegrand r θ ≤ 2 / r
-/
lemma innerIntegrand_le_two_div_r {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    innerIntegrand r θ ≤ 2 / r := by
      exact div_le_div_of_nonneg_right ( by linarith [ Real.neg_one_le_cos ( r * Real.cos θ ), Real.cos_le_one ( r * Real.cos θ ) ] ) hr.le
/-
Non-negativity of innerIntegrand
-/
lemma innerIntegrand_nonneg {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    0 ≤ innerIntegrand r θ := by
      exact div_nonneg ( sub_nonneg.2 ( Real.cos_le_one _ ) ) hr.le
/-
Inner integral bound for r > 0: ≤ π * r
-/
lemma innerIntegral_le_pi_mul_r {r : ℝ} (hr : 0 < r) :
    innerIntegral r ≤ π * r := by
      refine' le_trans ( intervalIntegral.integral_mono_on _ _ _ _ ) _;
      refine' fun x => r / 2;
      · linarith [ Real.pi_pos ];
      · exact Continuous.intervalIntegrable ( by exact Continuous.div_const ( by continuity ) _ ) _ _;
      · norm_num;
      · exact fun x _ => innerIntegrand_le_half_r hr x;
      · norm_num ; linarith [ Real.pi_pos ]
/-
Inner integral bound for r > 0: ≤ 4π / r
-/
lemma innerIntegral_le_four_pi_div_r {r : ℝ} (hr : 0 < r) :
    innerIntegral r ≤ 4 * π / r := by
      convert intervalIntegral.integral_mono_on _ _ _ fun x hx => innerIntegrand_le_two_div_r hr x;
      · norm_num ; ring;
      · linarith [ Real.pi_pos ];
      · exact Continuous.intervalIntegrable ( by exact Continuous.div_const ( by continuity ) _ ) _ _;
      · norm_num
/-
Inner integral non-negativity
-/
lemma innerIntegral_nonneg {r : ℝ} (hr : 0 < r) :
    0 ≤ innerIntegral r := by
      refine' intervalIntegral.integral_nonneg _ _;
      · linarith [ Real.pi_pos ];
      · exact fun u hu => innerIntegrand_nonneg hr u
/-
The inner integral is bounded by π on [0, 1]
-/
lemma innerIntegral_le_pi_on_01 {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    innerIntegral r ≤ π := by
      exact le_trans ( innerIntegral_le_pi_mul_r hr ) ( mul_le_of_le_one_right Real.pi_pos.le hr1 )
/-
IntervalIntegrable for the inner integral on [0, 1]
-/
lemma innerIntegral_intervalIntegrable_01 :
    IntervalIntegrable innerIntegral volume 0 1 := by
      rw [ intervalIntegrable_iff_integrableOn_Ioc_of_le ] <;> norm_num [ innerIntegral ];
      refine' MeasureTheory.Integrable.mono' _ _ _;
      refine' fun r => Real.pi;
      · norm_num;
      · refine' MeasureTheory.AEStronglyMeasurable.congr _ _;
        exact fun r => ∫ θ in -Real.pi..Real.pi, ( 1 - Real.cos ( r * Real.cos θ ) ) / r;
        · refine' ContinuousOn.aestronglyMeasurable _ measurableSet_Ioc;
          refine' ContinuousOn.congr _ fun r hr => _;
          exact fun r => ( ∫ θ in -Real.pi..Real.pi, ( 1 - Real.cos ( r * Real.cos θ ) ) ) / r;
          · refine' ContinuousOn.div _ continuousOn_id fun r hr => ne_of_gt hr.1;
            refine' Continuous.continuousOn _;
            fun_prop (disch := norm_num);
          · rw [ intervalIntegral.integral_div ];
        · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioc ] with r hr using rfl;
      · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioc ] with r hr using by rw [ Real.norm_of_nonneg ( innerIntegral_nonneg hr.1 ) ] ; exact innerIntegral_le_pi_on_01 hr.1 hr.2;
/-
IntervalIntegrable for (4π/r) on [1, x] for x ≥ 1
-/
lemma four_pi_div_r_intervalIntegrable {x : ℝ} (hx : 1 ≤ x) :
    IntervalIntegrable (fun r => 4 * π / r) volume 1 x := by
      exact ContinuousOn.intervalIntegrable ( by intro y hy; exact ContinuousAt.continuousWithinAt <| by exact ContinuousAt.div continuousAt_const continuousAt_id <| by linarith [ Set.mem_Icc.mp <| by simpa [ hx ] using hy ] ) ..
/-
IntervalIntegrable for innerIntegral on [1, x]
-/
lemma innerIntegral_intervalIntegrable_1x {x : ℝ} (hx : 1 ≤ x) :
    IntervalIntegrable innerIntegral volume 1 x := by
      apply_rules [ ContinuousOn.intervalIntegrable ];
      refine' ContinuousOn.congr _ _;
      exact fun r => ∫ θ in -Real.pi..Real.pi, ( 1 - Real.cos ( r * Real.cos θ ) ) / r;
      · refine' ContinuousOn.congr _ fun r hr => _;
        exact fun r => ( ∫ θ in -Real.pi..Real.pi, ( 1 - Real.cos ( r * Real.cos θ ) ) ) / r;
        · refine' ContinuousOn.div _ continuousOn_id fun r hr => _;
          · refine' Continuous.continuousOn _;
            fun_prop;
          · cases Set.mem_uIcc.mp hr <;> linarith;
        · rw [ intervalIntegral.integral_div ];
      · exact fun r hr => rfl
/-
IntervalIntegrable for innerIntegral on [0, x] for x ≥ 1
-/
lemma innerIntegral_intervalIntegrable_0x {x : ℝ} (hx : 1 ≤ x) :
    IntervalIntegrable innerIntegral volume 0 x := by
      apply IntervalIntegrable.trans;
      exacts [ innerIntegral_intervalIntegrable_01, innerIntegral_intervalIntegrable_1x hx ]
/-
Integral of 4π/r from 1 to x equals 4π log x
-/
lemma integral_four_pi_div_r {x : ℝ} (hx : 1 < x) :
    ∫ r in (1:ℝ)..x, 4 * π / r = 4 * π * log x := by
      norm_num [ div_eq_mul_inv, hx.le ]
/-
Bound on integral from 0 to 1
-/
lemma integral_innerIntegral_01_le :
    ∫ r in (0:ℝ)..(1:ℝ), innerIntegral r ≤ π := by
      rw [ intervalIntegral.integral_of_le zero_le_one ];
      refine' le_trans ( MeasureTheory.setIntegral_mono_on _ _ measurableSet_Ioc fun x hx => innerIntegral_le_pi_on_01 hx.1 hx.2 ) _;
      · exact innerIntegral_intervalIntegrable_01.1;
      · norm_num;
      · norm_num
/-
Bound on integral from 1 to x
-/
lemma integral_innerIntegral_1x_le {x : ℝ} (hx : 1 ≤ x) :
    ∫ r in (1:ℝ)..x, innerIntegral r ≤ 4 * π * log x := by
      have h_innerIntegral_le_four_pi_div_r : ∀ r ∈ Set.Icc (1 : ℝ) x, innerIntegral r ≤ 4 * Real.pi / r := by
        exact fun r hr => innerIntegral_le_four_pi_div_r <| zero_lt_one.trans_le hr.1;
      rw [ intervalIntegral.integral_of_le hx ];
      refine' le_trans ( MeasureTheory.setIntegral_mono_on _ _ measurableSet_Ioc fun r hr => h_innerIntegral_le_four_pi_div_r r <| Set.Ioc_subset_Icc_self hr ) _;
      · exact ( innerIntegral_intervalIntegrable_1x hx ) |> fun h => h.1.mono_set <| Set.Ioc_subset_Ioc le_rfl le_rfl;
      · exact ContinuousOn.integrableOn_Icc ( by exact continuousOn_of_forall_continuousAt fun r hr => ContinuousAt.div continuousAt_const continuousAt_id <| by linarith [ hr.1 ] ) |> fun h => h.mono_set <| Set.Ioc_subset_Icc_self;
      · rw [ ← intervalIntegral.integral_of_le ] <;> norm_num [ div_eq_mul_inv, hx ]
/-
Total bound for x ≥ 1
-/
lemma total_bound {x : ℝ} (hx : 1 ≤ x) :
    ∫ r in (0:ℝ)..x, innerIntegral r ≤ π + 4 * π * log x := by
      convert add_le_add ( integral_innerIntegral_01_le ) ( integral_innerIntegral_1x_le ( by linarith : ( 1:ℝ ) ≤ x ) ) using 1;
      rw [ intervalIntegral.integral_add_adjacent_intervals ] <;> apply_rules [ innerIntegral_intervalIntegrable_01, innerIntegral_intervalIntegrable_1x ]
/-
The original integrand equals innerIntegral
-/
lemma original_eq_innerIntegral (x : ℝ) :
    (∫ (r : ℝ) in 0..x, ∫ (θ : ℝ) in -π..π, (1 - cos (r * cos θ)) / r) =
    ∫ r in (0:ℝ)..x, innerIntegral r := by
      congr! 2
/-
Non-negativity of total integral for x ≥ 0
-/
lemma total_nonneg {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ ∫ r in (0:ℝ)..x, innerIntegral r := by
      -- Since the integrand innerIntegral r is non-negative for r > 0, the integral over [0, x] is also non-negative.
      have h_integral_nonneg : ∀ r ∈ Set.Icc 0 x, 0 ≤ innerIntegral r := by
        intro r hr; cases eq_or_lt_of_le hr.left <;> simp_all +decide [ innerIntegral ] ;
        · subst_vars; norm_num [ innerIntegrand ] ;
        · exact intervalIntegral.integral_nonneg ( by linarith [ Real.pi_pos ] ) fun θ _ => div_nonneg ( sub_nonneg.2 ( Real.cos_le_one _ ) ) ( by linarith );
      apply_rules [ intervalIntegral.integral_nonneg ]
theorem asymptotic_bessel :
    (fun x ↦ ∫ (r : ℝ) in 0..x, ∫ (θ : ℝ) in -π..π, (1 - cos (r * cos θ)) / r) =O[atTop] log := by
  -- By the properties of the integral, we can bound the integral by the sum of the bounds of the integrals over subintervals.
  have h_integral_bound : ∀ x : ℝ, 1 ≤ x → |∫ r in (0:ℝ)..x, innerIntegral r| ≤ Real.pi + 4 * Real.pi * Real.log x := by
    exact fun x hx => by rw [ abs_of_nonneg ( total_nonneg ( by linarith ) ) ] ; exact total_bound hx;
  refine' Asymptotics.IsBigO.of_bound ( Real.pi + 4 * Real.pi ) _;

  filter_upwards [ Filter.eventually_ge_atTop 1, Filter.eventually_gt_atTop ( Real.exp 1 ) ]
    with x hx₁ hx₂ using le_trans (( by
      simpa [innerIntegral, innerIntegrand] using h_integral_bound x hx₁
    ) : ‖∫ (r : ℝ) in 0..x, ∫ (θ : ℝ) in -π..π, (1 - cos (r * cos θ)) / r‖ ≤ π + 4 * π * log x) (
    by
      rw [ Real.norm_of_nonneg ( Real.log_nonneg hx₁ ) ] ;
      nlinarith [ Real.pi_pos, Real.log_exp 1 ▸ Real.log_le_log ( by positivity ) hx₂.le ]
     )
