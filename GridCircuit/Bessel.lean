import Mathlib

-- Whole file from Aristotle

open Real MeasureTheory Asymptotics Filter intervalIntegral Set

noncomputable section

open scoped Real


/-- The Bessel function J₀ defined via integral representation -/
def besselJ₀ (x : ℝ) : ℝ := (2 * π)⁻¹ * ∫ θ in (-π)..π, cos (x * cos θ)

/-
J₀ is bounded by 1 in absolute value.
    Proof: |J₀(x)| = |(2π)⁻¹ ∫ cos(x cos θ) dθ| ≤ (2π)⁻¹ ∫ |cos(x cos θ)| dθ ≤ (2π)⁻¹ · 2π = 1
-/
lemma abs_besselJ₀_le_one (x : ℝ) : |besselJ₀ x| ≤ 1 := by
  refine' abs_le.mpr ⟨ _, _ ⟩;
  · refine' le_trans _ ( mul_le_mul_of_nonneg_left ( intervalIntegral.integral_mono_on _ _ _ fun θ _ => neg_one_le_cos _ ) ( by positivity ) ) <;> norm_num;
    · nlinarith [ Real.pi_pos, mul_inv_cancel₀ Real.pi_ne_zero ];
    · positivity;
    · exact Continuous.intervalIntegrable ( Real.continuous_cos.comp <| by continuity ) _ _;
  · refine' le_trans ( mul_le_mul_of_nonneg_left ( intervalIntegral.integral_mono_on _ _ _ _ ) ( by positivity ) ) _ <;> norm_num;
    exacts [ fun _ => 1, Real.pi_pos.le, Continuous.intervalIntegrable ( Real.continuous_cos.comp <| by continuity ) _ _, Continuous.intervalIntegrable continuous_const _ _, fun _ _ _ => Real.cos_le_one _, by norm_num; nlinarith [ Real.pi_gt_three, mul_inv_cancel₀ Real.pi_ne_zero ] ]

/-
Symmetry: ∫_{-π}^{π} cos(r cos θ) dθ = 2 ∫_{0}^{π} cos(r cos θ) dθ
-/
lemma bessel_symmetry (r : ℝ) :
    ∫ θ in (-π)..π, cos (r * cos θ) = 2 * ∫ θ in (0:ℝ)..π, cos (r * cos θ) := by
      -- Using the fact that the integral of an even function over a symmetric interval around zero is twice the integral over the positive half of that interval.
      have h_int_symm : ∫ θ in (-Real.pi)..0, Real.cos (r * Real.cos θ) = ∫ θ in (0)..Real.pi, Real.cos (r * Real.cos θ) := by
        convert intervalIntegral.integral_comp_neg _ using 2 <;> norm_num;
      rw [ ← h_int_symm, two_mul, ← intervalIntegral.integral_add_adjacent_intervals ];
      exacts [ by rw [ h_int_symm ], Continuous.intervalIntegrable ( Real.continuous_cos.comp <| by continuity ) _ _, Continuous.intervalIntegrable ( Real.continuous_cos.comp <| by continuity ) _ _ ]

/-
Integration by parts: for 0 < a < b < π with sin θ > 0 on [a,b],
    ∫_a^b cos(r cos θ) dθ = -sin(r cos θ)/(r sin θ)|_a^b - ∫_a^b sin(r cos θ) cos θ/(r sin²θ) dθ
-/
lemma ibp_cos_integral (r a b : ℝ) (hr : 0 < r) (ha : 0 < a) (hab : a < b) (hb : b < π) :
    ∫ θ in a..b, cos (r * cos θ) =
    -sin (r * cos b) / (r * sin b) + sin (r * cos a) / (r * sin a) -
    ∫ θ in a..b, sin (r * cos θ) * cos θ / (r * sin θ ^ 2) := by
      rw [ eq_sub_iff_add_eq, ← intervalIntegral.integral_add ];
      · rw [ intervalIntegral.integral_eq_sub_of_hasDerivAt ];
        rotate_right;
        use fun x => -Real.sin ( r * Real.cos x ) / ( r * Real.sin x );
        · ring;
        · intro x hx; convert! HasDerivAt.div ( HasDerivAt.neg ( HasDerivAt.sin ( HasDerivAt.const_mul r ( Real.hasDerivAt_cos x ) ) ) ) ( HasDerivAt.const_mul r ( Real.hasDerivAt_sin x ) ) ( mul_ne_zero hr.ne' ( ne_of_gt ( Real.sin_pos_of_pos_of_lt_pi ( by cases Set.mem_uIcc.mp hx <;> linarith ) ( by cases Set.mem_uIcc.mp hx <;> linarith ) ) ) ) using 1 ; ring;
          by_cases h : Real.sin x = 0 <;> simp_all +decide [ sq, mul_assoc, mul_comm r, hr.ne' ] ; ring;
          · exact absurd h ( ne_of_gt ( Real.sin_pos_of_pos_of_lt_pi ( by cases Set.mem_uIcc.mp hx <;> linarith ) ( by cases Set.mem_uIcc.mp hx <;> linarith ) ) );
          · exact Or.inl <| by ring;
        · apply_rules [ ContinuousOn.intervalIntegrable ];
          exact continuousOn_of_forall_continuousAt fun x hx => ContinuousAt.add ( Real.continuous_cos.continuousAt.comp <| ContinuousAt.mul continuousAt_const <| Real.continuous_cos.continuousAt ) <| ContinuousAt.div ( ContinuousAt.mul ( Real.continuous_sin.continuousAt.comp <| ContinuousAt.mul continuousAt_const <| Real.continuous_cos.continuousAt ) <| Real.continuous_cos.continuousAt ) ( ContinuousAt.mul continuousAt_const <| Real.continuous_sin.continuousAt.pow 2 ) <| ne_of_gt <| mul_pos hr <| sq_pos_of_pos <| Real.sin_pos_of_pos_of_lt_pi ( by cases Set.mem_uIcc.mp hx <;> linarith ) ( by cases Set.mem_uIcc.mp hx <;> linarith );
      · exact Continuous.intervalIntegrable ( Real.continuous_cos.comp <| by continuity ) _ _;
      · apply_rules [ ContinuousOn.intervalIntegrable ];
        exact ContinuousOn.div ( Continuous.continuousOn ( by continuity ) ) ( Continuous.continuousOn ( by continuity ) ) fun x hx => mul_ne_zero hr.ne' ( pow_ne_zero 2 ( ne_of_gt ( Real.sin_pos_of_pos_of_lt_pi ( by cases Set.mem_uIcc.mp hx <;> linarith ) ( by cases Set.mem_uIcc.mp hx <;> linarith ) ) ) )

/-
The integral ∫_δ^{π/2} cos θ / sin²θ dθ = 1/sin δ - 1
-/
lemma integral_cos_div_sin_sq (δ : ℝ) (hδ : 0 < δ) (hδ' : δ < π / 2) :
    ∫ θ in δ..(π / 2), cos θ / sin θ ^ 2 = 1 / sin δ - 1 := by
      rw [ intervalIntegral.integral_eq_sub_of_hasDerivAt ];
      rotate_right;
      use fun x => -1 / Real.sin x;
      · norm_num ; ring;
      · intro x hx;
        convert! HasDerivAt.div ( hasDerivAt_const _ _ ) ( Real.hasDerivAt_sin x )
         ( ne_of_gt ( Real.sin_pos_of_mem_Ioo ⟨ by cases Set.mem_uIcc.mp hx <;> linarith,
         by cases Set.mem_uIcc.mp hx <;> linarith ⟩ ) ) using 1 ;
        ring;
      · apply_rules [ ContinuousOn.intervalIntegrable ];
        exact continuousOn_of_forall_continuousAt fun x hx => ContinuousAt.div ( Real.continuous_cos.continuousAt ) ( Real.continuous_sin.continuousAt.pow 2 ) ( ne_of_gt ( sq_pos_of_pos ( Real.sin_pos_of_pos_of_lt_pi ( by cases Set.mem_uIcc.mp hx <;> linarith ) ( by cases Set.mem_uIcc.mp hx <;> linarith ) ) ) )

/-
IBP bound on [δ, π-δ]: |∫_δ^{π-δ} cos(r cos θ) dθ| ≤ 4/(r sin δ)
-/
lemma ibp_integral_bound (r δ : ℝ) (hr : 0 < r) (hδ : 0 < δ) (hδ' : δ < π / 2) :
    |∫ θ in δ..(π - δ), cos (r * cos θ)| ≤ 4 / (r * sin δ) := by
      -- Apply the integration by parts result to the integral.
      have h_int_parts : ∫ θ in δ..Real.pi - δ, cos (r * Real.cos θ) =
        -Real.sin (r * Real.cos (Real.pi - δ)) / (r * Real.sin (Real.pi - δ)) +
        Real.sin (r * Real.cos δ) / (r * Real.sin δ) -
        ∫ θ in δ..Real.pi - δ, Real.sin (r * Real.cos θ) * Real.cos θ / (r * Real.sin θ ^ 2) := by
          convert ibp_cos_integral r δ ( Real.pi - δ ) hr hδ ( by linarith ) ( by linarith ) using 1;
      -- Split the integral at $\pi/2$.
      have h_split : ∫ θ in δ..Real.pi - δ, |Real.sin (r * Real.cos θ) * Real.cos θ / (r * Real.sin θ ^ 2)| ≤
        (1 / r) * (∫ θ in δ..(Real.pi / 2), |Real.cos θ| / (Real.sin θ ^ 2)) +
        (1 / r) * (∫ θ in (Real.pi / 2)..Real.pi - δ, |Real.cos θ| / (Real.sin θ ^ 2)) := by
          have h_split : ∫ θ in δ..Real.pi - δ, |Real.sin (r * Real.cos θ) * Real.cos θ / (r * Real.sin θ ^ 2)| ≤
            ∫ θ in δ..Real.pi - δ, |Real.cos θ| / (r * Real.sin θ ^ 2) := by
              refine' intervalIntegral.integral_mono_on _ _ _ _ <;> norm_num [ abs_div, abs_mul ];
              · linarith;
              · apply_rules [ ContinuousOn.intervalIntegrable ];
                exact ContinuousOn.div ( ContinuousOn.mul ( ContinuousOn.abs ( Real.continuous_sin.comp_continuousOn ( continuousOn_const.mul ( Real.continuousOn_cos ) ) ) ) ( ContinuousOn.abs ( Real.continuousOn_cos ) ) ) ( ContinuousOn.mul continuousOn_const ( Real.continuousOn_sin.pow 2 ) ) fun x hx => mul_ne_zero ( ne_of_gt ( abs_pos.mpr hr.ne' ) ) ( pow_ne_zero 2 ( ne_of_gt ( Real.sin_pos_of_pos_of_lt_pi ( by cases Set.mem_uIcc.mp hx <;> linarith ) ( by cases Set.mem_uIcc.mp hx <;> linarith ) ) ) );
              · apply_rules [ ContinuousOn.intervalIntegrable ];
                exact continuousOn_of_forall_continuousAt fun x hx => ContinuousAt.div ( Real.continuous_cos.continuousAt.abs ) ( ContinuousAt.mul continuousAt_const ( Real.continuous_sin.continuousAt.pow 2 ) ) ( mul_ne_zero hr.ne' ( pow_ne_zero 2 ( ne_of_gt ( Real.sin_pos_of_pos_of_lt_pi ( by cases Set.mem_uIcc.mp hx <;> linarith ) ( by cases Set.mem_uIcc.mp hx <;> linarith ) ) ) ) );
              · intro x hx₁ hx₂; rw [ abs_of_pos hr ] ; exact mul_le_mul_of_nonneg_right ( mul_le_of_le_one_left ( abs_nonneg _ ) ( Real.abs_sin_le_one _ ) ) ( by positivity ) ;
          convert h_split using 1 ; norm_num [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, ← intervalIntegral.integral_const_mul ];
          rw [ intervalIntegral.integral_add_adjacent_intervals ] <;> apply_rules [ ContinuousOn.intervalIntegrable ]; all_goals exact ContinuousOn.mul continuousOn_const <| ContinuousOn.mul ( Real.continuousOn_cos.abs ) <| ContinuousOn.inv₀ ( Real.continuousOn_sin.pow 2 ) fun x hx => ne_of_gt <| sq_pos_of_pos <| Real.sin_pos_of_pos_of_lt_pi ( by cases Set.mem_uIcc.mp hx <;> linarith ) ( by cases Set.mem_uIcc.mp hx <;> linarith );
      -- Evaluate the integrals of $|\cos \theta| / \sin^2 \theta$ over $[\delta, \pi/2]$ and $[\pi/2, \pi - \delta]$.
      have h_eval : (∫ θ in δ..(Real.pi / 2), |Real.cos θ| / (Real.sin θ ^ 2)) + (∫ θ in (Real.pi / 2)..Real.pi - δ, |Real.cos θ| / (Real.sin θ ^ 2)) = 2 * (1 / Real.sin δ - 1) := by
        have h_eval : (∫ θ in δ..(Real.pi / 2), |Real.cos θ| / (Real.sin θ ^ 2)) = 1 / Real.sin δ - 1 := by
          convert integral_cos_div_sin_sq δ hδ hδ' using 1;
          refine' intervalIntegral.integral_congr fun x hx => by rw [ abs_of_nonneg ( Real.cos_nonneg_of_mem_Icc ⟨ by linarith [ Set.mem_Icc.mp ( by simpa [ le_of_lt hδ, le_of_lt hδ' ] using hx ) ], by linarith [ Set.mem_Icc.mp ( by simpa [ le_of_lt hδ, le_of_lt hδ' ] using hx ) ] ⟩ ) ] ;
        have h_eval2 : (∫ θ in (Real.pi / 2)..Real.pi - δ, |Real.cos θ| / (Real.sin θ ^ 2)) = 1 / Real.sin δ - 1 := by
          rw [ ← h_eval ];
          convert intervalIntegral.integral_comp_sub_left _ π using 2 <;> norm_num ; ring
        rw [h_eval, h_eval2]
        ring;
      -- Combine the bounds from the integration by parts and the split integral.
      have h_combined : |∫ θ in δ..Real.pi - δ, cos (r * Real.cos θ)| ≤ |Real.sin (r * Real.cos δ) / (r * Real.sin δ) + Real.sin (r * Real.cos δ) / (r * Real.sin δ)| + (1 / r) * (2 * (1 / Real.sin δ - 1)) := by
        rw [ ← h_eval ];
        rw [ h_int_parts ];
        refine' le_trans ( abs_sub _ _ ) ( add_le_add _ _ );
        · norm_num [ neg_div, add_comm ];
        · refine' le_trans ( intervalIntegral.abs_integral_le_integral_abs _ ) _;
          · linarith;
          · simpa only [ mul_add ] using h_split;
      refine le_trans h_combined ?_ ; ring_nf ; norm_num [ hr.ne', hδ.ne' ];
      rw [ abs_of_pos hr, abs_of_pos ( Real.sin_pos_of_pos_of_lt_pi hδ ( by linarith ) ) ] ; nlinarith [ inv_pos.mpr hr, inv_pos.mpr ( Real.sin_pos_of_pos_of_lt_pi hδ ( by linarith ) ), mul_inv_cancel₀ hr.ne', mul_inv_cancel₀ ( ne_of_gt ( Real.sin_pos_of_pos_of_lt_pi hδ ( by linarith ) ) ), abs_nonneg ( sin ( r * cos δ ) ), Real.abs_sin_le_one ( r * cos δ ), mul_le_mul_of_nonneg_left ( Real.abs_sin_le_one ( r * cos δ ) ) ( inv_nonneg.mpr hr.le ), mul_le_mul_of_nonneg_left ( Real.abs_sin_le_one ( r * cos δ ) ) ( inv_nonneg.mpr ( Real.sin_nonneg_of_nonneg_of_le_pi hδ.le ( by linarith ) ) ) ] ;

/-
J₀ decays like 1/√r for large r
-/
lemma abs_besselJ₀_le_sqrt (r : ℝ) (hr : 2 ≤ r) : |besselJ₀ r| ≤ 3 / √r := by
  -- Set δ = 1/√r. For r ≥ 2, we have δ = 1/√r ≤ 1/√2 < π/2.
  set δ := 1 / Real.sqrt r with hδ_def
  have hδ_pos : 0 < δ := by
    positivity
  have hδ_lt_pi_div_2 : δ < Real.pi / 2 := by
    exact lt_of_le_of_lt ( div_le_self zero_le_one <| Real.le_sqrt_of_sq_le <| by linarith ) <| by linarith [ Real.pi_gt_three ] ;
  -- Split ∫_0^π = ∫_0^δ + ∫_δ^{π-δ} + ∫_{π-δ}^π  (using integral_add_adjacent_intervals)
  have h_split : abs (∫ θ in (0 : ℝ)..Real.pi, Real.cos (r * Real.cos θ)) ≤ δ + 4 / (r * Real.sin δ) + δ := by
    -- Bounds:
    have h_bound1 : abs (∫ θ in (0 : ℝ)..δ, Real.cos (r * Real.cos θ)) ≤ δ := by
      refine' le_trans ( intervalIntegral.abs_integral_le_integral_abs _ ) _ <;> norm_num [ hδ_pos.le ];
      exact le_trans ( intervalIntegral.integral_mono_on ( by positivity ) ( by exact Continuous.intervalIntegrable ( by continuity ) _ _ ) ( by norm_num ) fun x hx => Real.abs_cos_le_one _ ) ( by norm_num )
    have h_bound2 : abs (∫ θ in (δ : ℝ)..(Real.pi - δ), Real.cos (r * Real.cos θ)) ≤ 4 / (r * Real.sin δ) := by
      convert ibp_integral_bound r δ ( by positivity ) hδ_pos hδ_lt_pi_div_2 using 1
    have h_bound3 : abs (∫ θ in (Real.pi - δ : ℝ)..Real.pi, Real.cos (r * Real.cos θ)) ≤ δ := by
      refine' le_trans ( intervalIntegral.abs_integral_le_integral_abs _ ) _;
      · linarith;
      · refine' le_trans ( intervalIntegral.integral_mono_on _ _ _ _ ) _;
        exacts [ fun _ => 1, by linarith, Continuous.intervalIntegrable ( by continuity ) _ _, Continuous.intervalIntegrable ( by continuity ) _ _, fun _ _ => Real.abs_cos_le_one _, by norm_num ];
    convert! le_trans ( abs_add_three _ _ _ ) ( add_le_add_three h_bound1 h_bound2 h_bound3 ) using 1;
    rw [ intervalIntegral.integral_add_adjacent_intervals, intervalIntegral.integral_add_adjacent_intervals ] <;> apply_rules [ Continuous.intervalIntegrable ] <;> exact Real.continuous_cos.comp <| by continuity;
  -- Now sin δ = sin(1/√r) ≥ 2·(1/√r)/π = 2/(π√r)  (using sin x ≥ 2x/π for x ∈ [0, π/2])
  have h_sin_bound : Real.sin δ ≥ 2 * δ / Real.pi := by
    exact le_trans ( by ring_nf; norm_num ) ( Real.mul_le_sin ( by positivity ) hδ_lt_pi_div_2.le );
  -- So 4/(r sin δ) ≤ 4/(r · 2/(π√r)) = 4π√r/(2r) = 2π/√r
  have h_sin_bound_simplified : 4 / (r * Real.sin δ) ≤ 2 * Real.pi / Real.sqrt r := by
    rw [ div_le_div_iff₀ ] <;> try positivity;
    · rw [ ge_iff_le, div_le_iff₀ ] at h_sin_bound <;> nlinarith [ Real.pi_gt_three, Real.sqrt_nonneg r, Real.sq_sqrt <| show 0 ≤ r by positivity, mul_div_cancel₀ 1 <| ne_of_gt <| Real.sqrt_pos.mpr <| show 0 < r by positivity ];
    · exact mul_pos ( by positivity ) ( lt_of_lt_of_le ( by positivity ) h_sin_bound );
  -- Now use the fact that |besselJ₀ r| = |(2π)⁻¹ ∫_{-π}^π cos(r cos θ) dθ| = |(1/π) ∫_0^π cos(r cos θ) dθ|
  have h_besselJ₀ : abs (besselJ₀ r) = abs (∫ θ in (0 : ℝ)..Real.pi, Real.cos (r * Real.cos θ)) / Real.pi := by
    unfold besselJ₀;
    rw [ bessel_symmetry ] ; ring;
    rw [ abs_mul, abs_of_nonneg ( by positivity ) ];
  rw [ h_besselJ₀, div_le_iff₀ ] <;> ring_nf at * <;> nlinarith [ Real.pi_gt_three, Real.sqrt_nonneg r, Real.sq_sqrt <| show 0 ≤ r by positivity, mul_inv_cancel₀ <| ne_of_gt <| Real.sqrt_pos.mpr <| show 0 < r by positivity ]

/-
The integrand can be rewritten using J₀
-/
lemma integrand_eq (r : ℝ) :
    (2 * π)⁻¹ * (∫ θ in (-π)..π, (1 - cos (r * cos θ)) / r) =
    (1 - besselJ₀ r) / r := by
      rw [ intervalIntegral.integral_div, intervalIntegral.integral_sub ] <;> norm_num;
      · unfold besselJ₀; ring;
        rw [ mul_inv_cancel₀ Real.pi_ne_zero, one_mul, add_comm ];
      · exact Continuous.intervalIntegrable ( Real.continuous_cos.comp <| by continuity ) _ _

/-
Pull the constant (2π)⁻¹ inside the outer integral
-/
lemma pull_const (x : ℝ) :
    (2 * π)⁻¹ * ∫ r in (0:ℝ)..x, ∫ θ in (-π)..π, (1 - cos (r * cos θ)) / r =
    ∫ r in (0:ℝ)..x, (1 - besselJ₀ r) / r := by
      rw [ ← intervalIntegral.integral_const_mul ] ; congr ; ext r ; rw [ integrand_eq ] ;

/-
∫₁ˣ r⁻¹ dr = log x for x ≥ 1
-/
lemma integral_inv_eq_log (x : ℝ) (hx : 1 ≤ x) :
    ∫ r in (1:ℝ)..x, r⁻¹ = log x := by
      norm_num [ hx ]

/-
The integral ∫₁ˣ |J₀(r)/r| dr is bounded, using |J₀(r)| ≤ 3/√r for r ≥ 2
-/
lemma integral_besselJ₀_div_bounded :
    ∃ M : ℝ, ∀ x : ℝ, 1 ≤ x → |∫ r in (1:ℝ)..x, besselJ₀ r / r| ≤ M := by
      -- Split the integral at 2: ∫₁ˣ J₀(r)/r dr = ∫₁² J₀(r)/r dr + ∫₂ˣ J₀(r)/r dr.
      suffices h_split : ∃ M, ∀ x : ℝ, 2 ≤ x → abs (∫ r in (2:ℝ)..x, besselJ₀ r / r) ≤ M by
        -- By combining the results from the two parts, we can conclude the proof.
        obtain ⟨M, hM⟩ := h_split;
        use M + (∫ r in (1:ℝ)..2, abs (besselJ₀ r / r)); (
        intro x hx; cases le_total x 2 <;> simp_all +decide [ intervalIntegral ] ;
        · refine' le_trans ( MeasureTheory.norm_integral_le_integral_norm ( _ : ℝ → ℝ ) ) ( le_add_of_nonneg_of_le ( by exact le_trans ( abs_nonneg _ ) ( hM 2 le_rfl ) ) ( MeasureTheory.setIntegral_mono_set _ _ _ ) );
          · refine' ContinuousOn.integrableOn_Icc _ |> fun h => h.mono_set <| Set.Ioc_subset_Icc_self;
            refine' ContinuousOn.norm ( ContinuousOn.div _ continuousOn_id fun x hx => by linarith [ hx.1 ] );
            refine' Continuous.continuousOn _;
            refine' continuous_const.mul _;
            fun_prop (disch := norm_num);
          · exact Filter.Eventually.of_forall fun _ => norm_nonneg _;
          · exact MeasureTheory.ae_of_all _ fun y hy => ⟨ hy.1, hy.2.trans ‹_› ⟩;
        · -- Using the triangle inequality, we can split the integral into two parts:
          have h_split : ∫ r in (1:ℝ)..x, besselJ₀ r / r = (∫ r in (1:ℝ)..2, besselJ₀ r / r) + (∫ r in (2:ℝ)..x, besselJ₀ r / r) := by
            rw [ intervalIntegral.integral_add_adjacent_intervals ] <;> apply_rules [ ContinuousOn.intervalIntegrable ];
            · refine' ContinuousOn.div _ continuousOn_id fun r hr => by norm_num at hr; linarith;
              refine' Continuous.continuousOn _;
              refine' continuous_const.mul _;
              fun_prop (disch := norm_num);
            · refine' ContinuousOn.div _ continuousOn_id fun r hr => by cases Set.mem_uIcc.mp hr <;> linarith;
              refine' Continuous.continuousOn _;
              refine' continuous_const.mul _;
              fun_prop (disch := norm_num);
          simp_all +decide [ intervalIntegral.integral_of_le ];
          exact abs_le.mpr ⟨ by linarith [ abs_le.mp ( hM x ‹_› ), abs_le.mp ( show |∫ r in Ioc 1 2, besselJ₀ r / r ∂volume| ≤ ∫ r in Ioc 1 2, |besselJ₀ r / r| ∂volume from MeasureTheory.norm_integral_le_integral_norm ( _ : ℝ → ℝ ) ) ], by linarith [ abs_le.mp ( hM x ‹_› ), abs_le.mp ( show |∫ r in Ioc 1 2, besselJ₀ r / r ∂volume| ≤ ∫ r in Ioc 1 2, |besselJ₀ r / r| ∂volume from MeasureTheory.norm_integral_le_integral_norm ( _ : ℝ → ℝ ) ) ] ⟩);
      -- For the second part: |J₀(r)/r| ≤ 3/(r√r) = 3r^(-3/2) on [2,∞) (using abs_besselJ₀_le_sqrt).
      have h_bound : ∀ r : ℝ, 2 ≤ r → abs (besselJ₀ r / r) ≤ 3 * r^(-3 / 2 : ℝ) := by
        -- For $r \geq 2$, we have $|J_0(r)| \leq \frac{3}{\sqrt{r}}$.
        have h_bound : ∀ r : ℝ, 2 ≤ r → abs (besselJ₀ r) ≤ 3 / Real.sqrt r := by
          exact fun r a => abs_besselJ₀_le_sqrt r a;
        intro r hr; rw [ abs_div, abs_of_nonneg ( by positivity : 0 ≤ r ) ] ; convert! mul_le_mul_of_nonneg_right ( h_bound r hr ) ( inv_nonneg.mpr ( by positivity : 0 ≤ r ) ) using 1 ; ring;
        rw [ Real.sqrt_eq_rpow, ← Real.rpow_neg ( by positivity ), ← Real.rpow_neg_one, ← Real.rpow_add ( by positivity ) ] ; norm_num;
      -- So |∫₂ˣ J₀(r)/r dr| ≤ ∫₂ˣ 3r^(-3/2) dr ≤ ∫₂^∞ 3r^(-3/2) dr = 3 · 2/√2 = 3√2.
      have h_integral_bound : ∀ x : ℝ, 2 ≤ x → abs (∫ r in (2:ℝ)..x, besselJ₀ r / r) ≤ ∫ r in (2:ℝ)..x, 3 * r^(-3 / 2 : ℝ) := by
        intros x hx; rw [ intervalIntegral.integral_of_le hx, intervalIntegral.integral_of_le hx ] ; refine' le_trans ( MeasureTheory.norm_integral_le_integral_norm ( _ : ℝ → ℝ ) ) ( MeasureTheory.integral_mono_of_nonneg _ _ _ );
        · exact Filter.Eventually.of_forall fun _ => norm_nonneg _;
        · exact ContinuousOn.integrableOn_Icc ( by exact continuousOn_of_forall_continuousAt fun r hr => by exact ContinuousAt.mul continuousAt_const <| ContinuousAt.rpow continuousAt_id continuousAt_const <| Or.inl <| by linarith [ hr.1 ] ) |> fun h => h.mono_set <| Set.Ioc_subset_Icc_self;
        · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioc ] with r hr using h_bound r hr.1.le;
      -- Evaluate the integral ∫₂ˣ 3r^(-3/2) dr.
      have h_integral_eval : ∀ x : ℝ, 2 ≤ x → ∫ r in (2:ℝ)..x, 3 * r^(-3 / 2 : ℝ) = 3 * (2 * (2 : ℝ)^(-1 / 2 : ℝ) - 2 * x^(-1 / 2 : ℝ)) := by
        intro x hx; rw [ intervalIntegral.integral_const_mul, integral_rpow ] <;> norm_num ; ring;
        norm_num [ hx ];
      exact ⟨ 3 * ( 2 * 2 ^ ( -1 / 2 : ℝ ) ), fun x hx => le_trans ( h_integral_bound x hx ) ( by rw [ h_integral_eval x hx ] ; exact mul_le_mul_of_nonneg_left ( sub_le_self _ <| by positivity ) <| by positivity ) ⟩

/-
The full expression equals a constant minus ∫₁ˣ J₀(r)/r dr
-/
lemma expression_rewrite (x : ℝ) (hx : 1 ≤ x) :
    (2 * π)⁻¹ * (∫ r in (0:ℝ)..x, ∫ θ in (-π)..π, (1 - cos (r * cos θ)) / r) - log x =
    (∫ r in (0:ℝ)..1, (1 - besselJ₀ r) / r) -
    ∫ r in (1:ℝ)..x, besselJ₀ r / r := by
      -- Split the integral: ∫₀ˣ = ∫₀¹ + ∫₁ˣ (using intervalIntegral.integral_add_adjacent_intervals).
      have h_split : ∫ r in (0:ℝ)..x, (1 - besselJ₀ r) / r = (∫ r in (0:ℝ)..1, (1 - besselJ₀ r) / r) + (∫ r in (1:ℝ)..x, (1 - besselJ₀ r) / r) := by
        have h_integrable : MeasureTheory.IntegrableOn (fun r => (1 - besselJ₀ r) / r) (Set.Ioc 0 1) := by
          -- We'll use the fact that $|1 - J_0(r)| \leq r^2$ for $r \in [0, 1]$.
          have h_bound : ∀ r ∈ Set.Ioc 0 1, abs ((1 - besselJ₀ r) / r) ≤ r := by
            -- Using the fact that $|1 - J_0(r)| \leq r^2$ for $r \in (0, 1]$, we can bound the integrand.
            have h_bound : ∀ r ∈ Set.Ioc 0 1, abs (1 - besselJ₀ r) ≤ r^2 := by
              intro r hr
              have h_integral_bound : abs (∫ θ in (-Real.pi)..Real.pi, (1 - Real.cos (r * Real.cos θ))) ≤ 2 * Real.pi * r^2 := by
                -- Using the fact that $|1 - \cos(r \cos \theta)| \leq r^2 \cos^2 \theta$ for all $\theta$, we can bound the integral.
                have h_integral_bound : ∀ θ ∈ Set.Icc (-Real.pi) Real.pi, abs (1 - Real.cos (r * Real.cos θ)) ≤ r^2 * Real.cos θ^2 := by
                  -- Using the fact that $|1 - \cos(x)| \leq x^2$ for all $x$, we can bound the integral.
                  have h_cos_bound : ∀ x : ℝ, |1 - Real.cos x| ≤ x^2 := by
                    -- Using the fact that $|1 - \cos(x)| \leq x^2$ for all $x$, we can bound the integral. This follows from the trigonometric identity $1 - \cos(x) = 2 \sin^2(x/2)$ and the fact that $|\sin(x/2)| \leq |x/2|$.
                    have h_sin_bound : ∀ x : ℝ, |Real.sin (x / 2)| ≤ |x / 2| := by
                      grind +suggestions;
                    intro x; specialize h_sin_bound x; rw [ show 1 - Real.cos x = 2 * Real.sin ( x / 2 ) ^ 2 by rw [ Real.sin_sq, Real.cos_sq ] ; ring ] ; rw [ abs_le ] ; constructor <;> cases abs_cases ( x / 2 ) <;> nlinarith [ abs_le.mp h_sin_bound ] ;
                  exact fun θ hθ => le_trans ( h_cos_bound _ ) ( by rw [ mul_pow ] );
                refine' le_trans ( intervalIntegral.abs_integral_le_integral_abs _ ) _;
                · linarith [ Real.pi_pos ];
                · refine' le_trans ( intervalIntegral.integral_mono_on _ _ _ h_integral_bound ) _ <;> norm_num;
                  · positivity;
                  · exact Continuous.intervalIntegrable ( by continuity ) _ _;
                  · exact Continuous.intervalIntegrable ( by continuity ) _ _;
                  · nlinarith [ Real.pi_pos ];
              -- Using the definition of $J_0(r)$, we can rewrite the integral.
              have h_integral_rewrite : ∫ θ in (-Real.pi)..Real.pi, (1 - Real.cos (r * Real.cos θ)) = 2 * Real.pi * (1 - besselJ₀ r) := by
                rw [ intervalIntegral.integral_sub ] <;> norm_num [ besselJ₀ ] ; ring;
                · norm_num [ mul_assoc, mul_comm, mul_left_comm, Real.pi_ne_zero ];
                · exact Continuous.intervalIntegrable ( Real.continuous_cos.comp <| by continuity ) _ _;
              exact abs_le.mpr ⟨ by nlinarith [ abs_le.mp h_integral_bound, Real.pi_pos ], by nlinarith [ abs_le.mp h_integral_bound, Real.pi_pos ] ⟩;
            exact fun r hr => by rw [ abs_div, abs_of_nonneg hr.1.le ] ; exact div_le_of_le_mul₀ ( by linarith [ hr.1 ] ) ( by linarith [ hr.1 ] ) ( by nlinarith [ h_bound r hr ] ) ;
          refine' MeasureTheory.Integrable.mono' _ _ _;
          refine' fun r => r;
          · exact continuous_id.integrableOn_Ioc;
          · refine' ContinuousOn.aestronglyMeasurable _ measurableSet_Ioc;
            refine' ContinuousOn.div ( continuousOn_const.sub _ ) continuousOn_id fun r hr => ne_of_gt hr.1;
            refine' Continuous.continuousOn _;
            refine' continuous_const.mul _;
            fun_prop;
          · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioc ] with r hr using h_bound r hr;
        rw [ intervalIntegral.integral_add_adjacent_intervals ];
        · rwa [ intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one ];
        · apply_rules [ ContinuousOn.intervalIntegrable ];
          refine' ContinuousOn.div ( continuousOn_const.sub _ ) continuousOn_id fun r hr => by cases Set.mem_uIcc.mp hr <;> linarith;
          refine' Continuous.continuousOn _;
          refine' continuous_const.mul _;
          fun_prop;
      -- For ∫₁ˣ (1 - J₀(r))/r dr: split as ∫₁ˣ 1/r dr - ∫₁ˣ J₀(r)/r dr = log x - ∫₁ˣ J₀(r)/r dr (using integral_inv_eq_log and intervalIntegral.integral_sub).
      have h_split_integral : ∫ r in (1:ℝ)..x, (1 - besselJ₀ r) / r = (∫ r in (1:ℝ)..x, r⁻¹) - (∫ r in (1:ℝ)..x, besselJ₀ r / r) := by
        rw [ ← intervalIntegral.integral_sub ] ; congr ; ext ; ring;
        · norm_num [ hx ];
        · apply_rules [ ContinuousOn.intervalIntegrable ];
          refine' ContinuousOn.div _ continuousOn_id fun r hr => by cases Set.mem_uIcc.mp hr <;> linarith;
          refine' Continuous.continuousOn _;
          refine' continuous_const.mul _;
          fun_prop (disch := norm_num);
      rw [ pull_const ] ; rw [ h_split, h_split_integral ] ; norm_num [ hx ] ; ring;

theorem asymptotic_bessel :
    (fun x ↦ ((2 * π)⁻¹ * ∫ r in 0..x, ∫ θ in -π..π, (1 - cos (r * cos θ)) / r) - log x)
    =O[atTop] (1 : ℝ → ℝ) := by
  -- By expression_rewrite, the expression equals C₁ - ∫₁ˣ J₀(r)/r dr for x ≥ 1.
  suffices h_suff : ∃ C₁ M : ℝ, ∀ x : ℝ, 1 ≤ x → |((2 * Real.pi)⁻¹ * (∫ r in (0:ℝ)..x, ∫ θ in (-Real.pi)..Real.pi, (1 - cos (r * cos θ)) / r) - Real.log x)| ≤ |C₁| + M by
    obtain ⟨ C₁, M, h ⟩ := h_suff; erw [ Asymptotics.isBigO_iff ] ; use |C₁| + M; filter_upwards [ Filter.eventually_ge_atTop 1 ] with x hx using by simpa using h x hx;
  have := @integral_besselJ₀_div_bounded;
  exact ⟨ ∫ r in ( 0 : ℝ )..1, ( 1 - besselJ₀ r ) / r, this.choose, fun x hx => by rw [ expression_rewrite x hx ] ; exact abs_sub_le_iff.mpr ⟨ by cases abs_cases ( ∫ r in ( 0 : ℝ )..1, ( 1 - besselJ₀ r ) / r ) <;> linarith [ abs_le.mp ( this.choose_spec x hx ) ], by cases abs_cases ( ∫ r in ( 0 : ℝ )..1, ( 1 - besselJ₀ r ) / r ) <;> linarith [ abs_le.mp ( this.choose_spec x hx ) ] ⟩ ⟩
