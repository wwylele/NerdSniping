module

public import Mathlib

public section

open Real Filter Asymptotics

theorem bddBelow_range_sub {α : Type*} {β : Type*} [LinearOrder β] [AddCommGroup β]
    [IsOrderedAddMonoid β]
    {a b : α → β} (ha : BddBelow (Set.range a)) (hb : BddAbove (Set.range b)) :
    BddBelow (Set.range (a - b)) := by
  obtain ⟨ca, ha⟩ := ha
  obtain ⟨cb, hb⟩ := hb
  use ca - cb
  suffices ∀ (x : α), ca - cb ≤ a x - b x by simpa [mem_lowerBounds]
  have ha : ∀ (x : α), ca ≤ a x:= by simpa [mem_lowerBounds] using ha
  have hb : ∀ (x : α), b x ≤ cb := by simpa [mem_upperBounds] using hb
  exact fun x ↦ sub_le_sub (ha x) (hb x)

theorem bddAbove_range_sub {α : Type*} {a b : α → ℝ} (ha : BddAbove (Set.range a))
    (hb : BddBelow (Set.range b)) :
    BddAbove (Set.range (a - b)) := by
  obtain ⟨ca, ha⟩ := ha
  obtain ⟨cb, hb⟩ := hb
  use ca - cb
  suffices ∀ (x : α), a x - b x ≤ ca - cb by simpa [mem_upperBounds]
  have ha : ∀ (x : α), a x ≤ ca := by simpa [mem_upperBounds] using ha
  have hb : ∀ (x : α), cb ≤ b x := by simpa [mem_lowerBounds] using hb
  exact fun x ↦ sub_le_sub (ha x) (hb x)

theorem Pi.intCast_single {n : ℕ} (a : Fin n) (b : ℤ) (x : Fin n) :
    ((Pi.single (M := fun (_ : Fin n) ↦ ℤ) a b x) : ℝ) =
    (Pi.single (M := fun (_ : Fin n) ↦ ℝ) a b x) := by
  by_cases h : a = x
  · aesop
  · aesop

theorem Pi.single_mul_left_const_apply {ι : Type*} {α : Type*}
    [MulZeroClass α] [DecidableEq ι] (i j : ι) (a : α) (f : α) :
    single (M := fun _ ↦ α) i (a * f) j = single (M := fun _ ↦ α) i a j * f := by
  by_cases h : i = j <;> aesop


-- Aristotle
lemma abs_sin_add_le (a b : ℝ) : |sin (a + b)| ≤ |sin a| + |sin b| := by
  rw [abs_le]
  constructor
  <;> cases abs_cases (sin a)
  <;> cases abs_cases (sin b)
  <;> nlinarith [abs_le.mp (Real.abs_cos_le_one a), abs_le.mp (Real.abs_cos_le_one b),
    Real.sin_add a b]

lemma abs_sin_sum_le {ι : Type*} (s : Finset ι) (a : ι → ℝ) :
    |sin (∑ i ∈ s, a i)| ≤ ∑ i ∈ s, |sin (a i)| := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s h ih =>
    simp only [Finset.sum_cons]
    apply (abs_sin_add_le _ _).trans
    grw [ih]

-- Aristotle
lemma abs_sin_nat_mul_le (m : ℕ) (y : ℝ) :
    |sin (m * y)| ≤ m * |sin y| := by
  induction m with
  | zero => simp
  | succ n ih =>
    simp only [Nat.cast_add, Nat.cast_one, add_mul, one_mul, sin_add]
    rw [abs_le]
    constructor
    · cases abs_cases (Real.sin y)
      <;> nlinarith [abs_le.mp ‹_›, abs_le.mp (Real.abs_cos_le_one ((↑‹ℕ› : ℝ) * y)),
        abs_le.mp (Real.abs_cos_le_one y) ]
    · cases abs_cases (Real.sin y)
      <;> nlinarith [abs_le.mp ‹_›, abs_le.mp (Real.abs_cos_le_one ((↑‹ℕ› : ℝ) * y)),
        abs_le.mp (Real.abs_cos_le_one y) ]


theorem sin_inequality {n : ℕ} (x : Fin n → ℤ) (y : Fin n → ℝ) :
    sin (∑ i, x i * y i) ^ 2 ≤ (∑ k, (x k : ℝ) ^ 2) * ∑ i, sin (y i) ^ 2 := by
  simp_rw [← sq_abs (x _ : ℝ), ← sq_abs (sin _)]
  apply le_trans ?_ (Finset.sum_mul_sq_le_sq_mul_sq _ _ _)
  rw [sq_le_sq₀ (by simp) (by positivity)]
  apply (abs_sin_sum_le _ _).trans
  refine Finset.sum_le_sum fun i _ ↦ ?_
  convert abs_sin_nat_mul_le (Int.natAbs (x i)) (y i) using 0
  congrm ?_ ≤ $(by simp) * _
  rw [Nat.cast_natAbs, Int.cast_abs]
  rcases abs_cases (x i : ℝ) with ⟨hx, h⟩ | ⟨hx, h⟩
  · simp [hx]
  · simp [hx]

theorem integral_comp_polarCoord_symm_disk {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ × ℝ → E) :
    ∫ p in Set.Ioc 0 1 ×ˢ Set.Ioo (-π) π, p.1 • f (p.1 * Real.cos p.2, p.1 * Real.sin p.2) =
    ∫ p in {p | p.1 ^ 2 + p.2 ^ 2 ≤ 1}, f p := by
  conv_rhs =>
    rw [← MeasureTheory.integral_indicator (by measurability), ← integral_comp_polarCoord_symm]
    conv in fun p ↦ _ =>
      ext p
      rw [← Set.indicator_comp_right]
      simp only [Set.preimage_setOf_eq, polarCoord_symm_apply, mul_pow, ← mul_add,
        cos_sq_add_sin_sq, mul_one, sq_le_one_iff_abs_le_one]
      rw [show p.1 • {a | |a.1| ≤ 1}.indicator (f ∘ ↑polarCoord.symm) p =
        {a | |a.1| ≤ 1}.indicator (fun p ↦ p.1 • (f ∘ polarCoord.symm) p) p by
        rw [Set.indicator_smul]]
    rw [MeasureTheory.setIntegral_indicator (by measurability)]
  simp only [polarCoord_target, Function.comp_apply, polarCoord_symm_apply]
  congr
  grind

theorem two_mul_one_sub_cos_le (x : ℝ) : 2 * (1 - cos x) ≤ x ^ 2 := by
  grw [← one_sub_sq_div_two_le_cos]
  apply le_of_eq
  ring

theorem one_sub_cos_le (x : ℝ) : (1 - cos x) ≤ x ^ 2 / 2 := by
  grw [← two_mul_one_sub_cos_le]
  simp


-- Aristotle
theorem cofinite_int_le_cobounded_real :
    Filter.map (fun (x : Fin 2 → ℤ) ↦ ((x 0 : ℝ), (x 1 : ℝ))) cofinite ≤
    Bornology.cobounded (ℝ × ℝ) := by
  refine Filter.map_le_iff_le_comap.mpr ?_;
  have h_preimage_finite : ∀ (S : Set (ℝ × ℝ)),
      Bornology.IsBounded S → Set.Finite {x : Fin 2 → ℤ | ((x 0 : ℝ), (x 1 : ℝ)) ∈ S} := by
    intro S hS;
    -- Since S is bounded, there exists some R such that for all (x, y) in S, x^2 + y^2 ≤ R^2.
    obtain ⟨R, hR⟩ : ∃ R : ℝ, ∀ p ∈ S, p.1^2 + p.2^2 ≤ R^2 := by
      obtain ⟨ R, hR ⟩ := hS.exists_pos_norm_le;
      norm_num [ Prod.norm_def ] at hR;
      exact ⟨ R + R, fun p hp =>
        by nlinarith [ abs_le.mp ( hR.2 _ _ hp |>.1 ), abs_le.mp ( hR.2 _ _ hp |>.2 ) ] ⟩;
    refine Set.Finite.subset ( Set.finite_Icc ( -⌈R^2⌉₊ : Fin 2 → ℤ ) ⌈R^2⌉₊ ) ?_;
    intro x hx
    constructor <;> intro i <;> fin_cases i <;> norm_num <;>
      exact Int.le_of_lt_add_one <|
      by { rw [ ← @Int.cast_lt ℝ ] ; push_cast ; nlinarith [ Nat.le_ceil ( R ^ 2 ), hR _ hx ] } ;
  intro s hs
  simp only [mem_cofinite]
  obtain ⟨ t, ht, hts ⟩ := hs
  specialize h_preimage_finite tᶜ
  simp only [Bornology.isBounded_compl_iff, Fin.isValue, Set.mem_compl_iff] at h_preimage_finite
  exact Set.Finite.subset ( h_preimage_finite ht ) fun x hx => by contrapose! hx; aesop;

-- Aristotle
theorem map_polarCoord_eq_cobounded :
    Filter.map (polarCoord.symm) (atTop ×ˢ 𝓟 (Set.Icc (-π) π)) = Bornology.cobounded (ℝ × ℝ) := by
  refine le_antisymm ?_ ?_
  · intro T hT;
    obtain ⟨R, hR⟩ : ∃ R > 0, ∀ p : ℝ × ℝ, p.1^2 + p.2^2 ≥ R^2 → p ∈ T := by
      have h_cobounded : ∃ R > 0, ∀ p : ℝ × ℝ, p.1^2 + p.2^2 ≥ R^2 → p ∈ T := by
        have h_compl_bounded : Bornology.IsBounded (Tᶜ) :=
          Bornology.isBounded_compl_iff.mpr hT
        obtain ⟨ R, hR ⟩ := h_compl_bounded.exists_pos_norm_le;
        norm_num [ Prod.norm_def ] at hR;
        exact ⟨ R * 2, mul_pos hR.1 zero_lt_two,
          fun p hp => Classical.not_not.1 fun h => by
            nlinarith [ abs_le.mp ( hR.2 _ _ h |>.1 ), abs_le.mp ( hR.2 _ _ h |>.2 ) ] ⟩;
      exact h_cobounded;
    refine Filter.mem_prod_iff.mpr ⟨ Set.Ici R, Filter.mem_atTop_sets.mpr ⟨ R, fun x hx => hx ⟩,
      Set.Icc ( -Real.pi ) Real.pi, Filter.mem_principal_self _, ?_ ⟩;
    rintro ⟨ r, θ ⟩ ⟨ hr, hθ ⟩ ;
    exact hR.2 _ ( by simpa [ mul_pow, Real.cos_sq' ] using by nlinarith [ Set.mem_Ici.mp hr ] )
  · refine fun s hs ↦ ?_;
    obtain ⟨R, hR⟩ : ∃ R > 0, ∀ r ≥ R, ∀ θ ∈ Set.Icc (-Real.pi) Real.pi,
        (r * Real.cos θ, r * Real.sin θ) ∈ s := by
      rw [ Filter.mem_map, Filter.mem_prod_iff ] at hs;
      norm_num +zetaDelta at *;
      obtain ⟨ t₁, ⟨ a, ha ⟩, t₂, ht₂, h ⟩ := hs;
      exact ⟨ Max.max a 1, by positivity,
        fun r hr θ hθ₁ hθ₂ =>
        h ( Set.mk_mem_prod ( ha r ( le_trans ( le_max_left _ _ ) hr ) ) ( ht₂ ⟨ hθ₁, hθ₂ ⟩ ) ) ⟩
    have h_cobounded : ∀ p : ℝ × ℝ, Real.sqrt (p.1^2 + p.2^2) ≥ R → p ∈ s := by
      intro p hp;
      specialize hR;
      have := hR.2 ( Real.sqrt ( p.1 ^ 2 + p.2 ^ 2 ) ) hp
        ( Complex.arg ( p.1 + p.2 * Complex.I ) ) ?_
      · simp_all only [mem_map, gt_iff_lt, ge_iff_le, Set.mem_Icc, and_imp, Complex.sin_arg,
          Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
          mul_one, Complex.I_re, mul_zero, add_zero, zero_add]
        by_cases h : p.1 + p.2 * Complex.I = 0
        · simp_all [ Complex.ext_iff ]
          linarith;
        · simp_all [Complex.cos_arg, Complex.normSq, Complex.norm_def, sq ]
          grind;
      · exact ⟨ Complex.neg_pi_lt_arg _ |> le_of_lt, Complex.arg_le_pi _ ⟩;
    refine Filter.mem_of_superset ?_ ?_ (x := { p : ℝ × ℝ | Real.sqrt ( p.1 ^ 2 + p.2 ^ 2 ) ≥ R })
    · rw [ Metric.cobounded_eq_cocompact ];
      rw [ Filter.mem_cocompact ];
      refine ⟨ Metric.closedBall ( 0 : ℝ × ℝ ) R,
        ProperSpace.isCompact_closedBall _ _, fun p hp => ?_ ⟩ ;
      simp_all only [mem_map, gt_iff_lt, ge_iff_le, Set.mem_Icc, and_imp, Prod.forall,
        Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le, Set.mem_setOf_eq]
      exact le_trans hp.le ( max_le_iff.mpr ⟨
        Real.abs_le_sqrt <| by nlinarith, Real.abs_le_sqrt <| by nlinarith ⟩ );
    · grind

theorem sin_cube_bound {x : ℝ} (hx : x ∈ Set.Icc (-1) 1) :
    |(x + sin x) * (x - sin x)| ≤ 2 * (π / 4) ^ 2 * (sin x ^ 2 * x ^ 2) := by
  wlog h0 : 0 ≤ x
  · have hx' : -x ∈ Set.Icc (-1) 1 := by
      rw [Set.neg_mem_Icc_iff]
      simpa using hx
    have h0' : 0 ≤ -x := by grind
    convert this hx' h0' using 2
    · simp_rw [sin_neg]
      ring
    · simp_rw [sin_neg]
      ring
  have hxpi : x ∈ Set.Icc 0 π := by
    refine ⟨h0, ?_⟩
    apply hx.2.trans
    apply le_trans (by simp) pi_gt_three.le
  have hxsin : 0 ≤ x - sin x := sub_nonneg.mpr (sin_le h0)
  rw [abs_of_nonneg (mul_nonneg (add_nonneg h0 (Real.sin_nonneg_of_mem_Icc hxpi)) hxsin)]
  rw [show 2 * (π / 4) ^ 2 * (sin x ^ 2 * x ^ 2) =
    (x + x) * ((π / 4) ^ 2 * sin x ^ 2 * x) by ring]
  refine mul_le_mul_of_nonneg' (add_le_add_right (sin_le h0) _) ?_ hxsin (by simpa using h0)
  trans ((π / 4) ^ 2 * (2 / Real.pi * x) ^ 2 * x); swap
  · refine mul_le_mul_of_nonneg_right ?_ h0
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    rw [sq_le_sq₀ (by positivity) (Real.sin_nonneg_of_mem_Icc hxpi)]
    apply Real.mul_le_sin h0 (le_trans hx.2 one_le_pi_div_two)
  suffices x - sin x ≤ x ^ 3 / 4 by
    convert this using 1
    field
  rw [sub_le_comm]
  by_cases hx0 : x = 0
  · simp [hx0]
  exact (sin_gt_sub_cube (lt_of_le_of_ne' h0 hx0) hx.2).le


-- Should Fix Asymptotics.isBigO_one_nat_atTop_iff
theorem bounded_of_isBigO_cofinite {α : Type*} {f : α → ℝ} (hf : f =O[cofinite] (1 : α → ℝ)) :
    ∃ c : ℝ, ∀ x, |f x| ≤ c := by
  rw [isBigO_cofinite_iff (by simp)] at hf
  simpa using hf
