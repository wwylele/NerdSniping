import Mathlib

open Real MeasureTheory Filter Topology

variable {n : ℕ}

noncomputable section

-- https://math.stackexchange.com/a/4452978/1197328
theorem liouville_lemma1 [NeZero n] (f : (Fin n → ℤ) → ℝ)
    (hharmonic : ∀ x, ∑ k, (f (x - Pi.single k 1) - f x) + ∑ k, (f (x + Pi.single k 1) - f x) = 0)
    (l : ℝ) (e : Fin n)
    (hbound : ∀ x, ∀ k : ℕ, ∑ i ∈ Finset.range k, f (x + i • Pi.single e 1) ≤ l) :
    ∀ x, f x ≤ 0 := by
  have hboundabove : BddAbove (Set.range f) := by
    use l
    suffices ∀ x, f x ≤ l by simpa [mem_upperBounds]
    intro x
    specialize hbound x 1
    simpa using hbound
  have hn0 : 0 < n := NeZero.pos n
  let m : ℝ := sSup (Set.range f)
  have hfm (x : Fin n → ℤ) : f x ≤ m := le_csSup hboundabove (by simp)
  suffices m ≤ 0 by
    intro x
    apply le_trans (hfm x) this
  have h1 (d : ℝ) (hd : 0 < d) (x : Fin n → ℤ) (h : m - d < f x) :
      m - 2 * n * d < f (x + Pi.single e 1) := by
    specialize hharmonic x
    contrapose! hharmonic
    apply ne_of_lt
    conv_lhs =>
      right
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ e)]
    have : (∑ _ : Fin n, d) + (∑ _ ∈ (Finset.univ.erase e : Finset (Fin n)),
        d + (d - 2 * n * d)) = 0 := by
      simp [hn0]
      ring
    rw [← this]
    gcongr ?_ + ?_
    · refine Finset.sum_lt_sum_of_nonempty (by simp) fun i _ ↦ ?_
      rw [sub_lt_comm]
      exact lt_of_le_of_lt (sub_le_sub_right (hfm _) _) h
    · apply add_lt_add_of_le_of_lt
      · refine Finset.sum_le_sum fun i _ ↦ ?_
        rw [sub_le_comm]
        apply le_trans (sub_le_sub_right (hfm _) _) h.le
      · linarith
  have h2 (d : ℝ) (hd : 0 < d) (x : Fin n → ℤ) (h : m - d < f x) (i : ℕ) :
      m - (2 * n) ^ i * d < f (x + i • Pi.single e 1) := by
    induction i with
    | zero => simpa using h
    | succ i h =>
      rw [add_smul, one_smul, ← add_assoc, add_comm i 1, pow_add, pow_one, mul_assoc]
      apply h1 _ (mul_pos (pow_pos (by simpa using hn0) i) hd)
      exact h
  by_contra! hm
  have h3 (x : Fin n → ℤ) (k : ℕ) (h : m - 2⁻¹ * m / (2 * n) ^ k < f x) (i : ℕ) (hik : i < k) :
      2⁻¹ * m < f (x + i • Pi.single e 1) := by
    apply lt_trans ?_ (h2 (2⁻¹ * m / (2 * n) ^ k) (by positivity) x h i)
    rw [mul_div_left_comm, ← inv_div,
      div_eq_mul_inv, ← pow_sub₀ _ (by simpa using NeZero.ne n) hik.le, mul_right_comm,
      ← one_sub_mul]
    refine mul_lt_mul_of_pos_right ?_ hm
    rw [lt_sub_comm]
    norm_num
    apply inv_lt_one_of_one_lt₀
    refine one_lt_pow₀ ?_ (by simpa [tsub_eq_zero_iff_le] using hik)
    norm_cast
    grind
  have h4 (x : Fin n → ℤ) (k : ℕ) (hk : k ≠ 0) (h : m - 2⁻¹ * m / (2 * n) ^ k < f x) :
      k * (2⁻¹ * m) < ∑ i ∈ Finset.range k, f (x + i • Pi.single e 1) := by
    rw [show k * (2⁻¹ * m) = ∑ _ ∈ Finset.range k, 2⁻¹ * m by simp]
    refine Finset.sum_lt_sum_of_nonempty (by simpa using hk) fun i hik ↦ ?_
    exact h3 _ _ h _ (by simpa using hik)
  have h5 (d : ℝ) (hd : 0 < d) : ∃ x, m - d < f x := by
    by_contra! h5
    have : ∀ y ∈ Set.range f, y ≤ m - d := by simpa using h5
    have : sSup (Set.range f) ≤ m - d := csSup_le (by
      rw [Set.range_nonempty_iff_nonempty]; infer_instance) this
    simp [m, hd.not_ge] at this
  let k : ℕ := ⌈l / (2⁻¹ * m)⌉₊ + 1
  obtain ⟨x, hx⟩ := h5 (2⁻¹ * m / (2 * n) ^ k) (by positivity)
  specialize h4 x k (by simp [k]) hx
  specialize hbound x k
  contrapose! hbound
  refine lt_of_le_of_lt ?_ h4
  unfold k
  push_cast
  rw [← div_le_iff₀ (by simpa using hm)]
  exact (Nat.le_ceil _).trans (by simp)

theorem liouville_lemma1' [NeZero n] (f : (Fin n → ℤ) → ℝ)
    (hharmonic : ∀ x, ∑ k, (f (x - Pi.single k 1) - f x) + ∑ k, (f (x + Pi.single k 1) - f x) = 0)
    (l : ℝ) (e : Fin n)
    (hbound : ∀ x, ∀ k : ℕ, |∑ i ∈ Finset.range k, f (x + i • Pi.single e 1)| ≤ l) :
    f = 0 := by
  simp_rw [abs_le] at hbound
  ext x
  apply le_antisymm
  · apply liouville_lemma1 f hharmonic l e
    intro x k
    exact (hbound x k).2
  · apply nonneg_of_neg_nonpos
    refine liouville_lemma1 (-f) ?_ l e ?_ x
    · intro x
      convert congr(-$(hharmonic x)) using 1
      · rw [add_comm (Finset.sum _ _)]
        simp [neg_add_eq_sub]
      · simp
    · intro x k
      obtain h := (hbound x k).1
      rw [neg_le] at h
      simpa using h



structure IsElectricPotential (cur : (Fin n → ℤ) → ℝ) (pot : (Fin n → ℤ) → ℝ) : Prop where
  kirchhoff (x : Fin n → ℤ) :
    ∑ k, (pot (x - Pi.single k 1) - pot x) + ∑ k, (pot (x + Pi.single k 1) - pot x) = cur x
  boundary : Tendsto pot (Bornology.cobounded (Fin n → ℤ)) (𝓝 0)

theorem isElectricPotential_zero_iff (pot : (Fin n → ℤ) → ℝ) :
    IsElectricPotential 0 pot ↔ pot = 0 where
  mp := sorry
  mpr := sorry

def cur (x : Fin n → ℤ) : ℝ := Pi.single (M := fun (_ : Fin n → ℤ) ↦ ℝ) 0 1 x


theorem Pi.intCast_single (a : Fin n) (b : ℤ) (x : Fin n) :
    ((Pi.single (M := fun (_ : Fin n) ↦ ℤ) a b x) : ℝ) =
    (Pi.single (M := fun (_ : Fin n) ↦ ℝ) a b x) := by
  by_cases h : a = x
  · aesop
  · aesop

theorem Pi.single_mul_left_const_apply {ι : Type*} {α : Type*}
    [MulZeroClass α] [DecidableEq ι] (i j : ι) (a : α) (f : α) :
    single (M := fun _ ↦ α) i (a * f) j = single (M := fun _ ↦ α) i a j * f := by
  by_cases h : i = j <;> aesop

theorem cur_eq (x : Fin n → ℤ) :
    cur x = (2 * π)⁻¹ ^ n *
    ∫ (w : Fin n → ℝ) in Set.Icc 0 (fun _ ↦ 2 * π), cos (∑ i, x i * w i) := by
  suffices cur x = (2 * π)⁻¹ ^ n *
      RCLike.re (∫ (w : Fin n → ℝ) in Set.Icc 0 (fun _ ↦ 2 * π),
      Complex.exp ((∑ i, x i * w i : ℝ) * Complex.I)) by
    rw [this]
    rw [← integral_re ?_]
    · simp_rw [RCLike.re_to_complex, Complex.exp_ofReal_mul_I_re]
    · apply Continuous.integrableOn_Icc
      fun_prop
  push_cast
  simp_rw [Finset.sum_mul, Complex.exp_sum]
  rw [← Set.pi_univ_Icc, volume_pi, Measure.restrict_pi_pi]
  rw [integral_fintype_prod_eq_prod
    (fun (i : Fin n) (w : ℝ) ↦ Complex.exp ((x i) * (w : ℂ) * Complex.I))]
  by_cases h0 : x = 0
  · have hmax : max (2 * π) 0 = 2 * π := by simpa using pi_nonneg
    have hpow : ((2 * π : ℂ) ^ n).re = (2 * π) ^ n := by
      trans (2 * π : ℝ) ^ (n : ℝ)
      · rw [Real.rpow_def]
        simp
      simp
    simp [cur, h0, hmax, hpow, ← mul_pow]
    field_simp
    simp
  · suffices ∏ x_1, ∫ w  in Set.Icc 0 (2 * π), Complex.exp (x x_1 * w * Complex.I) = 0 by
      simp [cur, h0, this]
    simp_rw [funext_iff, Pi.zero_apply, not_forall] at h0
    obtain ⟨k, hk⟩ := h0
    apply Finset.prod_eq_zero (Finset.mem_univ k)
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by simpa using pi_nonneg)]
    have hderiv : ∀ w ∈ Set.uIcc 0 (2 * π), HasDerivAt
        (fun (w : ℝ) ↦ Complex.exp (x k * w * Complex.I) * (x k * Complex.I)⁻¹)
        ((fun (w : ℝ) ↦ Complex.exp (x k * w * Complex.I)) w) w := by
      intro w _
      suffices HasDerivAt
          (fun (w : ℝ) ↦ Complex.exp (x k * Complex.I * w) * (x k * Complex.I)⁻¹)
          (Complex.exp (x k * Complex.I * w) * (x k * Complex.I * (1 : ℝ)) * (x k * Complex.I)⁻¹)
          w by
        rw [mul_assoc, Complex.ofReal_one, mul_one, mul_inv_cancel₀ (by simpa using hk)] at this
        convert this using 2
        · ring_nf
        · ring_nf
      apply HasDerivAt.mul_const
      apply HasDerivAt.cexp
      apply HasDerivAt.const_mul
      apply HasDerivAt.ofReal_comp
      exact hasDerivAt_id' w
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      (Continuous.intervalIntegrable (by fun_prop) _ _)]
    rw [mul_assoc (x k : ℂ)]
    simp


def φ (x : Fin n → ℤ) : ℝ :=
  (2 * π)⁻¹ ^ n * ∫ (w : Fin n → ℝ) in Set.Icc 0 (fun _ ↦ 2 * π),
    (1 - Real.cos (∑ i, x i * w i)) / ∑ i, (2 - 2 * Real.cos (w i))

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


theorem sin_inequality (x : Fin n → ℤ) (y : Fin n → ℝ) :
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

theorem integrable_φ [NeZero n] (x : Fin n → ℤ) :
    IntegrableOn (fun w ↦ (1 - cos (∑ k, x k * w k)) / ∑ k, (2 - 2 * cos (w k)))
      (Set.Icc 0 (fun _ ↦ 2 * π)) := by
  rw [IntegrableOn, ← Set.pi_univ_Icc, volume_pi, Measure.restrict_pi_pi]
  simp_rw [← restrict_Ioo_eq_restrict_Icc]
  rw [← Measure.restrict_pi_pi]
  refine IntegrableOn.of_bound ?_ ?_ (2⁻¹ * ∑ k, (x k : ℝ) ^ 2) ?_
  · simp [NeZero.ne n]
    finiteness
  · refine ContinuousOn.aestronglyMeasurable ?_
      (MeasurableSet.pi Set.countable_univ fun i _ ↦ measurableSet_Ioo)
    refine ContinuousOn.div₀ (by fun_prop) (by fun_prop) ?_
    intro i hi
    refine (Finset.sum_pos (fun j hj ↦ ?_) (by simp)).ne'
    specialize hi j (Set.mem_univ j)
    suffices cos (i j) < 1 by simpa
    apply lt_of_le_of_ne (cos_le_one _)
    rw [ne_eq, cos_eq_one_iff_of_lt_of_lt (lt_trans (by simp [pi_pos]) hi.1) hi.2]
    exact hi.1.ne'
  apply ae_restrict_of_forall_mem (MeasurableSet.pi Set.countable_univ fun i _ ↦ measurableSet_Ioo)
  intro w hw
  rw [norm_div]
  apply div_le_of_le_mul₀ (by simp) (by positivity)
  let y (k : Fin n) := w k / 2
  have hw (k : Fin n) : w k = 2 * y k := by simp [y, mul_div_cancel₀]
  simp_rw [hw, mul_left_comm _ (2 : ℝ), ← Finset.mul_sum, cos_two_mul_eq_one_sub, mul_one_sub,
    sub_sub_cancel]
  simp_rw [← Finset.mul_sum, norm_mul, norm_ofNat, norm_eq_abs]
  rw [abs_sq, abs_of_nonneg (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)]
  grw [sin_inequality]
  apply le_of_eq
  ring

theorem φ_equation [NeZero n] (x : Fin n → ℤ) :
    (∑ k, (φ (x - Pi.single k 1) + φ (x + Pi.single k 1))) - 2 * n * φ x = cur x := by
  rw [show 2 * n * φ x = ∑ k : Fin n, (2 * φ x) by simp; ring]
  rw [← Finset.sum_sub_distrib]
  unfold φ
  conv in ∑ k, _ =>
    right; ext k
    rw [← mul_add, mul_left_comm 2, ← mul_sub, ← integral_const_mul]
    rw [← integral_add (integrable_φ _) (integrable_φ _)]
    rw [← integral_sub ((integrable_φ _).fun_add (integrable_φ _)) ((integrable_φ _).const_mul _)]
  rw [← Finset.mul_sum]
  rw [← integral_finsetSum _ (fun k _ ↦ by
    apply IntegrableOn.fun_sub
    · exact (integrable_φ _).fun_add (integrable_φ _)
    · exact (integrable_φ _).const_mul _
  )]
  conv in ∫ w in _, _ =>
    right; ext w
    conv in ∑ k, _ =>
      right; ext k
      rw [← add_div, ← mul_div_assoc, ← sub_div]
      rw [mul_sub, mul_one]
      rw [show ∀ x y z : ℝ, 1 - x + (1 - y) - (2 - z) = z - x - y by intro x y z; ring]
      simp only [Pi.sub_apply, Int.cast_sub, Pi.add_apply, Int.cast_add, sub_mul, add_mul]
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
      rw [sub_sub, add_comm, cos_add_cos, add_add_sub_cancel, add_sub_sub_cancel, add_self_div_two,
        add_self_div_two, mul_comm 2, mul_assoc, ← mul_sub]
      simp only [Pi.intCast_single, Int.cast_one, ← Pi.single_mul_left_const_apply, one_mul,
        Pi.single_comm k, Finset.sum_pi_single, Finset.mem_univ, ↓reduceIte]
      rw [mul_div_assoc]
    rw [← Finset.mul_sum, ← Finset.sum_div]
  have hcongr (f : (Fin n → ℝ) → ℝ) :
      (fun w ↦ f w * ((∑ x, (2 - 2 * cos (w x))) / ∑ x, (2 - 2 * cos (w x))))
      =ᵐ[volume.restrict (Set.Icc 0 (fun _ ↦ 2 * π))] f := by
    refine EventuallyEq.filter_mono ?_ ae_restrict_le
    suffices ∀ᵐ w : Fin n → ℝ, ∀ z : Fin n → ℤ, w ≠ fun k ↦ z k * (2 * π) by
      unfold EventuallyEq
      filter_upwards [this] with w h
      rw [div_self ?_, mul_one]
      contrapose! h
      rw [Finset.sum_eq_zero_iff_of_nonneg (fun k _ ↦ by simpa using Real.cos_le_one (w k))] at h
      have h : ∀ (i : Fin n), ∃ n : ℤ, n * (2 * π) = w i := by
        simpa [sub_eq_zero, Real.cos_eq_one_iff] using h
      choose z hz using h
      use z
      grind
    rw [eventually_countable_forall]
    intro z
    exact Measure.ae_ne volume fun k ↦ z k * (2 * π)
  rw [integral_congr_ae (hcongr _)]
  rw [← cur_eq]
