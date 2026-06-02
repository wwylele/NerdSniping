import Mathlib

open Real MeasureTheory Filter

variable {n : ℕ}

noncomputable section

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

theorem cur_eq [NeZero n] (x : Fin n → ℤ) :
    cur x = (2 * Real.pi)⁻¹ ^ n *
    ∫ (w : Fin n → ℝ) in Set.Icc 0 (fun _ ↦ 2 * Real.pi), cos (∑ i, x i * w i) := by

  sorry

def φ (x : Fin n → ℤ) : ℝ :=
  (2 * Real.pi)⁻¹ ^ n * ∫ (w : Fin n → ℝ) in Set.Icc 0 (fun _ ↦ 2 * Real.pi),
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
      <;> nlinarith [ abs_le.mp ‹_›, abs_le.mp (Real.abs_cos_le_one ((↑‹ℕ› : ℝ) * y)),
        abs_le.mp (Real.abs_cos_le_one y) ]
    · cases abs_cases (Real.sin y)
      <;> nlinarith [ abs_le.mp ‹_›, abs_le.mp (Real.abs_cos_le_one ((↑‹ℕ› : ℝ) * y)),
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
      (Set.Icc 0 (fun _ ↦ 2 * Real.pi)) := by
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
      =ᵐ[volume.restrict (Set.Icc 0 (fun _ ↦ 2 * Real.pi))] f := by
    refine EventuallyEq.filter_mono ?_ ae_restrict_le
    suffices ∀ᵐ w : Fin n → ℝ, ∀ z : Fin n → ℤ, w ≠ fun k ↦ z k * (2 * Real.pi) by
      unfold EventuallyEq
      filter_upwards [this] with w h
      rw [div_self ?_, mul_one]
      contrapose! h
      rw [Finset.sum_eq_zero_iff_of_nonneg (fun k _ ↦ by simpa using Real.cos_le_one (w k))] at h
      have h : ∀ (i : Fin n), ∃ n : ℤ, n * (2 * Real.pi) = w i := by
        simpa [sub_eq_zero, Real.cos_eq_one_iff] using h
      choose z hz using h
      use z
      grind
    rw [eventually_countable_forall]
    intro z
    exact Measure.ae_ne volume fun k ↦ z k * (2 * Real.pi)
  rw [integral_congr_ae (hcongr _)]
  rw [← cur_eq]
