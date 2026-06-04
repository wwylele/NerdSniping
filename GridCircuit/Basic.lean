import Mathlib

open Real MeasureTheory Filter Topology Asymptotics

variable {n : ℕ}

noncomputable section

-- https://math.stackexchange.com/a/4452978/1197328
theorem liouville_lemma1 (f : (Fin n → ℤ) → ℝ)
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
  have : NeZero n := Fin.neZero e
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

theorem liouville_lemma1' (f : (Fin n → ℤ) → ℝ)
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

theorem liouville_neighbor (f : (Fin n → ℤ) → ℝ)
    (hharmonic : ∀ x, ∑ k, (f (x - Pi.single k 1) - f x) + ∑ k, (f (x + Pi.single k 1) - f x) = 0)
    (hbelow : BddBelow (Set.range f)) (habove : BddAbove (Set.range f)) (e : Fin n) :
    ∀ x, f x = f (x + Pi.single e 1) := by
  let g := fun x ↦ f (x + Pi.single e 1) - f x
  suffices g = 0 by
    unfold g at this
    rw [funext_iff] at this
    intro x
    symm
    simpa [sub_eq_zero] using this x
  obtain ⟨a, ha⟩ := habove
  have ha : ∀ x, f x ≤ a := by simpa [mem_upperBounds] using ha
  obtain ⟨b, hb⟩ := hbelow
  have hb : ∀ x, b ≤ f x := by simpa [mem_lowerBounds] using hb
  refine liouville_lemma1' g ?_ (a - b) e ?_
  · unfold g
    intro x
    conv_lhs =>
      left
      conv in fun k ↦ _ =>
        ext k
        rw [sub_sub_sub_comm]
        rw [← add_sub_right_comm]
      rw [Finset.sum_sub_distrib]
    conv_lhs =>
      right
      conv in fun k ↦ _ =>
        ext k
        rw [sub_sub_sub_comm]
        rw [← add_right_comm]
      rw [Finset.sum_sub_distrib]
    rw [sub_add_sub_comm, hharmonic, hharmonic, sub_zero]
  · intro x k
    unfold g
    have (i : ℕ) : x + i • Pi.single e 1 + Pi.single e 1 = x + (i + 1) • Pi.single e 1 := by ring
    simp_rw [this]
    rw [Finset.sum_range_sub (fun i ↦ f (x + i • (Pi.single e 1 : Fin n → ℤ))) k]
    rw [abs_le', neg_sub]
    constructor <;> apply sub_le_sub (ha _) (hb _)

theorem liouville_line (f : (Fin n → ℤ) → ℝ)
    (hharmonic : ∀ x, ∑ k, (f (x - Pi.single k 1) - f x) + ∑ k, (f (x + Pi.single k 1) - f x) = 0)
    (hbelow : BddBelow (Set.range f)) (habove : BddAbove (Set.range f)) (e : Fin n) (l : ℤ) :
    ∀ x, f x = f (x + Pi.single e l) := by
  induction l with
  | zero => simp
  | succ l h =>
    intro x
    rw [liouville_neighbor f hharmonic hbelow habove e x, h (x + Pi.single e 1), add_right_comm,
      add_assoc, Pi.single_add]
  | pred l h =>
    intro x
    rw [h x]
    rw [liouville_neighbor f hharmonic hbelow habove e (x + (Pi.single e (-↑l - 1) : Fin n → ℤ))]
    rw [add_assoc, ← Pi.single_add, sub_add_cancel]

theorem liouville (f : (Fin n → ℤ) → ℝ)
    (hharmonic : ∀ x, ∑ k, (f (x - Pi.single k 1) - f x) + ∑ k, (f (x + Pi.single k 1) - f x) = 0)
    (hbelow : BddBelow (Set.range f)) (habove : BddAbove (Set.range f)) :
    ∀ x y, f x = f y := by
  suffices ∀ x y, f x = f (x + y) by
    intro x y
    simpa using this x (y - x)
  intro x y
  induction y using Pi.single_induction generalizing x with
  | zero => simp
  | single a l => apply liouville_line f hharmonic hbelow habove
  | add a b ha hb => rw [ha x, hb (x + a), add_assoc]

structure IsElectricPotential (cur : (Fin n → ℤ) → ℝ) (pot : (Fin n → ℤ) → ℝ) : Prop where
  kirchhoff (x : Fin n → ℤ) :
    ∑ k, (pot (x - Pi.single k 1) - pot x) + ∑ k, (pot (x + Pi.single k 1) - pot x) = cur x
  bddBelow : BddBelow (Set.range pot)
  bddAbove : BddAbove (Set.range pot)

theorem isElectricPotential_zero [NeZero n] {pot : (Fin n → ℤ) → ℝ} :
    IsElectricPotential 0 pot ↔ ∃ c, pot = fun _ ↦ c where
  mp h := by
    have hconstant : pot = fun _ ↦ pot 0 := by
      ext x
      exact liouville pot h.kirchhoff h.bddBelow h.bddAbove x 0
    use pot 0
  mpr h := by
    obtain ⟨c, rfl⟩ := h
    exact {
      kirchhoff := by simp
      bddBelow := ⟨c, by simp⟩
      bddAbove := ⟨c, by simp⟩
    }

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

theorem isElectrictPotential_unique [NeZero n] {cur : (Fin n → ℤ) → ℝ} {a b : (Fin n → ℤ) → ℝ}
    (ha : IsElectricPotential cur a) (hb : IsElectricPotential cur b) :
    ∃ c, a - b = fun _ ↦ c := by
  rw [← isElectricPotential_zero]
  constructor
  · intro x
    convert congr($(ha.kirchhoff x) - $(hb.kirchhoff x)) using 1
    · rw [add_sub_add_comm, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
      congr
      all_goals
      · ext x
        simp
        ring
    · simp
  · exact bddBelow_range_sub ha.bddBelow hb.bddAbove
  · exact bddAbove_range_sub ha.bddAbove hb.bddBelow

def unitCur (c x : Fin n → ℤ) : ℝ := Pi.single (M := fun (_ : Fin n → ℤ) ↦ ℝ) c 1 x

open Classical in
def equivResistance (x : Fin n → ℤ) : Option ℝ :=
  if h : ∃ pot, IsElectricPotential (unitCur x - unitCur 0) pot then
    some <| h.choose x - h.choose 0
  else
    none

theorem equivResistance_eq [NeZero n] {x : Fin n → ℤ} {pot : (Fin n → ℤ) → ℝ}
    (h : IsElectricPotential (unitCur x - unitCur 0) pot) :
    equivResistance x = some (pot x - pot 0) := by
  have h' : ∃ pot, IsElectricPotential (unitCur x - unitCur 0) pot := ⟨pot, h⟩
  obtain ⟨c, hc⟩ := isElectrictPotential_unique h'.choose_spec h
  rw [sub_eq_iff_eq_add] at hc
  simp [equivResistance, h', hc]

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

theorem fourier_unitCur (x : Fin n → ℤ) :
    unitCur 0 x = (2 * π)⁻¹ ^ n *
    ∫ (w : Fin n → ℝ) in Set.Icc (fun _ ↦ -π) (fun _ ↦ π), cos (∑ i, x i * w i) := by
  suffices unitCur 0 x = (2 * π)⁻¹ ^ n *
      RCLike.re (∫ (w : Fin n → ℝ) in Set.Icc (fun _ ↦ -π) (fun _ ↦ π),
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
  · have hmax : max (π + π) 0 = 2 * π := by simpa [two_mul] using pi_nonneg
    have hpow : ((2 * π  : ℂ) ^ n).re = (2 * π) ^ n := by
      trans (2 * π : ℝ) ^ (n : ℝ)
      · rw [Real.rpow_def]
        simp
      simp
    simp [unitCur, h0, hmax, hpow, ← mul_pow]
    field_simp
    simp
  · suffices ∏ x_1, ∫ w in Set.Icc (-π) π, Complex.exp (x x_1 * w * Complex.I) = 0 by
      simp [unitCur, h0, this]
    simp_rw [funext_iff, Pi.zero_apply, not_forall] at h0
    obtain ⟨k, hk⟩ := h0
    apply Finset.prod_eq_zero (Finset.mem_univ k)
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by simpa using pi_nonneg)]
    have hderiv : ∀ w ∈ Set.uIcc (-π) π, HasDerivAt
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
    rw [← sub_mul]
    apply mul_eq_zero_of_left
    rw [sub_eq_zero]
    apply eq_of_div_eq_one
    rw [← Complex.exp_sub]
    convert Complex.exp_int_mul_two_pi_mul_I (x k) using 2
    push_cast
    ring

def φ (x : Fin n → ℤ) : ℝ :=
  (2 * π)⁻¹ ^ n * ∫ (w : Fin n → ℝ) in Set.Icc (fun _ ↦ -π) (fun _ ↦ π),
    (1 - Real.cos (∑ i, x i * w i)) / ∑ i, (2 - 2 * Real.cos (w i))

@[simp]
theorem φ_zero : φ (n := n) 0 = 0 := by
  simp [φ]

theorem φ_nonneg (x : Fin n → ℤ) : 0 ≤ φ x := by
  unfold φ
  apply mul_nonneg (pow_nonneg (by simpa using pi_nonneg) _)
  apply integral_nonneg
  intro x
  simp only
  apply div_nonneg
  · simpa using cos_le_one _
  · refine Finset.sum_nonneg fun i _ ↦ ?_
    simpa using cos_le_one _

@[simp]
theorem φ_symmetry (x : Fin n → ℤ) (i : Fin n) : φ (Function.update x i (-x i)) = φ x := by
  unfold φ
  let f : (Fin n → ℝ) → (Fin n → ℝ) := Pi.map fun j ↦ if j = i then (fun (x : ℝ) ↦ -x) else id
  let f' (w : Fin n → ℝ) : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
    ContinuousLinearMap.piMap
    fun j ↦ if j = i then -(ContinuousLinearMap.id _ _) else (ContinuousLinearMap.id _ _)
  have hf' (w : Fin n → ℝ) (_ : w ∈ Set.Icc (fun _ ↦ -π) (fun _ ↦ π)) :
      HasFDerivWithinAt f (f' w) (Set.Icc (fun _ ↦ -π) (fun _ ↦ π)) w := by
    apply HasFDerivAt.hasFDerivWithinAt
    unfold f'
    rw [ContinuousLinearMap.piMap, hasFDerivAt_pi]
    intro j
    by_cases h : j = i
    · simp only [h, Pi.map_apply, ↓reduceIte, ContinuousLinearMap.neg_comp,
        ContinuousLinearMap.id_comp]
      exact (hasFDerivAt_apply i w).neg
    · simpa [h] using hasFDerivAt_apply j w
  have hset : Set.Icc (fun _ ↦ -π) (fun _ ↦ π) = f '' Set.Icc (fun _ ↦ -π) (fun _ ↦ π) := by
    rw [← Set.pi_univ_Icc, Set.piMap_image_univ_pi]
    congrm Set.univ.pi fun j ↦ ?_
    by_cases h : j = i <;> simp [h]
  have hinj : Set.InjOn f (Set.Icc (fun _ ↦ -π) (fun _ ↦ π)) := by
    apply Function.Injective.injOn
    intro x y h
    rw [funext_iff] at h
    ext j
    specialize h j
    by_cases hj : j = i <;> simpa [f, hj] using h
  have hdet (w : Fin n → ℝ) : (f' w).det = -1 := by
    suffices ∏ x, (if x = i then -ContinuousLinearMap.id ℝ ℝ else ContinuousLinearMap.id ℝ ℝ) 1
        = -1 by
      simpa [f', ContinuousLinearMap.piMap, ContinuousLinearMap.det_pi]
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
    convert (show (1 : ℝ) * -1 = -1 by simp)
    · refine Finset.prod_eq_one fun j hj ↦ ?_
      have : ¬ j = i := by simpa using hj
      simp [this]
    · simp only [↓reduceIte]
      rfl
  conv_lhs => rw [hset]
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume measurableSet_Icc hf' hinj]
  simp_rw [hdet, abs_neg, abs_one, one_smul]
  congr with w
  congr with j
  · by_cases h : j = i <;> simp [f, h]
  · by_cases h : j = i <;> simp [f, h]

theorem bddBelow_φ : BddBelow (Set.range <| φ (n := n)) := by
  use 0
  simpa [mem_lowerBounds] using φ_nonneg

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
      (Set.Icc (fun _ ↦ -π) (fun _ ↦ π)) := by
  have hm : MeasurableSet (Set.Icc (fun x ↦ -π) fun x ↦ π : Set (Fin n → ℝ)) := by
    rw [← Set.pi_univ_Icc]
    apply MeasurableSet.pi Set.countable_univ fun i _ ↦ measurableSet_Icc
  refine IntegrableOn.of_bound ?_ ?_ (2⁻¹ * ∑ k, (x k : ℝ) ^ 2) ?_
  · simp [Real.volume_Icc_pi]
  · rw [← Measure.restrict_inter_add_diff _ (measurableSet_singleton 0)]
    rw [Set.inter_eq_right.mpr (by simp [Pi.le_def, pi_nonneg])]
    rw [Measure.restrict_singleton', zero_add]
    refine ContinuousOn.aestronglyMeasurable ?_ (hm.diff (measurableSet_singleton 0))
    refine ContinuousOn.div₀ (by fun_prop) (by fun_prop) ?_
    intro i hi
    simp only [Set.mem_diff, Set.mem_Icc, Set.mem_singleton_iff] at hi
    obtain ⟨⟨hi1, hi2⟩, hi3⟩ := hi
    contrapose! hi3 with hj
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun j _ ↦ by simpa using cos_le_one (i j))] at hj
    ext j
    rw [Pi.zero_apply, ← cos_eq_one_iff_of_lt_of_lt ((lt_of_lt_of_le (by grind [pi_pos]) (hi1 j)))
      ((hi2 j).trans_lt (by grind [pi_pos]))]
    simpa [sub_eq_zero] using hj j (Finset.mem_univ j)
  apply ae_restrict_of_forall_mem hm
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

theorem abs_φ_le (hn : 3 ≤ n) (x : Fin n → ℤ) :
    |φ x| ≤ (2 * π)⁻¹ ^ n * ∫ (w : Fin n → ℝ) in Set.Icc (fun _ ↦ -π) (fun _ ↦ π),
    1 / ∑ i, (1 - Real.cos (w i)) := by
  have : NeZero n := ⟨fun h ↦ by simp [h] at hn⟩
  have hn1 : 1 ≤ n := le_trans (by simp) hn
  have hn2 : 2 < n := lt_of_lt_of_le (by simp) hn
  have hn2' : (2 : ℝ) < Module.finrank ℝ (Fin n → ℝ) := by
    simpa using hn2
  unfold φ
  have hleft : 0 ≤ (2 * π)⁻¹ ^ n := by
    apply pow_nonneg
    simpa using pi_nonneg
  rw [abs_mul, abs_of_nonneg hleft]
  refine mul_le_mul_of_nonneg_left ?_ hleft
  rw [← norm_eq_abs]
  refine norm_integral_le_of_norm_le ?_ ?_
  · conv in fun w ↦ _ =>
      ext w
      conv in fun i ↦ _ =>
        ext i
        rw [show w i = 2 * (w i / 2) by simp [mul_div]]
        rw [cos_two_mul_eq_one_sub, sub_sub_cancel]
      rw [← Finset.mul_sum, mul_comm, ← div_div]
    apply Integrable.div_const
    suffices (fun (w : Fin n → ℝ) ↦ 1 / ∑ i, sin (w i / 2) ^ 2) =O[nhds 0] (‖·‖ ^ (-2 : ℤ)) by
      obtain ⟨c, hc⟩ := isBigO_iff.mp this
      obtain ⟨r, hr0, hr⟩ := Metric.eventually_nhds_iff_ball.mp hc
      simp_rw [norm_zpow, norm_norm, ← Real.rpow_intCast] at hr
      push_cast at hr
      rw [← IntegrableOn,
        ← Set.inter_union_diff (Set.Icc (fun _ ↦ -π) (fun _ ↦ π)) (Metric.ball 0 r),
        integrableOn_union]
      constructor
      · apply IntegrableOn.mono_set ?_ Set.inter_subset_right
        apply integrableOn_ball_of_norm_le_rpow (by simpa using hn1) hn2'
          (ae_restrict_of_forall_mem measurableSet_ball hr)
        apply StronglyMeasurable.aestronglyMeasurable
        fun_prop
      · apply ContinuousOn.integrableOn_compact (IsCompact.diff isCompact_Icc Metric.isOpen_ball)
        apply ContinuousOn.div₀ (by fun_prop) (by fun_prop)
        intro x hx
        obtain ⟨⟨hleft, hright⟩, hball⟩ : ((fun x ↦ -π) ≤ x ∧ x ≤ fun x ↦ π) ∧ r ≤ ‖x‖ := by
          simpa using hx
        contrapose! hball with hsum
        suffices x = 0 by simpa [this] using hr0
        rw [Finset.sum_eq_zero_iff_of_nonneg (fun j _ ↦ sq_nonneg _)] at hsum
        ext i
        specialize hsum i (Finset.mem_univ i)
        specialize hleft i
        specialize hright i
        rw [sq_eq_zero_iff, sin_eq_zero_iff_of_lt_of_lt ?_ ?_] at hsum
        · simpa using hsum
        · rw [lt_div_iff₀ (by simp)]
          refine lt_of_lt_of_le ?_ hleft
          simp [mul_two, pi_pos]
        · rw [div_lt_iff₀ (by simp)]
          refine lt_of_le_of_lt hright ?_
          simp [mul_two, pi_pos]
    simp_rw [← inv_eq_one_div, zpow_neg]
    refine IsBigO.inv_rev ?_ ?_
    · trans fun w ↦ (sin (‖w‖ / 2)) ^ 2
      · simp_rw [zpow_ofNat]
        apply IsBigO.pow
        rw [← isBigO_const_mul_left_iff (show (2⁻¹ : ℝ) ≠ 0 by simp)]
        simp_rw [mul_comm (2⁻¹ : ℝ), ← div_eq_mul_inv]
        apply IsEquivalent.isBigO
        have hinner : Tendsto (fun (w : Fin n → ℝ) ↦ ‖w‖ / 2) (𝓝 0) (𝓝 0) := by
          simpa using tendsto_norm_zero.div_const 2
        exact isEquivalent_sin.symm.comp_tendsto hinner
      · apply Filter.Eventually.isBigO
        rw [Metric.eventually_nhds_iff_ball]
        refine ⟨π, pi_pos, fun w hw ↦ ?_⟩
        have hw : ‖w‖ < π := by simpa using hw
        rw [norm_eq_abs]
        rw [abs_of_nonneg (sq_nonneg _)]
        obtain ⟨i, _, hi⟩ :
            ∃ i ∈ (Finset.univ : Finset (Fin n)), Finset.univ.sup (‖w ·‖₊) = ‖w i‖₊ :=
          Finset.exists_mem_eq_sup _ (by simp) _
        have hnorm : ‖w‖₊ = ‖w i‖₊ := hi ▸ Pi.nnnorm_def w
        have hnorm : ‖w‖ = |w i| := by simpa using congr(((↑) : _ → ℝ) $hnorm)
        rw [hnorm] at ⊢
        apply (Finset.single_le_sum (by simp [sq_nonneg]) (Finset.mem_univ i)).trans
        refine le_of_eq (Finset.sum_congr rfl fun i _ ↦ ?_)
        rw [sq_eq_sq_iff_abs_eq_abs]
        have habs : |w i| / 2 ≤ π := by
          apply div_le_of_le_mul₀ (by simp) pi_nonneg
          refine le_trans ?_ (le_trans hw.le (by simp [mul_two, pi_nonneg]))
          simpa using norm_le_pi_norm w i
        rw [Real.abs_sin_eq_sin_abs_of_abs_le_pi (by simpa [abs_div] using habs)]
        rw [Real.abs_sin_eq_sin_abs_of_abs_le_pi (by simpa [abs_div] using habs)]
        simp [abs_div]
    · apply Eventually.of_forall fun x ↦ ?_
      simp +contextual [zpow_eq_zero_iff]
  · refine Eventually.of_forall fun x ↦ ?_
    have hnonneg : 0 ≤ ∑ i, (1 - cos (x i)) := by
      refine Finset.sum_nonneg fun i _ ↦ ?_
      simpa using cos_le_one (x i)
    simp_rw [← mul_one_sub]
    rw [norm_eq_abs, ← Finset.mul_sum, ← div_div, abs_div, abs_div]
    rw [abs_of_nonneg hnonneg, abs_of_nonneg (by simpa using cos_le_one _), abs_of_nonneg (by simp)]
    refine div_le_div_of_nonneg_right ?_ hnonneg
    apply div_le_of_le_mul₀ (by simp) (by simp)
    rw [sub_le_comm]
    norm_num
    apply neg_one_le_cos

theorem bddAbove_φ (hn : 3 ≤ n) : BddAbove (Set.range <| φ (n := n)) := by
  obtain habs := abs_φ_le hn
  simp_rw [abs_le] at habs
  use (2 * π)⁻¹ ^ n * ∫ (w : Fin n → ℝ) in Set.Icc (fun _ ↦ -π) (fun _ ↦ π),
    1 / ∑ i, (1 - Real.cos (w i))
  simp_rw [mem_upperBounds, Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff]
  exact fun x ↦ (habs x).2

theorem φ_kirchhoff [NeZero n] (x : Fin n → ℤ) :
    ∑ k, (φ (x - Pi.single k 1) - φ x) + ∑ k, (φ (x + Pi.single k 1) - φ x) = unitCur 0 x := by
  rw [← Finset.sum_add_distrib]
  simp_rw [sub_add_sub_comm, ← two_mul]
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
      =ᵐ[volume.restrict (Set.Icc (fun _ ↦ -π) (fun _ ↦ π))] f := by
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
  rw [← fourier_unitCur]

theorem isElectricPotential_φ [NeZero n] (a b : Fin n → ℤ) :
    IsElectricPotential (unitCur a - unitCur b) (fun x ↦ φ (x - a) - φ (x - b)) where
  kirchhoff x := by
    conv_lhs =>
      left
      conv in fun k ↦ _ =>
        ext k
        rw [sub_sub_sub_comm]
        rw [sub_right_comm _ _ a]
        rw [sub_right_comm _ _ b]
      rw [Finset.sum_sub_distrib]
    conv_lhs =>
      right
      conv in fun k ↦ _ =>
        ext k
        rw [sub_sub_sub_comm]
        rw [add_sub_right_comm]
        rw [add_sub_right_comm]
      rw [Finset.sum_sub_distrib]
    rw [sub_add_sub_comm, φ_kirchhoff, φ_kirchhoff, Pi.sub_apply]
    unfold unitCur
    congrm ?_ - ?_
    · by_cases h : x = a
      · simp [h]
      · have : x - a ≠ 0 := sub_eq_zero.ne.mpr h
        simp [h, this]
    · by_cases h : x = b
      · simp [h]
      · have : x - b ≠ 0 := sub_eq_zero.ne.mpr h
        simp [h, this]
  bddAbove := sorry
  bddBelow := sorry
  /-boundary := by
    unfold φ
    conv in fun x ↦ _ =>
      ext x
      rw [← mul_sub]
      rw [← integral_sub sorry sorry]
      conv in fun w ↦ _ - _ =>
        ext w
        rw [← sub_div, sub_sub_sub_cancel_left, cos_sub_cos, ← Finset.sum_add_distrib,
          ← Finset.sum_sub_distrib]
        conv in fun k ↦ _ * _ + _ * _ =>
          ext k
          rw [← add_mul, ← Int.cast_add, ← Pi.add_apply, sub_add_sub_comm, ← two_mul]
        conv in fun k ↦ _ * _ - _ * _ =>
          ext k
          rw [← sub_mul, ← Int.cast_sub, ← Pi.sub_apply, sub_sub_sub_cancel_left]

    sorry
-/
