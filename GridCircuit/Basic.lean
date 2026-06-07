import GridCircuit.Misc
import GridCircuit.Bessel

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
theorem φ_reflect (x : Fin n → ℤ) (i : Fin n) : φ (Function.update x i (-x i)) = φ x := by
  unfold φ
  let f : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) := ContinuousLinearMap.piMap
    fun j ↦ if j = i then -(ContinuousLinearMap.id _ _) else (ContinuousLinearMap.id _ _)
  let f' (_ : Fin n → ℝ) : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) := f
  have hf' (w : Fin n → ℝ) (_ : w ∈ Set.Icc (fun _ ↦ -π) (fun _ ↦ π)) :
      HasFDerivWithinAt f (f' w) (Set.Icc (fun _ ↦ -π) (fun _ ↦ π)) w :=
    f.hasFDerivAt.hasFDerivWithinAt
  have hset : Set.Icc (fun _ ↦ -π) (fun _ ↦ π) = f '' Set.Icc (fun _ ↦ -π) (fun _ ↦ π) := by
    unfold f
    rw [ContinuousLinearMap.coe_piMap', ← Set.pi_univ_Icc, Set.piMap_image_univ_pi]
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
      simpa [f', f, ContinuousLinearMap.piMap, ContinuousLinearMap.det_pi]
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

@[simp]
theorem φ_neg (x : Fin n → ℤ) : φ (-x) = φ x := by
  unfold φ
  let f : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
    ContinuousLinearMap.piMap fun j ↦ -(ContinuousLinearMap.id _ _)
  let f' (_ : Fin n → ℝ) : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) := f
  have hf' (w : Fin n → ℝ) (_ : w ∈ Set.Icc (fun _ ↦ -π) (fun _ ↦ π)) :
      HasFDerivWithinAt f (f' w) (Set.Icc (fun _ ↦ -π) (fun _ ↦ π)) w :=
    f.hasFDerivAt.hasFDerivWithinAt
  have hset : Set.Icc (fun _ ↦ -π) (fun _ ↦ π) = f '' Set.Icc (fun _ ↦ -π) (fun _ ↦ π) := by
    unfold f
    rw [ContinuousLinearMap.coe_piMap', ← Set.pi_univ_Icc, Set.piMap_image_univ_pi]
    congrm Set.univ.pi fun j ↦ ?_
    simp
  have hinj : Set.InjOn f (Set.Icc (fun _ ↦ -π) (fun _ ↦ π)) := by
    apply Function.Injective.injOn
    intro x y h
    rw [funext_iff] at h
    ext j
    specialize h j
    simpa [f] using h
  have hdet (w : Fin n → ℝ) : |(f' w).det| = 1 := by
    unfold f' f
    rw [ContinuousLinearMap.det, ContinuousLinearMap.coe_piMap, LinearMap.piMap, LinearMap.det_pi]
    simp
  conv_lhs => rw [hset]
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume measurableSet_Icc hf' hinj]
  simp_rw [hdet, one_smul]
  simp [f]

@[simp]
theorem φ_perm (x : Fin n → ℤ) (p : Fin n ≃ Fin n) : φ (x ∘ p) = φ x := by
  unfold φ
  let f : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
    ContinuousLinearMap.pi fun j ↦ ContinuousLinearMap.proj (p j)
  let f' (_ : Fin n → ℝ) : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) := f
  have hf' (w : Fin n → ℝ) (_ : w ∈ Set.Icc (fun _ ↦ -π) (fun _ ↦ π)) :
      HasFDerivWithinAt f (f' w) (Set.Icc (fun _ ↦ -π) (fun _ ↦ π)) w :=
    f.hasFDerivAt.hasFDerivWithinAt
  have hset : Set.Icc (fun _ ↦ -π) (fun _ ↦ π) = f '' Set.Icc (fun _ ↦ -π) (fun _ ↦ π) := by
    ext x
    suffices (x ∈ Set.Icc (fun x ↦ -π) fun x ↦ π) ↔
        ∃ w ∈ Set.Icc (fun x ↦ -π) fun x ↦ π, (fun i ↦ w (p i)) = x by
      simpa [f]
    simp_rw [← Set.pi_univ_Icc, Set.mem_univ_pi]
    refine ⟨fun h ↦ ?_, fun ⟨y, hy, hyeq⟩ ↦ ?_⟩
    · use x ∘ p.symm
      simp only [Function.comp_apply, Equiv.symm_apply_apply, and_true]
      intro j
      exact h (p.symm j)
    · rw [funext_iff] at hyeq
      intro j
      rw [← hyeq]
      exact hy (p j)
  have hinj : Set.InjOn f (Set.Icc (fun _ ↦ -π) (fun _ ↦ π)) := by
    apply Function.Injective.injOn
    intro a b h
    rw [funext_iff] at ⊢ h
    intro i
    simpa [f] using h (p.symm i)
  have hperm (w : Fin n → ℝ) : f' w = (Equiv.Perm.permMatrix ℝ p).toLin' := by
    ext r j
    simp [f', f]
    by_cases h : p j = r <;> simp [h]
  have hdet (w : Fin n → ℝ) : |(f' w).det| = 1 := by
    rw [ContinuousLinearMap.det, hperm w, LinearMap.det_toLin', Matrix.det_permutation]
    norm_cast
    simp
  conv_lhs => rw [hset]
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume measurableSet_Icc hf' hinj]
  simp_rw [hdet, one_smul]
  congr with w
  congrm (1 - cos ?_) / ?_
  · simp only [Function.comp_apply, ContinuousLinearMap.coe_pi', ContinuousLinearMap.proj_apply, f]
    exact Finset.sum_equiv p (by simp) (by simp)
  · simp only [ContinuousLinearMap.coe_pi', ContinuousLinearMap.proj_apply, f]
    exact Finset.sum_equiv p (by simp) (by simp)

theorem φ_single_perm (e e' : Fin n) (l : ℤ) :
    φ (Pi.single e l) = φ (Pi.single e' l) := by
  let p : Fin n ≃ Fin n := Equiv.swap e e'
  have : Pi.single e l ∘ p = Pi.single e' l := by
    rw [Pi.single_comp_equiv]
    simp [p]
  rw [← this, φ_perm]

theorem bddBelow_φ : BddBelow (Set.range <| φ (n := n)) := by
  use 0
  simpa [mem_lowerBounds] using φ_nonneg

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

theorem φ_2d :
    φ = fun (x : Fin 2 → ℤ) ↦ (4 * π ^ 2)⁻¹ * ∫ w in Set.Icc (-π) π ×ˢ Set.Icc (-π) π,
    (1 - cos (x 0 * w.1 + x 1 * w.2)) / (4 - (2 * cos w.1 + 2 * cos w.2)) := by
  unfold φ
  ext x
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
  rw [← (measurePreserving_finTwoArrow _).integral_comp']
  rw [← Measure.restrict_pi_pi]
  simp only [mul_inv_rev, Fin.sum_univ_two, Fin.isValue, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat, Set.pi_univ_Icc,
    MeasurableEquiv.finTwoArrow_apply]
  congr
  · simp [mul_pow]
    norm_num
  · norm_num


theorem eq_zero_of_φ_2d_deno_le_zero
    {p : ℝ × ℝ} (hp : p ∈ Set.Icc (-π) π ×ˢ Set.Icc (-π) π)
    (h : 4 - (2 * cos p.1 + 2 * cos p.2) ≤ 0) : p = 0 := by
  rw [show 4 - (2 * cos p.1 + 2 * cos p.2) = 2 * (1 - cos p.1) + 2 * (1 - cos p.2) by ring] at h
  have h := le_antisymm h (add_nonneg (by simpa using cos_le_one _) (by simpa using cos_le_one _))
  rw [(add_eq_zero_iff_of_nonneg (by simpa using cos_le_one _)
    (by simpa using cos_le_one _))] at h
  simp only [mul_eq_zero, OfNat.ofNat_ne_zero, sub_eq_zero, false_or] at h
  have h1 := h.1.symm
  have h2 := h.2.symm
  rw [Set.mem_prod] at hp
  rw [Real.cos_eq_one_iff_of_lt_of_lt (lt_of_lt_of_le (by simp [pi_pos]) hp.1.1)
    (lt_of_le_of_lt hp.1.2 (by simp [pi_pos]))] at h1
  rw [Real.cos_eq_one_iff_of_lt_of_lt (lt_of_lt_of_le (by simp [pi_pos]) hp.2.1)
    (lt_of_le_of_lt hp.2.2 (by simp [pi_pos]))] at h2
  ext
  · exact h1
  · exact h2

theorem two_mul_one_sub_cos_le (x : ℝ) : 2 * (1 - cos x) ≤ x ^ 2 := by
  grw [← one_sub_sq_div_two_le_cos]
  apply le_of_eq
  ring

theorem one_sub_cos_le (x : ℝ) : (1 - cos x) ≤ x ^ 2 / 2 := by
  grw [← two_mul_one_sub_cos_le]
  simp

theorem φ_integrable_2d (x : Fin 2 → ℤ) :
    IntegrableOn (fun w ↦ (1 - cos (x 0 * w.1 + x 1 * w.2)) / (4 - (2 * cos w.1 + 2 * cos w.2)))
    (Set.Icc (-π) π ×ˢ Set.Icc (-π) π) volume := by
  rw [Measure.volume_eq_prod, IntegrableOn, ← Measure.prod_restrict]
  rw [← (measurePreserving_finTwoArrow _).integrable_comp (by
    apply StronglyMeasurable.aestronglyMeasurable
    fun_prop
  )]
  rw [← Measure.restrict_pi_pi, ← IntegrableOn, ← MeasureTheory.volume_pi, Set.pi_univ_Icc]
  convert integrable_φ x with x
  simp [show (2 : ℝ) * 2 = 4 by norm_num]

theorem φ_integrable_2d' (x : Fin 2 → ℤ) :
    IntegrableOn (fun w ↦ ((1 - cos (x 0 * w.1 + x 1 * w.2)) / (w.1 ^ 2 + w.2 ^ 2)))
      (Set.Icc (-π) π ×ˢ Set.Icc (-π) π) volume := by
  apply Integrable.mono_nonneg (φ_integrable_2d x) ?_ ?_ ?_
  · apply AEStronglyMeasurable.restrict
    apply StronglyMeasurable.aestronglyMeasurable
    fun_prop
  · refine Eventually.of_forall fun p ↦ div_nonneg ?_ ?_
    · simpa using cos_le_one _
    · positivity
  · refine ae_restrict_of_forall_mem (by measurability) fun p hp ↦ ?_
    by_cases hp0 : p = 0
    · simp [hp0]
    apply div_le_div_of_nonneg_left (by simpa using cos_le_one _)
    · contrapose! hp0
      apply eq_zero_of_φ_2d_deno_le_zero hp hp0
    rw [show 4 - (2 * cos p.1 + 2 * cos p.2) = 2 * (1 - cos p.1) + 2 * (1 - cos p.2) by ring]
    exact add_le_add (two_mul_one_sub_cos_le _) (two_mul_one_sub_cos_le _)

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

theorem one_isLittleO_log :
    (1 : (Fin 2 → ℤ) → ℝ) =o[cofinite] fun (x : Fin 2 → ℤ) ↦ log ((x 0) ^ 2 + (x 1) ^ 2) := by
  rw [isLittleO_iff]
  intro c hc
  suffices {x : Fin 2 → ℤ | c * |log (x 0 ^ 2 + x 1 ^ 2)| < 1}.Finite by simpa
  conv in fun x ↦ _ =>
    ext x
    rw [abs_of_nonneg (by
      norm_cast
      apply Real.log_intCast_nonneg
    )]
  suffices ({x : ℤ | c * log (x ^ 2) < 1}).Finite by
    have : ((Set.univ : Set (Fin 2)).pi fun _ ↦ {x : ℤ | c * log (x ^ 2) < 1}).Finite :=
      Set.Finite.pi fun _ ↦ this
    apply this.subset
    suffices (∀ (x : Fin 2 → ℤ), c * log (x 0 ^ 2 + x 1 ^ 2) < 1 → c * (log (x 0 ^ 2)) < 1) ∧
        ∀ (x : Fin 2 → ℤ), c * log (x 0 ^ 2 + x 1 ^ 2) < 1 → c * log (x 1 ^ 2) < 1 by
      simpa [Set.subset_pi_iff]
    constructor
    <;> intro x hx
    <;> refine lt_of_le_of_lt ?_ hx
    <;> refine mul_le_mul_of_nonneg_left ?_ hc.le
    · by_cases h0 : x 0 = 0
      · simpa [h0] using Real.log_intCast_nonneg (x 1)
      exact Real.log_le_log (by simpa [sq_pos_iff] using h0) (by simpa using sq_nonneg _)
    · by_cases h0 : x 1 = 0
      · simpa [h0] using Real.log_intCast_nonneg (x 0)
      exact Real.log_le_log (by simpa [sq_pos_iff] using h0) (by simpa using sq_nonneg _)
  simp only [log_pow, Nat.cast_ofNat, ← mul_assoc]
  apply (Set.finite_Icc (-⌈exp (c * 2)⁻¹⌉) (⌈exp (c * 2)⁻¹⌉)).subset
  intro x hx
  rw [Set.mem_setOf_eq, ← lt_inv_mul_iff₀ (mul_pos hc (by simp)), mul_one] at hx
  rcases lt_trichotomy x 0 with hx0 | hx0 | hx0
  · set y := -x
    obtain hy : x = -y := by simp [y]
    rw [hy] at ⊢ hx0 hx
    rw [Int.cast_neg, log_neg_eq_log] at hx
    rw [log_lt_iff_lt_exp (by simpa using hx0)] at hx
    constructor
    · rw [neg_le_neg_iff, Int.le_ceil_iff]
      apply lt_trans (by simp) hx
    · exact le_trans hx0.le (by simp [Int.ceil_nonneg, exp_nonneg])
  · simp [hx0, Int.ceil_nonneg, exp_nonneg]
  · rw [log_lt_iff_lt_exp (by simpa using hx0)] at hx
    constructor
    · exact le_trans (by simp [Int.ceil_nonneg, exp_nonneg]) hx0.le
    · rw [Int.le_ceil_iff]
      apply lt_trans (by simp) hx

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

theorem disk_subset :
    {p | p.1 ^ 2 + p.2 ^ 2 ≤ 1} ⊆ Set.Icc (-(1 : ℝ)) 1 ×ˢ Set.Icc (-(1 : ℝ)) 1 := by
  intro p hp
  suffices p.1 ^ 2 ≤ 1 ^ 2 ∧ p.2 ^ 2 ≤ 1 ^ 2 by
    rw [Set.mem_prod]
    convert this using 1 <;> simp [abs_le]
  simp only [Set.mem_setOf_eq] at hp
  contrapose! +distrib hp
  obtain hp | hp := hp
  · exact lt_add_of_lt_of_nonneg (by simpa using hp) (sq_nonneg _)
  · exact lt_add_of_nonneg_of_lt (sq_nonneg _) (by simpa using hp)

theorem disk_subset' : {p | p.1 ^ 2 + p.2 ^ 2 ≤ 1} ⊆ Set.Icc (-π) π ×ˢ Set.Icc (-π) π := by
  have honepi : 1 ≤ π := le_trans (by simp) pi_gt_three.le
  apply disk_subset.trans
  simp only [Set.Icc_prod_Icc]
  apply Set.Icc_subset_Icc
  · simp [honepi]
  · simp [honepi]

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

theorem isEquivalent_circle_integral :
    (fun x ↦ (∫ (w : ℝ × ℝ) in {p | p.1 ^ 2 + p.2 ^ 2 ≤ 1},
      (1 - cos (x 0 * w.1 + x 1 * w.2)) / (4 - (2 * cos w.1 + 2 * cos w.2))) -
    ∫ (w : ℝ × ℝ) in {p | p.1 ^ 2 + p.2 ^ 2 ≤ 1}, (
      1 - cos (x 0 * w.1 + x 1 * w.2)) / (w.1 ^ 2 + w.2 ^ 2)) =O[cofinite]
    (1 : (Fin 2 → ℤ) → ℝ) := by
  have honepi : 1 < π := lt_trans (by simp) pi_gt_three
  rw [isBigO_iff]
  use ∫ (w : ℝ × ℝ) in {p | p.1 ^ 2 + p.2 ^ 2 ≤ 1},
    2 * ‖((4 - (2 * cos w.1 + 2 * cos w.2)))⁻¹ - (w.1 ^ 2 + w.2 ^ 2)⁻¹‖
  refine Eventually.of_forall fun x ↦ ?_
  rw [Pi.one_apply, norm_one, mul_one]
  rw [← integral_sub (IntegrableOn.mono_set (φ_integrable_2d x) disk_subset')
    (IntegrableOn.mono_set (φ_integrable_2d' x) disk_subset')]
  conv in fun w ↦ _ - _ =>
    ext w
    rw [div_eq_mul_inv, div_eq_mul_inv, ← mul_sub]
  refine norm_integral_le_of_norm_le ?_ ?_; swap
  · refine Eventually.of_forall fun w ↦ ?_
    rw [norm_mul]
    refine mul_le_mul_of_nonneg_right ?_ (by simp)
    rw [norm_eq_abs, abs_of_nonneg (by simpa using cos_le_one _)]
    rw [sub_le_comm]
    norm_num
    exact neg_one_le_cos _
  apply IntegrableOn.of_bound (measure_lt_top_mono disk_subset' (by
    simp only [Measure.volume_eq_prod, Measure.prod_prod, volume_Icc, sub_neg_eq_add]
    finiteness)) (by fun_prop) (2 * (4⁻¹ * (2 * (π / 4) ^ 2))) ?_
  apply ae_restrict_of_forall_mem (by measurability) fun w hw ↦ ?_
  by_cases h0 : w = 0
  · rw [h0]
    norm_num
    positivity
  have hw' := Set.mem_prod.mp <| Set.mem_of_mem_of_subset hw disk_subset
  have hw1l : -1 < w.1 / 2 := by
    rw [lt_div_iff₀ (by simp)]
    exact lt_of_lt_of_le (by simp) hw'.1.1
  have hw2l : -1 < w.2 / 2 := by
    rw [lt_div_iff₀ (by simp)]
    exact lt_of_lt_of_le (by simp) hw'.2.1
  have hw1r : w.1 / 2 < 1 := by
    rw [div_lt_iff₀ (by simp)]
    exact hw'.1.2.trans_lt (by simp)
  have hw2r : w.2 / 2 < 1 := by
    rw [div_lt_iff₀ (by simp)]
    exact hw'.2.2.trans_lt (by simp)
  rw [norm_mul, norm_norm, norm_eq_abs, norm_eq_abs, abs_of_nonneg (by simp)]
  refine mul_le_mul_of_nonneg_left ?_ (by simp)
  rw [show 4 - (2 * cos w.1 + 2 * cos w.2) =
    2 * (1 - cos (2 * (w.1 / 2))) + 2 * (1 - cos (2 * (w.2 / 2))) by ring_nf]
  rw [cos_two_mul_eq_one_sub, cos_two_mul_eq_one_sub, sub_sub_cancel, sub_sub_cancel]
  have : sin (w.1 / 2) ^ 2 + sin (w.2 / 2) ^ 2 ≠ 0 := by
    contrapose! h0
    rw [add_eq_zero_iff_of_nonneg (sq_nonneg _) (sq_nonneg _), sq_eq_zero_iff, sq_eq_zero_iff] at h0
    rw [sin_eq_zero_iff_of_lt_of_lt (lt_trans (by simpa using honepi) hw1l) (hw1r.trans honepi),
      sin_eq_zero_iff_of_lt_of_lt (lt_trans (by simpa using honepi) hw2l) (hw2r.trans honepi)] at h0
    ext
    · simpa using h0.1
    · simpa using h0.2
  have : w.1 ^ 2 + w.2 ^ 2 ≠ 0 := by
    contrapose! h0
    rw [add_eq_zero_iff_of_nonneg (sq_nonneg _) (sq_nonneg _), sq_eq_zero_iff, sq_eq_zero_iff] at h0
    ext
    · simpa using h0.1
    · simpa using h0.2
  suffices |4⁻¹ * (((w.1 / 2 + sin (w.1 / 2)) * (w.1 / 2 - sin (w.1 / 2)) +
      (w.2 / 2 + sin (w.2 / 2)) * (w.2 / 2 - sin (w.2 / 2))) /
      ((sin (w.1 / 2) ^ 2 + sin (w.2 / 2) ^ 2) * ((w.1 / 2) ^ 2 + (w.2 / 2) ^ 2)))| ≤
      4⁻¹ * (2 * (π / 4) ^ 2) by
    convert this using 2
    field
  rw [abs_mul, abs_div, abs_of_nonneg (by simp)]
  refine mul_le_mul_of_nonneg_left ?_ (by simp)
  apply div_le_of_le_mul₀ (abs_nonneg _) (by positivity)
  apply (abs_add_le _ _).trans
  conv_rhs => rw [abs_of_nonneg (by positivity)]
  trans (2 * (π / 4) ^ 2 *
    (sin (w.1 / 2) ^ 2 * (w.1 / 2) ^ 2 + sin (w.2 / 2) ^ 2 * (w.2 / 2) ^ 2)); swap
  · refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [add_mul, mul_add, mul_add]
    rw [← sub_nonneg]
    ring_nf
    positivity
  rw [mul_add]
  apply add_le_add
  · apply sin_cube_bound ⟨hw1l.le, hw1r.le⟩
  · apply sin_cube_bound ⟨hw2l.le, hw2r.le⟩

theorem φ_equiv_log_2d :
    (φ (n := 2) - fun (x : Fin 2 → ℤ) ↦ (4 * π)⁻¹ * log (x 0 ^ 2 + x 1 ^ 2)) =O[cofinite]
    (1 : (Fin 2 → ℤ) → ℝ) := by
  rw [φ_2d]
  let disk : Set (ℝ × ℝ) := {p | p.1 ^ 2 + p.2 ^ 2 ≤ 1}
  let odisk : Set (ℝ × ℝ) := {p | p.1 ^ 2 + p.2 ^ 2 < 1}
  have hodisk : IsOpen odisk := by
    unfold odisk
    have : Continuous (fun (p : ℝ × ℝ) ↦ p.1 ^ 2 + p.2 ^ 2) := by fun_prop
    apply this.isOpen_preimage _ (isOpen_Iio' 1)
  have hdiskdisk : odisk ⊆ disk := by
    grind
  have hdiskmeasureable : MeasurableSet disk := by measurability
  conv_lhs =>
    left
    ext x
    rw [← integral_inter_add_diff hdiskmeasureable (φ_integrable_2d _),
      Set.inter_eq_right.mpr disk_subset']
    rw [mul_add]
  rw [← Pi.add_def, add_sub_right_comm]
  apply IsBigO.add; swap
  · apply IsBigO.const_mul_left
    rw [isBigO_iff]
    use ∫ w in Set.Icc (-π) π ×ˢ Set.Icc (-π) π \ disk, 2 / (4 - (2 * cos w.1 + 2 * cos w.2))
    refine Eventually.of_forall fun x ↦ ?_
    rw [norm_eq_abs, norm_eq_abs, abs_of_nonneg (integral_nonneg (by
      intro x
      apply div_nonneg
      · simpa using cos_le_one _
      · grw [sub_nonneg, cos_le_one, cos_le_one]
        norm_num))]
    rw [Pi.one_apply, abs_one, mul_one]
    apply setIntegral_mono ?_ ?_ ?_
    · refine IntegrableOn.mono_set ?_ (Set.diff_subset_diff_right hdiskdisk)
      apply ContinuousOn.integrableOn_compact
        ((IsCompact.prod isCompact_Icc isCompact_Icc).diff hodisk)
      apply ContinuousOn.div (by fun_prop) (by fun_prop)
      intro p hp
      rw [Set.mem_diff] at hp
      obtain ⟨hp1, hp2⟩ := hp
      contrapose! hp2
      simp [odisk, eq_zero_of_φ_2d_deno_le_zero hp1 hp2.le]
    · refine IntegrableOn.mono_set ?_ (Set.diff_subset_diff_right hdiskdisk)
      apply ContinuousOn.integrableOn_compact
        ((IsCompact.prod isCompact_Icc isCompact_Icc).diff hodisk)
      apply ContinuousOn.div (by fun_prop) (by fun_prop)
      intro p hp
      rw [Set.mem_diff] at hp
      obtain ⟨hp1, hp2⟩ := hp
      contrapose! hp2
      simp [odisk, eq_zero_of_φ_2d_deno_le_zero hp1 hp2.le]
    · intro p
      refine div_le_div_of_nonneg_right ?_ ?_
      · rw [sub_le_comm]
        norm_num
        exact neg_one_le_cos _
      · rw [show 4 - (2 * cos p.1 + 2 * cos p.2) = 2 * (1 - cos p.1) + 2 * (1 - cos p.2) by ring]
        exact add_nonneg (by simpa using cos_le_one _) (by simpa using cos_le_one _)
  rw [← (isEquivalent_circle_integral.const_mul_left (4 * π ^ 2)⁻¹).sub_iff_left]
  simp_rw [Pi.sub_apply, mul_sub, sub_sub_sub_cancel_left]
  let zr (x : Fin 2 → ℤ) : ℝ × ℝ := (x 0, x 1)
  change ((fun (x : ℝ × ℝ) ↦ ((4 * π ^ 2)⁻¹ * ∫ (w : ℝ × ℝ) in {p | p.1 ^ 2 + p.2 ^ 2 ≤ 1},
      (1 - cos (x.1 * w.1 + x.2 * w.2)) / (w.1 ^ 2 + w.2 ^ 2)) -
      (4 * π)⁻¹ * log (x.1 ^ 2 + x.2 ^ 2)) ∘ zr) =O[cofinite] ((1 : (ℝ × ℝ) → ℝ) ∘ zr)
  rw [← isBigO_map]
  refine IsBigO.mono ?_ cofinite_int_le_cobounded_real
  rw [← map_polarCoord_eq_cobounded, isBigO_map]
  change ((fun (x : ℝ × ℝ) ↦ ((4 * π ^ 2)⁻¹ * ∫ (w : ℝ × ℝ) in {p | p.1 ^ 2 + p.2 ^ 2 ≤ 1},
      (1 - cos ((x.1 * cos x.2) * w.1 + (x.1 * sin x.2) * w.2)) / (w.1 ^ 2 + w.2 ^ 2)) -
      (4 * π)⁻¹ * log ((x.1 * cos x.2) ^ 2 + (x.1 * sin x.2) ^ 2)))
      =O[atTop ×ˢ 𝓟 (Set.Icc (-π) π)] ((1 : (ℝ × ℝ) → ℝ))
  conv_lhs =>
    ext x
    rw [← integral_comp_polarCoord_symm_disk]
    simp only [mul_pow, ← mul_add, cos_sq_add_sin_sq, mul_one, smul_eq_mul]
    rw [log_pow, Nat.cast_ofNat, ← mul_assoc]
    rw [show (4 * π)⁻¹ * 2 = (2 * π)⁻¹ by ring]
    conv in fun p ↦ _ =>
      ext p
      rw [mul_mul_mul_comm x.1 _ p.1, mul_mul_mul_comm x.1 _ p.1]
      rw [← mul_add, mul_comm (cos x.2), mul_comm (sin x.2), ← cos_sub]
      rw [mul_comm p.1, div_mul]
      rw [show p.1 ^ 2 / p.1 = p.1 by grind]
    rw [Measure.volume_eq_prod, setIntegral_prod _ (integrable_bessel _ _)]
    simp only
    conv in fun r ↦ _ =>
      ext r
      rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by simp [pi_nonneg])]
      rw [intervalIntegral.integral_comp_sub_right (fun θ ↦ (1 - cos (x.1 * r * cos θ)) / r) x.2]
      rw [show π - x.2 = -π - x.2 + 2 * π by ring]
      rw [Function.Periodic.intervalIntegral_add_eq (by intro x; simp) _ (-π)]
      rw [show -π + 2 * π = π by ring]
      conv in fun θ ↦ _ =>
        ext θ
        rw [show (1 - cos (x.1 * r * cos θ)) / r =
            x.1 • ((1 - cos (x.1 * r * cos θ)) / (x.1 * r)) by
          by_cases h0 : x.1 = 0
          · simp [h0]
          nth_rw 3 [mul_comm x.1 r]
          rw [← div_div]
          rw [smul_eq_mul, mul_div_cancel₀ _ h0]]
      rw [intervalIntegral.integral_smul]
    rw [← intervalIntegral.integral_of_le (by simp), intervalIntegral.integral_smul]
    rw [intervalIntegral.smul_integral_comp_mul_left
      (fun r ↦ ∫ θ in -π..π, (1 - cos (r * cos θ)) / r) x.1]
    rw [mul_zero, mul_one]
    rw [show (4 * π ^ 2)⁻¹ = (2 * π)⁻¹ * (2 * π)⁻¹ by ring]
    rw [mul_assoc, ← mul_sub]
  apply IsBigO.const_mul_left
  exact asymptotic_bessel.comp_fst _

-- Should Fix Asymptotics.isBigO_one_nat_atTop_iff
theorem bounded_of_isBigO_cofinite {α : Type*} {f : α → ℝ} (hf : f =O[cofinite] (1 : α → ℝ)) :
    ∃ c : ℝ, ∀ x, |f x| ≤ c := by
  rw [isBigO_cofinite_iff (by simp)] at hf
  simpa using hf

theorem φ_2d_sub_log_bounded :
    ∃ c : ℝ, ∀ x : Fin 2 → ℤ, |φ x - (4 * π)⁻¹ * log (x 0 ^ 2 + x 1 ^ 2)| ≤ c :=
  bounded_of_isBigO_cofinite φ_equiv_log_2d

theorem log_shift_equiv (a b : ℤ) :
    (fun x ↦ log ((x 0 + a) ^ 2 + (x 1 + b) ^ 2) - log (x 0 ^ 2 + x 1 ^ 2)) =O[cofinite]
    (1 : (Fin 2 → ℤ) → ℝ) := by
  rw [isBigO_iff]
  use 3 * (a ^ 2 + b ^ 2)
  rw [eventually_cofinite]
  apply (show Set.Finite ({0, -![a, b]} : Set (Fin 2 → ℤ)) by simp).subset
  intro x
  contrapose
  intro h
  suffices |log ((x 0 + a) ^ 2 + (x 1 + b) ^ 2) - log (x 0 ^ 2 + x 1 ^ 2)| ≤
      3 * (a ^ 2 + b ^ 2) by
    simpa
  wlog h0 : 0 ≤ log ((x 0 + a) ^ 2 + (x 1 + b) ^ 2) - log (x 0 ^ 2 + x 1 ^ 2)
  · have h' : -x -![a, b] ∉ ({0, -![a, b]} : Set (Fin 2 → ℤ)) := by grind
    convert this a b h' ?_ using 1
    · rw [abs_sub_comm]
      simp
      ring_nf
    · rw [not_le, sub_neg] at h0
      rw [sub_nonneg]
      convert h0.le using 1
      · simp
        ring_nf
      · simp
  rw [abs_of_nonneg h0]
  have habsq : (x 0 + a : ℝ) ^ 2 + (x 1 + b : ℝ) ^ 2 ≠ 0 := by
    contrapose! h
    rw [add_eq_zero_iff_of_nonneg (sq_nonneg _) (sq_nonneg _), sq_eq_zero_iff, sq_eq_zero_iff] at h
    norm_cast at h
    suffices x = ![-a, -b] by simp [this]
    ext i
    fin_cases i
    · simp
      linear_combination h.1
    · simp
      linear_combination h.2
  have hsq : (x 0 : ℝ) ^ 2 + (x 1 : ℝ) ^ 2 ≠ 0 := by
    contrapose! h
    rw [add_eq_zero_iff_of_nonneg (sq_nonneg _) (sq_nonneg _), sq_eq_zero_iff, sq_eq_zero_iff] at h
    norm_cast at h
    suffices x = ![0, 0] by simp [this]
    ext i
    fin_cases i
    · simpa using h.1
    · simpa using h.2
  have hsq' : 0 < (x 0 : ℝ) ^ 2 + (x 1 : ℝ) ^ 2 := by positivity
  rw [← log_div habsq hsq]
  apply (log_le_sub_one_of_pos (div_pos (by positivity) hsq')).trans
  rw [show ((x 0 + a) ^ 2 + (x 1 + b) ^ 2 : ℝ) =
    x 0 ^ 2 + x 1 ^ 2 + (a ^ 2 + b ^ 2 + (2 * (a * x 0) + 2 * (b * x 1))) by ring]
  rw [← one_add_div hsq]
  rw [add_sub_cancel_left]
  rw [div_le_iff₀ hsq']
  rw [show (3 * (a ^ 2 + b ^ 2) * (x 0 ^ 2 + x 1 ^ 2) : ℝ) =
    (a ^ 2 + b ^ 2) * (x 0 ^ 2 + x 1 ^ 2) +
    (2 * (((a * x 0) ^ 2 + (b * x 0) ^ 2)) + 2 * ((a * x 1) ^ 2 + (b * x 1) ^ 2)) by ring]
  apply add_le_add
  · apply le_mul_of_one_le_right (add_nonneg (sq_nonneg _) (sq_nonneg _))
    norm_cast
    rw [← Int.sub_one_lt_iff, sub_self]
    exact_mod_cast hsq'
  · apply add_le_add
    · refine mul_le_mul_of_nonneg_left ?_ (by simp)
      apply le_add_of_le_of_nonneg (by exact_mod_cast Int.le_self_sq _) (sq_nonneg _)
    · refine mul_le_mul_of_nonneg_left ?_ (by simp)
      apply le_add_of_nonneg_of_le (sq_nonneg _) (by exact_mod_cast Int.le_self_sq _)

theorem log_shift_equiv' (a b c d : ℤ) :
    (fun x ↦ log ((x 0 - a) ^ 2 + (x 1 - b) ^ 2) - log ((x 0 - c) ^ 2 + (x 1 - d) ^ 2))
    =O[cofinite] (1 : (Fin 2 → ℤ) → ℝ) := by
  convert (log_shift_equiv (-a) (-b)).sub (log_shift_equiv (-c) (-d)) using 2 with x
  push_cast
  simp [← sub_eq_add_neg]

theorem bound_φ_2d (a b : Fin 2 → ℤ) : ∃ c, ∀ x, |φ (x - a) - φ (x - b)| ≤ c := by
  obtain ⟨c, h⟩ := φ_2d_sub_log_bounded
  obtain ⟨d, h'⟩ := bounded_of_isBigO_cofinite (log_shift_equiv' (a 0) (a 1) (b 0) (b 1))
  use c + ((4 * π)⁻¹ * d + c)
  intro x
  apply (abs_sub_le _ ((4 * π)⁻¹ * log ((x - a) 0 ^ 2 + (x - a) 1 ^ 2)) _).trans
  apply add_le_add (h _)
  apply (abs_sub_le _ ((4 * π)⁻¹ * log ((x - b) 0 ^ 2 + (x - b) 1 ^ 2)) _).trans
  conv_lhs =>
    right
    rw [abs_sub_comm]
  refine add_le_add ?_ (h _)
  rw [← mul_sub, abs_mul, abs_of_nonneg (by simp [pi_nonneg])]
  refine mul_le_mul_of_nonneg_left ?_ (by simp [pi_nonneg])
  simp_rw [Pi.sub_apply]
  push_cast
  exact h' x

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

theorem φ_one_off_center (e : Fin n) : φ (Pi.single e 1) = (2 * n : ℝ)⁻¹ := by
  have : NeZero n := e.neZero
  apply eq_inv_of_mul_eq_one_right
  simpa [φ_single_perm _ 0, ← two_mul, unitCur, ← mul_assoc] using φ_kirchhoff (n := n) 0

theorem φ_one_dimensional_nat (x : ℕ) : φ ![x] = 2⁻¹ * x := by
  induction x using Nat.twoStepInduction with
  | zero => exact φ_zero.trans (by simp)
  | one =>
    refine Eq.trans ?_ ((φ_one_off_center (0 : Fin 1)).trans ?_)
    · rfl
    · simp
  | more n h1 h2 =>
    push_cast at ⊢ h2
    conv_lhs => rw [← one_add_one_eq_two, ← add_assoc]
    obtain h := φ_kirchhoff ![n + 1]
    conv_rhs at h => rw [unitCur, Pi.single_eq_of_ne (by simp; grind)]
    simp [Matrix.vecHead, h1, h2] at h
    linear_combination h

theorem φ_one_dimensional (x : ℤ) : φ ![x] = 2⁻¹ * |x| := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg x
  · simp [φ_one_dimensional_nat]
  · trans φ (-![(n : ℤ)])
    · simp
    · rw [φ_neg, φ_one_dimensional_nat]
      simp

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
