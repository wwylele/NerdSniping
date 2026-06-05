import Mathlib

open Real

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



@[simp]
theorem Asymptotics.isTheta_map {α : Type*} {β : Type*} {E : Type*} {F : Type*} [Norm E] [Norm F]
    {f : α → E} {g : α → F} {k : β → α} {l : Filter β} :
    f =Θ[Filter.map k l] g ↔ (f ∘ k) =Θ[l] (g ∘ k) := by
  unfold IsTheta
  simp
