module

public import Mathlib

public section

open Real Filter Asymptotics MeasureTheory

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

theorem Pi.apply_single' {ι : Type*} {M : ι → Type*} {N : ι → Type*}
    [(i : ι) → Zero (M i)] [(i : ι) → Zero (N i)] [DecidableEq ι]
    {F : ι → Type*} [∀ i, FunLike (F i) (M i) (N i)] [∀ i, ZeroHomClass (F i) (M i) (N i)]
    (f' : (i : ι) → F i) (i : ι) (x : M i) (j : ι) :
    f' j (single i x j) = single i (f' i x) j := by
  apply Pi.apply_single _ (by simp)

theorem Pi.intCast_single {ι : Type*} [DecidableEq ι] (a : ι) (b : ℤ) (x : ι) :
    ((Pi.single (M := fun (_ : ι) ↦ ℤ) a b x) : ℝ) =
    (Pi.single (M := fun (_ : ι) ↦ ℝ) a b x) := by
  apply Pi.apply_single' (fun _ ↦ Int.castAddHom ℝ)

theorem Pi.single_mul_left_const_apply {ι : Type*} {α : Type*}
    [MulZeroClass α] [DecidableEq ι] (i j : ι) (a : α) (f : α) :
    single (M := fun _ ↦ α) i (a * f) j = single (M := fun _ ↦ α) i a j * f :=
  single_mul_left_apply i j a (fun _ ↦ f)

lemma abs_sin_add_le (a b : ℝ) : |sin (a + b)| ≤ |sin a| + |sin b| := by
  rw [sin_add]
  apply (abs_add_le _ _).trans
  simp_rw [abs_mul]
  apply add_le_add
  · apply mul_le_of_le_one_right (abs_nonneg _) (abs_cos_le_one _)
  · apply mul_le_of_le_one_left (abs_nonneg _) (abs_cos_le_one _)

lemma abs_sin_sum_le {ι : Type*} (s : Finset ι) (a : ι → ℝ) :
    |sin (∑ i ∈ s, a i)| ≤ ∑ i ∈ s, |sin (a i)| := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s h ih =>
    simp only [Finset.sum_cons]
    apply (abs_sin_add_le _ _).trans
    grw [ih]

lemma abs_sin_nat_mul_le (m : ℕ) (y : ℝ) :
    |sin (m * y)| ≤ m * |sin y| := by
  induction m with
  | zero => simp
  | succ n ih =>
    push_cast
    rw [add_one_mul, add_one_mul]
    grw [abs_sin_add_le, ih]


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

theorem cofinite_int_le_cobounded_real :
    Filter.map (fun (x : Fin 2 → ℤ) ↦ ((x 0 : ℝ), (x 1 : ℝ))) cofinite ≤
    Bornology.cobounded (ℝ × ℝ) := by
  have hfinite (S : Set (ℝ × ℝ)) (hS : Bornology.IsBounded S):
      {x : Fin 2 → ℤ | ((x 0 : ℝ), (x 1 : ℝ)) ∈ S}.Finite := by
    obtain ⟨c, hc0, hc⟩ := hS.exists_pos_norm_le
    apply (Set.finite_Icc (⌈-c⌉ : Fin 2 → ℤ) ⌊c⌋).subset
    intro x hx
    rw [Set.mem_setOf_eq] at hx
    specialize hc _ hx
    rw [Prod.norm_def, max_le_iff, norm_eq_abs, norm_eq_abs, abs_le, abs_le] at hc
    rw [← Set.pi_univ_Icc, Set.mem_univ_pi]
    intro j
    suffices -c ≤ x j ∧ x j ≤ c by simpa [Int.le_floor, Int.ceil_le]
    fin_cases j
    · exact hc.1
    · exact hc.2
  refine Filter.map_le_iff_le_comap.mpr fun s hs ↦ ?_
  rw [mem_cofinite]
  obtain ⟨t, ht, hts⟩ := hs
  specialize hfinite tᶜ
  simp only [Bornology.isBounded_compl_iff, Set.mem_compl_iff] at hfinite
  refine (hfinite ht).subset fun x hx ↦ ?_
  contrapose! hx
  aesop

theorem map_polarCoord_eq_cobounded :
    Filter.map (polarCoord.symm) (atTop ×ˢ 𝓟 (Set.Icc (-π) π)) = Bornology.cobounded (ℝ × ℝ) := by
  refine le_antisymm ?_ ?_
  · intro T hT
    obtain ⟨R, hR0, hR⟩ : ∃ R > 0, ∀ p : ℝ × ℝ, p.1 ^ 2 + p.2 ^ 2 ≥ R ^ 2 → p ∈ T := by
      have h_compl_bounded : Bornology.IsBounded (Tᶜ) := Bornology.isBounded_compl_iff.mpr hT
      obtain ⟨R, hR0, hR⟩ := h_compl_bounded.exists_pos_norm_le
      simp_rw [Prod.norm_def, norm_eq_abs, max_le_iff, Set.mem_compl_iff] at hR
      refine ⟨R * 2, by simpa using hR0, fun p hp ↦ ?_⟩
      contrapose! hp
      obtain ⟨h1, h2⟩ := hR p hp
      have h1 := sq_abs p.1 ▸ pow_le_pow_left₀ (abs_nonneg _) h1 2
      have h2 := sq_abs p.2 ▸ pow_le_pow_left₀ (abs_nonneg _) h2 2
      grw [h1, h2]
      rw [← sub_pos]
      suffices 0 < 2 * R ^ 2 by
        convert! this using 1
        ring
      simpa [sq_pos_iff] using hR0.ne'
    refine mem_prod_iff.mpr ⟨Set.Ici R, Ici_mem_atTop R, Set.Icc (-π) π, mem_principal_self _, ?_⟩
    rintro ⟨r, θ⟩ ⟨hr, hθ⟩
    suffices (r * cos θ, r * sin θ) ∈ T by simpa
    apply hR
    suffices R ^ 2 ≤ r ^ 2 by simpa [mul_pow, ← mul_add]
    apply pow_le_pow_left₀ hR0.le hr
  · refine fun s hs ↦ ?_
    obtain ⟨R, hR0, hR⟩ : ∃ R > 0, ∀ r ≥ R, ∀ θ ∈ Set.Icc (-π) π,
        (r * Real.cos θ, r * Real.sin θ) ∈ s := by
      rw [Filter.mem_map, Filter.mem_prod_iff] at hs
      simp only [gt_iff_lt, ge_iff_le, Set.mem_Icc, and_imp]
      simp only [mem_atTop_sets, mem_principal] at hs
      obtain ⟨t₁, ⟨a, ha⟩, t₂, ht₂, h⟩ := hs
      refine ⟨max a 1, by positivity, fun r hr θ hθ₁ hθ₂ ↦ ?_⟩
      exact h (Set.mk_mem_prod (ha r ((le_max_left _ _).trans hr)) (ht₂ ⟨hθ₁, hθ₂⟩))
    have h_cobounded : ∀ p : ℝ × ℝ, R ≤ √(p.1 ^ 2 + p.2 ^ 2) → p ∈ s := by
      intro p hp
      by_cases h : p.1 + p.2 * Complex.I = 0
      · rw [Complex.ext_iff] at h
        obtain ⟨h1, h2⟩ : p.1 = 0 ∧ p.2 = 0 := by simpa using h
        have : R ≤ 0 := by simpa [h1, h2] using hp
        exact (this.not_gt hR0).elim
      have h0 : √(p.1 ^ 2 + p.2 ^ 2) ≠ 0 := by
        rw [← Complex.norm_add_mul_I, Complex.norm_eq_zero_iff.ne]
        exact h
      have := hR √(p.1 ^ 2 + p.2 ^ 2) hp (Complex.arg (p.1 + p.2 * Complex.I))
        ⟨Complex.neg_pi_lt_arg _ |> le_of_lt, Complex.arg_le_pi _⟩
      rw [Complex.sin_arg, Complex.cos_arg h, Complex.norm_add_mul_I,
        mul_div_cancel₀ _ h0, mul_div_cancel₀ _ h0] at this
      simpa using this
    refine Filter.mem_of_superset ?_ ?_ (x := {p : ℝ × ℝ | √(p.1 ^ 2 + p.2 ^ 2) ≥ R})
    · rw [Metric.cobounded_eq_cocompact, Filter.mem_cocompact]
      refine ⟨Metric.closedBall (0 : ℝ × ℝ) R,
        ProperSpace.isCompact_closedBall _ _, fun p hp ↦ ?_⟩
      simp only [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le] at hp
      simp only [ge_iff_le, Set.mem_setOf_eq]
      exact hp.le.trans (max_le_iff.mpr ⟨
        Real.abs_le_sqrt <| by nlinarith, Real.abs_le_sqrt <| by nlinarith⟩)
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
  suffices x - sin x ≤ x ^ 3 / 6 by
    apply this.trans
    gcongr
    norm_num
  rw [sub_le_comm]
  by_cases hx0 : x = 0
  · simp [hx0]
  exact (sin_gt_sub_cube (lt_of_le_of_ne' h0 hx0)).le


theorem bounded_of_isBigO_cofinite {α : Type*} {f : α → ℝ} (hf : f =O[cofinite] (1 : α → ℝ)) :
    ∃ c : ℝ, ∀ x, |f x| ≤ c := by
  rw [isBigO_cofinite_iff (by simp)] at hf
  simpa using hf
