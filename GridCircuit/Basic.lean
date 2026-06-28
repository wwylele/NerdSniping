module

public import GridCircuit.Misc
public import GridCircuit.Bessel

public section

/-!

# Nerd Sniping - the Infinite Grid of Resistors

In this file we formalize the answer and related results to [xkcd's "nerd sniping" question](https://xkcd.com/356/)

![I first saw this problem on the Google Labs Aptitude Test.  A professor and I filled a blackboard without getting anywhere.  Have fun.](https://imgs.xkcd.com/comics/nerd_sniping.png)

Here we state the problem in a more general form in aribtrary dimensions: On the $n$-dimensional
grid where each neighboring nodes are connected by an one-ohm resistor, what is the equivalent
resistance between the two specified nodes?

This file formalizes the following result
* `equivResistance`: formal mathematical model of the problem.
* `equivResistance_eq`: proof of the unique solution (if exists).
* `equivResistance_formula`: The general formula in arbitrary dimensions and for any pair of nodes.
* `computeφ`: explicit computation for the solution in the two-dimension case.
* `equivResistance_2_1`: the answer to the question in xkcd.


Hopefully this can protect me from a car accident.
-/

open Real MeasureTheory Filter Topology Asymptotics

variable {n : ℕ}

noncomputable section

/-!

## 1. Mathematical Model

The equivalent resistance is computed by $V / I$, where $V$ is the electrical potential difference
between the two nodes, and $I$ is the current into one node and equally out from the other.
Throughout the file, we will assume the standard units (ohm, volt, and amp) and omit them from
formulas. By this convention, if we fix the input current to 1, the equivalent resistance is equal
to the potential difference.

Once voltage is applied to the two nodes, there are two laws that determine the current and the
potential:
* Ohm's law: $R = V / I$ for any segment of the curcuit. Since every segment between two
  neighboring nodes has a resistance of 1, we can simplify this to $I(p, q) = U(p) - U(q)$ for any
  pair of neighboring nodes $p$ and $q$, where $U(p)$ is the potential at node $p$, and $I(p, q)$
  is the current from $p$ to $q$.
* Kirchhoff's current law: the signed sum of currents at a node is zero. In our $n$-dimensional
  grid, each node has $2n$ currents with neighbors, and possibly one external current input. In our
  convention, the current out from the node is positive, and the current into the node is negative.

We can combine the two laws to form a formula about potentials $U(p)$ and external currents $I(p)$,
whih we simply call "Kirchhoff's law" in the code:
$$
\left(\sum_{i=0}^{n-1} U(p + e_i) - U(p)\right) + \left(\sum_{i=0}^{n-1} U(p - e_i) - U(p)\right)
= I(p)
$$
where $e_i$ are unit vectors in each direction.

In addition to the laws, we add another constraint: the potential as a function of node should be
bounded. This is to rule out existence of a global external electrical field, where there is no
external current input, but internal current is still induced.

We group these contraints in `IsValidCircuit I U`, where `I : (Fin n → ℤ) → ℝ` is the external
current at each node, and `U : (Fin n → ℤ) → ℝ` is the potential at each node.
-/

/-- `IsValidCircuit I U` means the external current input `I` and potential `U` forms a valid
circuit over the infinite grid. -/
structure IsValidCircuit (cur : (Fin n → ℤ) → ℝ) (pot : (Fin n → ℤ) → ℝ) : Prop where
  /-- A valid circuit should follow Ohm's law and Kirchhoff's law. -/
  kirchhoff (x : Fin n → ℤ) :
    ∑ k, (pot (x - Pi.single k 1) - pot x) + ∑ k, (pot (x + Pi.single k 1) - pot x) = cur x
  /-- A valid potential function should be bounded below. -/
  bddBelow : BddBelow (Set.range pot)
  /-- A valid potential function should be bounded above. -/
  bddAbove : BddAbove (Set.range pot)

/-!

Once we have the definition of a valid circuit, the formalization of equivalent resistance is to
ask the potential difference given a pair of unit input current. We use `unitCur c` to express a
current input function that consists of a unit input at node `c : Fin n → ℤ`. The formalized
question them becomes: given a valid circuit for `(unitCur 0 - unitCur x)`, find the potential
between `0` and `x`.

-/

/-- The unit input current at node `c`, as a function over nodes. -/
def unitCur (c x : Fin n → ℤ) : ℝ := Pi.single (M := fun (_ : Fin n → ℤ) ↦ ℝ) c 1 x

open Classical in
/-- The definition of the solution. This definition uses `Exists.choose` to nonstructively return
the return the potential difference for input current `(unitCur 0 - unitCur x)`, and returns `none`.
if no valid circuit exists. We will later show the existence of the valid circuit constructively,
as well as their uniqueness. -/
def equivResistance (x : Fin n → ℤ) : Option ℝ :=
  if h : ∃ pot, IsValidCircuit (unitCur 0 - unitCur x) pot then
    some <| h.choose x - h.choose 0
  else
    none

/-!

## 2. Uniqueness of Solution

This section justifies the mathematical model by showing that its solution space is sub-singleton.
This follows from the discrete version of Liouville's theorem applied to bounded harmonic function,
which we will prove first.

Liouville's theorem says that if bounded function (above and below) satisfies the Laplace's equation
everywhere (which is equivalent to Kirchhoff's law with null external current), then it is a
constant function. There are stronger versions of this theorem (e.g. only requiring one-side
boundedness, and only requiring a large portion of nodes to satisfy the equation), but the
elementary version will suffice here.

We follow the proof posted at https://math.stackexchange.com/a/4452978/1197328

-/

/-- Lemma 1 for Liouville's theorem: if a discrete harmonic function
$f : \mathbb{Z}^n \to \mathbb{R}$ satisfies that for certain $L$ and a unit direction $e$
$$|f(x) + f(x + e) + f(x + 2e) + \cdots + f(x + ke)| \le L$$
for all $x$ and $k$, then $f$ is constantly 0. In the first version we shows the nonpositivity of
$f$, and then use antisymmetry in the next version. -/
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

/-- Full lemma 1 for Liouville's theorem: use antisymmetry on the previous lemma. -/
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

/-- Liouville's theorem for two neighboring points: for a harmonic $f$, set
$g(x) = f(x + e) - f(x)$, then $g$ satisfies the condition for lemma 1, and thus constantly zero,
showing $f(x + e) = f(x)$. -/
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

/-- By inductiog on the previous lemma, a bounded harmonic function is constant on a line in any
direction. -/
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

/-- By induction on the previous lemma, we get Liouville's theorem: a bounded harmonic function is
constant globally. -/
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

/-- Equivalent to Liouville's theorem, the only valid potential functions for null external current
are constant functions. -/
theorem isValidCircuit_zero [NeZero n] {pot : (Fin n → ℤ) → ℝ} :
    IsValidCircuit 0 pot ↔ ∃ c, pot = fun _ ↦ c where
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

/-- For any specific external current functions, the valid potential function, if exists, is unique
up to a constant. -/
theorem isValidCircuit_unique [NeZero n] {cur : (Fin n → ℤ) → ℝ} {a b : (Fin n → ℤ) → ℝ}
    (ha : IsValidCircuit cur a) (hb : IsValidCircuit cur b) :
    ∃ c, a - b = fun _ ↦ c := by
  rw [← isValidCircuit_zero]
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

/-- Since the uniqueness of the potential function, the infinite grid question can be answered
whenever a valid potential function is found. -/
theorem equivResistance_eq [NeZero n] {x : Fin n → ℤ} {pot : (Fin n → ℤ) → ℝ}
    (h : IsValidCircuit (unitCur 0 - unitCur x) pot) :
    equivResistance x = some (pot x - pot 0) := by
  have h' : ∃ pot, IsValidCircuit (unitCur 0 - unitCur x) pot := ⟨pot, h⟩
  obtain ⟨c, hc⟩ := isValidCircuit_unique h'.choose_spec h
  rw [sub_eq_iff_eq_add] at hc
  simp [equivResistance, h', hc]

/-!

## 3. Fourier Transform: a Potential Solution

In this section, we construct a function `φ` that represents the potential function corresponding to
a *singleton* external current (as opposite to a pair of in/out current as we have been discussing).
Physically, such current dissipates via the grid to infinity. It is *almost* a valid solution to
`IsValidCircuit (unitCur 0) φ`, but it is not necessarily bounded. We will further discuss its
asymptotic behavior in the next section.

The construction of `φ` is obtained by taking an inverse Fourier transform of a certain function.
The full derivation via Fourier transform is omitted, but you can get the general idea by the proof
here.
-/

/--
We compute the discrete Fourier transform of `unitCur 0`, then state the result using inverse
Fourier transform to recover `unitCur 0`, which is a integral over a hypercube
$$
I (x_0, x_1,\cdots,x_{n-1}) =
\frac{1}{(2\pi)^n} \int_{[-\pi, \pi]^n} \left(\cos \sum_i x_i w_i\right) dw
$$
-/
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

/--
Then we define function `φ` also as a similar inverse Fourier transform
$$
\varphi (x_0, x_1,\cdots,x_{n-1}) =
\frac{1}{(2\pi)^n} \int_{[-\pi, \pi]^n}
\frac{1 - \cos \sum_i x_i w_i}{\sum_i 2 - 2\cos w_i} dw
$$
-/
def φ (x : Fin n → ℤ) : ℝ :=
  (2 * π)⁻¹ ^ n * ∫ (w : Fin n → ℝ) in Set.Icc (fun _ ↦ -π) (fun _ ↦ π),
    (1 - Real.cos (∑ i, x i * w i)) / ∑ i, (2 - 2 * Real.cos (w i))

/-!

We start exploring some basic properties of `φ`:
- `φ 0 = 0`.
- `φ` is non-negative, and therefore bounded below.
- `φ` has mirror symmetry along any axies. (`φ_reflect`)
- `φ` is symmetric for coordinate permutation. (`φ_perm`)
-/

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

theorem bddBelow_φ : BddBelow (Set.range <| φ (n := n)) := by
  use 0
  simpa [mem_lowerBounds] using φ_nonneg

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
theorem φ_neg_0 (x y : ℤ) : φ ![-x, y] = φ ![x, y] := by
  rw [← φ_reflect _ 0]
  congrm φ ?_
  ext i
  fin_cases i
  · simp
  · simp

@[simp]
theorem φ_neg_1 (x y : ℤ) : φ ![x, -y] = φ ![x, y] := by
  rw [← φ_reflect _ 1]
  congrm φ ?_
  ext i
  fin_cases i
  · simp
  · simp

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

/-- Special case for swapping coordinates in the 2D case. -/
theorem φ_swap (x y : ℤ) : φ ![x, y] = φ ![y, x] := by
  rw [← φ_perm _ (Equiv.swap 0 1)]
  simp

/-!
We should justify that the integral in `φ` actually makes sense. This is not trivial: the integrant
has an unremovable singularity at 0. It turns out that this singularity is bounded, so you can
either treat it as 0 using Lean's junk value, or remove the singularity from integration.
-/

theorem integrable_φ [NeZero n] (x : Fin n → ℤ) :
    IntegrableOn (fun w ↦ (1 - cos (∑ k, x k * w k)) / ∑ k, (2 - 2 * cos (w k)))
      (Set.Icc (fun _ ↦ -π) (fun _ ↦ π)) := by
  have hm : MeasurableSet (Set.Icc (fun x ↦ -π) fun x ↦ π : Set (Fin n → ℝ)) := by
    rw [← Set.pi_univ_Icc]
    apply MeasurableSet.pi Set.countable_univ fun i _ ↦ measurableSet_Icc
  refine IntegrableOn.of_bound ?_ ?_ (2⁻¹ * ∑ k, (x k : ℝ) ^ 2) ?_
  · simp [Real.volume_Icc_pi]
  · rw [← Measure.restrict_inter_add_sdiff _ (measurableSet_singleton 0)]
    rw [Set.inter_eq_right.mpr (by simp [Pi.le_def, pi_nonneg])]
    rw [Measure.restrict_singleton', zero_add]
    refine ContinuousOn.aestronglyMeasurable ?_ (hm.diff (measurableSet_singleton 0))
    refine ContinuousOn.div₀ (by fun_prop) (by fun_prop) ?_
    intro i hi
    simp only [Set.mem_sdiff, Set.mem_Icc, Set.mem_singleton_iff] at hi
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

/-!
Lastly, we show that `φ` satisfies Kirchhoff's law for singleton unit current, making it an *almost*
solution. As a corollary, we compute the value of `φ eᵢ` for a unit vector `eᵢ` in `φ_off_center`
using Kirchhoff's law and symmetry.
-/

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

/-- A specialized version of `φ_kirchhoff` for 2D and not at the center. -/
theorem φ_2d_kirchhoff_of_ne_zero (x y : ℤ) (hxy : x ≠ 0 ∨ y ≠ 0) :
    4 * φ ![x, y] = φ ![x - 1, y] + φ ![x + 1, y] + φ ![x, y - 1] + φ ![x, y + 1] := by
  obtain h := φ_kirchhoff ![x, y]
  rw [unitCur, Pi.single_eq_of_ne (by contrapose! hxy; simpa using hxy)] at h
  have hsum (f : Fin 2 → ℝ) : ∑ k, f k = f 0 + f 1 := by simp
  have h0 : Pi.single 0 (1 : ℤ) = ![1, 0] := by ext i; fin_cases i <;> simp
  have h1 : Pi.single 1 (1 : ℤ) = ![0, 1] := by ext i; fin_cases i <;> simp
  simp_rw [hsum, h0, h1] at h
  simp at h
  linear_combination -h

theorem φ_off_center (e : Fin n) : φ (Pi.single e 1) = (2 * n : ℝ)⁻¹ := by
  have : NeZero n := e.neZero
  apply eq_inv_of_mul_eq_one_right
  simpa [φ_single_perm _ 0, ← two_mul, unitCur, ← mul_assoc] using φ_kirchhoff (n := n) 0

/-- A specialized version of `φ_off_center` for 2D. -/
theorem φ_2d_1_0 : φ ![1, 0] = 4⁻¹ := by
  convert φ_off_center (0 : Fin 2)
  · ext i; fin_cases i <;> simp
  · norm_num

/-!

## 4. Asymptotic Behavior of `φ`

In this section, we show the asymptotic behavior of `φ` in different dimensions $n$:
- When $n \ge 3$, `φ x` is bounded
- When $n = 2$, `φ x` grows like $\log \lVert x \rVert$
- When $n = 1$, `φ x` grows linearly

Compare this to physical intuition: in a $n$-dimensional space, current density sourced from a point
should decrease like ${\lVert x \rVert}^{-(n - 1)}$ (inverse-square law in 3D), and the potential,
being the integral of t, should grow like ${\lVert x \rVert}^{-(n - 2)}$ except for $n = 2$, where
the integral becomes $\log \lVert x \rVert$.

We start with the $n \ge 3$ case
-/

/--
For $n \ge 3$, it is possible to bound the integral by bounding the numerator to 1. This creates
poles at 0, but it is still integrable.
-/
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
        ← Set.inter_union_sdiff (Set.Icc (fun _ ↦ -π) (fun _ ↦ π)) (Metric.ball 0 r),
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

/-- Thus `φ` is bounded above for $n \ge 3$. -/
theorem bddAbove_φ (hn : 3 ≤ n) : BddAbove (Set.range <| φ (n := n)) := by
  obtain habs := abs_φ_le hn
  simp_rw [abs_le] at habs
  use (2 * π)⁻¹ ^ n * ∫ (w : Fin n → ℝ) in Set.Icc (fun _ ↦ -π) (fun _ ↦ π),
    1 / ∑ i, (1 - Real.cos (w i))
  simp_rw [mem_upperBounds, Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff]
  exact fun x ↦ (habs x).2

/-!

We show the asymptotic behavior for $n = 2$ next. The precise statement we want to prove is: the
function $g(x)$ defined below is bounded above and below

$$
g(x, y) = \varphi(x, y) - \frac{1}{4 \pi} \log (x^2 + y^2) =
\varphi(x, y) - \frac{1}{2 \pi} \log \lVert (x, y) \rVert_2
$$

(This assumes the junk value $\log 0 = 0$, but a single point isn't important for the global bound)

We show this using a chain of asymptotic equivalences:
$$
\varphi(x, y)
\sim \iint_{[-\pi,\pi]^2} \frac{1-\cos (x u + y v)}{4 - (2 \cos u + 2 \cos v)}du dv
$$
$$
\sim \iint_{u^2+v^2\le 1} \frac{1-\cos (x u + y v)}{4 - (2 \cos u + 2 \cos v)}du dv
$$
$$
\sim \iint_{u^2+v^2\le 1} \frac{1-\cos (x u + y v)}{u^2 + v^2}du dv
$$
$$
\sim \int_{r=0}^{\lVert (x, y) \rVert_2} \int_{\theta=-\pi}^{\pi}
\frac{1-\cos (r \cos(\theta))}{r}dr d\theta
$$
$$
\sim \log \lVert (x, y) \rVert_2
$$
where each equivalence means bounded difference between two sides after multiplying by some
constants. The main idea here is that the logarithmic growth comes from the integration around the
singularity, so we can carve out a small disk (a unit disk will suffice), and change to polar
coordinates. The last equivalence is a property of Bessel function, which is proved at
`asymptotic_bessel`.

-/

/-- Specialize the integral to 2D case. -/
theorem φ_2d (x : Fin 2 → ℤ) :
    φ x = (4 * π ^ 2)⁻¹ * ∫ w in Set.Icc (-π) π ×ˢ Set.Icc (-π) π,
    (1 - cos (x 0 * w.1 + x 1 * w.2)) / (4 - (2 * cos w.1 + 2 * cos w.2)) := by
  unfold φ
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

/-- A common lemma we will use to determine that the only singularity is at 0. -/
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

/-- Specialize integrability to 2D. -/
theorem φ_integrable_2d (x : Fin 2 → ℤ) :
    IntegrableOn (fun w ↦ (1 - cos (x 0 * w.1 + x 1 * w.2)) / (4 - (2 * cos w.1 + 2 * cos w.2)))
    (Set.Icc (-π) π ×ˢ Set.Icc (-π) π) volume := by
  rw [Measure.volume_eq_prod, IntegrableOn, ← Measure.prod_restrict]
  rw [← (measurePreserving_finTwoArrow _).integrable_comp (by
    apply StronglyMeasurable.aestronglyMeasurable
    fun_prop
  )]
  rw [← Measure.restrict_pi_pi, ← IntegrableOn, ← MeasureTheory.volume_pi, Set.pi_univ_Icc]
  convert! integrable_φ x with x
  simp [show (2 : ℝ) * 2 = 4 by norm_num]

/-- Integrability of an equivalent function we will use. -/
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

/-- The unit disk is a subset of the containing square. -/
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

/-- The unit disk is a subset of the original square to integrate on. -/
theorem disk_subset' : {p | p.1 ^ 2 + p.2 ^ 2 ≤ 1} ⊆ Set.Icc (-π) π ×ˢ Set.Icc (-π) π := by
  have honepi : 1 ≤ π := le_trans (by simp) pi_gt_three.le
  apply disk_subset.trans
  simp only [Set.Icc_prod_Icc]
  apply Set.Icc_subset_Icc
  · simp [honepi]
  · simp [honepi]

/-- Equivalence when we change the denominator of the integrant. -/
theorem φ_integral_change_deno :
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
    convert! this using 2
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

/-- Logarithmatic equivalence for `φ` in 2D. -/
theorem φ_equiv_log_2d :
    (fun (x : Fin 2 → ℤ) ↦ φ x - (4 * π)⁻¹ * log (x 0 ^ 2 + x 1 ^ 2)) =O[cofinite]
    (1 : (Fin 2 → ℤ) → ℝ) := by
  simp_rw [φ_2d]
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
    ext x
    rw [← integral_inter_add_sdiff hdiskmeasureable (φ_integrable_2d _),
      Set.inter_eq_right.mpr disk_subset']
    rw [mul_add]
    rw [add_sub_right_comm]
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
    · refine IntegrableOn.mono_set ?_ (Set.sdiff_subset_sdiff_right hdiskdisk)
      apply ContinuousOn.integrableOn_compact
        ((IsCompact.prod isCompact_Icc isCompact_Icc).diff hodisk)
      apply ContinuousOn.div (by fun_prop) (by fun_prop)
      intro p hp
      rw [Set.mem_sdiff] at hp
      obtain ⟨hp1, hp2⟩ := hp
      contrapose! hp2
      simp [odisk, eq_zero_of_φ_2d_deno_le_zero hp1 hp2.le]
    · refine IntegrableOn.mono_set ?_ (Set.sdiff_subset_sdiff_right hdiskdisk)
      apply ContinuousOn.integrableOn_compact
        ((IsCompact.prod isCompact_Icc isCompact_Icc).diff hodisk)
      apply ContinuousOn.div (by fun_prop) (by fun_prop)
      intro p hp
      rw [Set.mem_sdiff] at hp
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
  rw [← (φ_integral_change_deno.const_mul_left (4 * π ^ 2)⁻¹).sub_iff_left]
  simp_rw [mul_sub, sub_sub_sub_cancel_left]
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

/-- Restating logarithmatic equivalence for `φ` in 2D in terms of a global bound. -/
theorem φ_2d_sub_log_bounded :
    ∃ c : ℝ, ∀ x : Fin 2 → ℤ, |φ x - (4 * π)⁻¹ * log (x 0 ^ 2 + x 1 ^ 2)| ≤ c :=
  bounded_of_isBigO_cofinite φ_equiv_log_2d

/-!
Finally, we turn to the 1D case. We can direclty compute using induction that
$$
\varphi (x) = \frac{1}{2} |x|
$$
and thus `φ` grows linearly in 1D case.
-/

theorem φ_1d_nat (x : ℕ) : φ ![x] = 2⁻¹ * x := by
  induction x using Nat.twoStepInduction with
  | zero => exact φ_zero.trans (by simp)
  | one =>
    refine Eq.trans ?_ ((φ_off_center (0 : Fin 1)).trans ?_)
    · rfl
    · simp
  | more n h1 h2 =>
    push_cast at ⊢ h2
    conv_lhs => rw [← one_add_one_eq_two, ← add_assoc]
    obtain h := φ_kirchhoff ![n + 1]
    conv_rhs at h => rw [unitCur, Pi.single_eq_of_ne (by simp; grind)]
    simp [Matrix.vecHead, h1, h2] at h
    linear_combination h

theorem φ_1d (x : ℤ) : φ ![x] = 2⁻¹ * |x| := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg x
  · simp [φ_1d_nat]
  · trans φ (-![(n : ℤ)])
    · simp
    · rw [φ_neg, φ_1d_nat]
      simp

theorem φ_1d' (x : Fin 1 → ℤ) : φ x = 2⁻¹ * |x 0| := by
  rw [show x = ![x 0] by
    ext i
    fin_cases i
    simp
  ]
  rw [φ_1d]
  simp

/-!

## 5. Solution to `IsValidCircuit`

In this section, we prove
`IsValidCircuit (unitCur a - unitCur b) (fun x ↦ φ (x - a) - φ (x - b))`. The two conditions
for this are now within reach:
- Because of linarity, Kirchhoff's law holds for any linear combination of `φ`.
- The difference between two `φ` is bounded thanks to the tame asymptotics.

The hardest part in this is to show the boundedness for 2D cases. We will first show that
the difference between two `log`-like functions are bounded, then transfer the result to `φ`.

-/

/-- The difference between $log \lVert x \rVert_2^2$ and $log \lVert x+(a,b) \rVert_2^2$ is
bounded. -/
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
      convert! h0.le using 1
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

/-- Generalize the previous statement to any pair of points. -/
theorem log_shift_equiv' (a b c d : ℤ) :
    (fun x ↦ log ((x 0 - a) ^ 2 + (x 1 - b) ^ 2) - log ((x 0 - c) ^ 2 + (x 1 - d) ^ 2))
    =O[cofinite] (1 : (Fin 2 → ℤ) → ℝ) := by
  convert! (log_shift_equiv (-a) (-b)).sub (log_shift_equiv (-c) (-d)) using 2 with x
  push_cast
  simp [← sub_eq_add_neg]

/-- The difference between two `φ` in 2D is bounded. -/
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

/-- We also show the difference between two `φ` in 1D as a direct result of linear growth. -/
theorem bound_φ_1d (a b : Fin 1 → ℤ) : ∃ c, ∀ x, |φ (x - a) - φ (x - b)| ≤ c := by
  use 2⁻¹ * |b 0 - a 0|
  intro x
  simp_rw [φ_1d']
  simp only [Fin.isValue, Pi.sub_apply, Int.cast_abs, Int.cast_sub]
  rw [← mul_sub, abs_mul, abs_of_nonneg (by simp)]
  refine mul_le_mul_of_nonneg_left ?_ (by simp)
  grw [abs_abs_sub_abs_le_abs_sub]
  simp

/-- Combining all cases above, we show that `fun x ↦ φ (x - a) - φ (x - b)` is the
unique solution to `IsValidCircuit (unitCur a - unitCur b)`. -/
theorem isValidCircuit_φ [NeZero n] (a b : Fin n → ℤ) :
    IsValidCircuit (unitCur a - unitCur b) (fun x ↦ φ (x - a) - φ (x - b)) where
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
  bddAbove := match hn : n with
  | 0 => by simp
  | 1 => by
    obtain ⟨c, hc⟩ := bound_φ_1d a b
    use c
    suffices ∀ x, φ (x - a) - φ (x - b) ≤ c by simpa [mem_upperBounds]
    exact fun x ↦ (le_abs_self _).trans (hc x)
  | 2 => by
    obtain ⟨c, hc⟩ := bound_φ_2d a b
    use c
    suffices ∀ x, φ (x - a) - φ (x - b) ≤ c by simpa [mem_upperBounds]
    exact fun x ↦ (le_abs_self _).trans (hc x)
  | n + 3 => by
    apply bddAbove_range_sub
    · change BddAbove (Set.range (φ ∘ fun x ↦ (x - a)))
      apply BddAbove.mono (Set.range_comp_subset_range _ _)
      exact bddAbove_φ (by simp)
    · change BddBelow (Set.range (φ ∘ fun x ↦ (x - b)))
      apply BddBelow.mono (Set.range_comp_subset_range _ _)
      exact bddBelow_φ
  bddBelow := match hn : n with
  | 0 => by simp
  | 1 => by
    obtain ⟨c, hc⟩ := bound_φ_1d a b
    use -c
    suffices ∀ x, -c ≤ φ (x - a) - φ (x - b) by simpa [mem_lowerBounds]
    exact fun x ↦ le_trans (by simpa using hc x) (neg_abs_le _)
  | 2 => by
    obtain ⟨c, hc⟩ := bound_φ_2d a b
    use -c
    suffices ∀ x, -c ≤ φ (x - a) - φ (x - b) by simpa [mem_lowerBounds]
    exact fun x ↦ le_trans (by simpa using hc x) (neg_abs_le _)
  | n + 3 => by
    apply bddBelow_range_sub
    · change BddBelow (Set.range (φ ∘ fun x ↦ (x - a)))
      apply BddBelow.mono (Set.range_comp_subset_range _ _)
      exact bddBelow_φ
    · change BddAbove (Set.range (φ ∘ fun x ↦ (x - b)))
      apply BddAbove.mono (Set.range_comp_subset_range _ _)
      exact bddAbove_φ (by simp)

/-- And as an immediate corollary, the equivalent resistance is two times `φ` in all cases. -/
theorem equivResistance_eq_two_mul_φ [NeZero n] (x : Fin n → ℤ) :
    equivResistance x = some (2 * φ x) := by
  rw [equivResistance_eq (isValidCircuit_φ 0 x)]
  simp [two_mul]

/-- We can also write out the full formula for the equivalent resistance. -/
theorem equivResistance_formula [NeZero n] (x : Fin n → ℤ) :
  equivResistance x =
    some (2 * (2 * π)⁻¹ ^ n * ∫ (w : Fin n → ℝ) in Set.Icc (fun _ ↦ -π) (fun _ ↦ π),
    (1 - Real.cos (∑ i, x i * w i)) / ∑ i, (2 - 2 * Real.cos (w i))) := by
  rw [equivResistance_eq_two_mul_φ, φ, ← mul_assoc]

/-- Applying this to the neighbor of the center, we get that the equivalent resistance between
two neighboring points is $1 / n$. -/
theorem equivResistance_off_center [NeZero n] (e : Fin n) :
    equivResistance (Pi.single e 1) = some ((n : ℝ)⁻¹) := by
  rw [equivResistance_eq_two_mul_φ, φ_off_center, mul_inv, ← mul_assoc, mul_inv_cancel₀ (by simp),
    one_mul]

/-!

## 6. Calculation for the 2D case

In this section, we derive more closed-form results for the 2D case, and answers the original
nerd sniping question.

The key result is that `φ ![x, x]` along the diagonal line has a simple formula
$$
\varphi(x, x) = \frac{1}{\pi}\left(1 + \frac{1}{3} + \frac{1}{5} + \cdots + \frac{1}{2x - 1}\right)
$$

Combining with the known value `φ ![1, 0] = 4⁻¹`, it is possible to calculate any `φ ![x, y]`
using symmetry and Kirchhoff's law, and they will be some rational combinations of $1$ and $π$.

To calculate the integral on the diagonal line, we expand the integral domain from the square
to the diamond $(2\pi, 0) - (0, 2\pi) - (-2\pi, 0) - (0, -2π)$. Because of the periodicity of
the integrand, this simply doubles the resulting value. We then change the variable to rotate
it by 45 degrees. The new integral can have variables separated, allowing us to calculate it.

This process is unfortunately tedious to formalize. We start with defining the `diamond` region,
as well as the four triangles `triangleU`, `triangleD`, `triangleL`, and `triangleR` between the
diamand and the square.
-/

def triangleU : Set (ℝ × ℝ) := {p | π ≤ p.2 ∧ p.1 + p.2 ≤ 2 * π ∧ p.2 - p.1 ≤ 2 * π}
def triangleD : Set (ℝ × ℝ) := {p | p.2 ≤ -π ∧ -2 * π ≤ p.1 + p.2 ∧ -2 * π ≤ p.2 - p.1}
def triangleL : Set (ℝ × ℝ) := {p | p.1 ≤ -π ∧ -2 * π ≤ p.1 + p.2 ∧ p.2 - p.1 ≤ 2 * π}
def triangleR : Set (ℝ × ℝ) := {p | π ≤ p.1 ∧ p.1 + p.2 ≤ 2 * π ∧ -2 * π ≤ p.2 - p.1}
def diamond : Set (ℝ × ℝ) :=
  {p | p.1 + p.2 ≤ 2 * π ∧ -2 * π ≤ p.1 + p.2 ∧ p.2 - p.1 ≤ 2 * π ∧ -2 * π ≤ p.2 - p.1}

/-- `diamand` is the union of the square and the four triangles. -/
theorem diamond_decomp :
    diamond =
    triangleU ∪ triangleD ∪ triangleL ∪ triangleR ∪ (Set.Icc (-π) π ×ˢ Set.Icc (-π) π) := by
  apply Set.Subset.antisymm
  · intro p hp
    by_cases hp2 : p ∈ Set.Icc (-π) π ×ˢ Set.Icc (-π) π
    · apply Set.mem_union_right _ hp2
    rw [Set.mem_prod, Set.mem_Icc, Set.mem_Icc] at hp2
    push +distrib Not at hp2
    simp only [diamond, Set.mem_setOf_eq] at hp
    obtain (hp2 | hp2) | (hp2 | hp2) := hp2
    · suffices p ∈ triangleL by simp [this]
      simp only [triangleL, Set.mem_setOf_eq]
      refine ⟨hp2.le, ?_, ?_⟩ <;> linarith
    · suffices p ∈ triangleR by simp [this]
      simp only [triangleR, Set.mem_setOf_eq]
      refine ⟨hp2.le, ?_, ?_⟩ <;> linarith
    · suffices p ∈ triangleD by simp [this]
      simp only [triangleD, Set.mem_setOf_eq]
      refine ⟨hp2.le, ?_, ?_⟩ <;> linarith
    · suffices p ∈ triangleU by simp [this]
      simp only [triangleU, Set.mem_setOf_eq]
      refine ⟨hp2.le, ?_, ?_⟩ <;> linarith
  · refine Set.union_subset (Set.union_subset (Set.union_subset (Set.union_subset ?_ ?_) ?_) ?_) ?_
    · intro p hp
      simp only [triangleU, Set.mem_setOf_eq] at hp
      obtain ⟨hp1, hp2, hp3⟩ := hp
      simp only [diamond, Set.mem_setOf_eq]
      refine ⟨hp2, ?_, hp3, ?_⟩ <;> linarith
    · intro p hp
      simp only [triangleD, Set.mem_setOf_eq] at hp
      obtain ⟨hp1, hp2, hp3⟩ := hp
      simp only [diamond, Set.mem_setOf_eq]
      refine ⟨?_, hp2, ?_, hp3⟩ <;> linarith
    · intro p hp
      simp only [triangleL, Set.mem_setOf_eq] at hp
      obtain ⟨hp1, hp2, hp3⟩ := hp
      simp only [diamond, Set.mem_setOf_eq]
      refine ⟨?_, hp2, hp3, ?_⟩ <;> linarith
    · intro p hp
      simp only [triangleR, Set.mem_setOf_eq] at hp
      obtain ⟨hp1, hp2, hp3⟩ := hp
      simp only [diamond, Set.mem_setOf_eq]
      refine ⟨hp2, ?_, ?_, hp3⟩ <;> linarith
    · intro p hp
      rw [Set.mem_prod, Set.mem_Icc, Set.mem_Icc] at hp
      simp only [diamond, Set.mem_setOf_eq]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

/-- The square is the union of the same four triangles after translation. -/
theorem square_comp :
    (Set.Icc (-π) π ×ˢ Set.Icc (-π) π) =
    (MeasurableEquiv.addRight (0, -2 * π) '' triangleU) ∪
    (MeasurableEquiv.addRight (0, 2 * π) '' triangleD) ∪
    (MeasurableEquiv.addRight (2 * π, 0) '' triangleL) ∪
    (MeasurableEquiv.addRight (-2 * π, 0) '' triangleR) := by
  apply Set.Subset.antisymm
  · intro p hp
    rw [Set.mem_prod, Set.mem_Icc, Set.mem_Icc] at hp
    simp_rw [Set.mem_union]
    rcases le_total p.1 p.2 with h1 | h1
    · rcases le_total p.1 (-p.2) with h2 | h2
      · suffices p ∈ MeasurableEquiv.addRight (-2 * π, 0) '' triangleR by
          simp only [this]
          simp
        simp only [MeasurableEquiv.coe_addRight, Set.image_add_right, Prod.neg_mk, triangleR,
          Set.preimage_setOf_eq, Prod.snd_add, Prod.fst_add, Set.mem_setOf_eq]
        refine ⟨?_, ?_, ?_⟩ <;> linarith
      · suffices p ∈ MeasurableEquiv.addRight (0, 2 * π) '' triangleD by
          simp only [this]
          simp
        simp only [MeasurableEquiv.coe_addRight, Set.image_add_right, Prod.neg_mk, triangleD,
          Set.preimage_setOf_eq, Prod.snd_add, Prod.fst_add, Set.mem_setOf_eq]
        refine ⟨?_, ?_, ?_⟩ <;> linarith
    · rcases le_total p.1 (-p.2) with h2 | h2
      · suffices p ∈ MeasurableEquiv.addRight (0, -2 * π) '' triangleU by
          simp only [this]
          simp
        simp only [MeasurableEquiv.coe_addRight, Set.image_add_right, Prod.neg_mk, triangleU,
          Set.preimage_setOf_eq, Prod.snd_add, Prod.fst_add, Set.mem_setOf_eq]
        refine ⟨?_, ?_, ?_⟩ <;> linarith
      · suffices p ∈ MeasurableEquiv.addRight (2 * π, 0) '' triangleL by
          simp only [this]
          simp
        simp only [MeasurableEquiv.coe_addRight, Set.image_add_right, Prod.neg_mk, triangleL,
          Set.preimage_setOf_eq, Prod.snd_add, Prod.fst_add, Set.mem_setOf_eq]
        refine ⟨?_, ?_, ?_⟩ <;> linarith
  · refine Set.union_subset (Set.union_subset (Set.union_subset ?_ ?_) ?_) ?_
    · intro p hp
      simp only [MeasurableEquiv.coe_addRight, Set.image_add_right, Prod.neg_mk, triangleU,
        Set.preimage_setOf_eq, Prod.snd_add, Prod.fst_add, Set.mem_setOf_eq] at hp
      rw [Set.mem_prod, Set.mem_Icc, Set.mem_Icc]
      refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> linarith
    · intro p hp
      simp only [MeasurableEquiv.coe_addRight, Set.image_add_right, Prod.neg_mk, triangleD,
        Set.preimage_setOf_eq, Prod.snd_add, Prod.fst_add, Set.mem_setOf_eq] at hp
      rw [Set.mem_prod, Set.mem_Icc, Set.mem_Icc]
      refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> linarith
    · intro p hp
      simp only [MeasurableEquiv.coe_addRight, Set.image_add_right, Prod.neg_mk, triangleL,
        Set.preimage_setOf_eq, Prod.snd_add, Prod.fst_add, Set.mem_setOf_eq] at hp
      rw [Set.mem_prod, Set.mem_Icc, Set.mem_Icc]
      refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> linarith
    · intro p hp
      simp only [MeasurableEquiv.coe_addRight, Set.image_add_right, Prod.neg_mk, triangleR,
        Set.preimage_setOf_eq, Prod.snd_add, Prod.fst_add, Set.mem_setOf_eq] at hp
      rw [Set.mem_prod, Set.mem_Icc, Set.mem_Icc]
      refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> linarith

/-! We show that the integration in `φ` makes sense in all these regions. -/

theorem φ_integrable_mapU (x : Fin 2 → ℤ) :
    IntegrableOn (fun w ↦ (1 - cos (x 0 * w.1 + x 1 * w.2)) / (4 - (2 * cos w.1 + 2 * cos w.2)))
    (MeasurableEquiv.addRight (0, -2 * π) '' triangleU) := by
  apply (φ_integrable_2d x).mono_set
  rw [square_comp]
  grind

theorem φ_integrable_mapD (x : Fin 2 → ℤ) :
    IntegrableOn (fun w ↦ (1 - cos (x 0 * w.1 + x 1 * w.2)) / (4 - (2 * cos w.1 + 2 * cos w.2)))
    (MeasurableEquiv.addRight (0, 2 * π) '' triangleD) := by
  apply (φ_integrable_2d x).mono_set
  rw [square_comp]
  grind

theorem φ_integrable_mapL (x : Fin 2 → ℤ) :
    IntegrableOn (fun w ↦ (1 - cos (x 0 * w.1 + x 1 * w.2)) / (4 - (2 * cos w.1 + 2 * cos w.2)))
    (MeasurableEquiv.addRight (2 * π, 0) '' triangleL) := by
  apply (φ_integrable_2d x).mono_set
  rw [square_comp]
  grind

theorem φ_integrable_mapR (x : Fin 2 → ℤ) :
    IntegrableOn (fun w ↦ (1 - cos (x 0 * w.1 + x 1 * w.2)) / (4 - (2 * cos w.1 + 2 * cos w.2)))
    (MeasurableEquiv.addRight (-2 * π, 0) '' triangleR) := by
  apply (φ_integrable_2d x).mono_set
  rw [square_comp]
  grind

theorem φ_integrable_U (x : Fin 2 → ℤ) :
    IntegrableOn (fun w ↦ (1 - cos (x 0 * w.1 + x 1 * w.2)) / (4 - (2 * cos w.1 + 2 * cos w.2)))
    triangleU := by
  obtain h := φ_integrable_mapU x
  rw [MeasurePreserving.integrableOn_image (by exact measurePreserving_add_right _ _)
    (MeasurableEquiv.measurableEmbedding _)] at h
  convert! h with p
  simp only [Fin.isValue, neg_mul, MeasurableEquiv.coe_addRight, Function.comp_apply, Prod.fst_add,
    add_zero, Prod.snd_add, ← sub_eq_add_neg, cos_sub_two_pi]
  congrm (1 - ?_) / $(by simp)
  rw [mul_sub, ← add_sub_assoc, Real.cos_sub_int_mul_two_pi]

theorem φ_integrable_D (x : Fin 2 → ℤ) :
    IntegrableOn (fun w ↦ (1 - cos (x 0 * w.1 + x 1 * w.2)) / (4 - (2 * cos w.1 + 2 * cos w.2)))
    triangleD := by
  obtain h := φ_integrable_mapD x
  rw [MeasurePreserving.integrableOn_image (by exact measurePreserving_add_right _ _)
    (MeasurableEquiv.measurableEmbedding _)] at h
  convert! h with p
  simp only [Fin.isValue, MeasurableEquiv.coe_addRight, Function.comp_apply, Prod.fst_add, add_zero,
    Prod.snd_add, cos_add_two_pi]
  congrm (1 - ?_) / $(by simp)
  rw [mul_add, ← add_assoc, Real.cos_add_int_mul_two_pi]

theorem φ_integrable_L (x : Fin 2 → ℤ) :
    IntegrableOn (fun w ↦ (1 - cos (x 0 * w.1 + x 1 * w.2)) / (4 - (2 * cos w.1 + 2 * cos w.2)))
    triangleL := by
  obtain h := φ_integrable_mapL x
  rw [MeasurePreserving.integrableOn_image (by exact measurePreserving_add_right _ _)
    (MeasurableEquiv.measurableEmbedding _)] at h
  convert! h with p
  simp only [Fin.isValue, MeasurableEquiv.coe_addRight, Function.comp_apply, Prod.fst_add, add_zero,
    Prod.snd_add, cos_add_two_pi]
  congrm (1 - ?_) / $(by simp)
  rw [mul_add, add_right_comm, Real.cos_add_int_mul_two_pi]

theorem φ_integrable_R (x : Fin 2 → ℤ) :
    IntegrableOn (fun w ↦ (1 - cos (x 0 * w.1 + x 1 * w.2)) / (4 - (2 * cos w.1 + 2 * cos w.2)))
    triangleR := by
  obtain h := φ_integrable_mapR x
  rw [MeasurePreserving.integrableOn_image (by exact measurePreserving_add_right _ _)
    (MeasurableEquiv.measurableEmbedding _)] at h
  convert! h with p
  simp only [Fin.isValue, neg_mul, MeasurableEquiv.coe_addRight, Function.comp_apply, Prod.fst_add,
    add_zero, Prod.snd_add, ← sub_eq_add_neg, cos_sub_two_pi]
  congrm (1 - ?_) / $(by simp)
  rw [mul_sub, ← add_sub_right_comm, Real.cos_sub_int_mul_two_pi]

theorem φ_integrable_diamond (x : Fin 2 → ℤ) :
    IntegrableOn (fun w ↦ (1 - cos (x 0 * w.1 + x 1 * w.2)) / (4 - (2 * cos w.1 + 2 * cos w.2)))
    diamond := by
  rw [diamond_decomp]
  refine IntegrableOn.union ?_ (φ_integrable_2d x)
  refine IntegrableOn.union ?_ (φ_integrable_R x)
  refine IntegrableOn.union ?_ (φ_integrable_L x)
  exact IntegrableOn.union (φ_integrable_U x) (φ_integrable_D x)

/-! We then show there is no overlap between regions. -/

theorem disjoint_U_D : AEDisjoint volume triangleU triangleD := by
  apply Disjoint.aedisjoint
  apply Set.disjoint_left.mpr fun p h1 h2 ↦ ?_
  simp [triangleU] at h1
  simp [triangleD] at h2
  linarith [pi_pos]

theorem disjoint_U_L : AEDisjoint volume triangleU triangleL := by
  suffices triangleU ∩ triangleL ⊆ {(-π, π)} from Measure.mono_null this (by simp)
  intro p hp
  simp only [triangleU, triangleL, Set.mem_inter_iff, Set.mem_setOf_eq] at hp
  rw [Set.mem_singleton_iff]
  ext
  · simp only
    linarith
  · simp only
    linarith

theorem disjoint_D_L : AEDisjoint volume triangleD triangleL := by
  suffices triangleD ∩ triangleL ⊆ {(-π, -π)} from Measure.mono_null this (by simp)
  intro p hp
  simp only [triangleD, triangleL, Set.mem_inter_iff, Set.mem_setOf_eq] at hp
  rw [Set.mem_singleton_iff]
  ext
  · simp only
    linarith
  · simp only
    linarith

theorem disjoint_U_R : AEDisjoint volume triangleU triangleR := by
  suffices triangleU ∩ triangleR ⊆ {(π, π)} from Measure.mono_null this (by simp)
  intro p hp
  simp only [triangleU, triangleR, Set.mem_inter_iff, Set.mem_setOf_eq] at hp
  rw [Set.mem_singleton_iff]
  ext
  · simp only
    linarith
  · simp only
    linarith

theorem disjoint_D_R : AEDisjoint volume triangleD triangleR := by
  suffices triangleD ∩ triangleR ⊆ {(π, -π)} from Measure.mono_null this (by simp)
  intro p hp
  simp only [triangleD, triangleR, Set.mem_inter_iff, Set.mem_setOf_eq] at hp
  rw [Set.mem_singleton_iff]
  ext
  · simp only
    linarith
  · simp only
    linarith

theorem disjoint_L_R : AEDisjoint volume triangleL triangleR := by
  apply Disjoint.aedisjoint
  apply Set.disjoint_left.mpr fun p h1 h2 ↦ ?_
  simp [triangleL] at h1
  simp [triangleR] at h2
  linarith [pi_pos]

theorem disjoint_U_sq : AEDisjoint volume triangleU (Set.Icc (-π) π ×ˢ Set.Icc (-π) π) := by
  suffices triangleU ∩ (Set.Icc (-π) π ×ˢ Set.Icc (-π) π) ⊆ Set.univ ×ˢ {π} by
    apply Measure.mono_null this
    simp [Measure.volume_eq_prod]
  intro p hp
  simp only [triangleU, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_prod, Set.mem_Icc] at hp
  simp only [Set.mem_prod, Set.mem_univ, Set.mem_singleton_iff, true_and]
  linarith

theorem disjoint_D_sq : AEDisjoint volume triangleD (Set.Icc (-π) π ×ˢ Set.Icc (-π) π) := by
  suffices triangleD ∩ (Set.Icc (-π) π ×ˢ Set.Icc (-π) π) ⊆ Set.univ ×ˢ {-π} by
    apply Measure.mono_null this
    simp [Measure.volume_eq_prod]
  intro p hp
  simp only [triangleD, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_prod, Set.mem_Icc] at hp
  simp only [Set.mem_prod, Set.mem_univ, Set.mem_singleton_iff, true_and]
  linarith

theorem disjoint_L_sq : AEDisjoint volume triangleL (Set.Icc (-π) π ×ˢ Set.Icc (-π) π) := by
  suffices triangleL ∩ (Set.Icc (-π) π ×ˢ Set.Icc (-π) π) ⊆ {-π} ×ˢ Set.univ by
    apply Measure.mono_null this
    simp [Measure.volume_eq_prod]
  intro p hp
  simp only [triangleL, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_prod, Set.mem_Icc] at hp
  simp only [Set.mem_prod, Set.mem_singleton_iff, Set.mem_univ, and_true]
  linarith

theorem disjoint_R_sq : AEDisjoint volume triangleR (Set.Icc (-π) π ×ˢ Set.Icc (-π) π) := by
  suffices triangleR ∩ (Set.Icc (-π) π ×ˢ Set.Icc (-π) π) ⊆ {π} ×ˢ Set.univ by
    apply Measure.mono_null this
    simp [Measure.volume_eq_prod]
  intro p hp
  simp only [triangleR, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_prod, Set.mem_Icc] at hp
  simp only [Set.mem_prod, Set.mem_singleton_iff, Set.mem_univ, and_true]
  linarith

theorem disjoint_map_U_D : AEDisjoint volume (MeasurableEquiv.addRight (0, -2 * π) '' triangleU)
    (MeasurableEquiv.addRight (0, 2 * π) '' triangleD) := by
  suffices (MeasurableEquiv.addRight (0, -2 * π) '' triangleU) ∩
      (MeasurableEquiv.addRight (0, 2 * π) '' triangleD) ⊆ {(0, 0)} by
    apply Measure.mono_null this
    simp
  intro p hp
  simp only [MeasurableEquiv.coe_addRight, Set.image_add_right, Prod.neg_mk,
    triangleU, Set.preimage_setOf_eq, Prod.snd_add, Prod.fst_add,
    triangleD, Set.mem_inter_iff, Set.mem_setOf_eq] at hp
  rw [Set.mem_singleton_iff]
  ext
  · simp only
    linarith
  · simp only
    linarith

theorem null_volume_diag : volume ({p | p.1 = p.2} : Set (ℝ × ℝ)) = 0 := by
  let f : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) := {
    toFun p := (p.1, p.1)
    map_add' a b := by simp
    map_smul' c a := by simp
  }
  have hmap : ({p | p.1 = p.2} : Set (ℝ × ℝ)) = f '' Set.univ := by
    aesop
  have hf : LinearMap.det f = 0 := by
    rw [LinearMap.det_eq_zero_iff_ker_ne_bot, Submodule.ne_bot_iff]
    use (0, 1)
    simp [f]
  rw [hmap, Measure.addHaar_image_linearMap, hf]
  simp

theorem null_volume_diag' : volume ({p | p.1 = -p.2} : Set (ℝ × ℝ)) = 0 := by
  let f : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) := {
    toFun p := (p.1, -p.1)
    map_add' a b := by simp [add_comm]
    map_smul' c a := by simp
  }
  have hmap : ({p | p.1 = -p.2} : Set (ℝ × ℝ)) = f '' Set.univ := by
    aesop
  have hf : LinearMap.det f = 0 := by
    rw [LinearMap.det_eq_zero_iff_ker_ne_bot, Submodule.ne_bot_iff]
    use (0, 1)
    simp [f]
  rw [hmap, Measure.addHaar_image_linearMap, hf]
  simp

theorem disjoint_map_U_L : AEDisjoint volume (MeasurableEquiv.addRight (0, -2 * π) '' triangleU)
    (MeasurableEquiv.addRight (2 * π, 0) '' triangleL) := by
  suffices (MeasurableEquiv.addRight (0, -2 * π) '' triangleU) ∩
      (MeasurableEquiv.addRight (2 * π, 0) '' triangleL) ⊆ {p | p.1 = -p.2} by
    exact Measure.mono_null this null_volume_diag'
  intro p hp
  simp only [MeasurableEquiv.coe_addRight, Set.image_add_right, Prod.neg_mk,
    triangleU, Set.preimage_setOf_eq, Prod.snd_add, Prod.fst_add,
    triangleL, Set.mem_inter_iff, Set.mem_setOf_eq] at hp
  rw [Set.mem_setOf_eq]
  linarith

theorem disjoint_map_D_L : AEDisjoint volume (MeasurableEquiv.addRight (0, 2 * π) '' triangleD)
    (MeasurableEquiv.addRight (2 * π, 0) '' triangleL) := by
  suffices (MeasurableEquiv.addRight (0, 2 * π) '' triangleD) ∩
      (MeasurableEquiv.addRight (2 * π, 0) '' triangleL) ⊆ {p | p.1 = p.2} by
    exact Measure.mono_null this null_volume_diag
  intro p hp
  simp only [MeasurableEquiv.coe_addRight, Set.image_add_right, Prod.neg_mk,
    triangleD, Set.preimage_setOf_eq, Prod.snd_add, Prod.fst_add,
    triangleL, Set.mem_inter_iff, Set.mem_setOf_eq] at hp
  rw [Set.mem_setOf_eq]
  linarith

theorem disjoint_map_U_R : AEDisjoint volume (MeasurableEquiv.addRight (0, -2 * π) '' triangleU)
    (MeasurableEquiv.addRight (-2 * π, 0) '' triangleR) := by
  suffices (MeasurableEquiv.addRight (0, -2 * π) '' triangleU) ∩
      (MeasurableEquiv.addRight (-2 * π, 0) '' triangleR) ⊆ {p | p.1 = p.2} by
    exact Measure.mono_null this null_volume_diag
  intro p hp
  simp only [MeasurableEquiv.coe_addRight, Set.image_add_right, Prod.neg_mk,
    triangleU, Set.preimage_setOf_eq, Prod.snd_add, Prod.fst_add,
    triangleR, Set.mem_inter_iff, Set.mem_setOf_eq] at hp
  rw [Set.mem_setOf_eq]
  linarith

theorem disjoint_map_D_R : AEDisjoint volume (MeasurableEquiv.addRight (0, 2 * π) '' triangleD)
    (MeasurableEquiv.addRight (-2 * π, 0) '' triangleR) := by
  suffices (MeasurableEquiv.addRight (0, 2 * π) '' triangleD) ∩
      (MeasurableEquiv.addRight (-2 * π, 0) '' triangleR) ⊆ {p | p.1 = -p.2} by
    exact Measure.mono_null this null_volume_diag'
  intro p hp
  simp only [MeasurableEquiv.coe_addRight, Set.image_add_right, Prod.neg_mk,
    triangleD, Set.preimage_setOf_eq, Prod.snd_add, Prod.fst_add,
    triangleR, Set.mem_inter_iff, Set.mem_setOf_eq] at hp
  rw [Set.mem_setOf_eq]
  linarith

theorem disjoint_map_L_R : AEDisjoint volume (MeasurableEquiv.addRight (2 * π, 0) '' triangleL)
    (MeasurableEquiv.addRight (-2 * π, 0) '' triangleR) := by
  suffices (MeasurableEquiv.addRight (2 * π, 0) '' triangleL) ∩
      (MeasurableEquiv.addRight (-2 * π, 0) '' triangleR) ⊆ {(0, 0)} by
    apply Measure.mono_null this
    simp
  intro p hp
  simp only [MeasurableEquiv.coe_addRight, Set.image_add_right, Prod.neg_mk,
    triangleL, Set.preimage_setOf_eq, Prod.snd_add, Prod.fst_add,
    triangleR, Set.mem_inter_iff, Set.mem_setOf_eq] at hp
  rw [Set.mem_singleton_iff]
  ext
  · simp only
    linarith
  · simp only
    linarith

/-! Now we can rewrite `φ` as a integral on the diamond. -/

theorem φ_2d_diamond (x : Fin 2 → ℤ) :
    φ x = (8 * π ^ 2)⁻¹ * ∫ w in diamond,
    (1 - cos (x 0 * w.1 + x 1 * w.2)) / (4 - (2 * cos w.1 + 2 * cos w.2)) := by
  rw [show (8 * π ^ 2)⁻¹ = 2⁻¹ * (4 * π ^ 2)⁻¹ by ring]
  rw [diamond_decomp]
  rw [setIntegral_union₀
    (((disjoint_U_sq.union_left disjoint_D_sq).union_left disjoint_L_sq).union_left disjoint_R_sq)
    (by measurability)
    (((((φ_integrable_U x).union (φ_integrable_D x))).union (φ_integrable_L x)).union
    (φ_integrable_R x)) (φ_integrable_2d x)]
  rw [mul_assoc, mul_add]
  rw [← φ_2d, mul_add]
  rw [← sub_eq_iff_eq_add, ← one_sub_mul, show (1 - 2⁻¹ : ℝ) = 2⁻¹ by ring]
  rw [φ_2d, square_comp]
  rw [setIntegral_union₀
    ((disjoint_map_U_R.union_left disjoint_map_D_R).union_left disjoint_map_L_R)
    (by unfold triangleR; measurability)
    ((((φ_integrable_mapU x).union (φ_integrable_mapD x))).union (φ_integrable_mapL x))
    (φ_integrable_mapR x)]
  rw [setIntegral_union₀ (disjoint_map_U_L.union_left disjoint_map_D_L)
    (by unfold triangleL; measurability)
    ((φ_integrable_mapU x).union (φ_integrable_mapD x)) (φ_integrable_mapL x)]
  rw [setIntegral_union₀ disjoint_map_U_D (by unfold triangleD; measurability)
    (φ_integrable_mapU x) (φ_integrable_mapD x)]
  rw [setIntegral_union₀ ((disjoint_U_R.union_left disjoint_D_R).union_left disjoint_L_R)
    (by unfold triangleR; measurability)
    ((((φ_integrable_U x).union (φ_integrable_D x))).union (φ_integrable_L x))
    (φ_integrable_R x)]
  rw [setIntegral_union₀ (disjoint_U_L.union_left disjoint_D_L) (by unfold triangleL; measurability)
    ((φ_integrable_U x).union (φ_integrable_D x)) (φ_integrable_L x)]
  rw [setIntegral_union₀ disjoint_U_D (by unfold triangleD; measurability)
    (φ_integrable_U x) (φ_integrable_D x)]
  congrm _ * (_ * (?_ + ?_ + ?_ + ?_))
  <;> rw [MeasurePreserving.setIntegral_image_emb
      (by exact measurePreserving_add_right _ _) (MeasurableEquiv.measurableEmbedding _)]
  · simp only [Fin.isValue, neg_mul, MeasurableEquiv.coe_addRight, Prod.fst_add, add_zero,
      Prod.snd_add, ← sub_eq_add_neg, cos_sub_two_pi]
    congrm ∫ p in _, (1 - ?_) / $(by simp)
    rw [mul_sub, ← add_sub_assoc, Real.cos_sub_int_mul_two_pi]
  · simp only [Fin.isValue, MeasurableEquiv.coe_addRight, Prod.fst_add, add_zero, Prod.snd_add,
      cos_add_two_pi]
    congrm ∫ p in _, (1 - ?_) / _
    rw [mul_add, ← add_assoc, Real.cos_add_int_mul_two_pi]
  · simp only [Fin.isValue, MeasurableEquiv.coe_addRight, Prod.fst_add, Prod.snd_add, add_zero,
      cos_add_two_pi]
    congrm ∫ p in _, (1 - ?_) / _
    rw [mul_add, add_right_comm, Real.cos_add_int_mul_two_pi]
  · simp only [Fin.isValue, neg_mul, MeasurableEquiv.coe_addRight, Prod.fst_add, ← sub_eq_add_neg,
      Prod.snd_add, add_zero, cos_sub_two_pi]
    congrm ∫ p in _, (1 - ?_) / _
    rw [mul_sub, ← add_sub_right_comm, Real.cos_sub_int_mul_two_pi]

/-! We perform the rotation, and finalize the result -/

def diamondRotate : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) where
  toFun p := (p.1 + p.2, p.1 - p.2)
  map_add' a b := by ext <;> simp <;> ring
  map_smul' c a := by ext <;> simp <;> ring

theorem det_diamondRotate : diamondRotate.det = -2 := by
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℝ)]
  suffices Matrix.det !![(1 : ℝ), 1; 1, -1] = -2 by
    convert this
    ext i j
    fin_cases i <;> fin_cases j <;> simp [diamondRotate, LinearMap.toMatrix_apply]
  simp
  norm_num

theorem diamondRotate_injective : Function.Injective diamondRotate := by
  change Function.Injective diamondRotate.toLinearMap
  rw [← LinearMap.ker_eq_bot, ← LinearMap.det_eq_zero_iff_ker_ne_bot.ne_left,
    ← ContinuousLinearMap.det, det_diamondRotate]
  simp

theorem diamond_eq_map : diamond = diamondRotate '' (Set.Icc (-π) π ×ˢ Set.Icc (-π) π) := by
  ext p
  simp only [diamond, neg_mul, tsub_le_iff_right, neg_le_sub_iff_le_add, Set.mem_setOf_eq,
    diamondRotate, ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk, Set.Icc_prod_Icc,
    Set.mem_image, Set.mem_Icc, Prod.exists, Prod.mk_le_mk]
  constructor
  · intro hp
    use (p.1 + p.2) / 2, (p.1 - p.2) / 2
    grind
  · intro hp
    grind

/-- The inner integration that we need to calculate. -/
theorem integral_sub_cos_inv {a : ℝ} (h1 : -1 < a) (h2 : a < 1) :
    ∫ (x : ℝ) in Set.Icc (-π) π, (2 - 2 * a * cos x)⁻¹ = π / √(1 - a ^ 2) := by
  have h1a : 1 + a ≠ 0 := by grind
  have hlt1a : 0 < 1 + a := by grind
  have h1a' : 1 - a ≠ 0 := by grind
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by simp [pi_nonneg])]
  have hcont : Continuous (fun x ↦ (2 - 2 * a * cos x)⁻¹) :=
      Continuous.inv₀ (by fun_prop) (fun x ↦ by
      apply ne_of_gt
      rw [sub_pos, mul_assoc]
      simp only [Nat.ofNat_pos, mul_lt_iff_lt_one_right]
      apply (abs_lt.mp ?_).2
      rw [abs_mul]
      apply mul_lt_one_of_nonneg_of_lt_one_left (abs_nonneg a)
        (abs_lt.mpr ⟨h1, h2⟩) (abs_cos_le_one _)
    )
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0)
    (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)]
  conv in ∫ (x : ℝ) in -π..0, _ =>
    rw [show (0 : ℝ) = -0 by simp]
  rw [← intervalIntegral.integral_comp_neg]
  simp_rw [cos_neg]
  rw [← two_mul]
  rw [← intervalIntegral.integral_const_mul]
  simp_rw [mul_assoc, ← mul_one_sub, ← div_eq_mul_inv,
    div_mul_cancel_left₀ (show (2 : ℝ) ≠ 0 by simp)]
  rw [intervalIntegral.integral_of_le pi_nonneg]
  rw [integral_Ioc_eq_integral_Ioo]
  have hintegrable : IntegrableOn (fun x ↦ (1 - a * cos x)⁻¹) (Set.Ioo 0 π) :=
    (Continuous.integrableOn_Ioc <| Continuous.inv₀ (by fun_prop) (fun x ↦ by
      apply ne_of_gt
      rw [sub_pos]
      apply (abs_lt.mp ?_).2
      rw [abs_mul]
      apply mul_lt_one_of_nonneg_of_lt_one_left (abs_nonneg a)
        (abs_lt.mpr ⟨h1, h2⟩) (abs_cos_le_one _)
    )).mono_set (Set.Ioo_subset_Ioc_self)
  let g (t : ℝ) := 2 / (1 + a) / ((1 - a) / (1 + a) + t ^ 2)
  let f (x : ℝ) := tan (x / 2)
  let f' (x : ℝ) := 1 / (1 + cos x)
  have hfs : f '' Set.Ioo 0 π = Set.Ioi 0 := by
    ext x
    simp only [Set.mem_image, Set.mem_Ioo, Set.mem_Ioi, f]
    constructor
    · rintro ⟨y, h, rfl⟩
      apply tan_pos_of_pos_of_lt_pi_div_two (by simpa using h.1)
      exact div_lt_div_of_pos_right h.2 (by simp)
    · intro h
      use arctan x * 2
      suffices arctan x * 2 < π by simpa [h]
      rw [← lt_div_iff₀ (by simp)]
      exact arctan_lt_pi_div_two x
  have heq ⦃x : ℝ⦄ (hx : x ∈ Set.Ioo 0 π) : (1 - a * cos x)⁻¹ = |f' x| • g (f x) := by
    rw [smul_eq_mul]
    have hcos: cos x ≠ -1 := by
      rw [ne_eq, cos_eq_neg_one_iff]
      contrapose hx
      obtain ⟨k, rfl⟩ := hx
      simp only [Set.mem_Ioo, add_lt_iff_neg_left, not_and, not_lt]
      intro h
      rw [← neg_lt_iff_pos_add', neg_eq_neg_one_mul, ← mul_assoc,
        mul_lt_mul_iff_of_pos_right pi_pos, ← div_lt_iff₀ (by simp)] at h
      have h1k : (-1 : ℝ) < k := lt_trans (by norm_num) h
      have h1k : -1 < k := by exact_mod_cast h1k
      have h0k : 0 ≤ k := by simpa using Int.le_of_sub_one_lt h1k
      exact mul_nonneg (by simpa using h0k) (by simp [pi_nonneg])
    unfold f'
    rw [abs_of_nonneg (div_nonneg (by simp) (by grw [← neg_one_le_cos]; simp))]
    unfold g f
    rw [Real.cos_eq_two_mul_tan_half_div_one_sub_tan_half_sq _ hcos]
    rw [div_add' _ _ _ h1a, div_div_div_cancel_right₀ h1a]
    rw [one_add_div (by positivity), add_add_sub_cancel]
    rw [← mul_div_mul_comm, one_mul, one_add_one_eq_two]
    field
  rw [setIntegral_congr_fun measurableSet_Ioo heq]
  replace hintegrable := hintegrable.congr_fun heq measurableSet_Ioo
  have hderiv : ∀ x ∈ Set.Ioo 0 π, HasDerivWithinAt f (f' x) (Set.Ioo 0 π) x := by
    intro x hx
    unfold f f'
    apply HasDerivAt.hasDerivWithinAt
    have hcos : cos (x / 2) ≠ 0 := by
      rw [cos_ne_zero_iff]
      intro k h
      have h : x = (2 * k + 1 : ℤ) * π := by simpa using h
      rw [h, Set.mem_Ioo, mul_lt_iff_lt_one_left pi_pos, mul_pos_iff_of_pos_right pi_pos] at hx
      norm_cast at hx
      grind
    obtain h := (Real.hasDerivAt_tan (by exact hcos)).comp _ ((hasDerivAt_id x).div_const 2)
    convert! h using 1
    rw [cos_sq, id]
    rw [mul_div_cancel₀ _ (by simp)]
    rw [← mul_div_mul_comm, one_mul, add_mul, div_mul_cancel₀ _ (by simp),
      div_mul_cancel₀ _ (by simp)]
  have hinj : Set.InjOn f (Set.Ioo 0 π) := by
    intro a ha b hb h
    unfold f at h
    obtain h := tan_inj_of_lt_of_lt_pi_div_two (by
      grw [← ha.1]
      simp [pi_pos]) ((div_lt_div_iff_of_pos_right (by simp)).mpr ha.2) (by
      grw [← hb.1]
      simp [pi_pos]) ((div_lt_div_iff_of_pos_right (by simp)).mpr hb.2) h
    simpa using h
  rw [← integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hderiv hinj g, hfs]
  rw [← integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioo hderiv hinj g, hfs]
    at hintegrable
  unfold g at ⊢ hintegrable
  have hdivpos : 0 < (1 - a) / (1 + a) := by
    apply div_pos
    · simpa using h2
    · exact hlt1a
  rw [show (1 - a) / (1 + a) = (√((1 - a) / (1 + a))) ^ 2 by
    rw [sq_sqrt]
    exact hdivpos.le] at ⊢ hintegrable
  rw [show 2 / (1 + a) = 2 / √((1 - a) * (1 + a)) * √((1 - a) / (1 + a)) by
    rw [div_mul, ← sqrt_div (by
      apply mul_nonneg
      · simpa using h2.le
      · exact hlt1a.le)]
    rw [← div_mul, mul_div_cancel_left₀ _ h1a', sqrt_mul_self hlt1a.le]] at ⊢ hintegrable
  simp_rw [mul_div_assoc] at ⊢ hintegrable
  rw [integral_const_mul]
  rw [IntegrableOn, integrable_const_mul_iff (by
    rw [isUnit_iff_ne_zero]
    apply div_ne_zero (by simp)
    rw [sqrt_ne_zero']
    apply mul_pos
    · simpa using h2
    · exact hlt1a
  ), ← IntegrableOn] at hintegrable
  rw [mul_comm (1 - a), ← sq_sub_sq, one_pow]
  obtain htendsto := intervalIntegral_tendsto_integral_Ioi 0 hintegrable tendsto_id
  simp_rw [integral_div_sq_add_sq] at htendsto
  simp only [id_eq, zero_div, arctan_zero, sub_zero] at htendsto
  obtain h := Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds
  have htendsto' : Tendsto (fun i ↦ arctan (i / √((1 - a) / (1 + a)))) atTop (𝓝 (Real.pi / 2)) := by
    apply (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp
    apply tendsto_id.atTop_div_const
    rw [sqrt_pos]
    exact hdivpos
  rw [tendsto_nhds_unique htendsto htendsto']
  ring

/-- A sum-of-sin formula to be used soon. -/
theorem sum_sin (n : ℕ) (x : ℝ) :
    ∑ k ∈ Finset.range n, sin ((2 * k + 1) * x) = (1 - cos (n * (2 * x))) / (2 * sin x) := by
  by_cases hx : sin x = 0
  · suffices ∑ k ∈ Finset.range n, sin ((2 * k + 1) * x) = 0 by simpa [hx]
    refine Finset.sum_eq_zero fun k _ ↦ ?_
    rw [sin_eq_zero_iff] at hx ⊢
    obtain ⟨n, rfl⟩ := hx
    use (2 * k + 1) * n
    push_cast
    ring
  rw [eq_div_iff (by simpa using hx)]
  rw [Finset.sum_mul]
  simp_rw [mul_left_comm _ (2 : ℝ) _, ← mul_assoc, two_mul_sin_mul_sin]
  simp_rw [show ∀ k : ℕ, cos ((2 * k + 1) * x - x) - cos ((2 * k + 1) * x + x) =
      -cos ((k + 1 : ℕ) * (2 * x)) - -cos (k * (2 * x)) by
    intro k
    push_cast
    ring_nf]
  rw [Finset.sum_range_sub (fun k ↦ -cos (k * (2 * x)))]
  simp only [Nat.cast_zero, zero_mul, cos_zero]
  ring_nf

/-- Formula for `φ` on the diagonal in the 2D case. -/
theorem φ_2d_diagonal (n : ℕ) : φ (![n, n]) = π⁻¹ * ∑ k ∈ Finset.range n, (2 * k + 1 : ℝ)⁻¹ := by
  rw [φ_2d_diamond]
  obtain hintegrable := φ_integrable_diamond ![n, n]
  rw [diamond_eq_map] at ⊢ hintegrable
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume
    (by measurability) (fun _ _ ↦ diamondRotate.hasFDerivWithinAt) diamondRotate_injective.injOn _]
  rw [integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume
    (by measurability) (fun _ _ ↦ diamondRotate.hasFDerivWithinAt) diamondRotate_injective.injOn _]
    at hintegrable
  rw [Measure.volume_eq_prod, MeasureTheory.setIntegral_prod _ hintegrable]
  rw [det_diamondRotate, abs_neg, abs_of_nonneg (by simp)]
  suffices (8 * π ^ 2)⁻¹ * ∫ (x) (y) in Set.Icc (-π) π,
      2 * ((1 - cos (n * (2 * x))) / (4 - 2 * (2 * cos x * cos y))) =
      π⁻¹ * ∑ k ∈ Finset.range n, (2 * k + 1 : ℝ)⁻¹ by
    simpa [diamondRotate, ← mul_add, cos_add_cos, ← two_mul]
  simp_rw [mul_comm (2 : ℝ), div_mul, sub_div (4 : ℝ),
    mul_div_cancel_right₀ _ (show (2 : ℝ) ≠ 0 by simp), show (4 / 2 : ℝ) = 2 by norm_num,
    div_eq_mul_inv, integral_const_mul, mul_comm _ (2 : ℝ)]
  suffices (8 * π ^ 2)⁻¹ *
      ∫ (x : ℝ) in Set.Icc (-π) π, (1 - cos (↑n * (2 * |x|))) * ((2 * π) / (2 * sin |x|)) =
      π⁻¹ * ∑ k ∈ Finset.range n, (2 * k + 1 : ℝ)⁻¹ by
    convert this using 2
    apply setIntegral_congr_ae measurableSet_Icc
    filter_upwards [Measure.ae_ne _ (-π), Measure.ae_ne _ π, Measure.ae_ne _ 0] with x h0 h1 h2 hx
    congrm (1 - ?_) * ?_
    · rw [← cos_abs, abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _),
        abs_of_nonneg (Nat.ofNat_nonneg _)]
    · rw [mul_div_mul_left _ _ (by simp)]
      rw [integral_sub_cos_inv ?_ ?_, ← abs_sin_eq_sqrt_one_sub_cos_sq,
        Real.abs_sin_eq_sin_abs_of_abs_le_pi (abs_le.mpr hx)]
      · apply lt_of_le_of_ne' (neg_one_le_cos _)
        rw [ne_eq, cos_eq_neg_one_iff]
        by_contra h
        obtain ⟨k, rfl⟩ := h
        simp only [Set.mem_Icc, add_le_iff_nonpos_right] at hx
        obtain ⟨hx1, hx2⟩ := hx
        rw [← sub_le_iff_le_add', ← neg_add', ← two_mul, neg_eq_neg_one_mul,
          mul_le_mul_iff_of_pos_right (by positivity)] at hx1
        rw [← le_div_iff₀ (by positivity), zero_div] at hx2
        have hx1 : -1 ≤ k := by exact_mod_cast hx1
        have hx2 : k ≤ 0 := by exact_mod_cast hx2
        interval_cases k
        · ring_nf at h0
          simp at h0
        · simp at h1
      · apply lt_of_le_of_ne (cos_le_one _)
        rw [ne_eq, cos_eq_one_iff_of_lt_of_lt
          (lt_of_lt_of_le (by simp [two_mul, pi_pos]) hx.1)
          (lt_of_le_of_lt hx.2 (by simp [two_mul, pi_pos]))]
        exact h2
  simp_rw [← mul_div_assoc, mul_div_right_comm, integral_mul_const, ← sum_sin]
  rw [integral_finsetSum _ (fun k _ ↦ ContinuousOn.integrableOn_Icc (by fun_prop))]
  rw [Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]
  congr with k
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by simp [pi_nonneg])]
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0)
    (Continuous.intervalIntegrable (by fun_prop) _ _)
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  conv in ∫ (x : ℝ) in -π..0, _ =>
    rw [show (0 : ℝ) = -0 by simp]
  rw [← intervalIntegral.integral_comp_neg]
  simp_rw [abs_neg]
  rw [← two_mul]
  have : ∫ (x : ℝ) in 0..π, sin ((2 * ↑k + 1) * |x|) =
      ∫ (x : ℝ) in 0..π, sin ((2 * ↑k + 1) * x) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_lt pi_pos] at hx
    simp only
    rw [abs_of_nonneg hx.1]
  rw [this]
  rw [intervalIntegral.integral_comp_mul_left sin (by positivity)]
  rw [integral_sin, mul_zero, cos_zero, add_one_mul, mul_comm (2 : ℝ) k, mul_assoc (k : ℝ) 2,
    Real.cos_nat_mul_two_pi_add_pi, smul_eq_mul]
  field

/-! With the formula ready, we can calculate `φ` at any given point. In fact, we can write a
recursive algorithm for this. -/

/-- A triangular table that records value for `φ` -/
structure φTable where
  /-- All `φ` are rational combinations of `π` and `1`, so we use a rational vector to represent
  the coefficents. -/
  data : List (List (ℚ × ℚ))
  length_eq (i : ℕ) (h : i < data.length) : data[i].length = i + 1
  eq_φ (i : ℕ) (hi : i < data.length) (j : ℕ) (hj : j < data[i].length) :
    (fun (p : ℚ × ℚ) ↦ p.1 * π⁻¹ + p.2) data[i][j] = φ ![i, j]

set_option maxHeartbeats 800000 in
-- For some reason this is really slow
/-- Given a `φTable`, we can extend it by another column. -/
def growφTable (input : φTable) : φTable :=
  match hl : input.data.length with
  | 0 =>
    {
      data := input.data ++ [[(0, 0)]]
      length_eq i h := by
        have h : i ≤ input.data.length := by simpa using h
        rcases lt_or_eq_of_le h with h | h
        · rw [List.getElem_append_left h]
          exact input.length_eq i h
        · rw [List.getElem_append_right h.symm.le]
          simpa [hl] using h
      eq_φ i hi j hj := by
        have hi : i = 0 := by simpa [hl] using hi
        have hdata : input.data = [] := List.eq_nil_iff_length_eq_zero.mpr hl
        have hj : j = 0 := by simpa [hi, hdata] using hj
        simp [hi, hj, hdata, show ![(0 : ℤ), 0] = 0 by simp]
    }
  | 1 =>
    {
      data := input.data ++ [[(0, 4⁻¹), (1, 0)]]
      length_eq i h := by
        have h : i ≤ input.data.length := by simpa using h
        rcases lt_or_eq_of_le h with h | h
        · rw [List.getElem_append_left h]
          exact input.length_eq i h
        · rw [List.getElem_append_right h.symm.le]
          simpa [hl] using h
      eq_φ i hi j hj := by
        rw [List.length_append, List.length_singleton, Nat.lt_add_one_iff_lt_or_eq] at hi
        rcases hi with hi | hi
        · rw [List.getElem_append_left hi] at hj
          suffices (input.data ++ [[(0, 4⁻¹), (1, 0)]])[i][j] = input.data[i][j] by
            rw [this]
            exact input.eq_φ i hi j hj
          congrm ?_[j]
          rw [List.getElem_append_left hi]
        · rw [List.getElem_append_right hi.symm.le] at hj
          have hj : j ≤ 1 := by simpa [hl, hi] using hj
          have : (input.data ++ [[(0, 4⁻¹), (1, 0)]])[i][j] =
              [(0, 4⁻¹), (1, 0)][j]'(by simpa using hj) := by
            congrm ?_[j]'_
            rw [List.getElem_append_right hi.symm.le]
            simp [hi]
          rw [this]
          rw [hl] at hi
          interval_cases j
          · simp [hi, φ_2d_1_0]
          · rw [hi, φ_2d_diagonal 1]
            simp
    }
  | n + 2 =>
    {
      data := input.data ++ [List.ofFn fun (j : Fin (n + 3)) ↦
        if hj0 : j.val = 0 then
          haveI : 0 < input.data[n + 1].length := by
            simp [input.length_eq (n + 1)]
          haveI : 1 < input.data[n + 1].length := by
            simp [input.length_eq (n + 1)]
          haveI : 0 < input.data[n].length := by
            simp [input.length_eq n]
          4 * input.data[n + 1][0] - 2 * input.data[n + 1][1] - input.data[n][0]
        else if hj2 : j.val = n + 2 then
          haveI : n + 1 < input.data[n + 1].length := by
            simp [input.length_eq (n + 1)]
          input.data[n + 1][n + 1] + (((2 * n + 3 : ℕ) : ℚ)⁻¹, 0)
        else if hj1 : j.val = n + 1 then
          haveI : j.val < input.data[n + 1].length := by
            simp [input.length_eq (n + 1), hj1]
          haveI : j.val - 1 < input.data[n + 1].length := by
            simp [input.length_eq (n + 1), hj1]
          2 * input.data[n + 1][j.val] - input.data[n + 1][j.val - 1]
        else
          haveI : j.val < input.data[n + 1].length := by
            rw [input.length_eq (n + 1)]
            grind
          haveI : j.val + 1 < input.data[n + 1].length := by
            rw [input.length_eq (n + 1)]
            grind
          haveI : j.val - 1 < input.data[n + 1].length := by
            rw [input.length_eq (n + 1)]
            grind
          haveI : j.val < input.data[n].length := by
            rw [input.length_eq n]
            grind
          4 * input.data[n + 1][j.val] - input.data[n + 1][j.val - 1]
            - input.data[n + 1][j.val + 1] - input.data[n][j.val]
      ]
      length_eq i h := by
        have h : i ≤ input.data.length := by simpa using h
        rcases lt_or_eq_of_le h with h | h
        · rw [List.getElem_append_left h]
          exact input.length_eq i h
        · rw [List.getElem_append_right h.symm.le]
          have hl : input.data.length = n + 1 + 1 := by simpa using hl
          simpa [hl] using h.symm
      eq_φ i hi j hj := by
        have hl : input.data.length = n + 2 := by simpa using hl
        rw [List.length_append, List.length_singleton, Nat.lt_add_one_iff_lt_or_eq] at hi
        rcases hi with hi | hi
        · rw [List.getElem_append_left hi] at hj
          have (p : List (ℚ × ℚ)) (hi' : i < (input.data ++ [p]).length)
              (hj : j < (input.data ++ [p])[i].length):
              (input.data ++ [p])[i][j] = input.data[i][j] := by
            congrm ?_[j]'_
            rw [List.getElem_append_left hi]
          rw [this]
          exact input.eq_φ i hi j hj
        · rw [List.getElem_append_right hi.symm.le] at hj
          have hj : j ≤ n + 1 + 1 := by simpa using hj
          have (p : List (ℚ × ℚ)) (hi' : i < (input.data ++ [p]).length)
              (hj : j < (input.data ++ [p])[i].length) (hj' : j < p.length):
              (input.data ++ [p])[i][j] = p[j] := by
            congrm ?_[j]'_
            rw [List.getElem_append_right hi.symm.le]
            simp [hi]
          rw [this _ _ _ (by simpa using hj)]
          rw [List.getElem_ofFn]
          simp only [Nat.cast_ofNat, Nat.cast_add, dite_eq_ite, Nat.succ_eq_add_one, Nat.reduceAdd]
          split
          next hj0 =>
            have : 0 < input.data[n + 1].length := by
              simp [input.length_eq (n + 1)]
            have : 1 < input.data[n + 1].length := by
              simp [input.length_eq (n + 1)]
            have : 0 < input.data[n].length := by
              simp [input.length_eq n]
            suffices
                4 * (fun (p : ℚ × ℚ) ↦ p.1 * π⁻¹ + p.2) input.data[n + 1][0] -
                2 * (fun (p : ℚ × ℚ) ↦ p.1 * π⁻¹ + p.2) input.data[n + 1][1] -
                (fun (p : ℚ × ℚ) ↦ p.1 * π⁻¹ + p.2) input.data[n][0] = φ ![i, j] by
              simp at this ⊢
              linear_combination this
            simp_rw [input.eq_φ]
            rw [hj0, hi, hl]
            push_cast
            obtain h := φ_2d_kirchhoff_of_ne_zero (n + 1) 0 (by grind)
            simp [show ∀ (n : ℤ), n + 1 + 1 = n + 2 by intro n; ring] at h
            linear_combination h
          next hj0 =>
          split
          next hj2 =>
            have : n + 1 < input.data[n + 1].length := by
              simp [input.length_eq (n + 1)]
            suffices (fun (p : ℚ × ℚ) ↦ p.1 * π⁻¹ + p.2) input.data[n + 1][n + 1] +
                (fun (p : ℚ × ℚ) ↦ p.1 * π⁻¹ + p.2) (((2 * n + 3 : ℕ) : ℚ)⁻¹, 0) = φ ![i, j] by
              simp at this ⊢
              linear_combination this
            simp_rw [input.eq_φ]
            rw [hj2, hi, hl, φ_2d_diagonal, φ_2d_diagonal]
            conv_rhs =>
              rw [show n + 2 = n + 1 + 1 by ring, Finset.sum_range_succ]
            push_cast
            ring
          next hj2 =>
          split
          next hj1 =>
            haveI : j < input.data[n + 1].length := by
              simp [input.length_eq (n + 1), hj1]
            haveI : j - 1 < input.data[n + 1].length := by
              simp [input.length_eq (n + 1), hj1]
            suffices 2 * (fun (p : ℚ × ℚ) ↦ p.1 * π⁻¹ + p.2) input.data[n + 1][j] -
                (fun (p : ℚ × ℚ) ↦ p.1 * π⁻¹ + p.2) input.data[n + 1][j - 1] = φ ![i, j] by
              simp at this ⊢
              linear_combination this
            simp_rw [input.eq_φ]
            rw [hj1, hi, hl, Nat.add_sub_cancel]
            push_cast
            rw [← mul_left_inj' (show (2 : ℝ) ≠ 0 by simp)]
            obtain h := φ_2d_kirchhoff_of_ne_zero (n + 1) (n + 1) (by grind)
            simp [show ∀ (n : ℤ), n + 1 + 1 = n + 2 by intro n; ring,
              φ_swap n (n + 1), φ_swap (n + 1) (n + 2)] at h
            linear_combination h
          next hj1 =>
            haveI : j < input.data[n + 1].length := by
              rw [input.length_eq (n + 1)]
              grind
            haveI : j + 1 < input.data[n + 1].length := by
              rw [input.length_eq (n + 1)]
              grind
            haveI : j - 1 < input.data[n + 1].length := by
              rw [input.length_eq (n + 1)]
              grind
            haveI : j < input.data[n].length := by
              rw [input.length_eq n]
              grind
            suffices 4 * (fun (p : ℚ × ℚ) ↦ p.1 * π⁻¹ + p.2) input.data[n + 1][j] -
                (fun (p : ℚ × ℚ) ↦ p.1 * π⁻¹ + p.2) input.data[n + 1][j - 1] -
                (fun (p : ℚ × ℚ) ↦ p.1 * π⁻¹ + p.2) input.data[n + 1][j + 1] -
                (fun (p : ℚ × ℚ) ↦ p.1 * π⁻¹ + p.2) input.data[n][j] = φ ![↑i, ↑j] by
              simp at this ⊢
              linear_combination this
            simp_rw [input.eq_φ]
            rw [hi, hl]
            have hj1' : 1 ≤ j := by grind
            push_cast [hj1']
            obtain h := φ_2d_kirchhoff_of_ne_zero (n + 1) j (by grind)
            simp [show ∀ (n : ℤ), n + 1 + 1 = n + 2 by intro n; ring] at h
            linear_combination h
    }

/-- Compute `getφTable` of a specific size. -/
def getφTable (length : ℕ) : φTable :=
  match length with
  | 0 =>
    {
      data := []
      length_eq i h := by simp at h
      eq_φ i hi j hj := by simp at hi
    }
  | n + 1 =>
    growφTable (getφTable n)

@[simp]
theorem length_getφTable (length : ℕ) : (getφTable length).data.length = length := by
  induction length with
  | zero => simp [getφTable]
  | succ n ih =>
    rw [getφTable, growφTable]
    grind

/-- Compute `φ` at any point in the first quadrant. -/
def computeφ (x y : ℕ) : ℚ × ℚ :=
  if h : x ≤ y then
    ((getφTable (y + 1)).data[y]'(by simp))[x]'
      (h.trans_lt (by simp [(getφTable (y + 1)).length_eq]))
  else
    ((getφTable (x + 1)).data[x]'(by simp))[y]'
      ((lt_of_not_ge h).trans (by simp [(getφTable (x + 1)).length_eq]))

theorem computeφ_eq (x y : ℕ) :
    (fun (p : ℚ × ℚ) ↦ p.1 * π⁻¹ + p.2) (computeφ x y) = φ ![x, y] := by
  by_cases h : x ≤ y
  · simp only [computeφ, h, ↓reduceDIte, (getφTable (y + 1)).eq_φ]
    exact φ_swap y x
  · simp only [computeφ, h, ↓reduceDIte, (getφTable (x + 1)).eq_φ]

theorem equivResistance_eq_of_computeφ (x y : ℕ) (a b : ℚ) (h : computeφ x y = (a / 2, b / 2)) :
    equivResistance ![ofNat(x), ofNat(y)] = some (a * π⁻¹ + b) := by
  change equivResistance ![x, y] = some (a * π⁻¹ + b)
  rw [equivResistance_eq_two_mul_φ, ← computeφ_eq, h]
  simp
  ring

open Lean Qq in
meta def realToRatExpr (e : Q(ℝ)) : MetaM (TSyntax `term) := do
  match e with
  | ~q(OfNat.ofNat $n (self := _)) =>
    let some n := n.rawNatLit? | throwError "{n} is not a natural number"
    .pure <| quote n
  | ~q(OfNat.ofNat $m (self := _) / OfNat.ofNat $n (self := _)) =>
    let some m := m.rawNatLit? | throwError "{m} is not a natural number"
    let some n := n.rawNatLit? | throwError "{n} is not a natural number"
    `($(quote m) / $(quote n))
  | _ => throwError "Unsupported expression {e}"

open Lean Lean.Elab.Tactic Qq in
elab "comput_resistance" : tactic =>
  withMainContext do
    let e ← getMainTarget
    let ⟨u, α, e⟩ ← inferTypeQ e
    match u, α, e with
    | 1, ~q(Prop), ~q(equivResistance ![ofNat($x), ofNat($y)] = some ($rhs)) =>
      let some x := x.rawNatLit? | throwError "{x} is not a natural number"
      let some y := y.rawNatLit? | throwError "{y} is not a natural number"
      let x : TSyntax `term := quote x
      let y : TSyntax `term := quote y
      let (a, b) : TSyntax `term × TSyntax `term ← match rhs with
      | ~q($a * π⁻¹ + $b) =>
        let a ← realToRatExpr a
        let b ← realToRatExpr b
        .pure (a, b)
      | ~q($a * π⁻¹ - $b) =>
        let a ← realToRatExpr a
        let b ← realToRatExpr b
        let nb ← `(-$b)
        .pure (a, nb)
      | ~q($b - $a * π⁻¹) =>
        let a ← realToRatExpr a
        let b ← realToRatExpr b
        let na ← `(-$a)
        .pure (na, b)
      | ~q($a * π⁻¹) =>
        let a ← realToRatExpr a
        .pure (a, quote 0)
      | ~q($a) =>
        let a ← realToRatExpr a
        .pure (quote 0, a)
      | _ => throwError "Unsupported expression"
      evalTactic (← `(tactic| rw [equivResistance_eq_of_computeφ $x $y $a $b ?_]))
      evalTactic (← `(tactic| · congrm some ?_; ring))
      evalTactic (← `(tactic| · decide +kernel))
    | _, _, _ => throwError "Unsupported expression"

/-! Now we can verify the value of `φ` at any point in the first quadrant with just kernel
reduction. -/

theorem equivResistance_0_0 : equivResistance ![0, 0] = some (0) := by
  comput_resistance

theorem equivResistance_1_0 : equivResistance ![1, 0] = some (1 / 2) := by
  comput_resistance

theorem equivResistance_1_1 : equivResistance ![1, 1] = some (2 * π⁻¹) := by
  comput_resistance

theorem equivResistance_2_0 : equivResistance ![2, 0] = some (2 - 4 * π⁻¹) := by
  comput_resistance

/-- ✅ This is the answer of the original question: the equivalent resistance is $4 / \pi - 1 / 2$.
-/
theorem equivResistance_2_1 : equivResistance ![2, 1] = some (4 * π⁻¹ - 1 / 2) := by
  comput_resistance

theorem equivResistance_2_2 : equivResistance ![2, 2] = some (8 / 3 * π⁻¹) := by
  comput_resistance

theorem equivResistance_3_0 : equivResistance ![3, 0] = some (17 / 2 - 24 * π⁻¹) := by
  comput_resistance

theorem equivResistance_3_1 : equivResistance ![3, 1] = some (46 / 3 * π⁻¹ - 4) := by
  comput_resistance

theorem equivResistance_3_2 : equivResistance ![3, 2] = some (4 / 3 * π⁻¹ + 1 / 2) := by
  comput_resistance

theorem equivResistance_3_3 : equivResistance ![3, 3] = some (46 / 15 * π⁻¹) := by
  comput_resistance

theorem equivResistance_4_0 : equivResistance ![4, 0] = some (40 - 368 / 3 * π⁻¹) := by
  comput_resistance

theorem equivResistance_4_1 : equivResistance ![4, 1] = some (80 * π⁻¹ - 49 / 2) := by
  comput_resistance

theorem equivResistance_4_2 : equivResistance ![4, 2] = some (6 - 236 / 15 * π⁻¹) := by
  comput_resistance

theorem equivResistance_4_3 : equivResistance ![4, 3] = some (24 / 5 * π⁻¹ - 1 / 2) := by
  comput_resistance

theorem equivResistance_4_4 : equivResistance ![4, 4] = some (352 / 105 * π⁻¹) := by
  comput_resistance

/-- As a show case, the result can go really complicated for points far away. -/
theorem equivResistance_42_7 :
    equivResistance ![42, 7] =
    some (153187295540054887568710365479790124181572588052 / 200507537800595025 * π⁻¹ -
    486376034966331052956526218433 / 2) := by
  comput_resistance
