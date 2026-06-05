import Mathlib
open Real MeasureTheory Asymptotics Filter intervalIntegral

theorem asymptotic_bessel :
    (fun x ↦ ∫ (r : ℝ) in 0..x, ∫ (θ : ℝ) in -π..π, (1 - cos (r * cos θ)) / r) =Θ[atTop] log := by
  sorry
