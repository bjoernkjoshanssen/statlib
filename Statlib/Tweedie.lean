/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/
module
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Data.Real.StarOrdered
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Tweedie distribution: integral of the (compound-Poisson) density

  For `1 < p < 2` the Tweedie exponential dispersion model with mean `μ` and
  dispersion `φ` has a density supported on `(0, ∞)` whose integral is
  `1 - exp(-μ^(2-p) / (φ (2-p)))`; the
  remaining mass is the atom at `0`.

-/

@[expose] public section

open MeasureTheory Set

/-- The "a"-factor of the Tweedie density (the infinite series). -/
noncomputable def a (y φ p : ℝ) :=
  let α := (2 - p) / (1 - p)
  (1/y) * ∑' j : ℕ, (y ^ (- j * α) * (p - 1) ^(α * j)) /
  (φ ^ (j * (1 - α)) * (2 - p) ^ j * Nat.factorial j * Real.Gamma (- j * α))

/-- The Tweedie density. -/
noncomputable def tweediePDF (μ φ p : ℝ) :=
  Set.indicator ({y | 0 < y})
  (fun y => a y φ p * Real.exp ((1 / φ) * ((μ ^ ( 1 - p) / (1 - p)) * y - (μ ^ (2 - p) / (2 - p)))))

/-- The Poisson rate `z = μ^(2-p) / (φ (2-p))`; the answer is `1 - exp(-z)`. -/
noncomputable def tw_z (μ φ p : ℝ) : ℝ := μ ^ (2 - p) / (φ * (2 - p))

/-- The `j`-th summand of the integrand `a y * exp(...)`, faithful to the definition of `a`. -/
noncomputable def tw_G (μ φ p : ℝ) (j : ℕ) (y : ℝ) : ℝ :=
  let α := (2 - p) / (1 - p)
  (1/y) * ((y ^ (- j * α) * (p - 1) ^(α * j)) /
    (φ ^ (j * (1 - α)) * (2 - p) ^ j * Nat.factorial j * Real.Gamma (- j * α)))
  * Real.exp ((1 / φ) * ((μ ^ ( 1 - p) / (1 - p)) * y - (μ ^ (2 - p) / (2 - p))))

/-- Closed form of `tw_G j y` for `y > 0`: a constant times `y^(-jα-1) * exp(-(rate)·y)`. -/
lemma tw_pt (μ φ p : ℝ) (hp₁ : 1 < p) (hp₂ : p < 2) (hφ : 0 < φ) (j : ℕ) {y : ℝ} (hy : 0 < y) :
    tw_G μ φ p j y
    = (Real.exp (-tw_z μ φ p) * (p-1)^(((2-p)/(1-p))*(j:ℝ))
        / (φ^((j:ℝ)*(1-(2-p)/(1-p))) * (2-p)^j * (Nat.factorial j)
          * Real.Gamma (-(j:ℝ)*((2-p)/(1-p)))))
      * (y ^ (-(j:ℝ)*((2-p)/(1-p)) - 1) * Real.exp (-(μ ^ (1 - p) / (φ * (p - 1)) * y))) := by
  have h1p : (1 - p) ≠ 0 := by linarith
  have h2p : (2 - p) ≠ 0 := by linarith
  have hpm1 : (p - 1) ≠ 0 := by linarith
  rw [tw_G]
  have hexp : Real.exp ((1 / φ) * ((μ ^ ( 1 - p) / (1 - p)) * y - (μ ^ (2 - p) / (2 - p))))
      = Real.exp (-tw_z μ φ p) * Real.exp (-(μ ^ (1 - p) / (φ * (p - 1)) * y)) := by
    rw [← Real.exp_add]; congr 1; rw [tw_z]; field_simp; ring
  rw [hexp]
  have hypow : (1/y) * (y ^ (-(j:ℝ)*((2-p)/(1-p)))) = y ^ (-(j:ℝ)*((2-p)/(1-p)) - 1) := by
    rw [Real.rpow_sub hy, Real.rpow_one]; ring
  rw [← hypow]; ring

/-- The integrand is the pointwise tsum of the `tw_G` family. -/
lemma tw_pointwise (μ φ p : ℝ) (y : ℝ) :
    a y φ p * Real.exp ((1 / φ) * ((μ ^ ( 1 - p) / (1 - p)) * y - (μ ^ (2 - p) / (2 - p))))
      = ∑' j : ℕ, tw_G μ φ p j y := by
  simp only [a, tw_G]
  rw [tsum_mul_right, tsum_mul_left]

/-- The zeroth term vanishes identically (`Γ(0) = 0`). -/
lemma tw_G_zero (μ φ p y : ℝ) : tw_G μ φ p 0 y = 0 := by
  simp [tw_G, Real.Gamma_zero]

/-- The summand is nonnegative on `(0, ∞)`. -/
lemma tw_G_nonneg (μ φ p : ℝ) (hp₁ : 1 < p) (hp₂ : p < 2) (hφ : 0 < φ)
    (j : ℕ) {y : ℝ} (hy : 0 < y) : 0 ≤ tw_G μ φ p j y := by
  rcases Nat.eq_zero_or_pos j with hj0 | hjpos
  · subst hj0; rw [tw_G_zero]
  · have hjposR : 0 < (j:ℝ) := by exact_mod_cast hjpos
    have hαneg : (2 - p) / (1 - p) < 0 := div_neg_of_pos_of_neg (by linarith) (by linarith)
    have ha0pos : 0 < -(j:ℝ) * ((2-p)/(1-p)) := by
      have : -(j:ℝ) < 0 := by simpa using hjposR
      exact mul_pos_of_neg_of_neg this hαneg
    have hΓ : 0 < Real.Gamma (-(j:ℝ)*((2-p)/(1-p))) := Real.Gamma_pos_of_pos ha0pos
    have h2 : (0:ℝ) < 2 - p := by linarith
    have hp1 : (0:ℝ) < p - 1 := by linarith
    rw [tw_pt μ φ p hp₁ hp₂ hφ j hy]
    positivity

/-- Each `tw_G j` is integrable on `(0, ∞)`. -/
lemma tw_integrable_on (μ φ p : ℝ) (hp₁ : 1 < p) (hp₂ : p < 2) (hμ : 0 < μ) (hφ : 0 < φ)
    (j : ℕ) : IntegrableOn (fun y => tw_G μ φ p j y) (Set.Ioi 0) := by
  rcases Nat.eq_zero_or_pos j with hj0 | hjpos0
  · subst hj0; simp only [tw_G_zero]; exact integrableOn_zero
  · have h1p : (1 - p) ≠ 0 := by intro h; linarith
    have hp1 : (0:ℝ) < p - 1 := by linarith
    have hjpos : 0 < (j:ℝ) := by exact_mod_cast hjpos0
    have hαneg : (2 - p) / (1 - p) < 0 := div_neg_of_pos_of_neg (by linarith) (by linarith)
    have ha0pos : 0 < -(j:ℝ) * ((2-p)/(1-p)) := by
      have : -(j:ℝ) < 0 := by simpa using hjpos
      exact mul_pos_of_neg_of_neg this hαneg
    have hμpow : 0 < μ ^ (1 - p) := Real.rpow_pos_of_pos hμ _
    have hrpos : 0 < μ ^ (1 - p) / (φ * (p - 1)) := by positivity
    have hbase : IntegrableOn
        (fun y => y ^ (-(j:ℝ)*((2-p)/(1-p)) - 1)
          * Real.exp (-(μ ^ (1 - p) / (φ * (p - 1))) * y ^ (1:ℝ))) (Set.Ioi 0) :=
      integrableOn_rpow_mul_exp_neg_mul_rpow (by linarith [ha0pos]) (le_refl 1) hrpos
    have hbase2 : IntegrableOn
        (fun y => y ^ (-(j:ℝ)*((2-p)/(1-p)) - 1)
          * Real.exp (-(μ ^ (1 - p) / (φ * (p - 1)) * y))) (Set.Ioi 0) := by
      apply IntegrableOn.congr_fun hbase _ measurableSet_Ioi
      intro y hy; simp only [Real.rpow_one, neg_mul]
    have hconst : IntegrableOn
        (fun y => (Real.exp (-tw_z μ φ p) * (p-1)^(((2-p)/(1-p))*(j:ℝ))
          / (φ^((j:ℝ)*(1-(2-p)/(1-p))) * (2-p)^j * (Nat.factorial j)
            * Real.Gamma (-(j:ℝ)*((2-p)/(1-p)))))
          * (y ^ (-(j:ℝ)*((2-p)/(1-p)) - 1)
            * Real.exp (-(μ ^ (1 - p) / (φ * (p - 1)) * y)))) (Set.Ioi 0) :=
      hbase2.const_mul _
    apply IntegrableOn.congr_fun hconst _ measurableSet_Ioi
    intro y hy; simp only [Set.mem_Ioi] at hy
    exact (tw_pt μ φ p hp₁ hp₂ hφ j hy).symm

/-- The per-term integral for `j ≥ 1`: it equals `exp(-z) z^j / j!`. -/
lemma tw_integral_term (μ φ p : ℝ) (hp₁ : 1 < p) (hp₂ : p < 2) (hμ : 0 < μ) (hφ : 0 < φ)
    {j : ℕ} (hj : 1 ≤ j) :
    ∫ y in Set.Ioi (0:ℝ), tw_G μ φ p j y
      = Real.exp (-tw_z μ φ p) * (tw_z μ φ p) ^ j / (Nat.factorial j) := by
  have h1p : (1 - p) ≠ 0 := by intro h; linarith
  have h2p : (2 - p) ≠ 0 := by intro h; linarith
  have hp1 : (0:ℝ) < p - 1 := by linarith
  have hjpos : 0 < (j:ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hj
  have hαneg : (2 - p) / (1 - p) < 0 := div_neg_of_pos_of_neg (by linarith) (by linarith)
  have ha0pos : 0 < -(j:ℝ) * ((2-p)/(1-p)) := by
    have : -(j:ℝ) < 0 := by simpa using hjpos
    exact mul_pos_of_neg_of_neg this hαneg
  have hμpow : 0 < μ ^ (1 - p) := Real.rpow_pos_of_pos hμ _
  have hrpos : 0 < μ ^ (1 - p) / (φ * (p - 1)) := by positivity
  rw [setIntegral_congr_fun measurableSet_Ioi
      (fun y hy => tw_pt μ φ p hp₁ hp₂ hφ j hy)]
  rw [integral_const_mul]
  rw [Real.integral_rpow_mul_exp_neg_mul_Ioi ha0pos hrpos]
  set α := (2-p)/(1-p) with hα
  set r := μ ^ (1 - p) / (φ * (p - 1)) with hrdef
  have hrinvpos : 0 < 1/r := by positivity
  have hW : (p-1)^α * (1/r)^(-α) / (φ^(1-α)*(2-p)) = μ^(2-p)/(φ*(2-p)) := by
    have h1pneg : (1 - p) < 0 := by linarith
    have hkey : (1 - p) * α = 2 - p := by rw [hα]; field_simp
    have hrinv : (1/r) = φ * (p-1) / μ^(1-p) := by rw [hrdef, one_div_div]
    rw [hrinv]
    rw [Real.div_rpow (by positivity) (le_of_lt hμpow)]
    rw [Real.mul_rpow (le_of_lt hφ) (le_of_lt hp1)]
    rw [← Real.rpow_mul hμ.le]
    rw [show (1 - p) * (-α) = -(2-p) from by rw [mul_neg, hkey]]
    rw [Real.rpow_neg hμ.le (2-p), Real.rpow_neg hp1.le α, Real.rpow_neg hφ.le α]
    have hφfac : φ^(1-α) = φ^(1:ℝ) * φ^(-α) := by rw [← Real.rpow_add hφ]; ring_nf
    rw [hφfac, Real.rpow_one, Real.rpow_neg hφ.le α]
    field_simp
  have hcore : (p-1)^(α*(j:ℝ)) * (1/r)^(-(j:ℝ)*α) / (φ^((j:ℝ)*(1-α))*(2-p)^j)
      = (μ^(2-p)/(φ*(2-p)))^j := by
    have hn1 : (0:ℝ) ≤ (p-1)^α := Real.rpow_nonneg hp1.le α
    have hn2 : (0:ℝ) ≤ (1/r)^(-α) := Real.rpow_nonneg hrinvpos.le (-α)
    have hn3 : (0:ℝ) ≤ φ^(1-α) := Real.rpow_nonneg hφ.le (1-α)
    have hn4 : (0:ℝ) ≤ 2-p := by linarith
    rw [Real.rpow_mul hp1.le α (j:ℝ)]
    rw [show (-(j:ℝ)*α) = (-α)*(j:ℝ) from by ring]
    rw [Real.rpow_mul hrinvpos.le (-α) (j:ℝ)]
    rw [show (j:ℝ)*(1-α) = (1-α)*(j:ℝ) from by ring]
    rw [Real.rpow_mul hφ.le (1-α) (j:ℝ)]
    rw [← Real.rpow_natCast (2-p) j, ← Real.rpow_natCast (μ^(2-p)/(φ*(2-p))) j]
    rw [← Real.mul_rpow hn1 hn2]
    rw [← Real.mul_rpow hn3 hn4]
    rw [← Real.div_rpow (mul_nonneg hn1 hn2) (mul_nonneg hn3 hn4)]
    rw [hW]
  have hΓ : Real.Gamma (-(j:ℝ)*α) ≠ 0 := ne_of_gt (Real.Gamma_pos_of_pos ha0pos)
  have hfac : (Nat.factorial j : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  rw [tw_z]
  rw [show Real.exp (-(μ^(2-p)/(φ*(2-p)))) * (p-1)^(α*(j:ℝ))
        / (φ^((j:ℝ)*(1-α)) * (2-p)^j * (Nat.factorial j) * Real.Gamma (-(j:ℝ)*α))
        * ((1/r)^(-(j:ℝ)*α) * Real.Gamma (-(j:ℝ)*α))
      = Real.exp (-(μ^(2-p)/(φ*(2-p)))) / (Nat.factorial j)
          * (Real.Gamma (-(j:ℝ)*α)/Real.Gamma (-(j:ℝ)*α))
        * ((p-1)^(α*(j:ℝ)) * (1/r)^(-(j:ℝ)*α) / (φ^((j:ℝ)*(1-α))*(2-p)^j))
      from by field_simp]
  rw [div_self hΓ, hcore]
  ring

/-- The per-term integral for `j = 0` is `0`. -/
lemma tw_integral_zero (μ φ p : ℝ) :
    ∫ y in Set.Ioi (0:ℝ), tw_G μ φ p 0 y = 0 := by
  simp [tw_G_zero]

/-- Summability of the integral norms (needed to swap `∫` and `∑'`). -/
lemma tw_summable_norm (μ φ p : ℝ) (hp₁ : 1 < p) (hp₂ : p < 2) (hμ : 0 < μ) (hφ : 0 < φ) :
    Summable (fun j : ℕ => ∫ y in Set.Ioi (0:ℝ), ‖tw_G μ φ p j y‖) := by
  have hsum2 : Summable (fun j : ℕ =>
      Real.exp (-tw_z μ φ p) * (tw_z μ φ p) ^ j / (Nat.factorial j)) := by
    have := (Real.summable_pow_div_factorial (tw_z μ φ p)).mul_left (Real.exp (-tw_z μ φ p))
    simpa [mul_div_assoc] using this
  have hnorm_eq : ∀ j, ∫ y in Set.Ioi (0:ℝ), ‖tw_G μ φ p j y‖
      = ∫ y in Set.Ioi (0:ℝ), tw_G μ φ p j y := by
    intro j
    apply setIntegral_congr_fun measurableSet_Ioi
    intro y hy; simp only [Set.mem_Ioi] at hy
    exact Real.norm_of_nonneg (tw_G_nonneg μ φ p hp₁ hp₂ hφ j hy)
  apply Summable.of_nonneg_of_le _ _ hsum2
  · intro j; rw [hnorm_eq]
    exact setIntegral_nonneg measurableSet_Ioi
      (fun y hy => tw_G_nonneg μ φ p hp₁ hp₂ hφ j hy)
  · intro j
    rw [hnorm_eq]
    rcases Nat.eq_zero_or_pos j with hj0 | hjpos
    · subst hj0; rw [tw_integral_zero]; positivity
    · rw [tw_integral_term μ φ p hp₁ hp₂ hμ hφ hjpos]

/-- The series of per-term values sums to `1 - exp(-z)`. -/
lemma tw_tsum (μ φ p : ℝ) :
    ∑' j : ℕ, (if j = 0 then (0:ℝ)
      else Real.exp (-tw_z μ φ p) * (tw_z μ φ p) ^ j / (Nat.factorial j))
      = 1 - Real.exp (-tw_z μ φ p) := by
  set z := tw_z μ φ p
  have hexp : Real.exp z = ∑' n : ℕ, z ^ n / n.factorial := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  have hsum : Summable (fun n : ℕ => z ^ n / n.factorial) := Real.summable_pow_div_factorial z
  have hsum2 : Summable (fun n : ℕ => Real.exp (-z) * z ^ n / (Nat.factorial n)) := by
    have := hsum.mul_left (Real.exp (-z))
    simpa [mul_div_assoc] using this
  have hsum3 : Summable (fun j : ℕ =>
      (if j = 0 then Real.exp (-z) * z ^ j / (Nat.factorial j) else 0)) := by
    apply summable_of_ne_finset_zero (s := {0})
    intro b hb; simp at hb; simp [hb]
  have key : (fun j : ℕ => (if j = 0 then (0:ℝ) else Real.exp (-z) * z ^ j / (Nat.factorial j)))
      = (fun j => Real.exp (-z) * z ^ j / (Nat.factorial j)
          - (if j = 0 then Real.exp (-z) * z ^ j / (Nat.factorial j) else 0)) := by
    funext j; by_cases hj : j = 0 <;> simp [hj]
  rw [key, Summable.tsum_sub hsum2 hsum3]
  have h1 : ∑' j : ℕ, Real.exp (-z) * z ^ j / (Nat.factorial j) = 1 := by
    rw [show (fun j : ℕ => Real.exp (-z) * z ^ j / (Nat.factorial j))
          = (fun j => Real.exp (-z) * (z ^ j / (Nat.factorial j))) from by funext j; ring]
    rw [tsum_mul_left, ← hexp, ← Real.exp_add]; simp
  have h2 : ∑' j : ℕ, (if j = 0 then Real.exp (-z) * z ^ j / (Nat.factorial j) else 0)
      = Real.exp (-z) := by
    rw [tsum_eq_single 0]
    · simp
    · intro b hb; simp [hb]
  rw [h1, h2]

/-- The integral of the Tweedie density equals `1 - exp(-μ^(2-p)/(φ(2-p)))`. -/
lemma tweediePDF_integral (μ φ p) (hp₁ : 1 < p) (hp₂ : p < 2) (hμ : 0 < μ)
  (hφ : 0 < φ) :
  ∫ y, tweediePDF μ φ p y =
  1 - Real.exp (-μ ^ ( 2 - p) / (φ * (2 - p))) := by
  rw [tweediePDF]
  rw [show {y : ℝ | 0 < y} = Set.Ioi 0 from rfl]
  rw [MeasureTheory.integral_indicator measurableSet_Ioi]
  rw [setIntegral_congr_fun measurableSet_Ioi (fun y _ => tw_pointwise μ φ p y)]
  rw [← integral_tsum_of_summable_integral_norm
      (fun j => tw_integrable_on μ φ p hp₁ hp₂ hμ hφ j)
      (tw_summable_norm μ φ p hp₁ hp₂ hμ hφ)]
  rw [show (∑' j : ℕ, ∫ y in Set.Ioi (0:ℝ), tw_G μ φ p j y)
      = ∑' j : ℕ, (if j = 0 then (0:ℝ)
        else Real.exp (-tw_z μ φ p) * (tw_z μ φ p) ^ j / (Nat.factorial j)) from by
    apply tsum_congr
    intro j
    rcases Nat.eq_zero_or_pos j with hj0 | hjpos
    · subst hj0; rw [tw_integral_zero]; simp
    · rw [tw_integral_term μ φ p hp₁ hp₂ hμ hφ hjpos, if_neg (by omega)]]
  rw [tw_tsum, tw_z, neg_div]

open NNReal ENNReal Real
noncomputable section

/-- Probability of zero according to Tweedie distribution. -/
def tweedie_prob_zero (μ φ p : ℝ) : ℝ≥0 :=
    ⟨rexp (-μ ^ ( 2 - p) / (φ * (2 - p))), exp_nonneg _⟩

/-- Nonnegativity of the Tweedie PDF. -/
lemma tweediePDF_nonneg {y μ φ p : ℝ} (hφ : 0 ≤ φ)
  (hp₁ : 1 < p) (hp₂ : p ≤ 2)
  : tweediePDF μ φ p y ≥ 0 := by
    unfold tweediePDF
    simp only [indicator, mem_setOf_eq, a, one_div, neg_mul, ge_iff_le]
    split_ifs with g₀
    · apply mul_nonneg
      · apply mul_nonneg
        · positivity
        · refine tsum_nonneg ?_
          intro j
          apply mul_nonneg
          · apply mul_nonneg
            · positivity
            · apply rpow_nonneg
              linarith
          · simp only [mul_inv_rev]
            apply mul_nonneg
            · rw [inv_nonneg]
              refine Gamma_nonneg_of_nonneg ?_
              rw [mul_div, ← neg_div, ← neg_mul, mul_comm, ← mul_div]
              apply mul_nonneg
              · linarith
              suffices 0 ≤ j / (p - 1) by
                convert this using 1
                have : p - 1 = -(1 - p) := by simp
                rw [this]
                field_simp
              apply mul_nonneg
              · simp
              · simp;linarith
            · apply mul_nonneg
              · simp
              · apply mul_nonneg
                · rw [inv_nonneg];apply pow_nonneg;linarith
                · rw [inv_nonneg];apply rpow_nonneg;linarith
      · exact Real.exp_nonneg _
    simp

def tweediePDF' (μ : ℝ) {φ p : ℝ}
    (hp₁ : 1 < p) (hp₂ : p ≤ 2)
    (hφ : 0 ≤ φ) (y : ℝ) : ℝ≥0∞:=
    let nn : NNReal := (⟨tweediePDF μ φ p y, by
      by_cases H : y < 0
      · unfold tweediePDF
        simp only [indicator, mem_setOf_eq, one_div]
        rw [if_neg (by linarith)]
      · simp only [not_lt] at H
        exact tweediePDF_nonneg hφ hp₁ hp₂⟩ : NNReal)
    (nn : ENNReal)

def tweedieMeasure (μ : ℝ) {φ p : ℝ} (hφ : 0 ≤ φ)
    (hp₁ : 1 < p) (hp₂ : p < 2) : Measure ℝ :=
    (tweedie_prob_zero μ φ p) • (Measure.dirac 0)
    + (volume.withDensity (tweediePDF' μ hp₁ (by linarith) hφ))

/-- The Tweedie measure is a probability measure. -/
lemma tweedieMeasure_prob (μ : ℝ) (hμ : 0 < μ) {φ p : ℝ} (hφ : 0 < φ)
    (hp₁ : 1 < p) (hp₂ : p < 2) :
    IsProbabilityMeasure (tweedieMeasure μ (show 0 ≤ φ by linarith) hp₁ hp₂) := by
  refine isProbabilityMeasure_iff.mpr ?_
  unfold tweedieMeasure
  simp only [Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply, measure_univ,
    ENNReal.smul_one, MeasurableSet.univ, withDensity_apply, Measure.restrict_univ]
  unfold tweedie_prob_zero
  have : ∫⁻ (a : ℝ), tweediePDF' μ hp₁ (by linarith) (show 0 ≤ φ by linarith) a =
      1 - tweedie_prob_zero μ φ p := by
    have ht := @tweediePDF_integral μ φ p hp₁ hp₂ hμ hφ
    unfold tweedie_prob_zero
    have : tweedie_prob_zero μ φ p ≤ 1 := by
      unfold tweedie_prob_zero
      change rexp _ ≤ 1
      refine exp_le_one_iff.mpr ?_
      field_simp
      simp only [mul_zero, Left.neg_nonpos_iff]
      apply mul_nonneg
      · apply rpow_nonneg
        linarith
      · simp
        linarith
    have : (1 : NNReal) - ⟨rexp (-μ ^ ( 2 - p) / (φ * (2 - p))), exp_nonneg _⟩
      = ⟨1 - tweedie_prob_zero μ φ p, by
        generalize tweedie_prob_zero μ φ p = α at *
        exact sub_nonneg_of_le this⟩ := by
          unfold tweedie_prob_zero
          have (a : ℝ) (ha : a < 1) (ha' : 0 ≤ a) :
            (1 : NNReal) - ⟨a,ha'⟩ = ⟨1-a, by linarith⟩ := by
            refine (toNNReal_eq_iff_eq_coe ?_).mpr rfl
            have : 1 - a > 0 := by linarith
            exact Ne.symm (Std.ne_of_lt this)
          apply this
          refine exp_lt_one_iff.mpr ?_
          ring_nf
          simp only [Left.neg_neg_iff]
          apply _root_.mul_pos <| rpow_pos_of_pos hμ (2 - p)
          · simp only [inv_pos, lt_neg_add_iff_add_lt, add_zero]
            nth_rw 1 [mul_comm]
            exact (mul_lt_mul_iff_of_pos_left hφ).mpr hp₂
    have : (1 : ENNReal) - ENNReal.ofNNReal ⟨rexp (-μ ^ ( 2 - p) / (φ * (2 - p))), exp_nonneg _⟩
      = ENNReal.ofNNReal ⟨1 - tweedie_prob_zero μ φ p, by
        generalize tweedie_prob_zero μ φ p = α at *
        exact sub_nonneg_of_le (by simp;tauto)⟩ := by
          rw [← this]
          simp
    rw [this]
    unfold tweediePDF'
    simp only [tweedie_prob_zero]
    have : rexp (-μ ^ (2 - p) / (φ * (2 - p))) = 1 - ∫ (y : ℝ), tweediePDF μ φ p y := by linarith
    simp_rw [this]
    have (a : Real) (ha : 0 ≤ 1 - a)
      (ha' : 0 ≤ a)
      : ofNNReal (⟨(1 : ℝ) - (⟨1 - a, ha⟩ : NNReal),
      by simp;tauto⟩ : NNReal) = ofNNReal ⟨a, ha'⟩ := by simp
    specialize this (∫ (y : ℝ), tweediePDF μ φ p y) (by
      rw [tweediePDF_integral]
      all_goals try linarith
      simp only [_root_.sub_sub_cancel]
      exact exp_nonneg (-μ ^ (2 - p) / (φ * (2 - p))))
      (by
        rw [tweediePDF_integral]
        all_goals try linarith
        simp
        field_simp
        simp only [mul_zero, Left.neg_nonpos_iff]
        apply mul_nonneg
        · refine rpow_nonneg ?_ (2 - p)
          linarith
        · simp
          linarith)
    symm
    convert this
    · rw [MeasureTheory.lintegral_coe_eq_integral]
      · refine (toReal_eq_toReal_iff' ?_ ?_).mp ?_
        · simp
        · simp
        · simp only [coe_toReal]
          refine toReal_ofReal ?_
          refine integral_nonneg ?_
          intro
          simp
      · suffices Integrable (fun x ↦ tweediePDF μ φ p x) volume by
          convert this
        have h₀ := @tweediePDF_integral μ φ p hp₁ hp₂ hμ hφ
        have (f : ℝ → ℝ) (hf : ∫ x, f x ≠ 0) : Integrable f := by
          exact Integrable.of_integral_ne_zero hf
        apply this
        rw [h₀]
        have (a) (ha : a ≠ 0) : 1 - rexp a ≠ 0 := by
          contrapose! ha
          apply Real.exp_injective
          suffices rexp a = 1 by
            convert this
            simp
          linarith
        apply this
        simp only [ne_eq, _root_.div_eq_zero_iff, neg_eq_zero, mul_eq_zero, not_or]
        constructor
        · refine (rpow_ne_zero ?_ ?_).mpr ?_
          all_goals linarith
        · constructor
          all_goals linarith
  rw [this]
  unfold tweedie_prob_zero
  have (a : NNReal) (ha : 1 - a.1 > 0) :
     a + (1 - a) = 1 := by
      apply NNReal.coe_injective
      change a.toReal + (1-a).toReal = 1
      have : 1 - a.toReal = (1-a).toReal := by
        refine (toNNReal_eq_iff_eq_coe ?_).mp rfl
        apply ne_of_gt
        refine NNReal.coe_pos.mp ?_
        simp only [val_eq_coe, gt_iff_lt, sub_pos, coe_lt_one, NNReal.coe_pos,
          tsub_pos_iff_lt] at ha ⊢
        convert ha
      rw [← this]
      linarith
  have (a : NNReal) (ha : 1 - a.1 > 0) :
    ofNNReal a + ofNNReal (1 - a) = 1 := by
      rw [← ENNReal.coe_add]
      rw [this]
      · simp
      · tauto
  apply this
  simp
  field_simp
  simp only [mul_zero, Left.neg_neg_iff]
  apply div_pos
  · apply rpow_pos_of_pos
    linarith
  · linarith

def tweedieProbMeasure {μ φ p : ℝ} (hμ : 0 < μ) (hφ : 0 < φ)
    (hp₁ : 1 < p) (hp₂ : p < 2) : MeasureTheory.ProbabilityMeasure ℝ := {
      val := tweedieMeasure μ (by linarith) hp₁ hp₂
      property :=
        tweedieMeasure_prob μ hμ hφ hp₁ hp₂
    }
