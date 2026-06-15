/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

module

public import Mathlib.Probability.Kernel.Defs
public import Statlib.Inference
public import Mathlib.Probability.Distributions.Exponential
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Gamma
public import Mathlib.Probability.Process.Stopping
public import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue

/-!
# Concrete Neyman-Pearson

In this file we write `ρ(x∣θ)` as `ρ θ x`.

The Neyman-Pearson lemma is proved over `ℝ` in `NP` below.
We also include some work towards a `ℝ≥0∞` version,
to allow Radon-Nikodym generalization. We follow the Wikipedia
argument.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Real Set Filter Classical
open scoped ENNReal BigOperators Topology


/-- The Neyman-Pearson region. -/
def RNP (θ₀ θ₁ η : ℝ) (ρ : ℝ → ℝ → ℝ) : Set ℝ :=
    { x | ρ θ₁ x - η * ρ θ₀ x ≥ 0}

def μ' (θ₀ : ℝ) (ρ : ℝ → ℝ → ℝ≥0∞) : Measure ℝ := volume.withDensity (ρ θ₀)


-- Inference model corresponding to concrete case of Neyman-Pearson with 1 sample point.
noncomputable def M (θ₀ θ₁ η : ℝ) (ρ : ℝ → ℝ → ℝ≥0∞)
  (h : ∀ θ, Measurable (ρ θ))
  (hh : Measurable fun μ : ({μ' θ₀ ρ, μ' θ₁ ρ} : Set _) => if μ.1 = μ' θ₀ ρ then true else false)
  :
  @InferenceModelofMeasure (Fin 1)
    (fun _ => ℝ) -- Ω
    (fun _ => Bool) -- S
    (fun _ => ℝ) -- X
    (fun _ => Bool) -- Y
    (fun _ => measurableSpace)
    (fun _ => Bool.instMeasurableSpace)
    (fun _ => measurableSpace)
    (fun _ => Bool.instMeasurableSpace) := {
      domain := fun _ => {μ' θ₀ ρ, μ' θ₁ ρ}
      functional := fun _ μ => ite (μ.1 = μ' θ₀ ρ) true false
      measurable_functional := fun _ => hh
      data := fun _ => id
      measurable_data := by simp;exact measurable_id
      decision_rule := fun _ => {
        toFun := fun x => ite (x ∈ RNP θ₀ θ₁ η (fun θ x => (ρ θ x).toReal))
          (Measure.dirac true) (Measure.dirac false)
        measurable' := by
          unfold RNP
          simp;apply Measurable.ite
          · simp
            refine Measurable.le' ?_ (h _).ennreal_toReal
            · refine Measurable.mul (by simp) (h _).ennreal_toReal
          · simp
          · simp
      }
      loss_function := fun _ b c => ite (b=c) 0 1
      measurable_loss_function := fun _ =>
        measurable_from_prod_countable_right fun x ⦃t⦄ a => trivial}


theorem NP.intRNP₀ {θ₀ : ℝ} {R : Set ℝ} {ρ : ℝ → ℝ → ℝ}
    (hρ : 0 ≤ ρ)
    (hI : Integrable (ρ θ₀) volume)
    (hAE : AEStronglyMeasurable (R.indicator 1 * ρ θ₀) volume) :
    Integrable (R.indicator 1 * ρ θ₀) volume := by
  apply integrable_of_le_of_le
  · exact hAE
  · change 0 ≤ᶠ[ae volume] _
    simp only [EventuallyLE, Filter.Eventually, ae, Pi.zero_apply, Pi.mul_apply,
      mem_ofCountableUnion]
    suffices volume (∅: Set ℝ) = 0 by
      convert this
      ext x
      simp only [mem_compl_iff, mem_setOf_eq, not_le, mem_empty_iff_false, iff_false, not_lt]
      apply mul_nonneg
      · simp only [indicator, Pi.one_apply]
        split_ifs with g₀
        · simp
        · simp
      tauto
    simp
  change _ ≤ᶠ[ae volume] ρ θ₀
  simp [EventuallyLE, Filter.Eventually, ae]
  suffices volume (∅: Set ℝ) = 0 by
    convert this
    ext x
    simp [Set.indicator]
    split_ifs with g₀
    · simp
    · tauto
  simp
  refine (lintegral_ofReal_ne_top_iff_integrable ?_ ?_).mp ?_
  · exact aestronglyMeasurable_zero
  · exact EventuallyLE.refl (ae volume) 0
  · simp
  exact hI

theorem NP.intRNP₁ {θ₁ : ℝ} {R : Set ℝ} {ρ : ℝ → ℝ → ℝ}
    (hρ : 0 ≤ ρ)
    (hI : Integrable (ρ θ₁) volume)
    (hAE : AEStronglyMeasurable (R.indicator 1 * ρ θ₁) volume) :
    Integrable (R.indicator 1 * ρ θ₁) volume := by
  apply NP.intRNP₀ hρ hI hAE

/-- A basic arithmetic lemma that is used in
Wikipedia's proof of Neyman--Pearson. -/
lemma wiki_arith {η α : ℝ} (hηp : 0 ≤ η)
    {I₁ J₁ I₀ : ℝ} (hα' : I₀ ≤ α)
    (hi : 0 ≤ J₁ - η * α - I₁ + η * I₀) : I₁ ≤ J₁ := by
  suffices 0 ≤ J₁ - I₁ by linarith
  have : 0 ≤ J₁ - I₁ - η * (α - I₀) := by linarith
  apply le_trans this
  have : η * (α - I₀) ≥ 0 := by
    apply mul_nonneg hηp
    linarith
  linarith

/-- The basic inequality that gets Wikipedia's proof of N--P
off the ground. -/
lemma wiki (θ₀ θ₁ η : ℝ) (ρ : ℝ → ℝ → ℝ) (R : Set ℝ) (x : ℝ) :
  ((RNP θ₀ θ₁ η ρ).indicator 1 x - R.indicator 1 x) * (ρ θ₁ x - η * ρ θ₀ x) ≥ 0 := by
    simp only [indicator, RNP, ge_iff_le, sub_nonneg, mem_setOf_eq, Pi.one_apply]
    split_ifs with g₀ g₁
    · simp
    · simp only [sub_zero, one_mul, sub_nonneg]
      exact g₀
    · linarith
    · simp

/-- Like `wiki` but avoid subtraction. -/
lemma wiki_nonneg (θ₀ θ₁ η : ℝ) (ρ : ℝ → ℝ → ℝ) (R : Set ℝ) (x : ℝ) :
    ((RNP θ₀ θ₁ η ρ).indicator 1 x) * (ρ θ₁ x) + (R.indicator 1 x) * (η * ρ θ₀ x)
  ≥ (R.indicator 1 x) * (ρ θ₁ x) + ((RNP θ₀ θ₁ η ρ).indicator 1 x) * (η * ρ θ₀ x) := by
    simp only [indicator, RNP, ge_iff_le, sub_nonneg, mem_setOf_eq, Pi.one_apply]
    split_ifs with g₀ g₁
    · simp
    · simp
      linarith
    · linarith
    · simp

def RNPnnreal (θ₀ θ₁ η : ℝ) (ρ : ℝ → ℝ → NNReal) : Set ℝ :=
    { x | ρ θ₁ x ≥ η * ρ θ₀ x}

def RNPennreal (θ₀ θ₁ : ℝ) (η : NNReal) (ρ : ℝ → ℝ → ENNReal) : Set ℝ :=
    { x | ρ θ₁ x ≥ η * ρ θ₀ x}

/-- The basic inequality from Wikipedia holds over `ℝ≥0∞`. -/
lemma wiki_ennreal (θ₀ θ₁ : ℝ) (η : NNReal) (ρ : ℝ → ℝ → ENNReal) (R : Set ℝ) (x : ℝ) :
    ((RNPennreal θ₀ θ₁ η ρ).indicator 1 x) * (ρ θ₁ x) + (R.indicator 1 x) * (η * ρ θ₀ x)
  ≥ (R.indicator 1 x) * (ρ θ₁ x) + ((RNPennreal θ₀ θ₁ η ρ).indicator 1 x) * (η * ρ θ₀ x) := by
    simp [RNPennreal, Set.indicator]
    split_ifs with g₀ g₁
    · simp
    · simp
      apply le_of_not_ge g₁
    · simp;tauto
    · simp

lemma wiki_ennreal' (θ₀ θ₁ : ℝ) (η : NNReal) (ρ : ℝ → ℝ → ENNReal) (R : Set ℝ) :
    ∫⁻ x, ((RNPennreal θ₀ θ₁ η ρ).indicator 1 x) * (ρ θ₁ x) + (R.indicator 1 x) * (η * ρ θ₀ x)
  ≥ ∫⁻ x, (R.indicator 1 x) * (ρ θ₁ x) + ((RNPennreal θ₀ θ₁ η ρ).indicator 1 x) * (η * ρ θ₀ x) := by
    refine lintegral_mono ?_
    apply wiki_ennreal

/-- This will allow us to transport the Wiki argument to `ℝ≥0∞`. -/
lemma transport_ennreal {a b c d : ENNReal} (h : a + b ≤ c + d) (h₀ : d ≤ b)
  (h₂ : d ≠ ∞) : a ≤ c := by
  by_contra H
  simp at H
  have : c + d < a + b := ENNReal.add_lt_add_of_lt_of_le h₂ H h₀
  revert this
  simp
  exact h



lemma wiki_nnreal (θ₀ θ₁ η : ℝ) (ρ : ℝ → ℝ → NNReal) (R : Set ℝ) (x : ℝ) :
    ((RNPnnreal θ₀ θ₁ η ρ).indicator 1 x) * (ρ θ₁ x) + (R.indicator 1 x) * (η * ρ θ₀ x)
  ≥ (R.indicator 1 x) * (ρ θ₁ x) + ((RNPnnreal θ₀ θ₁ η ρ).indicator 1 x) * (η * ρ θ₀ x) := by
    simp only [indicator, RNPnnreal, ge_iff_le, mem_setOf_eq, Pi.one_apply]
    split_ifs with g₀ g₁
    · simp
    · simp
      linarith
    · simp;tauto
    · simp

open Classical in
lemma int_help (θ₁ : ℝ) {ρ : ℝ → ℝ → ℝ}
  {R : Set ℝ}
  (hR : MeasurableSet R) :
  ∫ (x : ℝ) in R, ρ θ₁ x = ∫ (x : ℝ), if x ∈ R then ρ θ₁ x else 0 := by
        repeat rw [← integral_indicator]
        simp [Set.indicator]
        exact hR

lemma int_help' (θ₀ η : ℝ) {ρ : ℝ → ℝ → ℝ} {R : Set ℝ} :
  ∫ (a : ℝ), R.indicator 1 a * η * ρ θ₀ a
  = η * ∫ (a : ℝ), R.indicator 1 a * ρ θ₀ a := by
    rw [← integral_const_mul]
    congr
    ext a
    ring_nf

/--
May 2, 2026.
The Neyman-Pearson lemma.
-/
lemma NP (θ₀ θ₁ η α : ℝ) (hηp : 0 ≤ η)
    {ρ : ℝ → ℝ → ℝ} (hρ : 0 ≤ ρ)
    (hmm : ∀ θ, Measurable (ρ θ))
    (hI : ∀ θ, Integrable (ρ θ) volume)
    (hα : ∫ x in (RNP θ₀ θ₁ η ρ), ρ θ₀ x = α)
    {R : Set ℝ} (hR : MeasurableSet R)
    (hα' : ∫ x in R, ρ θ₀ x ≤ α) :
    ∫ x in R, ρ θ₁ x ≤ ∫ x in (RNP θ₀ θ₁ η ρ), ρ θ₁ x := by
  have lem (f g : ℝ → ℝ) : (fun a => f a * η * g a)
    =       (fun a => η * f a * g a) := by ext;ring_nf
  have h₁ : AEStronglyMeasurable
        (fun a ↦ R.indicator (fun _ => (1 : ℝ)) a) volume :=
    AEStronglyMeasurable.indicator aestronglyMeasurable_const hR
  have hm : MeasurableSet (RNP θ₀ θ₁ η ρ) := by
    simp only [RNP, ge_iff_le, sub_nonneg, measurableSet_setOf]
    refine ((hmm _).const_mul _).le' (hmm _)
  have h₀ : AEStronglyMeasurable (fun a : ℝ ↦ (RNP θ₀ θ₁ η ρ).indicator
    (fun _ => (1:ℝ)) a) volume := by
    simp only [RNP, ge_iff_le, sub_nonneg]
    refine aestronglyMeasurable_const.indicator
      <| measurableSet_le (measurable_const.mul (hmm _)) (hmm _)
  have hi : ∫ x, (Set.indicator (RNP θ₀ θ₁ η ρ) 1 x - Set.indicator R 1 x)
    * (ρ θ₁ x - η * ρ θ₀ x) ≥ 0 := integral_nonneg (wiki _ _ _ _ _)
  ring_nf at hi
  have hAE (θ : ℝ) := h₀.mul (hI θ).aestronglyMeasurable
  have hAER (θ : ℝ) := h₁.mul (hI θ).aestronglyMeasurable
  have hI'' : Integrable (fun a ↦ R.indicator 1 a * ρ θ₀ a) volume :=
    NP.intRNP₀ hρ (hI _) <| hAER _
  have hI₀' : Integrable (fun a ↦ R.indicator 1 a * ρ θ₁ a) volume :=
    NP.intRNP₀ hρ (hI _) <| hAER _
  have hI₁ : Integrable (fun x ↦ (RNP θ₀ θ₁ η ρ).indicator 1 x * ρ θ₀ x) volume :=
    NP.intRNP₀ hρ (hI _) <| hAE _
  have hI₁' : Integrable (fun a ↦ (RNP θ₀ θ₁ η ρ).indicator 1 a * ρ θ₁ a) volume := by
    apply NP.intRNP₀ hρ (hI _) <| h₀.mul (hI _).aestronglyMeasurable
  rw [integral_add] at hi
  · repeat rw [integral_sub] at hi
    · repeat rw [int_help'] at hi
      rw [← integral_indicator] at hα
      · simp only [indicator, Pi.one_apply, ite_mul, one_mul, zero_mul, ge_iff_le] at hα hi
        rw [hα] at hi
        repeat rw [← int_help] at hi
        · exact wiki_arith hηp hα' hi
        · exact hR
        · exact hR
        · exact hm
      exact hm
    · apply NP.intRNP₁ hρ (hI _) <| hAE _
    · rw [lem]
      simp_rw [mul_assoc]
      apply MeasureTheory.Integrable.const_mul'
      apply NP.intRNP₀ hρ (hI _) <| hAE _
    · refine (integrable_add_iff_integrable_left' ?_).mpr ?_
      · simp only [integrable_fun_neg_iff]
        rw [lem]
        simp_rw [mul_assoc]
        apply MeasureTheory.Integrable.const_mul'
        exact NP.intRNP₁ hρ (hI _) <| hAE _
      · exact hI₁'
    · exact hI₀'
  · repeat apply Integrable.sub
    · exact NP.intRNP₁ hρ (hI _) <| hAE _
    · rw [lem]
      simp_rw [mul_assoc]
      apply MeasureTheory.Integrable.const_mul'
        <| NP.intRNP₁ hρ (hI _) <| hAE _
    · exact NP.intRNP₁ hρ (hI _) <| hAER _
  · rw [lem]
    simp_rw [mul_assoc]
    apply MeasureTheory.Integrable.const_mul' hI''
