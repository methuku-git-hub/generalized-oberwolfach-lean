module

public import Oberwolfach.RetentionConditioning
public import Oberwolfach.SimplifiedCliqueJointRetention

@[expose] public section

/-! Summing the conditional comparison over the retained colour at a root.
The term where this colour equals the tested colour is handled separately. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finiteLaw_event_covariance_bound {Ω : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) (E A : Ω → Prop) :
    |μ.probability (fun x=>E x ∧ A x)-μ.probability E*μ.probability A|≤μ.probability E := by
  have hEA0 := finiteLaw_probability_nonneg μ (fun x=>E x ∧ A x)
  have hEA1 := finiteLaw_probability_mono μ (fun x=>E x ∧ A x) E (fun _ h=>h.1)
  have hE0 := finiteLaw_probability_nonneg μ E
  have hA0 := finiteLaw_probability_nonneg μ A
  have hA1 : μ.probability A≤1 := by
    have h := finiteLaw_probability_compl μ A
    have hn := finiteLaw_probability_nonneg μ (fun x=>¬A x)
    linarith
  have hprod0 := mul_nonneg hE0 hA0
  have hprod1 := mul_le_mul_of_nonneg_left hA1 hE0
  apply abs_le.mpr
  constructor <;> nlinarith

theorem finiteLaw_survival_colour_sum
    {V C : Type*} [Fintype V] [Fintype C]
    (G : SimpleGraph V) (μ : FiniteLaw (V → C×Bool)) (v : V) (A : (V → C×Bool) → Prop) :
    μ.probability (fun σ=>coinColourSurvives G σ v ∧ A σ)=
      ∑ b,μ.probability (fun σ=>coinRetainedColour G σ v=some b ∧ A σ) := by
  rw [finiteLaw_probability_value_partition μ _ (fun σ=>(σ v).1)]
  apply Finset.sum_congr rfl
  intro b _
  apply finiteLaw_probability_congr
  intro σ
  rw [coinRetainedColour_eq_some]
  tauto

theorem equalized_survival_colour_covariance
    {V C : Type*} [Fintype V] [Fintype C]
    (G : SimpleGraph V) (L : V → Finset C) (hL : ∀ u,(L u).Nonempty)
    {l K : ℕ} (hl : 1<l) (hcard : ∀ u,(L u).card=l)
    (hbound : ∀ u c,(colourNeighbourSet G L u c).card≤K)
    (v : V) (c : C) (B : (V → Option Bool) → Prop) :
    let μ := FiniteLaw.pi (fun u=>(FiniteLaw.uniformOn (L u) (hL u)).withCoin
      (equalizationCoin G L l K u) (equalizationCoin_bounds G L (by omega) K u))
    let ρ := (1-1/(l : ℝ))^K
    |μ.probability (fun σ=>coinColourSurvives G σ v ∧ B (fun u=>colourMask c (σ u)))-
      ρ*μ.probability (fun σ=>B (fun u=>colourMask c (σ u)))|≤
      1/(l : ℝ)+ρ*(2/(l : ℝ)+2*(K : ℝ)/((l : ℝ)*((l : ℝ)-1))) := by
  classical
  dsimp only
  let μ := FiniteLaw.pi (fun u=>(FiniteLaw.uniformOn (L u) (hL u)).withCoin
    (equalizationCoin G L l K u) (equalizationCoin_bounds G L (by omega : 0<l) K u))
  let ρ := (1-1/(l : ℝ))^K
  let A := fun σ : V → C×Bool=>B (fun u=>colourMask c (σ u))
  let p := fun b=>μ.probability (fun σ=>coinRetainedColour G σ v=some b)
  let f := fun b=>μ.probability (fun σ=>coinRetainedColour G σ v=some b ∧ A σ)-p b*μ.probability A
  let δ := 2/(l : ℝ)+2*(K : ℝ)/((l : ℝ)*((l : ℝ)-1))
  have hlr : (1 : ℝ)<l := by exact_mod_cast hl
  have hl0 : (0 : ℝ)<l := by linarith
  have hden : 0<(l : ℝ)*((l : ℝ)-1) := mul_pos hl0 (by linarith)
  have hδ : 0≤δ := add_nonneg (by positivity) (div_nonneg (by positivity) hden.le)
  have hp0 (b : C) : 0≤p b := finiteLaw_probability_nonneg _ _
  have hsurv : μ.probability (fun σ=>coinColourSurvives G σ v)=ρ :=
    equalizedColour_survival_probability G L hL (by omega) hcard (fun u b _=>hbound u b) v
  have hpsum : (∑ b,p b)=ρ := by
    have h := finiteLaw_survival_colour_sum G μ v (fun _=>True)
    simp only [and_true] at h
    exact h.symm.trans hsurv
  have hpc : p c≤1/(l : ℝ) := by
    have h := equalizedColour_probability G L hL (by omega : 0<l) hcard
      (fun u b _=>hbound u b) v c
    change p c=(if c∈L v then (1/(l : ℝ))*ρ else 0) at h
    rw [h]
    split_ifs
    · have hρ := (equalized_retention_rate_bounds (l:=l) (by omega) K).2
      have hh := mul_le_mul_of_nonneg_left hρ (show 0≤1/(l : ℝ) by positivity)
      simpa only [mul_one] using hh
    · positivity
  have hf (b : C) : |f b|≤p b*δ+(if b=c then p c else 0) := by
    by_cases hb : b=c
    · subst b
      have h := finiteLaw_event_covariance_bound μ
        (fun σ=>coinRetainedColour G σ v=some c) A
      change |f c|≤p c at h
      simp only [ite_true]
      exact h.trans (by nlinarith [mul_nonneg (hp0 c) hδ])
    · simp only [hb,ite_false,add_zero]
      have h := retained_other_colour_covariance G L hL (equalizationCoin G L l K)
        (fun u=>equalizationCoin_bounds G L (by omega) K u) hl hcard v b c (Ne.symm hb) B
      dsimp only at h
      change |f b|≤p b*(2/(l : ℝ)+2*(colourNeighbourSet G L v b).card/((l : ℝ)*((l : ℝ)-1))) at h
      apply h.trans
      apply mul_le_mul_of_nonneg_left _ (hp0 b)
      apply add_le_add (le_refl _)
      apply div_le_div_of_nonneg_right _ hden.le
      gcongr
      exact_mod_cast hbound v b
  have hsumf : (∑ b,f b)=μ.probability (fun σ=>coinColourSurvives G σ v ∧ A σ)-ρ*μ.probability A := by
    dsimp only [f]
    rw [Finset.sum_sub_distrib,← Finset.sum_mul,hpsum,
      ← finiteLaw_survival_colour_sum G μ v A]
  change |μ.probability _-ρ*μ.probability A|≤1/(l : ℝ)+ρ*δ
  rw [← hsumf]
  calc
    _ ≤ ∑ b,|f b| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ b,(p b*δ+(if b=c then p c else 0)) := Finset.sum_le_sum (fun b _=>hf b)
    _ = ρ*δ+p c := by rw [Finset.sum_add_distrib,← Finset.sum_mul,hpsum];simp
    _ ≤ _ := by linarith

end Oberwolfach
