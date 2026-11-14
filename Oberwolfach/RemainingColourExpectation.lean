module

public import Oberwolfach.SurvivalColourCovariance
public import Oberwolfach.RemainingColourDegrees

@[expose] public section

/-! The mean of the actual remaining colour degree. Correlation between
root survival and colour availability is bounded in the original law. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2300000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finiteLaw_complement_covariance {Ω : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) (E A : Ω → Prop) :
    |μ.probability (fun x=>¬E x ∧ A x)-(1-μ.probability E)*μ.probability A|=
      |μ.probability (fun x=>E x ∧ A x)-μ.probability E*μ.probability A| := by
  have hh := finiteLaw_probability_split μ A E
  have h₁ : μ.probability (fun x=>A x ∧ E x)=μ.probability (fun x=>E x ∧ A x) :=
    finiteLaw_probability_congr _ _ _ (fun _=>and_comm)
  have h₂ : μ.probability (fun x=>A x ∧ ¬E x)=μ.probability (fun x=>¬E x ∧ A x) :=
    finiteLaw_probability_congr _ _ _ (fun _=>and_comm)
  rw [h₁,h₂] at hh
  have he : μ.probability (fun x=>¬E x ∧ A x)-(1-μ.probability E)*μ.probability A=
      -(μ.probability (fun x=>E x ∧ A x)-μ.probability E*μ.probability A) := by linarith
  rw [he,abs_neg]

theorem remainingColourVertices_expectation
    {V C J : Type*} [Fintype V] [Fintype C]
    (G : SimpleGraph V) (L : V → Finset C) (hL : ∀ u,(L u).Nonempty)
    {l K : ℕ} (hl : 1<l) (hcard : ∀ u,(L u).card=l)
    (hbound : ∀ u c,(colourNeighbourSet G L u c).card≤K)
    (U : Finset V) (Q : V → Finset J) (T : J → Finset V) (c : C) :
    let μ := FiniteLaw.pi (fun u=>(FiniteLaw.uniformOn (L u) (hL u)).withCoin
      (equalizationCoin G L l K u) (equalizationCoin_bounds G L (by omega) K u))
    let ρ := (1-1/(l : ℝ))^K
    |μ.expectation (fun σ=>((remainingColourVertices G U Q T c σ).card : ℝ))-
      ∑ v∈U,(1-ρ)*μ.probability (fun σ=>∀ j∈Q v,∀ w∈T j,coinRetainedColour G σ w≠some c)|≤
      (U.card : ℝ)*(1/(l : ℝ)+ρ*(2/(l : ℝ)+2*(K : ℝ)/((l : ℝ)*((l : ℝ)-1)))) := by
  classical
  dsimp only
  let μ := FiniteLaw.pi (fun u=>(FiniteLaw.uniformOn (L u) (hL u)).withCoin
    (equalizationCoin G L l K u) (equalizationCoin_bounds G L (by omega : 0<l) K u))
  let ρ := (1-1/(l : ℝ))^K
  let A := fun v σ=>∀ j∈Q v,∀ w∈T j,coinRetainedColour G σ w≠some c
  let B := fun v (τ : V → Option Bool)=>∀ j∈Q v,∀ w∈T j,¬maskRetains G τ w
  let ε := 1/(l : ℝ)+ρ*(2/(l : ℝ)+2*(K : ℝ)/((l : ℝ)*((l : ℝ)-1)))
  have hmask (v : V) (σ : V → C×Bool) : A v σ ↔ B v (fun u=>colourMask c (σ u)) := by
    simp only [A,B,ne_eq,coinRetainedColour_iff_mask]
  have hAprob (v : V) : μ.probability (A v)=μ.probability (fun σ=>B v (fun u=>colourMask c (σ u))) :=
    finiteLaw_probability_congr _ _ _ (hmask v)
  have hEprob (v : V) : μ.probability (fun σ=>coinColourSurvives G σ v ∧ A v σ)=
      μ.probability (fun σ=>coinColourSurvives G σ v ∧ B v (fun u=>colourMask c (σ u))) :=
    finiteLaw_probability_congr _ _ _ (fun σ=>and_congr_right' (hmask v σ))
  have hsurv (v : V) : μ.probability (fun σ=>coinColourSurvives G σ v)=ρ :=
    equalizedColour_survival_probability G L hL (by omega) hcard (fun u b _=>hbound u b) v
  have hpoint (v : V) :
      |μ.probability (fun σ=>¬coinColourSurvives G σ v ∧ A v σ)-(1-ρ)*μ.probability (A v)|≤ε := by
    have hh := equalized_survival_colour_covariance G L hL hl hcard hbound v c (B v)
    have he := finiteLaw_complement_covariance μ (fun σ=>coinColourSurvives G σ v) (A v)
    rw [hsurv v,hEprob v,hAprob v] at he
    rw [← hAprob v] at he
    rw [he]
    simpa only [hAprob v] using hh
  have hmean : μ.expectation (fun σ=>((remainingColourVertices G U Q T c σ).card : ℝ))=
      ∑ v∈U,μ.probability (fun σ=>¬coinColourSurvives G σ v ∧ A v σ) := by
    have hh := finiteLaw_expectation_count μ U (fun v σ=>¬coinColourSurvives G σ v ∧ A v σ)
    convert hh using 1
    apply congrArg μ.expectation
    funext σ
    apply congrArg (fun n : ℕ => (n : ℝ))
    apply congrArg Finset.card
    ext v
    simp only [remainingColourVertices,Finset.mem_filter,A]
  change |μ.expectation _-(∑ v∈U,(1-ρ)*μ.probability (A v))|≤(U.card : ℝ)*ε
  rw [hmean,← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ v∈U,|μ.probability (fun σ=>¬coinColourSurvives G σ v ∧ A v σ)-(1-ρ)*μ.probability (A v)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _v∈U,ε := Finset.sum_le_sum (fun v _=>hpoint v)
    _ = _ := by simp

end Oberwolfach
