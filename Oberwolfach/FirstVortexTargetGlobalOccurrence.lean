module

public import Oberwolfach.InnerRequiredTargets

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem first_vortex_target_global_occurrence
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (H:Finset U) (A:Finset (Fin n)) (reserved selected absorber occupied:U→Finset (Fin n))
    (θ η ζ ρ a γ:ℝ) (hθ:0≤θ) (hζ:0≤ζ) (hρ:0≤ρ)
    (hH:(H.card:ℝ)≤n) (hA:(A.card:ℝ)≤n)
    (hsub:(A.card:ℝ)^(3/4:ℝ)≤η*n) (hscale:max a γ*n≤ρ*A.card)
    (hcol:∀v∈A,((Finset.univ.filter (fun w=>v∈innerRequiredTargets H A reserved selected absorber occupied w)).card:ℝ)≤
      2*θ*H.card+(A.card:ℝ)^(3/4:ℝ)+ζ*H.card+max a γ*n):
    ∀v,((Finset.univ.filter (fun w=>v∈innerRequiredTargets H A reserved selected absorber occupied w)).card:ℝ)≤
      (2*θ+η+ζ+ρ)*n:=by
  have h1:=mul_le_mul_of_nonneg_left hH (by positivity : 0≤2*θ)
  have h2:=mul_le_mul_of_nonneg_left hH hζ
  have h3:=mul_le_mul_of_nonneg_left hA hρ
  have hcoef:0≤(2*θ+η+ζ+ρ)*n:=by
    have hn:(0:ℝ)≤n:=by positivity
    have hp:0≤(A.card:ℝ)^(3/4:ℝ):=by positivity
    nlinarith
  intro v
  by_cases hv:v∈A
  · have hh:=hcol v hv
    nlinarith
  · have hempty:Finset.univ.filter (fun w=>v∈innerRequiredTargets H A reserved selected absorber occupied w)=∅:=by
      apply Finset.filter_eq_empty_iff.mpr
      intro w hw
      by_cases hwH:w∈H <;> simp [innerRequiredTargets,hwH,hv]
    rw [hempty]
    simp only [Finset.card_empty,Nat.cast_zero]
    exact hcoef
end Oberwolfach
