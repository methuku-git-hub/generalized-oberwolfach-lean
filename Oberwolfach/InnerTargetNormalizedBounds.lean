module

public import Oberwolfach.LongInnerTargetsFromAlignedWheels

@[expose] public section
/-! Normalize row and column estimates by the host and hub sizes. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem inner_target_normalized_bounds
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (I:Finset (Fin n)) (Z:U→Finset (Fin n)) (θ ζ η ε β ρ:ℝ)
    (hθ:0≤θ) (hη:0≤η) (hρ:0≤ρ) (hβ:0<β) (hI:(I.card:ℝ)≤ε*n)
    (hU:β*n≤Fintype.card U) (hsub:(n:ℝ)^(3/4:ℝ)≤η*n)
    (hrow:∀w,((Z w).card:ℝ)≤2*θ*I.card+(n:ℝ)^(3/4:ℝ)+ζ*n+ρ*n)
    (hcol:∀v,((Finset.univ.filter (fun w=>v∈Z w)).card:ℝ)≤
      2*θ*Fintype.card U+(n:ℝ)^(3/4:ℝ)+ζ*Fintype.card U+ρ*n):
    (∀w,((Z w).card:ℝ)≤(2*θ*ε+η+ζ+ρ)*n) ∧
    (∀v,((Finset.univ.filter (fun w=>v∈Z w)).card:ℝ)≤
      (2*θ+ζ+(η+ρ)/β)*Fintype.card U):=by
  have hmult:2*θ*(I.card:ℝ)≤2*θ*(ε*n):=mul_le_mul_of_nonneg_left hI (by positivity)
  have hdiv:(n:ℝ)≤(Fintype.card U:ℝ)/β:=by
    apply (le_div_iff₀ hβ).2
    nlinarith
  have hscale:((η+ρ)*n)≤((η+ρ)/β)*Fintype.card U:=by
    have hh:=mul_le_mul_of_nonneg_left hdiv (add_nonneg hη hρ)
    convert hh using 1 <;> ring
  constructor
  · intro w
    have hh:=hrow w
    nlinarith
  · intro v
    have hh:=hcol v
    nlinarith
end Oberwolfach
