module

public import Oberwolfach.LongInnerTargetsFromAlignedWheels

@[expose] public section
/-! Put the target size and occurrence bounds on the host order scale. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem inner_target_host_order_bounds
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (I:Finset (Fin n)) (Z:U→Finset (Fin n)) (θ ζ η ε ρ:ℝ)
    (hθ:0≤θ) (hζ:0≤ζ) (hI:(I.card:ℝ)≤ε*n)
    (hU:Fintype.card U≤n) (hsub:(n:ℝ)^(3/4:ℝ)≤η*n)
    (hrow:∀w,((Z w).card:ℝ)≤2*θ*I.card+(n:ℝ)^(3/4:ℝ)+ζ*n+ρ*n)
    (hcol:∀v,((Finset.univ.filter (fun w=>v∈Z w)).card:ℝ)≤
      2*θ*Fintype.card U+(n:ℝ)^(3/4:ℝ)+ζ*Fintype.card U+ρ*n):
    (∀w,((Z w).card:ℝ)≤(2*θ*ε+η+ζ+ρ)*n) ∧
    (∀v,((Finset.univ.filter (fun w=>v∈Z w)).card:ℝ)≤(2*θ+η+ζ+ρ)*n):=by
  have hmult:2*θ*(I.card:ℝ)≤2*θ*(ε*n):=mul_le_mul_of_nonneg_left hI (by positivity)
  have hcard:(Fintype.card U:ℝ)≤n:=by exact_mod_cast hU
  have hmultU:2*θ*(Fintype.card U:ℝ)≤2*θ*n:=mul_le_mul_of_nonneg_left hcard (by positivity)
  have hmultζ:ζ*(Fintype.card U:ℝ)≤ζ*n:=mul_le_mul_of_nonneg_left hcard hζ
  constructor
  · intro w
    have hh:=hrow w
    nlinarith
  · intro v
    have hh:=hcol v
    nlinarith
end Oberwolfach
