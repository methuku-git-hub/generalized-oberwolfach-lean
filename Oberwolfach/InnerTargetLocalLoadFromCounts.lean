module

public import Oberwolfach.InnerTargetLocalOccurrenceBudget

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem inner_target_local_load_from_counts
    {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    (A:Finset V) (H:Finset U) (Z:U→Finset V) (θ δ η ζ ρ e:ℝ)
    (hθ:0≤θ) (hθδ:10*θ≤δ) (hη:η≤θ/4096) (hζ:ζ≤θ/4096) (hρ:ρ≤θ/4096) (hζ0:0≤ζ)
    (hH:(H.card:ℝ)≤A.card) (he:e≤η*A.card)
    (hdef:ℝ) (hdefbound:hdef≤ρ*A.card)
    (hcount:∀v∈A,((Finset.univ.filter (fun w=>v∈Z w)).card:ℝ)≤2*θ*H.card+e+ζ*H.card+hdef):
    ∀v∈A,((Finset.univ.filter (fun w=>v∈Z w)).card:ℝ)≤δ*A.card/4:=by
  intro v hv
  exact (hcount v hv).trans (inner_target_local_occurrence_budget A.card H.card θ δ η ζ ρ e hdef hθ hθδ hη hζ hρ hH hζ0 he hdefbound)
end Oberwolfach
