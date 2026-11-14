module

public import Oberwolfach.FirstVortexSummedLossInnerTransport

@[expose] public section
/-! Transfer the early smaller local budget to the caller's actual first inner
vortex domain and its prescribed larger local tolerance. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem first_vortex_summed_loss_caller_transport
    {n D m:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (G:SimpleGraph (Fin n)) (β ε:ℝ) (Q:Vortex U G D β ε m)
    (d:ℕ) (cSmall cLocal rho eta θ a γ ξPart κ Δ ζret ηBalance boundary:ℝ)
    (hc:cSmall≤cLocal)
    (h:FirstVortexSummedLossWitness n d ((Q.extendedVertices 1).card:ℝ) cSmall rho eta θ a γ ξPart κ Δ ζret ηBalance boundary):
    FirstVortexSummedLossWitness n d ((markedVortexInnerVertices Q 0).card:ℝ) cLocal rho eta θ a γ ξPart κ Δ ζret ηBalance boundary :=by
  have hinner:=first_vortex_summed_loss_inner_transport G β ε Q d cSmall rho eta θ a γ ξPart κ Δ ζret ηBalance boundary h
  exact first_vortex_summed_loss_mono n d ((markedVortexInnerVertices Q 0).card:ℝ)
    cSmall cLocal rho eta θ a γ ξPart κ Δ ζret ηBalance boundary (by positivity) hc hinner
end Oberwolfach
