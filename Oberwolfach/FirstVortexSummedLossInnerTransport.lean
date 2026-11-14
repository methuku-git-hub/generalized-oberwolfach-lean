module

public import Oberwolfach.FirstVortexSummedLossMonotone
public import Oberwolfach.MarkedFixedVortexSizes

@[expose] public section
/-! Use the actual first inner domain, rather than its ambient image, in the
local loss witness. The same numerical witnesses and sample are retained. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem first_vortex_summed_loss_inner_transport
    {n D m:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (G:SimpleGraph (Fin n)) (β ε:ℝ) (Q:Vortex U G D β ε m)
    (d:ℕ) (c rho eta θ a γ ξPart κ Δ ζret ηBalance boundary:ℝ)
    (h:FirstVortexSummedLossWitness n d ((Q.extendedVertices 1).card:ℝ) c rho eta θ a γ ξPart κ Δ ζret ηBalance boundary):
    FirstVortexSummedLossWitness n d ((markedVortexInnerVertices Q 0).card:ℝ) c rho eta θ a γ ξPart κ Δ ζret ηBalance boundary :=by
  have hcard:(markedVortexInnerVertices Q 0).card=(Q.extendedVertices 1).card:=by
    simpa only [Nat.zero_add] using (marked_vortex_inner_cardinalities Q 0).1
  simpa only [hcard] using h
end Oberwolfach
