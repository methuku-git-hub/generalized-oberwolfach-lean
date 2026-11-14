module

public import Oberwolfach.OrdinaryOriginalSelectorCallback

@[expose] public section
/-! Extract the actual probability callback from the original selector's
chosen index, reserve, sampling data and weights. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_original_selector_callback_from_witness
    (n qCount D rstar m k d K:ℕ) (hd:2≤d)
    (ρ₀ θ lam aRow γ lamList ζDel smin τ t ξ b σ ζ χpair χlist χbal χbd χnbr χpairR χpath a α:ℝ)
    (BO:Fin K→ℝ) (F:Fin qCount→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (i₀:Fin K) (rsv:ℝ) (C:∀u,Finset (F u).ConnectedComponent)
    (sampling:OrdinaryAssignedVortexExactSamplingData (D:=D) F hF K i₀ rsv θ ((m:ℝ)+1) ρ₀ smin d)
    (w:∀i:Fin K,OrdinaryCycle (ordinaryEligibleHost P π d) (longPaddedSeedExponent i+2)→ℝ)
    (seed:(Fin (m+1)→Fin n)→ℝ)    (h:OrdinaryOriginalSelectorFactorWitness n qCount D rstar m k d K hd ρ₀ θ lam aRow γ lamList ζDel smin τ t ξ b σ ζ χpair χlist χbal χbd χnbr χpairR χpath a α BO F hF P π i₀ rsv C sampling w seed):
    OrdinaryOriginalSelectorCallback n qCount D rstar m k d K hd ρ₀ θ lam aRow γ lamList ζDel smin τ t ξ b σ ζ χpair χlist χbal χbd χnbr χpairR χpath a α BO F hF P π i₀ rsv C sampling w seed :=by
  exact h.2.2.2.2.2.2.2.2.2.2.2
end Oberwolfach
