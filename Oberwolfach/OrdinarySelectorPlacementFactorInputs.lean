module

public import Oberwolfach.OrdinaryOriginalSelectorFactorWitness
public import Oberwolfach.OrdinaryClassReserveBound

@[expose] public section
/-! Extract the factor-side placement inputs from the original selector,
without adding a new reserve or component-size hypothesis. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
set_option synthInstance.maxSize 32768
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_selector_placement_factor_inputs
    (n qCount D rstar m k d K:ℕ) (hd:2≤d)
    (ρ₀ θ lam aRow γ lamList ζDel smin τ t ξ b σ ζ χpair χlist χbal χbd χnbr χpairR χpath a α:ℝ)
    (BO:Fin K→ℝ) (F:Fin qCount→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (i₀:Fin K) (rsv:ℝ) (C:∀u,Finset (F u).ConnectedComponent)
    (sampling:OrdinaryAssignedVortexExactSamplingData (D:=D) F hF K i₀ rsv θ ((m:ℝ)+1) ρ₀ smin d)
    (w:∀i:Fin K,OrdinaryCycle (ordinaryEligibleHost P π d) (longPaddedSeedExponent i+2)→ℝ)
    (seed:(Fin (m+1)→Fin n)→ℝ)
    (hsmin:0<smin)
    (hwitness:OrdinaryOriginalSelectorFactorWitness n qCount D rstar m k d K hd ρ₀ θ lam aRow γ lamList ζDel smin τ t ξ b σ ζ χpair χlist χbal χbd χnbr χpairR χpath a α BO F hF P π i₀ rsv C sampling w seed):
    0≤ rsv ∧ rsv≤ 1/100 ∧
    (∀u (c:↥(C u)),Fintype.card c.val=i₀.val+1) ∧
    (∀u,((i₀.val+1:ℕ):ℝ)*(C u).card=rsv*n) ∧
    OrdinaryClassReserveBound F hF i₀ rsv ∧
    (∀u,(∑g:Bool,ordinaryAssignedMarkedProbability F hF K θ ((m:ℝ)+1) u g)≤ 1/8) :=by
  unfold OrdinaryOriginalSelectorFactorWitness at hwitness
  have heq:=hwitness.1
  have hcomp:=hwitness.2.2.2.2.1
  have hcard:=hwitness.2.2.2.2.2.1
  have hclass:=hwitness.2.2.2.2.2.2.1
  refine ⟨(hsmin.trans_le hwitness.2.1).le,hwitness.2.2.1,?_,?_,hclass,sampling.hQ⟩
  · intro u c; rw [heq]; exact hcomp u c.val c.property
  · intro u; rw [heq]; exact hcard u
end Oberwolfach
