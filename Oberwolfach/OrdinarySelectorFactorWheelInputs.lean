module

public import Oberwolfach.OrdinaryOriginalSelectorFactorWitness
public import Oberwolfach.OrdinaryClassReserveBound

@[expose] public section
/-! The original factor witness supplies the reserved wheel sizes and
class-frequency reserve required by the same-sample cost bound. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_selector_factor_wheel_inputs
    (n qCount D rstar m k d K:ℕ) (hd:2≤d) (hr:1≤rstar)
    (ρ₀ θ lam aRow γ lamList ζDel smin τ t ξ b σ ζ χpair χlist χbal χbd χnbr χpairR χpath a α:ℝ)
    (BO:Fin K→ℝ) (F:Fin qCount→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (i₀:Fin K) (rsv:ℝ)
    (C:∀u,Finset (F u).ConnectedComponent)
    (sampling:OrdinaryAssignedVortexExactSamplingData (D:=D) F hF K i₀ rsv θ ((m:ℝ)+1) ρ₀ smin d)
    (w:∀i:Fin K,OrdinaryCycle (ordinaryEligibleHost P π d) (longPaddedSeedExponent i+2)→ℝ)
    (seed:(Fin (m+1)→Fin n)→ℝ)
    (h:OrdinaryOriginalSelectorFactorWitness n qCount D rstar m k d K hd ρ₀ θ lam aRow γ lamList ζDel smin τ t ξ b σ ζ χpair χlist χbal χbd χnbr χpairR χpath a α BO F hF P π i₀ rsv C sampling w seed):
    smin≤rsv ∧ rsv≤1/100 ∧
    (∀u (c:↥(C u)),Fintype.card c.val=(rstar-1)+1) ∧
    OrdinaryClassReserveBound F hF i₀ rsv :=by
  obtain ⟨_,hsmin,hrsv,_,hsize,_,hreserve,_⟩:=h
  refine ⟨hsmin,hrsv,?_,hreserve⟩
  intro u c
  simpa only [Nat.sub_add_cancel hr] using hsize u c.val c.property
end Oberwolfach
