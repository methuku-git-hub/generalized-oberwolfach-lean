module

public import Oberwolfach.OrdinaryOriginalSelectorFactorWitness

@[expose] public section
/-! The component family selected by the original triangle witness has the
exact size required by the ordinary wheel construction. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_original_triangle_selector_component_size
    (n qCount D m k d K:ℕ) (hd:2≤d)
    (ρ₀ θ lam aRow γ lamList ζDel smin τ t ξ b σ ζ χpair χlist χbal χbd χnbr χpairR χpath a α:ℝ)
    (BO:Fin K→ℝ) (F:Fin qCount→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (i₀:Fin K) (rsv:ℝ)
    (C:∀u,Finset (F u).ConnectedComponent)
    (sampling:OrdinaryAssignedVortexExactSamplingData (D:=D) F hF K i₀ rsv θ ((m:ℝ)+1) ρ₀ smin d)
    (w:∀i:Fin K,OrdinaryCycle (ordinaryEligibleHost P π d) (longPaddedSeedExponent i+2)→ℝ)
    (seed:(Fin (m+1)→Fin n)→ℝ)
    (hwitness:OrdinaryOriginalSelectorFactorWitness n qCount D 3 m k d K hd ρ₀ θ lam aRow γ lamList ζDel smin
      τ t ξ b σ ζ χpair χlist χbal χbd χnbr χpairR χpath a α BO F hF P π i₀ rsv C sampling w seed):
    ∀u (c:↥(C u)),Fintype.card c.val=2+1 :=by
  obtain ⟨_hi,_hr,_hrcap,_hcandidates,hsize,_rest⟩:=hwitness
  intro u c
  simpa using hsize u c.val c.property
end Oberwolfach
