module

public import Oberwolfach.OrdinaryFreshTriangleBoundaryEventInside
public import Oberwolfach.OrdinaryInnerFactorHost

@[expose] public section
/-! The actual inner factor host automatically satisfies the host-survival
input for the corrected same-sample triangle finish. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_finish_inputs_from_inner_fresh
    (Q F:SimpleGraph V) (H:V→U→Prop) (A:Finset V) (Z:Finset U)
    (γ κ b B ε η ζ p εreserve εsupport βe βh τ ν:ℝ)
    (data:MixedFreshParentDataInsideRoots γ κ b B ε η (spanningRestriction Q A) F
      (ordinaryPhysicalGraph (spanningRestriction Q A) (fun v u=>H v u∧v∈A∧u∈Z))
      (ordinaryPhysicalGraph F (fun _ _=>False)) (Function.Embedding.inl:V↪V⊕U)
      (ordinaryBoundaryHubSet H Z A) (fun i=>(ordinaryBoundaryRimSet Q A i).image Sum.inl)
      (fun i=>(ordinaryBoundaryRowSet H A Z i).image Sum.inr)) (σ:Sym2 (V⊕U)→Bool)
    (fresh:OrdinaryFreshTriangleBoundaryEventInside Q (spanningRestriction Q A) F H
      (fun v u=>H v u∧v∈A∧u∈Z) A Z γ κ b B ε η ζ p εreserve εsupport βe βh data σ)
    (num:OrdinaryTriangleFinishNumbers (V:=V) (U:=U) γ κ ζ p εsupport τ ν)
    (hQF:Disjoint Q F)
    (hbal:∀v,Q.degree v=2*(Finset.univ.filter (H v)).card)
    (hdiv:∀u,3∣(Finset.univ.filter (fun v=>H v u)).card):
    OrdinaryTriangleFinishSampleInputsInside Q (spanningRestriction Q A) F H
      (fun v u=>H v u∧v∈A∧u∈Z) A Z σ γ κ b B ε η ζ p εsupport τ ν:=by
  apply ordinary_triangle_finish_inputs_from_fresh_event_inside Q (spanningRestriction Q A) F H
    (fun v u=>H v u∧v∈A∧u∈Z) A Z γ κ b B ε η ζ p εreserve εsupport βe βh τ ν data σ fresh num
  · exact (ordinary_inner_factor_host_eq Q H A Z).le
  · exact hQF
  · exact hbal
  · exact hdiv
end Oberwolfach
