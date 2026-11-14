module

public import Oberwolfach.OrdinaryTriangleFinishSampleInputsInside
public import Oberwolfach.OrdinaryFreshTriangleBoundaryEvent
public import Oberwolfach.OrdinaryTriangleFinishSampleInputs
public import Oberwolfach.OrdinaryBoundaryLocalEvents
public import Oberwolfach.OrdinaryBoundaryReserveJointEvent

@[expose] public section
/-! Named bundle of the reserve, support, factor and cleanup events on one
fresh physical-edge sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

structure OrdinaryFreshTriangleBoundaryEventInside
    (Q₀ Q F:SimpleGraph V) (H₀ H:V→U→Prop) (X:Finset V) (Z:Finset U)
    (γ κ b B ε η ζ p εreserve εsupport βe βh:ℝ)
    (data:MixedFreshParentDataInsideRoots γ κ b B ε η Q F (ordinaryPhysicalGraph Q H)
      (ordinaryPhysicalGraph F (fun _ _=>False)) (Function.Embedding.inl:V↪V⊕U)
      (ordinaryBoundaryHubSet H₀ Z X) (fun i=>(ordinaryBoundaryRimSet Q₀ X i).image Sum.inl)
      (fun i=>(ordinaryBoundaryRowSet H₀ X Z i).image Sum.inr)) (σ:Sym2 (V⊕U)→Bool):Prop where
  reserve:OrdinaryBoundaryReserveGood Q₀ H₀ X Z p εreserve σ
  support:BoundaryReserveSupportGood (ordinaryBoundaryGraph Q₀ H₀ X Z) p εsupport σ
  factors:MixedFreshBoundaryAvoidingEvent p (2*p) ζ Q F (ordinaryPhysicalGraph Q H)
    (ordinaryPhysicalGraph F (fun _ _=>False)) (Function.Embedding.inl:V↪V⊕U)
    (ordinaryBoundaryHubSet H₀ Z X) (fun i=>(ordinaryBoundaryRimSet Q₀ X i).image Sum.inl)
    (fun i=>(ordinaryBoundaryRowSet H₀ X Z i).image Sum.inr)
    (fun j=>hubSpokeCoin j.val) (fun i=>physicalIncidentCoin (Sum.inl i.val)) data.endpoint_disjoint σ
  extensions:OrdinaryBoundaryExtensionGood Q₀ H₀ X βe p σ
  hub_pairs:OrdinaryBoundaryHubPairGood H₀ Z βh p σ


theorem ordinary_triangle_finish_inputs_from_fresh_event_inside
    (Q₀ Q F:SimpleGraph V) (H₀ H:V→U→Prop) (X:Finset V) (Z:Finset U)
    (γ κ b B ε η ζ p εreserve εsupport βe βh τ ν:ℝ)
    (data:MixedFreshParentDataInsideRoots γ κ b B ε η Q F (ordinaryPhysicalGraph Q H)
      (ordinaryPhysicalGraph F (fun _ _=>False)) (Function.Embedding.inl:V↪V⊕U)
      (ordinaryBoundaryHubSet H₀ Z X) (fun i=>(ordinaryBoundaryRimSet Q₀ X i).image Sum.inl)
      (fun i=>(ordinaryBoundaryRowSet H₀ X Z i).image Sum.inr)) (σ:Sym2 (V⊕U)→Bool)
    (fresh:OrdinaryFreshTriangleBoundaryEventInside Q₀ Q F H₀ H X Z γ κ b B ε η ζ p εreserve εsupport βe βh data σ)
    (num:OrdinaryTriangleFinishNumbers (V:=V) (U:=U) γ κ ζ p εsupport τ ν)
    (hbase:ordinaryPhysicalGraph Q H≤spanningRestriction (ordinaryPhysicalGraph Q₀ H₀) (ordinaryInnerVertices X Z))
    (hQF:Disjoint Q₀ F)
    (hbal:∀v,Q₀.degree v=2*(Finset.univ.filter (H₀ v)).card)
    (hdiv:∀u,3∣(Finset.univ.filter (fun v=>H₀ v u)).card):
    OrdinaryTriangleFinishSampleInputsInside Q₀ Q F H₀ H X Z σ γ κ b B ε η ζ p εsupport τ ν:=by
  exact ⟨num.gamma_pos,num.kappa_pos,num.zeta_pos,num.p_pos,num.p_le_one,num.tau_nonneg,num.nu_nonneg,
    num.hub_upper,⟨data,fresh.factors⟩,fresh.support,hbase,hQF,hbal,hdiv,num.support_small,num.deletion_small,
    num.density_small,num.sqrt_small,num.cleanup_small,num.order⟩
end Oberwolfach
