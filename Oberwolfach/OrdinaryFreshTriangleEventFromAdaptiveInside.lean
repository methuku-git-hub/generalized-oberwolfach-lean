module

public import Oberwolfach.OrdinaryFreshTriangleBoundaryEventInside
public import Oberwolfach.OrdinaryAdaptiveFreshTriangleCleanupSampleInside

@[expose] public section
/-! Package the existing adaptive-sampling bundle using the exact parent
data attached to the selected earlier outcome. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Ω:Type} [Fintype V] [Fintype U] [Fintype Ω] [DecidableEq V] [DecidableEq U]

theorem ordinary_fresh_triangle_event_from_adaptive_bundle_inside
    (E:Ω→Prop) (a:Ω) (ha:E a)
    (Q₀ Q F:Ω→SimpleGraph V) (H₀ H:Ω→V→U→Prop) (X:Ω→Finset V) (Z:Ω→Finset U)
    (γ κ b B ε η ζ p εreserve εsupport βe βh:ℝ)
    (data:∀a,E a→MixedFreshParentDataInsideRoots γ κ b B ε η (Q a) (F a)
      (ordinaryPhysicalGraph (Q a) (H a)) (ordinaryPhysicalGraph (F a) (fun _ _=>False))
      (Function.Embedding.inl:V↪V⊕U) (ordinaryBoundaryHubSet (H₀ a) (Z a) (X a))
      (fun i=>(ordinaryBoundaryRimSet (Q₀ a) (X a) i).image Sum.inl)
      (fun i=>(ordinaryBoundaryRowSet (H₀ a) (X a) (Z a) i).image Sum.inr))
    (σ:Sym2 (V⊕U)→Bool)
    (hreserve:OrdinaryBoundaryReserveGood (Q₀ a) (H₀ a) (X a) (Z a) p εreserve σ)
    (hsupport:BoundaryReserveSupportGood (ordinaryBoundaryGraph (Q₀ a) (H₀ a) (X a) (Z a)) p εsupport σ)
    (hfactor:∃hE:E a,MixedFreshBoundaryAvoidingEvent p (2*p) ζ (Q a) (F a)
      (ordinaryPhysicalGraph (Q a) (H a)) (ordinaryPhysicalGraph (F a) (fun _ _=>False))
      (Function.Embedding.inl:V↪V⊕U) (ordinaryBoundaryHubSet (H₀ a) (Z a) (X a))
      (fun i=>(ordinaryBoundaryRimSet (Q₀ a) (X a) i).image Sum.inl)
      (fun i=>(ordinaryBoundaryRowSet (H₀ a) (X a) (Z a) i).image Sum.inr)
      (fun j=>hubSpokeCoin j.val) (fun i=>physicalIncidentCoin (Sum.inl i.val)) (data a hE).endpoint_disjoint σ)
    (hext:OrdinaryBoundaryExtensionGood (Q₀ a) (H₀ a) (X a) βe p σ)
    (hpair:OrdinaryBoundaryHubPairGood (H₀ a) (Z a) βh p σ):
    OrdinaryFreshTriangleBoundaryEventInside (Q₀ a) (Q a) (F a) (H₀ a) (H a) (X a) (Z a)
      γ κ b B ε η ζ p εreserve εsupport βe βh (data a ha) σ:=by
  obtain ⟨ha',hfactor⟩:=hfactor
  have heq:ha'=ha:=Subsingleton.elim _ _
  subst ha'
  exact ⟨hreserve,hsupport,hfactor,hext,hpair⟩
end Oberwolfach
