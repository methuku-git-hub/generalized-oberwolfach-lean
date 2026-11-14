module

public import Oberwolfach.OrdinaryFreshTriangleBoundaryEventInside
public import Oberwolfach.OrdinaryAdaptiveFreshFromDeepParentEvent

@[expose] public section
/-! Package the five fresh-sample components while retaining the entire
prior event and its selected parent data. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1800000
set_option synthInstance.maxSize 8192
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Ω:Type} [Fintype V] [Fintype U] [Fintype Ω] [DecidableEq V] [DecidableEq U]

theorem ordinary_fresh_inside_bundle_event
    (μ:FiniteLaw (Σ _ : Ω, Sym2 (V⊕U)→Bool)) (E:Ω→Prop) (prob:ℝ)
    (Q₀ Q F:Ω→SimpleGraph V) (H₀ H:Ω→V→U→Prop) (X:Ω→Finset V) (Z:Ω→Finset U)
    (γ κ b B ε η ζ p εres εsup βe βh:ℝ)
    (data:∀ω,E ω→MixedFreshParentDataInsideRoots γ κ b B ε η (Q ω) (F ω)
      (ordinaryPhysicalGraph (Q ω) (H ω)) (ordinaryPhysicalGraph (F ω) (fun _ _=>False))
      (Function.Embedding.inl:V↪V⊕U) (ordinaryBoundaryHubSet (H₀ ω) (Z ω) (X ω))
      (fun i=>(ordinaryBoundaryRimSet (Q₀ ω) (X ω) i).image Sum.inl)
      (fun i=>(ordinaryBoundaryRowSet (H₀ ω) (X ω) (Z ω) i).image Sum.inr))
    (hprob:prob≤μ.probability (fun z=>E z.1 ∧
      OrdinaryBoundaryReserveGood (Q₀ z.1) (H₀ z.1) (X z.1) (Z z.1) p εres z.2 ∧
      BoundaryReserveSupportGood (ordinaryBoundaryGraph (Q₀ z.1) (H₀ z.1) (X z.1) (Z z.1)) p εsup z.2 ∧
      (∃hE:E z.1,MixedFreshBoundaryAvoidingEvent p (2*p) ζ (Q z.1) (F z.1)
        (ordinaryPhysicalGraph (Q z.1) (H z.1)) (ordinaryPhysicalGraph (F z.1) (fun _ _=>False))
        (Function.Embedding.inl:V↪V⊕U) (ordinaryBoundaryHubSet (H₀ z.1) (Z z.1) (X z.1))
        (fun i=>(ordinaryBoundaryRimSet (Q₀ z.1) (X z.1) i).image Sum.inl)
        (fun i=>(ordinaryBoundaryRowSet (H₀ z.1) (X z.1) (Z z.1) i).image Sum.inr)
        (fun j=>hubSpokeCoin j.val) (fun i=>physicalIncidentCoin (Sum.inl i.val))
        (data z.1 hE).endpoint_disjoint z.2) ∧
      OrdinaryBoundaryExtensionGood (Q₀ z.1) (H₀ z.1) (X z.1) βe p z.2 ∧
      OrdinaryBoundaryHubPairGood (H₀ z.1) (Z z.1) βh p z.2)) :
    prob≤μ.probability (fun z=>∃hE:E z.1,
      OrdinaryFreshTriangleBoundaryEventInside (Q₀ z.1) (Q z.1) (F z.1) (H₀ z.1) (H z.1) (X z.1) (Z z.1)
        γ κ b B ε η ζ p εres εsup βe βh (data z.1 hE) z.2) := by
  apply hprob.trans
  apply finiteLaw_probability_mono
  intro z hz
  obtain ⟨hE,hres,hsup,⟨hE',hfactors⟩,hext,hhub⟩:=hz
  refine ⟨hE',?_⟩
  exact ⟨hres,hsup,hfactors,hext,hhub⟩
end Oberwolfach
