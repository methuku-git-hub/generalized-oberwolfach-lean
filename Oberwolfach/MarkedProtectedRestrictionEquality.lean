module

public import Oberwolfach.RawMarkedPairRestriction

@[expose] public section
/-! Exact agreement on the first inner pair propagates to every deeper
restriction, regardless of the size of that level. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U W Z Γ Color:Type} [Fintype V] [Fintype U] [Fintype W] [Fintype Z]
  [Fintype Γ] [Fintype Color] [LinearOrder V] [LinearOrder W] [DecidableEq U] [DecidableEq Z]

theorem marked_protected_restriction_equality
    (σ τ:RawMarkedOutcome V U Γ Color) (H H':Bool→V→U→Prop)
    (I:Finset V) (J:Finset U) (f:W→V) (g:Z→U)
    (hf:∀x,f x∈I) (hg:∀u,g u∈J)
    (hrim:∀e:Sym2 V,e.toFinset⊆I→σ (Sum.inl e)=τ (Sum.inl e))
    (hinterval:∀e,σ (Sum.inr e)=τ (Sum.inr e))
    (hspoke:∀b v u,v∈I→u∈J→(H b v u↔H' b v u)):
    rawMarkedRestrictPair f g σ=rawMarkedRestrictPair f g τ ∧
    (fun b x u=>H b (f x) (g u))=(fun b x u=>H' b (f x) (g u)):=by
  constructor
  · funext e
    cases e with
    | inl e=>
      induction e using Sym2.ind with
      | _ x y=>
        have hh:=hrim s(f x,f y) (by
          intro v hv
          simp only [Sym2.toFinset_mk_eq,Finset.mem_insert,Finset.mem_singleton] at hv
          rcases hv with rfl|rfl
          · exact hf x
          · exact hf y)
        simpa [rawMarkedRestrictPair,rawMarkedRestrictVertices,rawMarkedVertexState,
          rawMarkedVertexCoordinate,rawMarkedRestrictHubs,rawMarkedHubState,rawMarkedHubCoordinate] using hh
    | inr e=>
      rcases e with ⟨u,e⟩
      cases e with
      | inl x=>simpa [rawMarkedRestrictPair,rawMarkedRestrictVertices,rawMarkedVertexState,
          rawMarkedVertexCoordinate,rawMarkedRestrictHubs,rawMarkedHubState,rawMarkedHubCoordinate] using hinterval _
      | inr e=>
        cases e with
        | inl x=>simpa [rawMarkedRestrictPair,rawMarkedRestrictVertices,rawMarkedVertexState,
            rawMarkedVertexCoordinate,rawMarkedRestrictHubs,rawMarkedHubState,rawMarkedHubCoordinate] using hinterval _
        | inr x=>simpa [rawMarkedRestrictPair,rawMarkedRestrictVertices,rawMarkedVertexState,
            rawMarkedVertexCoordinate,rawMarkedRestrictHubs,rawMarkedHubState,rawMarkedHubCoordinate] using hinterval _
  · funext b x u
    exact propext (hspoke b (f x) (g u) (hf x) (hg u))
end Oberwolfach
