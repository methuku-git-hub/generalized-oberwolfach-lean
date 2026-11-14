module

public import Oberwolfach.RawMarkedPairRestriction

@[expose] public section
/-! Agreement of all interval coordinates survives simultaneous restriction
of vertices and hubs. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W U Z Γ Color:Type} [Fintype V] [Fintype W] [Fintype U] [Fintype Z] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [LinearOrder W] [DecidableEq U] [DecidableEq Z]

theorem raw_marked_restriction_interval_agreement
    (f:W→V) (g:Z→U) (σ τ:RawMarkedOutcome V U Γ Color)
    (h:∀e,σ (Sum.inr e)=τ (Sum.inr e)):
    ∀e,(rawMarkedRestrictPair f g σ) (Sum.inr e)=(rawMarkedRestrictPair f g τ) (Sum.inr e):=by
  intro ⟨u,e⟩
  cases e with
  | inl v => simpa only [rawMarkedRestrictPair,rawMarkedRestrictVertices,rawMarkedRestrictHubs,
      rawMarkedVertexCoordinate,rawMarkedHubCoordinate,rawIntervalVertexCoordinate,rawMarkedVertexState,rawMarkedHubState,Sum.map_inl] using h (g u,Sum.inl (f v))
  | inr e =>
    cases e with
    | inl v => simpa only [rawMarkedRestrictPair,rawMarkedRestrictVertices,rawMarkedRestrictHubs,
        rawMarkedVertexCoordinate,rawMarkedHubCoordinate,rawIntervalVertexCoordinate,rawMarkedVertexState,rawMarkedHubState,Sum.map_inr,Sum.map_inl] using h (g u,Sum.inr (Sum.inl (f v)))
    | inr v => simpa only [rawMarkedRestrictPair,rawMarkedRestrictVertices,rawMarkedRestrictHubs,
        rawMarkedVertexCoordinate,rawMarkedHubCoordinate,rawIntervalVertexCoordinate,rawMarkedVertexState,rawMarkedHubState,Sum.map_inr] using h (g u,Sum.inr (Sum.inr (f v)))
end Oberwolfach
