module

public import Oberwolfach.RawMarkedPairRestriction

@[expose] public section
/-! Restriction by both identity maps leaves the entire raw outcome unchanged. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
namespace Oberwolfach
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]
theorem raw_marked_restrict_pair_identity (σ:RawMarkedOutcome V U Γ Color):
    rawMarkedRestrictPair (id:V→V) (id:U→U) σ=σ := by
  funext e
  cases e with
  | inl e=>
    simp [rawMarkedRestrictPair,rawMarkedRestrictVertices,rawMarkedRestrictHubs,
      rawMarkedVertexState,rawMarkedHubState,rawMarkedVertexCoordinate,rawMarkedHubCoordinate]
    rw [Sym2.map_id]
    rfl
  | inr a=>
    rcases a with ⟨u,i⟩
    cases i with
    | inl x=>rfl
    | inr z=>cases z <;> rfl
end Oberwolfach
