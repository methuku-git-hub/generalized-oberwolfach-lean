module

public import Oberwolfach.OrdinaryRawPairRestriction

@[expose] public section
/-! Restricting twice is exactly restricting once along the composed fixed
embeddings, so the local trace uses the same ambient random outcome. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V W A U Z B Γ Color:Type} [Fintype V] [Fintype W] [Fintype A] [Fintype U] [Fintype Z] [Fintype B]
  [Fintype Γ] [Fintype Color] [LinearOrder V] [LinearOrder W] [LinearOrder A]
  [DecidableEq U] [DecidableEq Z] [DecidableEq B]

theorem ordinary_raw_pair_restriction_comp
    (f:W↪V) (f₂:A↪W) (g:Z↪U) (g₂:B↪Z) (σ:RawWheelOutcome V U Γ Color):
    ordinaryRawRestrictPair f₂ g₂ (ordinaryRawRestrictPair f g σ)=
      ordinaryRawRestrictPair (f₂.trans f) (g₂.trans g) σ :=by
  funext e
  cases e with
  | inl e=>
    simp only [ordinaryRawRestrictPair,ordinaryRawPairState,ordinaryRawPairCoordinate,
      rawMarkedHubCoordinate,rawMarkedVertexCoordinate]
    rw [Sym2.map_map]
    rfl
  | inr e=>
    rcases e with ⟨u,e⟩
    cases e with
    | inl e=>rfl
    | inr e=>cases e <;> rfl
end Oberwolfach
