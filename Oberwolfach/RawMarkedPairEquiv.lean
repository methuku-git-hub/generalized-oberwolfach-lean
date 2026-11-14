module

public import Oberwolfach.RawMarkedPairRestriction

@[expose] public section
/-! Restriction to bijectively relabelled vertex and hub domains is a
bijection of the underlying raw marked outcomes. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W U Z Γ Color : Type} [Fintype V] [Fintype W] [Fintype U] [Fintype Z]
  [Fintype Γ] [Fintype Color] [LinearOrder V] [LinearOrder W] [DecidableEq U] [DecidableEq Z]

theorem raw_marked_restrict_pair_inverse
    (f : W ≃ V) (g : Z ≃ U) (σ : RawMarkedOutcome V U Γ Color) :
    rawMarkedRestrictPair f.symm g.symm (rawMarkedRestrictPair f g σ) = σ := by
  funext e
  cases e with
  | inl e =>
    induction e using Sym2.inductionOn with
    | _ x y =>
      simp [rawMarkedRestrictPair, rawMarkedRestrictVertices, rawMarkedRestrictHubs,
        rawMarkedVertexState, rawMarkedHubState, rawMarkedVertexCoordinate, rawMarkedHubCoordinate]
      rw [f.apply_symm_apply, f.apply_symm_apply]
  | inr e =>
    rcases e with ⟨u,e⟩
    cases e with
    | inl e =>
      simp [rawMarkedRestrictPair, rawMarkedRestrictVertices, rawMarkedRestrictHubs,
        rawMarkedVertexState, rawMarkedHubState, rawMarkedVertexCoordinate,
        rawMarkedHubCoordinate, rawIntervalVertexCoordinate]
      rw [g.apply_symm_apply, f.apply_symm_apply]
    | inr e =>
      cases e <;> simp [rawMarkedRestrictPair, rawMarkedRestrictVertices, rawMarkedRestrictHubs,
        rawMarkedVertexState, rawMarkedHubState, rawMarkedVertexCoordinate,
        rawMarkedHubCoordinate, rawIntervalVertexCoordinate] <;> rw [g.apply_symm_apply, f.apply_symm_apply]

def rawMarkedPairEquiv (f : W ≃ V) (g : Z ≃ U) :
    RawMarkedOutcome V U Γ Color ≃ RawMarkedOutcome W Z Γ Color where
  toFun := rawMarkedRestrictPair f g
  invFun := rawMarkedRestrictPair f.symm g.symm
  left_inv := raw_marked_restrict_pair_inverse f g
  right_inv := by
    intro σ
    simpa using raw_marked_restrict_pair_inverse f.symm g.symm σ
end Oberwolfach
