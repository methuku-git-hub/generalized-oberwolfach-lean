module

public import Oberwolfach.MarkedRetainedTypedRestriction
public import Oberwolfach.VortexInitialDomainInverse

@[expose] public section
/-! At level zero the retained marked rim and spoke relations are exactly
those on the original domains, under the canonical vortex equivalences. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
namespace Oberwolfach
variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [Nonempty V] [LinearOrder V] [DecidableEq U]
variable (G : SimpleGraph V) (D m : ℕ) (β ε : ℝ) (Q : Vortex U G D β ε m)
local instance vortexTypedVertexDecEq : DecidableEq V := fun a b => Classical.propDecidable (a = b)
local instance vortexTypedLocalVertexDecEq : DecidableEq (Q.vertices 0) := fun a b => Classical.propDecidable (a = b)
local instance vortexTypedLocalHubDecEq : DecidableEq (Q.indices 0) := fun a b => Classical.propDecidable (a = b)
local instance vortexTypedLocalNonempty : Nonempty (Q.vertices 0) :=
  ⟨vortexInitialVertexOrderIso G D m β ε Q (Classical.choice inferInstance)⟩

theorem marked_vortex_initial_typed_restriction
    (π : Equiv.Perm V) (P : SimpleGraph V) (d : ℕ) (a c : Γ) (j : Color)
    (z : RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a) :
    let F := vortexInitialVertexOrderEmbedding G D m β ε Q
    let f := vortexInitialVertexEquiv G D m β ε Q
    let g := (vortexInitialHubEquiv G D m β ε Q).symm
    let ρ := vortexInitialPermutation G D m β ε Q π
    let hc : ∀ w, f (ρ w) = π (f w) := vortex_initial_vertex_equiv_commutes G D m β ε Q π
    let z' := markedRetainedPairRestriction f g π ρ hc d a z
    (∀ e : (Q.vertices 0 × Q.vertices 0) ⊕ (Q.vertices 0 × Q.vertices 0),
      rawMarkedPairRims (P.comap F) ρ d z'.1 e ↔
      rawMarkedPairRims P π d z.1 (Sum.map (Prod.map F F) (Prod.map F F) e)) ∧
    (∀ (b : Bool) (w : Q.vertices 0) (u : Q.indices 0),
      retainedRawMarkedSpokes ρ d (fun e => z'.1 (Sum.inr e)) a
        (startRetentionMinimum (rawStartHubSet ρ d (fun e => z'.1 (Sum.inr e)) a)) z'.2 c j b w u ↔
      retainedRawMarkedSpokes π d (fun e => z.1 (Sum.inr e)) a
        (startRetentionMinimum (rawStartHubSet π d (fun e => z.1 (Sum.inr e)) a)) z.2 c j b (f w) (g u)) := by
  classical
  dsimp only
  exact marked_retained_typed_restriction (vortexInitialVertexOrderEmbedding G D m β ε Q)
    (vortexInitialVertexEquiv G D m β ε Q) (vortex_initial_embedding_equiv_agree G D m β ε Q)
    (vortexInitialHubEquiv G D m β ε Q).symm π (vortexInitialPermutation G D m β ε Q π)
    (vortex_initial_vertex_equiv_commutes G D m β ε Q π) P d a c j z
end Oberwolfach
