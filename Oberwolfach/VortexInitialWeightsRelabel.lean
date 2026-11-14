module

public import Oberwolfach.SuccessorWeightsRelabel
public import Oberwolfach.VortexInitialDomainInverse

@[expose] public section
/-! The initial vortex weights are the original fixed parent weights,
reindexed along the canonical full-domain equivalence. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]

theorem vortex_initial_successor_weights_relabel {c : ℕ}
    (G : SimpleGraph V) (D m : ℕ) (β ε : ℝ) (Q : Vortex U G D β ε m)
    (π : Equiv.Perm V) (b : ℕ) (Dref τ A B : ℝ)
    (w : (Fin c → V) → ℝ) (hw : SuccessorSequenceWeightConditions G π b Dref τ A B w) :
    SuccessorSequenceWeightConditions (G.comap (Subtype.val : Q.vertices 0 → V))
      (vortexInitialPermutation G D m β ε Q π) b Dref τ A B
      (fun z => w (Subtype.val ∘ z)) := by
  exact successor_sequence_weights_relabel (vortexInitialVertexEquiv G D m β ε Q) G π
    (vortexInitialPermutation G D m β ε Q π)
    (vortex_initial_vertex_equiv_commutes G D m β ε Q π) b Dref τ A B w hw
end Oberwolfach
