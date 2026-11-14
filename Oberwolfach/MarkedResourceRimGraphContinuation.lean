module

public import Oberwolfach.MarkedResourceRimGraph

@[expose] public section

/-! Feed the actual later reserved resources into a continuation that was
uniform in a bounded graph protected from the earlier deletion. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_resource_rim_graph_continuation
    (P : SimpleGraph V) (π : Equiv.Perm V) (d : ℕ)
    (σ : RawMarkedOutcome V U Γ Color) (D : MarkedReferenceDeletion P π d σ)
    (B : ℕ) (C : Finset (Finset V ⊕ (V × U)))
    (hcard : C.card ≤ B) (hdis : Disjoint D.removed C)
    (Conclusion : SimpleGraph V → Prop)
    (hLate : ∀ A : SimpleGraph V, (∀v, A.degree v ≤ B) →
      (∀x y, (markedSampleArcSetGraph P π d σ D.arcs).Adj x y → ¬ A.Adj x y) → Conclusion A) :
    Conclusion (markedResourceRimGraph C) := by
  apply hLate
  · intro v
    exact (markedResourceRimGraph_degree_le C v).trans hcard
  · exact markedReferenceDeletion_disjoint_resourceRimGraph P π d σ D C hdis
end Oberwolfach
