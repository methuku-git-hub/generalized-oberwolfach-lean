module

public import Oberwolfach.ClassColourBernoulli
public import Oberwolfach.ColourRestriction

@[expose] public section
/-! The Bernoulli membership mask for a class is exactly its physical
edge-colour graph, on the same categorical colouring. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem class_colour_membership_retained_graph {V:Type} {k:ℕ}
    (G:SimpleGraph V) (c:Sym2 V→Fin k) (a:Fin k):
    retainedGraph G (fun e=>classColourMembership a (c e))=edgeColourGraph G c a :=by
  ext x y
  simp [retainedGraph,edgeColourGraph,classColourMembership]
end Oberwolfach
