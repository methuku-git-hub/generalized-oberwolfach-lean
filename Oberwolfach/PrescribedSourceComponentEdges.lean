module

public import Oberwolfach.PrescribedSourcePathEdges
public import Oberwolfach.PrescribedFreePathPhysicalEdges
public import Oberwolfach.PrescribedCyclePhysicalEdges

@[expose] public section
/-! Ordered source paths and cycles use only edges of their original graph. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {X:Type} [Fintype X] [DecidableEq X]

theorem prescribed_free_path_source_edges (D:X→X→Prop) (Q F:SimpleGraph X)
    (hDQ:∀ x y,D x y→Q.Adj x y) (as:List X)
    (hpath:DirectedNonemptyPath D F true as):
    prescribedFreePathPhysicalEdges as⊆Q.edgeFinset := by
  cases as with
  | nil => contradiction
  | cons a xs => exact prescribed_one_ended_source_edges D Q F hDQ true xs a hpath

theorem prescribed_cycle_source_edges (D:X→X→Prop) (Q F:SimpleGraph X)
    (hDQ:∀ x y,D x y→Q.Adj x y) (as:List X)
    (hcycle:DirectedCycleThrough D F as):
    prescribedCyclePhysicalEdges as⊆Q.edgeFinset := by
  cases as with
  | nil => contradiction
  | cons a xs => exact prescribed_two_ended_source_edges D Q F hDQ a xs a hcycle
end Oberwolfach
