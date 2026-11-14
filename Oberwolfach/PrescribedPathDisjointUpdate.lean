module

public import Oberwolfach.PrescribedPathPhysicalEdges
public import Oberwolfach.PrescribedOneSidedPhysicalEdges
public import Oberwolfach.PrescribedEmbeddingDisjointUpdate

@[expose] public section
/-! Adding the physical edges of either kind of selected path to its factor
preserves pairwise physical edge-disjointness. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V I:Type} [Fintype V] [DecidableEq V] [DecidableEq I]

theorem prescribed_path_disjoint_update (D:V→V→Prop) (F:SimpleGraph V)
    (x y:V) (xs:List V) (hpath:DirectedPathThrough D F x y xs)
    (E:I→Finset (Sym2 V)) (k:I) (hpair:PairwisePhysicalDisjoint E)
    (hcover:∀ j,E j⊆F.edgeFinset):
    PairwisePhysicalDisjoint (Function.update E k (E k∪prescribedPathPhysicalEdges x y xs)) := by
  apply prescribed_embedding_disjoint_update E k _ hpair
  intro j hj
  apply Finset.disjoint_left.mpr
  intro e he heE
  exact (Finset.disjoint_left.mp (prescribed_path_physical_edges_avoid D F y xs x hpath)) he (hcover j heE)

theorem prescribed_one_sided_path_disjoint_update (D:V→V→Prop) (F:SimpleGraph V)
    (forward:Bool) (x:V) (xs:List V) (hpath:DirectedPathFrom D F forward x xs)
    (E:I→Finset (Sym2 V)) (k:I) (hpair:PairwisePhysicalDisjoint E)
    (hcover:∀ j,E j⊆F.edgeFinset):
    PairwisePhysicalDisjoint (Function.update E k (E k∪prescribedOneSidedPhysicalEdges x xs)) := by
  apply prescribed_embedding_disjoint_update E k _ hpair
  intro j hj
  apply Finset.disjoint_left.mpr
  intro e he heE
  exact (Finset.disjoint_left.mp (prescribed_one_sided_physical_edges_avoid D F forward xs x hpath)) he (hcover j heE)
end Oberwolfach
