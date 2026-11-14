module

public import Oberwolfach.PrescribedPathPhysicalMap
public import Oberwolfach.ExtendingListFreePath
public import Oberwolfach.PrescribedEmbeddingPhysicalStep

@[expose] public section
/-! Physical resources of an ordered path with no prescribed endpoint. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {X V I:Type} [Fintype X] [Fintype V] [DecidableEq X] [DecidableEq V] [DecidableEq I]

def prescribedFreePathPhysicalEdges (xs:List V):Finset (Sym2 V):=
  match xs with
  | []=>∅
  | x::zs=>prescribedOneSidedPhysicalEdges x zs

theorem prescribed_free_path_physical_map (g:X→V) (xs:List X):
    (prescribedFreePathPhysicalEdges xs).image (Sym2.map g)=
      prescribedFreePathPhysicalEdges (xs.map g) := by
  cases xs with
  | nil => simp [prescribedFreePathPhysicalEdges]
  | cons x zs => exact prescribed_one_sided_physical_map g zs x

theorem prescribed_free_path_physical_avoid (D:V→V→Prop) (F:SimpleGraph V)
    (xs:List V) (hpath:DirectedNonemptyPath D F true xs):
    Disjoint (prescribedFreePathPhysicalEdges xs) F.edgeFinset := by
  cases xs with
  | nil => contradiction
  | cons x zs => exact prescribed_one_sided_physical_edges_avoid D F true zs x hpath

theorem prescribed_free_path_mapped_physical_step (g:X→V) (D:V→V→Prop)
    (F J:SimpleGraph V) (as:List X) (hpath:DirectedNonemptyPath D F true (as.map g))
    (E:I→Finset (Sym2 V)) (k:I) (hpair:PairwisePhysicalDisjoint E)
    (hcover:∀ j,E j⊆F.edgeFinset) (hJ:J.edgeFinset⊆F.edgeFinset):
    let added:=(prescribedFreePathPhysicalEdges as).image (Sym2.map g);
    PairwisePhysicalDisjoint (Function.update E k (E k∪added)) ∧ Disjoint added J.edgeFinset := by
  apply prescribed_embedding_physical_step E k _ F J hpair hcover hJ
  rw [prescribed_free_path_physical_map]
  exact prescribed_free_path_physical_avoid D F (as.map g) hpath
end Oberwolfach
