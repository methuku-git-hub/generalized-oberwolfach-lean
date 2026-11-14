module

public import Oberwolfach.PrescribedMappedPathAvoidance
public import Oberwolfach.PrescribedCyclePhysicalEdges
public import Oberwolfach.PrescribedEmbeddingPhysicalStep

@[expose] public section
/-! Add the exact mapped physical edges of a source component to its factor,
protecting all other factors and the separately reserved graph. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {X V I:Type} [Fintype X] [Fintype V] [DecidableEq X] [DecidableEq V] [DecidableEq I]

theorem prescribed_two_ended_mapped_physical_step (g:X→V) (D:V→V→Prop)
    (F J:SimpleGraph V) (a b:X) (as:List X)
    (hpath:DirectedPathThrough D F (g a) (g b) (as.map g))
    (E:I→Finset (Sym2 V)) (k:I) (hpair:PairwisePhysicalDisjoint E)
    (hcover:∀ j,E j⊆F.edgeFinset) (hJ:J.edgeFinset⊆F.edgeFinset):
    let added:=(prescribedPathPhysicalEdges a b as).image (Sym2.map g);
    PairwisePhysicalDisjoint (Function.update E k (E k∪added)) ∧ Disjoint added J.edgeFinset := by
  exact prescribed_embedding_physical_step E k _ F J hpair hcover hJ
    (prescribed_two_ended_mapped_edges_avoid g D F a b as hpath)

theorem prescribed_one_ended_mapped_physical_step (g:X→V) (D:V→V→Prop)
    (F J:SimpleGraph V) (forward:Bool) (a:X) (as:List X)
    (hpath:DirectedPathFrom D F forward (g a) (as.map g))
    (E:I→Finset (Sym2 V)) (k:I) (hpair:PairwisePhysicalDisjoint E)
    (hcover:∀ j,E j⊆F.edgeFinset) (hJ:J.edgeFinset⊆F.edgeFinset):
    let added:=(prescribedOneSidedPhysicalEdges a as).image (Sym2.map g);
    PairwisePhysicalDisjoint (Function.update E k (E k∪added)) ∧ Disjoint added J.edgeFinset := by
  exact prescribed_embedding_physical_step E k _ F J hpair hcover hJ
    (prescribed_one_ended_mapped_edges_avoid g D F forward a as hpath)

theorem prescribed_cycle_mapped_physical_step (g:X→V) (D:V→V→Prop)
    (F J:SimpleGraph V) (as:List X) (hcycle:DirectedCycleThrough D F (as.map g))
    (E:I→Finset (Sym2 V)) (k:I) (hpair:PairwisePhysicalDisjoint E)
    (hcover:∀ j,E j⊆F.edgeFinset) (hJ:J.edgeFinset⊆F.edgeFinset):
    let added:=(prescribedCyclePhysicalEdges as).image (Sym2.map g);
    PairwisePhysicalDisjoint (Function.update E k (E k∪added)) ∧ Disjoint added J.edgeFinset := by
  exact prescribed_embedding_physical_step E k _ F J hpair hcover hJ
    (prescribed_cycle_mapped_edges_avoid g D F as hcycle)
end Oberwolfach
