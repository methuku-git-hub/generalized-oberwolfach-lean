module

public import Oberwolfach.ExtendingListOneSidedPath

@[expose] public section
/-! A forward or backward one-sided path avoids every forbidden physical edge. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V:Type} [Fintype V] [DecidableEq V]

def prescribedOneSidedPhysicalEdges (x:V):List V→Finset (Sym2 V)
  | []=>∅
  | z::zs=>insert s(x,z) (prescribedOneSidedPhysicalEdges z zs)

theorem prescribed_one_sided_physical_edges_avoid (D:V→V→Prop) (F:SimpleGraph V)
    (forward:Bool):∀ xs:List V,∀ x:V,DirectedPathFrom D F forward x xs→
      Disjoint (prescribedOneSidedPhysicalEdges x xs) F.edgeFinset := by
  intro xs
  induction xs with
  | nil => intro x hpath;simp [prescribedOneSidedPhysicalEdges]
  | cons z zs ih =>
    intro x hpath
    apply Finset.disjoint_left.mpr
    intro e he hF
    simp only [prescribedOneSidedPhysicalEdges,Finset.mem_insert] at he
    rcases he with he|he
    · subst e
      apply hpath.2.1
      simpa only [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet] using hF
    · exact (Finset.disjoint_left.mp (ih z hpath.2.2)) he hF
end Oberwolfach
