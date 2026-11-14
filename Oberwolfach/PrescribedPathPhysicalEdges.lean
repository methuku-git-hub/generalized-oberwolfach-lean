module

public import Oberwolfach.ExtendingListPathEmbedding

@[expose] public section
/-! The physical edges of a path selected outside a forbidden graph are
disjoint from that graph's edge set. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V:Type} [Fintype V] [DecidableEq V]

def prescribedPathPhysicalEdges (x y:V):List V→Finset (Sym2 V)
  | []=>{s(x,y)}
  | z::zs=>insert s(x,z) (prescribedPathPhysicalEdges z y zs)

theorem prescribed_path_physical_edges_avoid (D:V→V→Prop) (F:SimpleGraph V)
    (y:V):∀ xs:List V,∀ x:V,DirectedPathThrough D F x y xs→
      Disjoint (prescribedPathPhysicalEdges x y xs) F.edgeFinset := by
  intro xs
  induction xs with
  | nil =>
    intro x hpath
    apply Finset.disjoint_left.mpr
    intro e he hF
    have he':e=s(x,y):=by simpa [prescribedPathPhysicalEdges] using he
    subst e
    apply hpath.2
    simpa only [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet] using hF
  | cons z zs ih =>
    intro x hpath
    apply Finset.disjoint_left.mpr
    intro e he hF
    simp only [prescribedPathPhysicalEdges,Finset.mem_insert] at he
    rcases he with he|he
    · subst e
      apply hpath.2.1
      simpa only [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet] using hF
    · exact (Finset.disjoint_left.mp (ih z hpath.2.2)) he hF
end Oberwolfach
