module

public import Oberwolfach.PrescribedPathPhysicalMap

@[expose] public section
/-! The physical images of source-path edges avoid the forbidden graph. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {X V:Type} [Fintype X] [Fintype V] [DecidableEq X] [DecidableEq V]

theorem prescribed_two_ended_mapped_edges_avoid (g:X→V) (D:V→V→Prop)
    (F:SimpleGraph V) (a b:X) (as:List X)
    (hpath:DirectedPathThrough D F (g a) (g b) (as.map g)):
    Disjoint ((prescribedPathPhysicalEdges a b as).image (Sym2.map g)) F.edgeFinset := by
  rw [prescribed_path_physical_map]
  exact prescribed_path_physical_edges_avoid D F (g b) (as.map g) (g a) hpath

theorem prescribed_one_ended_mapped_edges_avoid (g:X→V) (D:V→V→Prop)
    (F:SimpleGraph V) (forward:Bool) (a:X) (as:List X)
    (hpath:DirectedPathFrom D F forward (g a) (as.map g)):
    Disjoint ((prescribedOneSidedPhysicalEdges a as).image (Sym2.map g)) F.edgeFinset := by
  rw [prescribed_one_sided_physical_map]
  exact prescribed_one_sided_physical_edges_avoid D F forward (as.map g) (g a) hpath
end Oberwolfach
