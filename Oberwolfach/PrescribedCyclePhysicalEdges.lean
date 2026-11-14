module

public import Oberwolfach.PrescribedPathPhysicalMap
public import Oberwolfach.ExtendingListCycleEmbedding

@[expose] public section
/-! Physical edge sets of an ordered cycle, including its closing edge. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {X V:Type} [Fintype X] [Fintype V] [DecidableEq X] [DecidableEq V]

def prescribedCyclePhysicalEdges (xs:List V):Finset (Sym2 V):=
  match xs with
  | []=>∅
  | x::zs=>prescribedPathPhysicalEdges x x zs

theorem prescribed_cycle_physical_edges_avoid (D:V→V→Prop) (F:SimpleGraph V)
    (xs:List V) (hcycle:DirectedCycleThrough D F xs):
    Disjoint (prescribedCyclePhysicalEdges xs) F.edgeFinset := by
  cases xs with
  | nil => contradiction
  | cons x zs => exact prescribed_path_physical_edges_avoid D F x zs x hcycle

theorem prescribed_cycle_physical_map (g:X→V) (xs:List X):
    (prescribedCyclePhysicalEdges xs).image (Sym2.map g)=
      prescribedCyclePhysicalEdges (xs.map g) := by
  cases xs with
  | nil => simp [prescribedCyclePhysicalEdges]
  | cons x zs => exact prescribed_path_physical_map g x zs x

theorem prescribed_cycle_mapped_edges_avoid (g:X→V) (D:V→V→Prop)
    (F:SimpleGraph V) (as:List X) (hcycle:DirectedCycleThrough D F (as.map g)):
    Disjoint ((prescribedCyclePhysicalEdges as).image (Sym2.map g)) F.edgeFinset := by
  rw [prescribed_cycle_physical_map]
  exact prescribed_cycle_physical_edges_avoid D F (as.map g) hcycle
end Oberwolfach
