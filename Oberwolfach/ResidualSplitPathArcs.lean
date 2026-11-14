module

public import Oberwolfach.ResidualSplitPathEdges
public import Oberwolfach.PrescribedPathDirectedEdges

@[expose] public section
/-! Splitting an ordered path preserves exactly its retained directed arcs. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

def splitPathArcUnion (H:SimpleGraph V) (xs:List V):Finset (V×V) :=
  (splitPathByGraph H xs).toFinset.biUnion prescribedDirectedPathEdges

theorem split_path_arc_union (H:SimpleGraph V):
    ∀ xs:List V,splitPathArcUnion H xs =
      (prescribedDirectedPathEdges xs).filter (fun e=>H.Adj e.1 e.2) := by
  intro xs
  induction xs with
  | nil => simp [splitPathArcUnion,splitPathByGraph,splitOrderedPath,prescribedDirectedPathEdges]
  | cons x xs ih =>
    cases xs with
    | nil => simp [splitPathArcUnion,splitPathByGraph,splitOrderedPath,prescribedDirectedPathEdges]
    | cons y ys =>
      obtain ⟨block,blocks,h⟩:=split_ordered_path_head (fun x y=>decide (H.Adj x y)) y ys
      have ih':( (y::block)::blocks).toFinset.biUnion prescribedDirectedPathEdges =
          (prescribedDirectedPathEdges (y::ys)).filter (fun e=>H.Adj e.1 e.2) := by
        simpa [splitPathArcUnion,splitPathByGraph,h] using ih
      by_cases hxy:H.Adj x y
      · have h' := congrArg (fun E:Finset (V×V)=>insert (x,y) E) ih'
        simpa [splitPathArcUnion,splitPathByGraph,splitOrderedPath,h,hxy,
          prescribedDirectedPathEdges,Finset.filter_insert,Finset.insert_union] using h'
      · simpa [splitPathArcUnion,splitPathByGraph,splitOrderedPath,h,hxy,
          prescribedDirectedPathEdges,Finset.filter_insert] using ih'
end Oberwolfach
