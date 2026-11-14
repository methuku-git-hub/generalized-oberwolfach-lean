module

public import Oberwolfach.ResidualSplitOrderedPath
public import Mathlib.Combinatorics.SimpleGraph.Finite

@[expose] public section
/-! Splitting an ordered path retains exactly the edges present in the
specified graph. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

def splitPathByGraph (H:SimpleGraph V) (xs:List V):List (List V) :=
  splitOrderedPath (fun x y=>decide (H.Adj x y)) xs

def splitPathEdgeUnion (H:SimpleGraph V) (xs:List V):Finset (Sym2 V) :=
  (splitPathByGraph H xs).toFinset.biUnion prescribedOrderedPathEdges

theorem split_path_edge_union (H:SimpleGraph V):
    ∀ xs:List V,splitPathEdgeUnion H xs =
      (prescribedOrderedPathEdges xs).filter (fun e=>e∈H.edgeFinset) := by
  intro xs
  induction xs with
  | nil => simp [splitPathEdgeUnion,splitPathByGraph,splitOrderedPath,prescribedOrderedPathEdges]
  | cons x xs ih =>
    cases xs with
    | nil => simp [splitPathEdgeUnion,splitPathByGraph,splitOrderedPath,prescribedOrderedPathEdges]
    | cons y ys =>
      obtain ⟨block,blocks,h⟩:=split_ordered_path_head (fun x y=>decide (H.Adj x y)) y ys
      have ih':( (y::block)::blocks).toFinset.biUnion prescribedOrderedPathEdges =
          (prescribedOrderedPathEdges (y::ys)).filter (fun e=>e∈H.edgeFinset) := by
        simpa [splitPathEdgeUnion,splitPathByGraph,h] using ih
      by_cases hxy:H.Adj x y
      · have he:s(x,y)∈H.edgeSet := hxy
        have h' := congrArg (fun E:Finset (Sym2 V)=>insert s(x,y) E) ih'
        simpa [splitPathEdgeUnion,splitPathByGraph,splitOrderedPath,h,hxy,
          prescribedOrderedPathEdges,SimpleGraph.mem_edgeFinset, Finset.filter_insert,he,
          Finset.insert_union] using h'
      · have he:s(x,y)∉H.edgeSet := hxy
        simpa [splitPathEdgeUnion,splitPathByGraph,splitOrderedPath,h,hxy,
          prescribedOrderedPathEdges,SimpleGraph.mem_edgeFinset,Finset.filter_insert,he] using ih'
end Oberwolfach
