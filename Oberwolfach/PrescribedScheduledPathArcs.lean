module

public import Oberwolfach.PrescribedPathDirectedEdges

@[expose] public section
/-! A path schedule preserves the distinction between initially prescribed
arcs and newly embedded directed arcs. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {X V:Type} [DecidableEq X]

theorem prescribed_scheduled_path_arcs (A:Finset X) (xs:List X)
    (f:X→V) (D:V→V→Prop)
    (hchains:∀ seg∈prescribedPathSegments A none [] xs,seg.free≠[]→
      List.IsChain D ((prescribedPathSegmentVertices seg).map f)):
    ∀ e∈prescribedDirectedPathEdges xs,(e.1∈A ∧ e.2∈A) ∨ D (f e.1) (f e.2) := by
  intro e he
  have he':e∈prescribedSegmentDirectedEdges (prescribedPathSegments A none [] xs):=by
    have hh:=prescribed_path_segments_directed_union A xs none []
    simpa using hh.symm ▸ he
  obtain ⟨seg,hseg,heSeg⟩:=Finset.mem_biUnion.mp he'
  have hseg':seg∈prescribedPathSegments A none [] xs:=List.mem_toFinset.mp hseg
  by_cases hempty:seg.free=[]
  · left
    have hb:=prescribed_path_segment_boundaries A xs none [] (by simp) seg hseg'
    exact prescribed_empty_segment_directed_edges A seg hempty hb.1 hb.2 e heSeg
  · right
    have hc:=hchains seg hseg' hempty
    have hc':List.IsChain (fun x y=>D (f x) (f y)) (prescribedPathSegmentVertices seg):=
      (List.isChain_map f).mp hc
    exact ((prescribed_directed_edges_chain (fun x y=>D (f x) (f y)) _).mp hc') e heSeg
end Oberwolfach
