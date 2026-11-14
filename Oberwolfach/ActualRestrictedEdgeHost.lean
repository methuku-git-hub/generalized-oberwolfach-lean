module

public import Oberwolfach.ActualRestrictedEdgeCover
public import Oberwolfach.ResidualActualLateContinuation

@[expose] public section
/-! Put the complement embedding into the physical host using the same old
packing and the directed residual embedding. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_restricted_edge_image_in_host
    {X V K J:Type} [Fintype X] [Fintype V] [DecidableEq X] [DecidableEq V] [DecidableEq K] [DecidableEq J]
    (F:SimpleGraph X) (hF:F.IsRegularOfDegree 2) (H:SimpleGraph V)
    (a:ActualResidualData (K:=K) (J:=J) F)
    (hCycle:a.t.biUnion (fun j=>(a.C j).support.toFinset)⊆a.Cembed)
    (D:Finset X) (finalEdges:Finset (Sym2 X))
    (fC:{x // x∉D}↪V) (ψ:X→V) (Φ:{x // x∈a.remaining}→V)
    (hold:∀(x:{x // x∉D}),x.val∈a.oldDomain→fC x=ψ x.val)
    (hnew:∀(x:{x // x∉D}) (hx:x.val∈a.remaining),fC x=Φ ⟨x.val,hx⟩)
    (Pack:Finset (Sym2 V)) (hOld:(a.deletedEdges\finalEdges).image (Sym2.map ψ)⊆Pack)
    (hPack:Pack⊆H.edgeFinset)
    (Dsrc:X→X→Prop) (hOrient:∀x y,F.Adj x y→Dsrc x y ∨ Dsrc y x)
    (hArc:∀x y:{x // x∈a.remaining},Dsrc x.1 y.1→a.graph.Adj x.1 y.1→H.Adj (Φ x) (Φ y)):
    (((F.deleteEdges (↑finalEdges:Set (Sym2 X))).induce {x | x∉D}).edgeFinset).image (Sym2.map fC)⊆H.edgeFinset :=by
  intro e he
  have hcover:=actual_restricted_edge_image_cover F hF a hCycle D finalEdges fC ψ Φ hold hnew he
  rcases Finset.mem_union.mp hcover with hOld'|hNew
  · exact hPack (hOld hOld')
  · obtain ⟨e',he',rfl⟩:=Finset.mem_image.mp hNew
    induction e' using Sym2.ind with
    | _ x y =>
      have hadj:a.graph.Adj x.1 y.1:=SimpleGraph.mem_edgeFinset.mp he'
      have hFadj:F.Adj x.1 y.1:=(a.graph_facts hF).1 hadj
      rcases hOrient _ _ hFadj with hxy|hyx
      · exact SimpleGraph.mem_edgeFinset.mpr (hArc x y hxy hadj)
      · exact SimpleGraph.mem_edgeFinset.mpr ((hArc y x hyx hadj.symm).symm)
end Oberwolfach
