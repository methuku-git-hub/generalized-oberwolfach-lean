module

public import Oberwolfach.OrdinaryUnreservedBufferedWalks
public import Oberwolfach.BufferedMarkerAnchorEmbedding

@[expose] public section
/-! Inducing a source walk and its buffered markers retains their exact
vertices under the subtype projection. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_unreserved_induced_walk_getVert
    {V:Type} (G:SimpleGraph V) (S:Set V) {x y:V} (p:G.Walk x y)
    (hmem:∀z∈p.support,z∈S) (k:ℕ):
    ((p.induce S hmem).getVert k).val=p.getVert k:=by
  have hh:=congrArg (fun q:G.Walk x y=>q.getVert k) (p.map_induce hmem)
  have hmap:=SimpleGraph.Walk.getVert_map (SimpleGraph.Embedding.induce S).toHom (p.induce S hmem) k
  exact hmap.symm.trans hh

theorem ordinary_unreserved_buffered_marker_projection
    {V:Type} (S:Set V) (c d:ℕ)
    (ext:Fin (c*d+5)↪V) (ext':Fin (c*d+5)↪S)
    (h:∀k,(ext' k).val=ext k) (j:Fin (d+1)):
    (bufferedMarker c d ext' j).val=bufferedMarker c d ext j:=by
  exact h _
end Oberwolfach
