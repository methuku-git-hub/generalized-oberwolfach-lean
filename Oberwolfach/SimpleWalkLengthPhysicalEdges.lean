module

public import Oberwolfach.SimpleWalkLengthEmbedding
public import Oberwolfach.FiniteSequenceWalkEdgeSet

@[expose] public section
/-! Consecutive vertices in the reindexed simple-walk embedding use one of
the walk's original physical edges. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem simple_walk_length_embedding_edge_mem
    {V:Type*} [DecidableEq V] (G:SimpleGraph V) {a b:V}
    (p:G.Walk a b) (hp:p.IsPath) (n:ℕ) (hlen:p.length=n):
    ∀k:Fin n,{simpleWalkLengthEmbedding G p hp n hlen k.castSucc,
      simpleWalkLengthEmbedding G p hp n hlen k.succ}∈walkPhysicalEdges p:=by
  classical
  subst n
  intro k
  have he:s(p.getVert k.val,p.getVert (k.val+1))∈p.edges:=by
    apply p.mk_mem_edges_iff_exists.mpr
    exact ⟨k.val,k.isLt,rfl⟩
  have he':Sym2.toFinset (s(p.getVert k.val,p.getVert (k.val+1)))∈walkPhysicalEdges p:=by
    apply List.mem_toFinset.mpr
    exact List.mem_map.mpr ⟨_,he,rfl⟩
  change {p.getVert k.val,p.getVert (k.val+1)}∈walkPhysicalEdges p
  simpa only [Sym2.toFinset_mk_eq] using he'
end Oberwolfach
