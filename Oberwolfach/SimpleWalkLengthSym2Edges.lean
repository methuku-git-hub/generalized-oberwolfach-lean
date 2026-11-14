module

public import Oberwolfach.SimpleWalkLengthEmbedding
public import Oberwolfach.FiniteSequenceWalkEdgeSet

@[expose] public section
/-! Consecutive indexed vertices of a simple walk determine an edge in its
original symmetric edge list. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem simple_walk_length_embedding_sym2_edge_mem
    {V:Type*} [DecidableEq V] (G:SimpleGraph V) {a b:V}
    (p:G.Walk a b) (hp:p.IsPath) (n:ℕ) (hlen:p.length=n):
    ∀k:Fin n,s(simpleWalkLengthEmbedding G p hp n hlen k.castSucc,
      simpleWalkLengthEmbedding G p hp n hlen k.succ)∈p.edges.toFinset:=by
  classical
  subst n
  intro k
  change s(p.getVert k.val,p.getVert (k.val+1))∈p.edges.toFinset
  apply List.mem_toFinset.mpr
  apply p.mk_mem_edges_iff_exists.mpr
  exact ⟨k.val,k.isLt,rfl⟩
end Oberwolfach
