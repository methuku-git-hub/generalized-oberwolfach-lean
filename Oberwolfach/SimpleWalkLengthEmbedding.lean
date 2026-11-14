module

public import Oberwolfach.SimpleWalkVertexSequence

@[expose] public section
/-! Reindex a simple walk by any equal natural-number length. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

def simpleWalkLengthEmbedding {V:Type*} (G:SimpleGraph V) {a b:V}
    (p:G.Walk a b) (hp:p.IsPath) (n:ℕ) (hlen:p.length=n):Fin (n+1)↪V:=
  (finCongr (congrArg (fun x:ℕ=>x+1) hlen.symm)).toEmbedding.trans (simpleWalkVertexEmbedding G p hp)

theorem simple_walk_length_embedding_adjacent {V:Type*} (G:SimpleGraph V) {a b:V}
    (p:G.Walk a b) (hp:p.IsPath) (n:ℕ) (hlen:p.length=n):
    ∀k:Fin n,G.Adj (simpleWalkLengthEmbedding G p hp n hlen k.castSucc)
      (simpleWalkLengthEmbedding G p hp n hlen k.succ):=by
  subst n
  simpa [simpleWalkLengthEmbedding] using simple_walk_vertex_embedding_adjacent G p hp

theorem simple_walk_length_embedding_support {V:Type*} [DecidableEq V]
    (G:SimpleGraph V) {a b:V} (p:G.Walk a b) (hp:p.IsPath) (n:ℕ) (hlen:p.length=n):
    Finset.univ.image (simpleWalkLengthEmbedding G p hp n hlen)=p.support.toFinset:=by
  subst n
  simpa [simpleWalkLengthEmbedding] using simple_walk_vertex_embedding_support G p hp
end Oberwolfach
