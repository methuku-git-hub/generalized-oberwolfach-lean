module

public import Oberwolfach.SimpleWalkLengthEmbedding

@[expose] public section
/-! Reindexing a simple walk preserves its getVert coordinates. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem simple_walk_length_embedding_getVert {V:Type} (G:SimpleGraph V) {a b:V}
    (p:G.Walk a b) (hp:p.IsPath) (n:ℕ) (hlen:p.length=n) (k:Fin (n+1)):
    simpleWalkLengthEmbedding G p hp n hlen k=p.getVert k.val:=by
  subst n
  rfl
end Oberwolfach
