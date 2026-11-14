module

public import Oberwolfach.SimpleWalkLengthEmbedding

@[expose] public section
/-! The reindexed walk preserves its start and finish vertices. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem simple_walk_length_embedding_endpoints {V:Type*} (G:SimpleGraph V) {a b:V}
    (p:G.Walk a b) (hp:p.IsPath) (n:ℕ) (hlen:p.length=n) :
    simpleWalkLengthEmbedding G p hp n hlen 0=a ∧
      simpleWalkLengthEmbedding G p hp n hlen (Fin.last n)=b := by
  subst n
  constructor
  · change p.getVert 0=a
    exact p.getVert_zero
  · change p.getVert p.length=b
    exact p.getVert_length
end Oberwolfach
