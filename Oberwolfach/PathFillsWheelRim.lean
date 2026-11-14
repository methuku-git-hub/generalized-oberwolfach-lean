module

public import Oberwolfach.SimpleWalkVertexSequence

@[expose] public section
/-! A simple path of length one less than the rim size, whose vertices lie
on an injective rim, covers the entire rim. -/
set_option autoImplicit false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem simple_path_fills_wheel_rim
    {V:Type} [DecidableEq V] (G:SimpleGraph V) {a b:V}
    (p:G.Walk a b) (hp:p.IsPath) (n:ℕ) (hlen:p.length=n)
    (rim:Fin (n+1)↪V)
    (hinner:∀k,k<p.length→∃j:Fin (n+1),p.getVert k=rim j)
    (hend:∃j:Fin (n+1),b=rim j):
    p.support.toFinset=Finset.univ.image rim:=by
  have hsub:p.support.toFinset⊆Finset.univ.image rim:=by
    rw [←simple_walk_vertex_embedding_support G p hp]
    intro x hx
    obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hx
    by_cases hi:i.val<p.length
    · obtain ⟨j,hj⟩:=hinner i.val hi
      exact Finset.mem_image.mpr ⟨j,Finset.mem_univ _,hj.symm⟩
    · have heq:i.val=p.length:=by have hi':=i.isLt;omega
      obtain ⟨j,hj⟩:=hend
      apply Finset.mem_image.mpr
      refine ⟨j,Finset.mem_univ _,?_⟩
      change rim j=p.getVert i.val
      rw [heq,SimpleGraph.Walk.getVert_length]
      exact hj.symm
  apply Finset.eq_of_subset_of_card_le hsub
  rw [←simple_walk_vertex_embedding_support G p hp]
  simp only [Finset.card_image_of_injective _ (simpleWalkVertexEmbedding G p hp).injective,
    Finset.card_image_of_injective _ rim.injective,Finset.card_univ,Fintype.card_fin,hlen]
  exact le_rfl
end Oberwolfach
