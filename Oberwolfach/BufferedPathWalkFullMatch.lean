module

public import Oberwolfach.BufferedPathWalkCompletion

@[expose] public section
/-! The completed embedding preserves both the reserved path map and the
complement map, including their common endpoints. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem buffered_walk_embeddings_complete_preserving_both_maps
    {X Y I:Type*} [Fintype X] [DecidableEq X] [Fintype I]
    (G:SimpleGraph X) (H:SimpleGraph Y) (hG:G.IsRegularOfDegree 2) (n:I→ℕ)
    (ext:∀i,Fin (n i+5)↪X) (inner:∀i,Fin (n i+1)↪X)
    (hinner:∀i p,inner i p=ext i ⟨p.val+2,by omega⟩)
    (hwalk:∀i,∃p:G.Walk (ext i ⟨0,by omega⟩) (ext i ⟨n i+4,by omega⟩),
      p.length=n i+4 ∧ p.support=List.ofFn (ext i))
    (fA:{x // x∈bufferedPathFullDomain n inner}↪Y)
    (fC:{x // x∉bufferedPathStrictInterior n inner}↪Y)
    (hA:∀x y (hx:x∈bufferedPathFullDomain n inner) (hy:y∈bufferedPathFullDomain n inner),
      G.Adj x y→H.Adj (fA ⟨x,hx⟩) (fA ⟨y,hy⟩))
    (hC:∀x y (hx:x∉bufferedPathStrictInterior n inner) (hy:y∉bufferedPathStrictInterior n inner),
      G.Adj x y→H.Adj (fC ⟨x,hx⟩) (fC ⟨y,hy⟩))
    (hend:∀i (p:Fin (n i+1)),(p=0 ∨ p=Fin.last (n i))→
      ∀ hpD:inner i p∉bufferedPathStrictInterior n inner,
      fA ⟨inner i p,buffered_path_vertex_mem_domain n inner i p⟩=fC ⟨inner i p,hpD⟩)
    (hdis:∀x (hx:x∈bufferedPathStrictInterior n inner) y (hy:y∉bufferedPathStrictInterior n inner),
      fA ⟨x,buffered_strict_interior_subset_domain n inner hx⟩≠fC ⟨y,hy⟩) :
    ∃f:X↪Y,(∀x (hx:x∈bufferedPathFullDomain n inner),f x=fA ⟨x,hx⟩) ∧
      (∀x (hx:x∉bufferedPathStrictInterior n inner),f x=fC ⟨x,hx⟩) ∧
      (∀x y,G.Adj x y→H.Adj (f x) (f y)) := by
  classical
  obtain ⟨f,hD,hC,hgraph⟩:=buffered_walk_embeddings_complete_of_endpoint_agreement
    G H hG n ext inner hinner hwalk fA fC hA hC hend hdis
  have hbound:∀x (hx:x∈bufferedPathFullDomain n inner) (hxD:x∉bufferedPathStrictInterior n inner),
      fA ⟨x,hx⟩=fC ⟨x,hxD⟩:=by
    intro x hx hxD
    obtain ⟨i,hi|hi⟩:=buffered_path_boundary_is_endpoint n inner x hx hxD
    · subst x
      exact hend i 0 (Or.inl rfl) hxD
    · subst x
      exact hend i (Fin.last (n i)) (Or.inr rfl) hxD
  refine ⟨f,?_,hC,hgraph⟩
  intro x hx
  by_cases hxD:x∈bufferedPathStrictInterior n inner
  · exact hD x hxD
  · rw [hC x hxD]
    exact (hbound x hx hxD).symm
end Oberwolfach
