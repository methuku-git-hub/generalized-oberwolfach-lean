module

public import Oberwolfach.BufferedPathInteriorCompletion

@[expose] public section
/-! Only the endpoints of the reserved paths belong to the shared boundary. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem buffered_path_vertex_mem_domain
    {X I:Type*} [Fintype I] [DecidableEq X]
    (n:I→ℕ) (inner:∀i,Fin (n i+1)↪X) (i:I) (p:Fin (n i+1)) :
    inner i p∈bufferedPathFullDomain n inner := by
  classical
  exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,Finset.mem_image.mpr ⟨p,Finset.mem_univ _,rfl⟩⟩

theorem buffered_path_boundary_is_endpoint
    {X I:Type*} [Fintype I] [DecidableEq X]
    (n:I→ℕ) (inner:∀i,Fin (n i+1)↪X) (x:X)
    (hx:x∈bufferedPathFullDomain n inner) (hxD:x∉bufferedPathStrictInterior n inner) :
    ∃i:I, x=inner i 0 ∨ x=inner i (Fin.last (n i)) := by
  classical
  rcases Finset.mem_biUnion.mp hx with ⟨i,_,hxi⟩
  rcases Finset.mem_image.mp hxi with ⟨p,_,rfl⟩
  have hpnot:¬(0<p.val ∧ p.val<n i):=by
    intro hp
    apply hxD
    exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,
      Finset.mem_image.mpr ⟨p,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hp⟩,rfl⟩⟩
  have hends:p.val=0 ∨ p.val=n i:=by have := p.isLt;omega
  rcases hends with hzero|hlast
  · refine ⟨i,Or.inl ?_⟩
    congr 1
    exact Fin.ext hzero
  · refine ⟨i,Or.inr ?_⟩
    congr 1
    exact Fin.ext hlast

theorem buffered_partial_embeddings_complete_of_endpoint_agreement
    {X Y I:Type*} [Fintype X] [DecidableEq X] [Fintype I]
    (G:SimpleGraph X) (H:SimpleGraph Y) (hG:G.IsRegularOfDegree 2) (n:I→ℕ)
    (ext:∀i,Fin (n i+5)↪X) (inner:∀i,Fin (n i+1)↪X)
    (hinner:∀i p,inner i p=ext i ⟨p.val+2,by omega⟩)
    (hstep:∀i (p:Fin (n i+4)),G.Adj (ext i ⟨p.val,by omega⟩) (ext i ⟨p.val+1,by omega⟩))
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
    ∃f:X↪Y,(∀x (hx:x∈bufferedPathStrictInterior n inner),
        f x=fA ⟨x,buffered_strict_interior_subset_domain n inner hx⟩) ∧
      (∀x (hx:x∉bufferedPathStrictInterior n inner),f x=fC ⟨x,hx⟩) ∧
      (∀x y,G.Adj x y→H.Adj (f x) (f y)) := by
  apply buffered_partial_embeddings_complete G H hG n ext inner hinner hstep fA fC hA hC ?_ hdis
  intro x hx hxD
  obtain ⟨i,hi|hi⟩:=buffered_path_boundary_is_endpoint n inner x hx hxD
  · subst x
    exact hend i 0 (Or.inl rfl) hxD
  · subst x
    exact hend i (Fin.last (n i)) (Or.inr rfl) hxD
end Oberwolfach
