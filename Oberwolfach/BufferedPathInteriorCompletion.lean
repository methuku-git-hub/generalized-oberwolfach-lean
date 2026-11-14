module

public import Oberwolfach.RegularTwoBufferedInteriorNeighbors
public import Oberwolfach.PartialEmbeddingInteriorGlue

@[expose] public section
/-! Strict buffered-path interiors can be reattached to a compatible embedding
of their complement without extra edge checks at the boundary. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def bufferedPathFullDomain {X I:Type*} [Fintype I] [DecidableEq X]
    (n:I→ℕ) (inner:∀i,Fin (n i+1)↪X) : Finset X :=
  Finset.univ.biUnion (fun i=>Finset.univ.image (inner i))

def bufferedPathStrictInterior {X I:Type*} [Fintype I] [DecidableEq X]
    (n:I→ℕ) (inner:∀i,Fin (n i+1)↪X) : Finset X :=
  Finset.univ.biUnion (fun i=>(Finset.univ.filter (fun p:Fin (n i+1)=>0<p.val ∧ p.val<n i)).image (inner i))

theorem buffered_strict_interior_subset_domain
    {X I:Type*} [Fintype I] [DecidableEq X]
    (n:I→ℕ) (inner:∀i,Fin (n i+1)↪X) :
    bufferedPathStrictInterior n inner ⊆ bufferedPathFullDomain n inner := by
  classical
  intro x hx
  rcases Finset.mem_biUnion.mp hx with ⟨i,_,hxi⟩
  rcases Finset.mem_image.mp hxi with ⟨p,_,rfl⟩
  exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,Finset.mem_image.mpr ⟨p,Finset.mem_univ _,rfl⟩⟩

theorem buffered_strict_interior_neighborhood
    {X I:Type*} [Fintype X] [DecidableEq X] [Fintype I]
    (G:SimpleGraph X) (hG:G.IsRegularOfDegree 2) (n:I→ℕ)
    (ext:∀i,Fin (n i+5)↪X) (inner:∀i,Fin (n i+1)↪X)
    (hinner:∀i p,inner i p=ext i ⟨p.val+2,by omega⟩)
    (hstep:∀i (p:Fin (n i+4)),G.Adj (ext i ⟨p.val,by omega⟩) (ext i ⟨p.val+1,by omega⟩)) :
    ∀x,x∈bufferedPathStrictInterior n inner→∀y,G.Adj x y→y∈bufferedPathFullDomain n inner := by
  classical
  intro x hx y hxy
  rcases Finset.mem_biUnion.mp hx with ⟨i,_,hxi⟩
  rcases Finset.mem_image.mp hxi with ⟨p,hp,rfl⟩
  have hp' := (Finset.mem_filter.mp hp).2
  obtain ⟨q,hq,_⟩:=regular_two_buffered_strict_inner_neighbor G hG (n i) (ext i) (inner i)
    (hinner i) (hstep i) p hp'.1 hp'.2 y hxy
  rw [hq]
  exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,Finset.mem_image.mpr ⟨q,Finset.mem_univ _,rfl⟩⟩

theorem buffered_partial_embeddings_complete
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
    (hbound:∀x (hx:x∈bufferedPathFullDomain n inner) (hxD:x∉bufferedPathStrictInterior n inner),
      fA ⟨x,hx⟩=fC ⟨x,hxD⟩)
    (hdis:∀x (hx:x∈bufferedPathStrictInterior n inner) y (hy:y∉bufferedPathStrictInterior n inner),
      fA ⟨x,buffered_strict_interior_subset_domain n inner hx⟩≠fC ⟨y,hy⟩) :
    ∃f:X↪Y,(∀x (hx:x∈bufferedPathStrictInterior n inner),
        f x=fA ⟨x,buffered_strict_interior_subset_domain n inner hx⟩) ∧
      (∀x (hx:x∉bufferedPathStrictInterior n inner),f x=fC ⟨x,hx⟩) ∧
      (∀x y,G.Adj x y→H.Adj (f x) (f y)) := by
  exact partial_embeddings_glue_across_interior G H (bufferedPathFullDomain n inner)
    (bufferedPathStrictInterior n inner) (buffered_strict_interior_subset_domain n inner)
    fA fC hA hC hbound hdis (buffered_strict_interior_neighborhood G hG n ext inner hinner hstep)
end Oberwolfach
