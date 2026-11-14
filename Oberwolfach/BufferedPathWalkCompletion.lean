module

public import Oberwolfach.BufferedPathBoundaryCompletion
public import Oberwolfach.BufferedPathEmbeddingEdgeCoverage

@[expose] public section
/-! Complete a factor embedding from the actual buffered-walk witnesses. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem buffered_walk_embeddings_complete_of_endpoint_agreement
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
    ∃f:X↪Y,(∀x (hx:x∈bufferedPathStrictInterior n inner),
        f x=fA ⟨x,buffered_strict_interior_subset_domain n inner hx⟩) ∧
      (∀x (hx:x∉bufferedPathStrictInterior n inner),f x=fC ⟨x,hx⟩) ∧
      (∀x y,G.Adj x y→H.Adj (f x) (f y)) := by
  have hstep:∀i (p:Fin (n i+4)),G.Adj (ext i ⟨p.val,by omega⟩) (ext i ⟨p.val+1,by omega⟩):=by
    intro i p
    obtain ⟨walk,hlen,hsupport⟩:=hwalk i
    exact walk_ofFn_support_adjacent G (n i+4) (ext i) walk hlen hsupport p
  exact buffered_partial_embeddings_complete_of_endpoint_agreement G H hG n ext inner hinner hstep fA fC hA hC hend hdis
end Oberwolfach
