module

public import Oberwolfach.ComplementImageDecompositionBounds
public import Oberwolfach.BufferedPathBoundaryCompletion

@[expose] public section
/-! The only excluded path-domain vertices in the complement are endpoints. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {X V I:Type} [Fintype X] [DecidableEq X] [DecidableEq V] [Fintype I]

theorem buffered_complement_decomposition_bounds
    (n:I→ℕ) (inner:∀i,Fin (n i+1)↪X) (old remaining:Finset X) (Y End:Finset V)
    (ψ:X→V) (Φ:{x // x∈remaining}→V)
    (f:{x // x∉bufferedPathStrictInterior n inner}→V)
    (hcover:old∪remaining=Finset.univ)
    (hremain:Disjoint (bufferedPathStrictInterior n inner) remaining)
    (hold:∀x:{x // x∉bufferedPathStrictInterior n inner},x.val∈old→f x=ψ x.val)
    (hnew:∀x:{x // x∈remaining},∀hx:x.val∉bufferedPathStrictInterior n inner,f ⟨x.val,hx⟩=Φ x)
    (hstart:∀i (hx:inner i 0∉bufferedPathStrictInterior n inner),f ⟨inner i 0,hx⟩∈Y)
    (hend:∀i (hx:inner i (Fin.last (n i))∉bufferedPathStrictInterior n inner),f ⟨inner i (Fin.last (n i)),hx⟩∈End):
    let Outside:=outsideBufferedPathImage n inner f
    let Old:Finset V:=(old\bufferedPathStrictInterior n inner).image ψ
    let New:Finset V:=Finset.univ.image Φ;
    Outside⊆Old∪New ∧ Old⊆Y∪(Outside∪End) ∧ New⊆Y∪(Outside∪End):=by
  intro Outside Old New
  apply complement_image_decomposition_bounds (bufferedPathStrictInterior n inner) (bufferedPathFullDomain n inner)
    old remaining Y End ψ Φ f
    (by intro x hx; exact buffered_strict_interior_subset_domain n inner hx) hcover hremain hold hnew
  intro x hx
  rcases x with ⟨x,hnot⟩
  obtain ⟨i,hi|hi⟩:=buffered_path_boundary_is_endpoint n inner x hx hnot
  · subst x
    exact Finset.mem_union_left _ (hstart i _)
  · subst x
    exact Finset.mem_union_right _ (hend i _)
end Oberwolfach
