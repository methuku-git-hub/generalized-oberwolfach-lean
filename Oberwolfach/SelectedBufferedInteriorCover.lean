module

public import Oberwolfach.SelectedBufferedPathRestriction
public import Oberwolfach.DisjointSequenceInteriorCover

@[expose] public section
/-! Restricting to final intervals preserves containment of strict path
interiors in the common reserved target set. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem buffered_selected_strict_interior_subset
    {X I:Type*} [Fintype I] [DecidableEq I] [DecidableEq X]
    (S:Finset I) (n:I→ℕ) (inner:∀i,Fin (n i+1)↪X) :
    bufferedPathStrictInterior (bufferedSelectedLengths S n) (bufferedSelectedPaths S n inner) ⊆
      bufferedPathStrictInterior n inner := by
  classical
  intro x hx
  rcases Finset.mem_biUnion.mp hx with ⟨i,_,hi⟩
  rcases Finset.mem_image.mp hi with ⟨p,hp,rfl⟩
  exact Finset.mem_biUnion.mpr ⟨i.val,Finset.mem_univ _,Finset.mem_image.mpr ⟨p,hp,rfl⟩⟩

theorem selected_buffered_strict_map_inside_reserved
    {X V I:Type*} [DecidableEq X] [DecidableEq V] [Fintype I] [DecidableEq I]
    (S:Finset I) (n:I→ℕ) (inner:∀i,Fin (n i+1)↪X)
    (g:{x // x∈bufferedPathFullDomain n inner}↪V)
    (f:∀i,Fin (n i+1)↪V) (R:Finset V)
    (hmatch:∀i p,g ⟨inner i p,buffered_path_vertex_mem_domain n inner i p⟩=f i p)
    (hdis:∀i j,i≠j→Disjoint (Finset.univ.image (f i)) (Finset.univ.image (f j)))
    (hcover:Finset.univ.biUnion (fun i=>Finset.univ.image (f i)) =
      R ∪ Finset.univ.image (fun i=>f i (Fin.last (n i)))) :
    ∀x (hx:x∈bufferedPathStrictInterior (bufferedSelectedLengths S n) (bufferedSelectedPaths S n inner)),
      restrictBufferedPathMap S n inner g
        ⟨x,buffered_strict_interior_subset_domain (bufferedSelectedLengths S n) (bufferedSelectedPaths S n inner) hx⟩∈R := by
  intro x hx
  exact buffered_strict_map_inside_reserved n inner g f R hmatch hdis hcover x
    (buffered_selected_strict_interior_subset S n inner hx)
end Oberwolfach
