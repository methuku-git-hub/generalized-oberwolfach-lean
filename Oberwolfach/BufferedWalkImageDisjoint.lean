module

public import Oberwolfach.BufferedActualResidualData

@[expose] public section
/-! Disjoint source-walk supports give disjoint image sets for the
corresponding enumerations, as required by buffered embedding. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem buffered_walk_images_disjoint
    {X I:Type} [Fintype X] [DecidableEq X]
    (G:SimpleGraph X) (L:ℕ) (ext:∀i:I,Fin (L+5)↪X)
    (P:∀i,G.Walk (ext i 0) (ext i (Fin.last (L+4))))
    (hsupp:∀i,(P i).support=List.ofFn (ext i))
    (hdis:∀i j,i≠j→Disjoint (P i).support.toFinset (P j).support.toFinset):
    ∀i j,i≠j→Disjoint (Finset.univ.image (ext i)) (Finset.univ.image (ext j)):=by
  intro i j hij
  have hi:=buffered_walk_support_finset G L (ext i) (P i) (hsupp i)
  have hj:=buffered_walk_support_finset G L (ext j) (P j) (hsupp j)
  rw [←hi,←hj]
  exact hdis i j hij
end Oberwolfach
