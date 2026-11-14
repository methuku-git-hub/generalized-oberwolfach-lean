module

public import Oberwolfach.FiniteForbiddenRootedFactors

@[expose] public section
/-! The new vertices avoid the entire forbidden set while prescribed roots
inside that set remain available for the covering factor. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem roots_preserved_avoiding_old_vertices {V:Type} [DecidableEq V]
    (A₁ A₂ W T S:Finset V) (hTW:T⊆W) (hTA:T⊆A₁∩A₂)
    (hS:S⊆(A₁∩A₂)\(W\T)) (hST:Disjoint S T):
    T⊆(A₁∩A₂)\(W\T) ∧ Disjoint S W:=by
  constructor
  · intro x hx
    refine Finset.mem_sdiff.mpr ⟨hTA hx,?_⟩
    intro h;exact (Finset.mem_sdiff.mp h).2 hx
  · apply Finset.disjoint_left.mpr
    intro x hxS hxW
    have hnot: x∉W\T:=(Finset.mem_sdiff.mp (hS hxS)).2
    have hxT:x∈T:=by
      by_contra h
      exact hnot (Finset.mem_sdiff.mpr ⟨hxW,h⟩)
    exact (Finset.disjoint_left.mp hST) hxS hxT
end Oberwolfach
