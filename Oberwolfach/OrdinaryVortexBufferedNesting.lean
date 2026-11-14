module

public import Oberwolfach.VortexExtended

@[expose] public section
/-! A deeper buffer protects all but a finite recent window of vortex levels. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U]

theorem ordinary_vortex_buffered_nesting
    (P:SimpleGraph V) (D m:ℕ) (β ε:ℝ) (Q:Vortex U P D β ε m) (i buffer:ℕ) (hbuffer:2≤buffer):
    let J:=Finset.Icc (i+2-buffer) i;
    (∀j∈J,j < i+1) ∧
    (∀j < i+1,j∉J→Q.extendedVertices (i+1)⊆Q.extendedVertices (j+buffer)) ∧
    (∀j < i+1,j∉J→Q.extendedIndices (i+1)⊆Q.extendedIndices (j+buffer)) ∧
    (∀j∈J,Q.extendedVertices (i+1)⊆Q.extendedVertices (j+1)) ∧
    (∀j∈J,Q.extendedIndices (i+1)⊆Q.extendedIndices (j+1)) :=by
  intro J
  have hJ:∀j∈J,j ≤ i:=by intro j hj;exact (Finset.mem_Icc.mp hj).2
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro j hj;have hh:=hJ j hj;omega
  · intro j hj hjnot
    have hj':¬(i+2-buffer≤j ∧ j ≤ i):=by simpa only [J,Finset.mem_Icc] using hjnot
    exact Q.extendedVertices_subset (by omega)
  · intro j hj hjnot
    have hj':¬(i+2-buffer≤j ∧ j ≤ i):=by simpa only [J,Finset.mem_Icc] using hjnot
    exact Q.extendedIndices_subset (by omega)
  · intro j hj;exact Q.extendedVertices_subset (by have hh:=hJ j hj;omega)
  · intro j hj;exact Q.extendedIndices_subset (by have hh:=hJ j hj;omega)
end Oberwolfach
