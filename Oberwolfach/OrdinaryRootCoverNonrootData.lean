module

public import Oberwolfach.OrdinaryRootCoverData

@[expose] public section
/-! A root cover whose physical degree is also small at every nonroot
vertex or hub, including those inside the enclosing pair. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

structure OrdinaryRootCoverNonrootData (Q F:SimpleGraph V) (H:V→U→Prop)
    (X T:Finset V) (Z W:Finset U) (r:ℕ) (η ell:ℝ)
    extends OrdinaryRootCoverData Q F H X T Z W r η ell where
  nonroot_degree:∀w∉ordinaryInnerVertices T W,((ordinaryPhysicalGraph rim spokes).degree w:ℝ)≤ell
end Oberwolfach
