module

public import Oberwolfach.ResidualSubtypePositionBudget

@[expose] public section
/-! Independence and prescribed images pass to the surviving vertex type. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W:Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

theorem residual_subtype_set_independent (R A:Finset V) (Q:SimpleGraph V)
    (hA:∀x∈A,∀y∈A,¬Q.Adj x y)
    (qs:List (PrescribedSourcePiece {x // x∈R}))
    (hgraph:prescribedDependentGraph (fun _ : Unit=>qs) ()=Q.induce (↑R:Set V)):
    ∀x∈residualSubtypeSet R A,∀y∈residualSubtypeSet R A,
      ¬(prescribedDependentGraph (fun _ : Unit=>qs) ()).Adj x y := by
  intro x hx y hy
  have hxA:x.1∈A:=(Finset.mem_filter.mp hx).2
  have hyA:y.1∈A:=(Finset.mem_filter.mp hy).2
  rw [hgraph]
  exact hA x.1 hxA y.1 hyA

theorem residual_subtype_image (R A:Finset V) (hAR:A⊆R) (f:V→W):
    (residualSubtypeSet R A).image (fun x=>f x.1)=A.image f := by
  calc
    (residualSubtypeSet R A).image (fun x=>f x.1) =
        ((residualSubtypeSet R A).image Subtype.val).image f := by rw [Finset.image_image];rfl
    _ = A.image f := by rw [residual_subtype_set_image R A hAR]
end Oberwolfach
