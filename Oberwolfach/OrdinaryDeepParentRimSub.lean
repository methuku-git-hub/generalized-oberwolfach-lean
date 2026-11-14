module

public import Oberwolfach.OrdinaryDeepParentIngredients

@[expose] public section
/-! The physical endpoint inclusion entails the ordinary rim inclusion. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 800000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

theorem ordinary_deep_parent_rim_sub
    (P Q F:SimpleGraph V) (H:V→U→Prop) (A:Finset V) (Z:Finset U)
    (π:Equiv.Perm V) (d:ℕ) (j:Color) (s:U→Color→ℝ) (weight:V→Sym2 (V⊕U)→ℝ)
    (γ κ b B εf η κe p pR pH density tR tH L Ledit βe βh δ ε t K:ℝ)
    (σ:RawWheelOutcome V U Γ Color)
    (inputs:OrdinaryDeepParentIngredients P Q F H A Z π d j s weight γ κ b B εf η κe p pR pH density
      tR tH L Ledit βe βh δ ε t K σ) : Q≤P\F := by
  intro x y hxy
  have h := inputs.geom.rim_sub (show (ordinaryPhysicalGraph (U:=U) Q (fun _ _=>False)).Adj
    (Sum.inl x) (Sum.inl y) from hxy)
  simpa only [SimpleGraph.sdiff_adj, ordinaryPhysicalGraph] using h
end Oberwolfach
