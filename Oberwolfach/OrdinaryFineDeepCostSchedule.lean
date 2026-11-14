module

public import Oberwolfach.MarkedFixedVortexGeometry

@[expose] public section
/-! The fine cover's protected-boundary cost at a level is proportional to
the next actual parent, so the same rate is available at the next step. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
variable {P:SimpleGraph V} {D m:ℕ} {β ε:ℝ}

theorem ordinary_vortex_inner_card_eq_next_parent (Q:Vortex U P D β ε m) (i:ℕ):
    (markedVortexInnerVertices Q i).card=Fintype.card (markedVortexVertexType Q (i+1)):=by
  have h:=congrArg Finset.card (marked_vortex_inner_images Q i).1
  rw [Finset.card_image_of_injective _ (markedVortexVertexEmbedding Q i).injective] at h
  simpa only [Fintype.card_coe] using h

def ordinaryFineDeepCost (Q:Vortex U P D β ε m) (ξ:ℝ) (i:ℕ):ℝ:=
  10*ξ*Fintype.card (markedVortexVertexType Q (i+1))

theorem ordinary_fine_deep_cost_at_level (Q:Vortex U P D β ε m) (ξ:ℝ) (i:ℕ):
    ordinaryFineDeepCost Q ξ i=10*ξ*(markedVortexInnerVertices Q i).card:=by
  rw [ordinaryFineDeepCost,ordinary_vortex_inner_card_eq_next_parent]

theorem ordinary_fine_deep_cost_nonneg (Q:Vortex U P D β ε m) (ξ:ℝ) (hξ:0≤ξ) (i:ℕ):
    0≤ordinaryFineDeepCost Q ξ i:=by
  dsimp [ordinaryFineDeepCost];positivity
end Oberwolfach
