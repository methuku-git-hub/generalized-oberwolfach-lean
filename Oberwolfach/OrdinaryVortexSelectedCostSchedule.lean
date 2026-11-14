module

public import Oberwolfach.OrdinaryFineDeepCostSchedule

@[expose] public section
/-! The certificate's selected global cost and its exact fine-cover deep
cost give the schedules used by the protected level chain. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
variable {P:SimpleGraph V} {D mv:ℕ} {β ε:ℝ} (Q:Vortex U P D β ε mv)

def ordinaryVortexSelectedCost (rate:ℝ) (i:ℕ):ℝ:=
  rate*Fintype.card (markedVortexVertexType Q i⊕markedVortexHubType Q i)

theorem ordinary_vortex_selected_cost_schedule
    (rate ξ C:ℝ) (hrate:0≤rate) (hξ:0≤ξ) (hC:0≤C):
    (∀i,0≤ordinaryVortexSelectedCost Q rate i) ∧
    (∀i,0≤ordinaryFineDeepCost Q ξ i) ∧
    (∀i,ordinaryVortexSelectedCost Q rate i≤
      4*rate*Fintype.card (markedVortexVertexType Q i⊕markedVortexHubType Q i)+C) ∧
    (∀i,ordinaryFineDeepCost Q ξ i=10*ξ*(markedVortexInnerVertices Q i).card):=by
  refine ⟨?_,?_,?_,?_⟩
  · intro i;dsimp [ordinaryVortexSelectedCost];positivity
  · intro i;exact ordinary_fine_deep_cost_nonneg Q ξ hξ i
  · intro i
    have hh:0≤rate*Fintype.card (markedVortexVertexType Q i⊕markedVortexHubType Q i):=by positivity
    dsimp [ordinaryVortexSelectedCost]
    nlinarith only [hh,hC]
  · intro i;exact ordinary_fine_deep_cost_at_level Q ξ i
end Oberwolfach
