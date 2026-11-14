module

public import Oberwolfach.OrdinaryVortexTwoStepCertificateLevelChain
public import Oberwolfach.OrdinaryVortexFineCertificateAtGeneralLoad
public import Oberwolfach.OrdinaryFineDeepCostSchedule

@[expose] public section
/-! The actual per-level cost bounds used by a fine certificate also fit the
uniform protected-history bound with zero additive error. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach

theorem ordinary_vortex_certificate_cost_choices
    (V U:Type) [Fintype V] [Fintype U] [LinearOrder V] [LinearOrder U]
    (P:SimpleGraph V) (D mv:ℕ) (β ε:ℝ) (Q:Vortex U P D β ε mv)
    (rate ξroot:ℝ) (hrate:0≤rate) (hξ:0≤ξroot):
    ∃cost deepCost:ℕ→ℝ,
      (∀i,cost i=rate*Fintype.card (markedVortexVertexType Q i⊕markedVortexHubType Q i)) ∧
      (∀i,deepCost i=10*ξroot*(markedVortexInnerVertices Q i).card) ∧
      (∀i,deepCost i=ordinaryFineDeepCost Q ξroot i) ∧
      (∀i,0≤cost i) ∧ (∀i,0≤deepCost i) ∧
      (∀i,cost i≤4*rate*Fintype.card (markedVortexVertexType Q i⊕markedVortexHubType Q i)+0) :=by
  let cost:ℕ→ℝ:=fun i=>rate*Fintype.card (markedVortexVertexType Q i⊕markedVortexHubType Q i)
  let deepCost:ℕ→ℝ:=fun i=>10*ξroot*(markedVortexInnerVertices Q i).card
  refine ⟨cost,deepCost,by intros; rfl,by intros; rfl,?_,?_,?_,?_⟩
  · intro i; dsimp [deepCost]; exact (ordinary_fine_deep_cost_at_level Q ξroot i).symm
  · intro i; dsimp [cost]; positivity
  · intro i; dsimp [deepCost]; positivity
  · intro i
    have h:0≤rate*(Fintype.card (markedVortexVertexType Q i⊕markedVortexHubType Q i):ℝ):=by positivity
    dsimp [cost]
    nlinarith
end Oberwolfach
