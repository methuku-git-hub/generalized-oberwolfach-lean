module

public import Oberwolfach.OrdinaryWheelLikelyEventSeparateCosts

@[expose] public section
/-! A likely wheel cover carries independent ordinary and deep costs. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

def OrdinaryWheelLikelySeparateCostsCertificate (Q F:SimpleGraph V) (H:V→U→Prop)
    (X T:Finset V) (Z W:Finset U) (r:ℕ) (cost deepCost:ℝ):Prop :=
  ∃(μ:FiniteLaw (Sym2 (V⊕U)→Bool)) (E:(Sym2 (V⊕U)→Bool)→Prop) (loss localCost localDeep:ℝ),
    16≤Fintype.card V ∧ loss≤1/4 ∧
    (1-(loss+2/(Fintype.card (V⊕U):ℝ))-
      (1/(Fintype.card V:ℝ)+1/(Fintype.card (V⊕U):ℝ))≤μ.probability E) ∧
    (∀σ,E σ→OrdinaryProtectedHostCoverDownResult Q F H X T Z W r localCost localDeep) ∧
    localCost≤cost ∧ localDeep≤deepCost

theorem ordinary_wheel_likely_separate_costs_certificate_coverdown
    (Q F:SimpleGraph V) (H:V→U→Prop) (X T:Finset V) (Z W:Finset U) (r:ℕ) (cost deepCost:ℝ)
    (h:OrdinaryWheelLikelySeparateCostsCertificate Q F H X T Z W r cost deepCost):
    OrdinaryProtectedHostCoverDownResult Q F H X T Z W r cost deepCost :=by
  obtain ⟨μ,E,loss,localCost,localDeep,hn,hloss,hprob,hevent,hcost,hdeep⟩:=h
  exact ordinary_wheel_coverdown_of_likely_event_separate_costs Q F H X T Z W r μ E
    loss localCost localDeep cost deepCost hn hloss hprob hevent hcost hdeep
end Oberwolfach
