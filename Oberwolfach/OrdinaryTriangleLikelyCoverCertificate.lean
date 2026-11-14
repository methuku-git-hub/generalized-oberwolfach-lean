module

public import Oberwolfach.OrdinaryTriangleLikelyEventCoverdown

@[expose] public section
/-! Package the local probability estimate and its actual cover-down event. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

def OrdinaryTriangleLikelyCoverCertificate (Q F:SimpleGraph V) (H:V→U→Prop)
    (X T:Finset V) (Z W:Finset U) (cost deepCost:ℝ):Prop :=
  ∃(μ:FiniteLaw (Sym2 (V⊕U)→Bool)) (E:(Sym2 (V⊕U)→Bool)→Prop) (loss localCost rate:ℝ),
    16≤Fintype.card V ∧ loss≤1/4 ∧
    (1-(loss+2/(Fintype.card (V⊕U):ℝ))-
      (1/(Fintype.card V:ℝ)+1/(Fintype.card (V⊕U):ℝ))≤μ.probability E) ∧
    (∀σ,E σ→OrdinaryProtectedHostCoverDownResult Q F H X T Z W 3 localCost localCost) ∧
    localCost≤rate*Fintype.card (V⊕U) ∧ rate*Fintype.card (V⊕U)≤cost ∧
    rate*Fintype.card (V⊕U)≤deepCost

theorem ordinary_triangle_likely_certificate_coverdown
    (Q F:SimpleGraph V) (H:V→U→Prop) (X T:Finset V) (Z W:Finset U) (cost deepCost:ℝ)
    (h:OrdinaryTriangleLikelyCoverCertificate Q F H X T Z W cost deepCost):
    OrdinaryProtectedHostCoverDownResult Q F H X T Z W 3 cost deepCost :=by
  obtain ⟨μ,E,loss,localCost,rate,hn,hloss,hprob,hevent,hlocal,hcost,hdeep⟩:=h
  have hh:=ordinary_triangle_coverdown_of_likely_event Q F H X T Z W μ E loss localCost rate
    hn hloss hprob hevent hlocal
  exact ordinary_protected_cover_down_cost_mono Q F H X T Z W 3
    (rate*Fintype.card (V⊕U)) (rate*Fintype.card (V⊕U)) cost deepCost hcost hdeep hh
end Oberwolfach
