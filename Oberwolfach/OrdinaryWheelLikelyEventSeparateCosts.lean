module

public import Oberwolfach.OrdinaryProtectedCoverDownCostMono
public import Oberwolfach.FiniteLawPositiveEventWitness

@[expose] public section
/-! A likely cover-down event may carry a sharper deep-boundary cost than
its total cost; the witness step preserves the two bounds independently. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_wheel_coverdown_of_likely_event_separate_costs
    (Q F:SimpleGraph V) (H:V→U→Prop) (X T:Finset V) (Z W:Finset U) (r:ℕ)
    (μ:FiniteLaw (Sym2 (V⊕U)→Bool)) (E:(Sym2 (V⊕U)→Bool)→Prop)
    (loss localCost localDeep cost deepCost:ℝ) (hn:16≤Fintype.card V) (hloss:loss≤1/4)
    (hprob:1-(loss+2/(Fintype.card (V⊕U):ℝ))-
      (1/(Fintype.card V:ℝ)+1/(Fintype.card (V⊕U):ℝ))≤μ.probability E)
    (hevent:∀σ,E σ→OrdinaryProtectedHostCoverDownResult Q F H X T Z W r localCost localDeep)
    (hcost:localCost≤cost) (hdeep:localDeep≤deepCost):
    OrdinaryProtectedHostCoverDownResult Q F H X T Z W r cost deepCost :=by
  have hnV:(16:ℝ)≤Fintype.card V:=by exact_mod_cast hn
  have hWV:Fintype.card V≤Fintype.card (V⊕U):=Fintype.card_le_of_injective Sum.inl Sum.inl_injective
  have hnW:(16:ℝ)≤Fintype.card (V⊕U):=by exact_mod_cast hn.trans hWV
  have h2:2/(Fintype.card (V⊕U):ℝ)≤2/16:=by gcongr
  have h1:1/(Fintype.card V:ℝ)≤1/16:=by gcongr
  have h1W:1/(Fintype.card (V⊕U):ℝ)≤1/16:=by gcongr
  have hpos:0<μ.probability E:=by linarith
  obtain ⟨σ,_,hσ⟩:=finiteLaw_positive_mass_witness_of_event μ E hpos
  exact ordinary_protected_cover_down_cost_mono Q F H X T Z W r localCost localDeep cost deepCost hcost hdeep (hevent σ hσ)
end Oberwolfach
