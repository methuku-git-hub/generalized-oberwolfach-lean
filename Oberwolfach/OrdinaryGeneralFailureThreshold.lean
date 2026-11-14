module

public import Oberwolfach.FiniteLawPositiveEventWitness

@[expose] public section
/-! Explicit large-host bounds make the root-cleanup plus pairing event
    positive when the earlier and reserve losses are each at most a quarter. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_general_failure_threshold {V U:Type} [Fintype V] [Fintype U]
    (e₀ loss:ℝ) (hn:16≤Fintype.card V) (he:e₀≤1/4) (hloss:loss≤1/4):
    (((e₀+loss)+2/(Fintype.card (V⊕U):ℝ))+1/(Fintype.card (V⊕U):ℝ))+
      1/(Fintype.card V:ℝ)<1 :=by
  have hnV:(16:ℝ)≤Fintype.card V:=by exact_mod_cast hn
  have hWV:Fintype.card V≤Fintype.card (V⊕U):=Fintype.card_le_of_injective Sum.inl Sum.inl_injective
  have hnW:(16:ℝ)≤Fintype.card (V⊕U):=by exact_mod_cast hn.trans hWV
  have h2:2/(Fintype.card (V⊕U):ℝ)≤2/16:=by gcongr
  have h1:1/(Fintype.card V:ℝ)≤1/16:=by gcongr
  have h1W:1/(Fintype.card (V⊕U):ℝ)≤1/16:=by gcongr
  linarith
end Oberwolfach
