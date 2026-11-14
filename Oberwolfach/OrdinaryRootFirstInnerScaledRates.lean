module

public import Oberwolfach.OrdinaryRootFirstTraceRatesMonotone

@[expose] public section
/-! Translate root-cover costs measured on the inner vertex set to rates
    on the ambient physical vertex set, without changing either cost. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_root_first_inner_scaled_rates
    {V U:Type} [Fintype V] [Fintype U] [DecidableEq V]
    (I:Finset V) (ξ δ cap:ℝ) (hn:0<Fintype.card (V⊕U))
    (hξ:0≤ξ) (hδ:0≤δ) (hξcap:10*ξ≤cap) (hδcap:δ≤cap):
    ∃ηrate ellrate:ℝ,0≤ηrate ∧ 0≤ellrate ∧ ηrate≤cap ∧ ellrate≤cap ∧
      ηrate*Fintype.card (V⊕U)=10*ξ*I.card ∧
      ellrate*Fintype.card (V⊕U)=δ*I.card :=by
  let n:ℝ:=Fintype.card (V⊕U)
  have hn':0<n:=by dsimp [n];exact_mod_cast hn
  have hI:(I.card:ℝ)≤n:=by
    have hv:I.card≤Fintype.card V:=Finset.card_le_univ I
    have hw:Fintype.card V≤Fintype.card (V⊕U):=Fintype.card_le_of_injective Sum.inl Sum.inl_injective
    change (I.card:ℝ)≤(Fintype.card (V⊕U):ℝ)
    exact_mod_cast hv.trans hw
  let ηrate:ℝ:=10*ξ*I.card/n
  let ellrate:ℝ:=δ*I.card/n
  have hη:0≤ηrate:=by dsimp [ηrate];positivity
  have hell:0≤ellrate:=by dsimp [ellrate];positivity
  have hηcap:ηrate≤cap:=by
    apply (div_le_iff₀ hn').2
    have h1:=mul_le_mul_of_nonneg_left hI (show 0≤10*ξ by positivity)
    have h2:=mul_le_mul_of_nonneg_right hξcap hn'.le
    nlinarith only [h1,h2]
  have hellcap:ellrate≤cap:=by
    apply (div_le_iff₀ hn').2
    have h1:=mul_le_mul_of_nonneg_left hI hδ
    have h2:=mul_le_mul_of_nonneg_right hδcap hn'.le
    nlinarith only [h1,h2]
  refine ⟨ηrate,ellrate,hη,hell,hηcap,hellcap,?_,?_⟩
  · change (10*ξ*I.card/n)*n=10*ξ*I.card
    exact div_mul_cancel₀ _ (ne_of_gt hn')
  · change (δ*I.card/n)*n=δ*I.card
    exact div_mul_cancel₀ _ (ne_of_gt hn')
end Oberwolfach
