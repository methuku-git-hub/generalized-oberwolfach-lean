module

public import Oberwolfach.MarkedAdaptiveAgreementProperty
public import Oberwolfach.MarkedChooseReservedTerminalReservoir

@[expose] public section
/-! A named predicate for the full agreement-inclusive retained event. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} {W Z Hdom:ℕ→Type}
  [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [LinearOrder V] [Nonempty V] [DecidableEq U]
  [∀ i,Fintype (W i)] [∀ i,Fintype (Z i)] [∀ i,LinearOrder (W i)] [∀ i,DecidableEq (Z i)]
  [∀ i,Fintype (Hdom i)] [∀ i,DecidableEq (Hdom i)]
variable (r d size a₀ b₀ e₀ aRob bRob eRob f₀ L hNbr:ℕ)
variable (β βCommon εAbs εRob ζRob εRef δRef γ p k s₀ tstar ζ εBal Kbal ζBal εNbr ζNbr Bload εLoad Kload ζLoad ζLocal ζConfig ρstar sstar kstar τ:ℝ)
variable (P:SimpleGraph V) (π:Equiv.Perm V)
variable (f:∀ i,W i↪oV) (g:∀ i,Z i↪U) (ρi:∀ i,Equiv.Perm (W i))
variable (A:∀ i,Finset (W i)) (Bset:∀ i,Finset (Z i))
variable (Scale:ℕ→ℕ) (D Dbal Dload:ℕ→ℝ) (b:∀ i,Hdom i↪Z i)
variable (weight:∀ i,(Fin ((r+4)+1)→W i)→ℝ)
variable (q:U→Γ→ℝ) (s:U→Color→ℝ) (a:Γ) (j:Color)


theorem marked_adaptive_agreement_robust_reserved_absorber
    (z:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a)
    (hEvent:MarkedAdaptiveAgreementProperty r d size a₀ b₀ e₀ aRob bRob eRob f₀ L hNbr
      β βCommon εAbs εRob ζRob εRef δRef γ p k s₀ tstar ζ εBal ζBal εNbr ζNbr Bload εLoad Kload ζLoad ζLocal ζConfig ρstar sstar kstar τ
      P π f g ρi A Bset Scale D Dload b weight q s a j z):
    let H:Bool→V→U→Prop:=retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
      (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j;
    ∀(DR:SimpleGraph V) (DS:SimpleGraph (V⊕U)),
      (∀v,(DR.degree v:ℝ)≤ζRob*Fintype.card V)→
      (∀z,(DS.degree z:ℝ)≤ζRob*Fintype.card V)→
    let σ':=rawMarkedDeleteRims z.1 DR.edgeFinset
    let H':=markedDeletePhysicalSpokes H DS
    let E':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) false
    let K':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) true;
    MarkedReservedTerminalAbsorberProperty (fun e:E'=>e.val.1) (fun e=>e.val.2)
      (fun e:K'=>e.val.1) (fun e=>e.val.2) (H' false) (H' true) π (3*d) r size aRob bRob eRob f₀ εRob :=by
  dsimp only [MarkedAdaptiveAgreementProperty] at hEvent
  first
    | exact hEvent.2
    | exact hEvent.1.2
    | exact hEvent.1.1.2
    | exact hEvent.1.1.1.2
    | exact hEvent.1.1.1.1.2
    | exact hEvent.1.1.1.1.1.2
    | exact hEvent.1.1.1.1.1.1.2
    | exact hEvent.1.1.1.1.1.1.1.2
    | exact hEvent.1.1.1.1.1.1.1.1.2
    | exact hEvent.1.1.1.1.1.1.1.1.1.2
    | exact hEvent.1.1.1.1.1.1.1.1.1.1.2
    | exact hEvent.1.1.1.1.1.1.1.1.1.1.1.2
end Oberwolfach
