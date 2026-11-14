module

public import Oberwolfach.MarkedPackingZeroDeletionAnyInstance
public import Oberwolfach.MarkedAdaptiveAgreementReferenceFields
public import Oberwolfach.MarkedEmptyPhysicalDeletion
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


theorem marked_adaptive_agreement_base_common_configurations
    (z:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a)
    (hEvent:MarkedAdaptiveAgreementProperty r d size a₀ b₀ e₀ aRob bRob eRob f₀ L hNbr
      β βCommon εAbs εRob ζRob εRef δRef γ p k s₀ tstar ζ εBal ζBal εNbr ζNbr Bload εLoad Kload ζLoad ζLocal ζConfig ρstar sstar kstar τ
      P π f g ρi A Bset Scale D Dload b weight q s a j z):
    ∀ i≤L,
      MarkedCommonConfigurationsWithSpokes r (P.comap (f i)) (ρi i) d βCommon ζ
        (rawMarkedRestrictPair (f i) (g i) z.1)
        (fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
          (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j b (f i x) (g i u)) := by
  dsimp only [MarkedAdaptiveAgreementProperty] at hEvent
  have hsource: ∀ i≤L,∀ δ:ℝ,0≤δ →
          ∀ (DR:SimpleGraph (W i)) (DS:SimpleGraph (W i⊕Z i)),
          (∀ x,(DR.degree x:ℝ)≤δ) → (∀ x,(DS.degree x:ℝ)≤δ) →
          MarkedCommonConfigurationsWithSpokes r (P.comap (f i)) (ρi i) d βCommon (ζ+4*δ/Fintype.card (W i))
            (rawMarkedDeleteRims (rawMarkedRestrictPair (f i) (g i) z.1) DR.edgeFinset)
            (markedDeletePhysicalSpokes
              (fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
                (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j b (f i x) (g i u)) DS) := by
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
      | exact hEvent.1.1.1.1.1.1.1.1.1.1.1.1.2
      | exact hEvent.1.1.1.1.1.1.1.1.1.1.1.1.1.2
      | exact hEvent.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2
      | exact hEvent.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2
      | exact hEvent.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1
  intro i hi
  have hh:=hsource i hi 0 (by norm_num) ⊥ ⊥ (by intro x; simp) (by intro x; simp)
  simpa only [mul_zero,zero_div,add_zero,graph_bottom_edgeFinset_any_instance,rawMarkedDeleteRims_empty,markedDeletePhysicalSpokes_bottom] using hh
end Oberwolfach
