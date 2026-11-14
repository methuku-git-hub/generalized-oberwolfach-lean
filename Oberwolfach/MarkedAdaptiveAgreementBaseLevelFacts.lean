module

public import Oberwolfach.MarkedLevelFiniteBalanceBound
public import Oberwolfach.MarkedAdaptiveAgreementBaseCommonConfigurations
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


theorem marked_adaptive_agreement_base_level_facts
    (z:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a)
    (hEvent:MarkedAdaptiveAgreementProperty r d size a₀ b₀ e₀ aRob bRob eRob f₀ L hNbr
      β βCommon εAbs εRob ζRob εRef δRef γ p k s₀ tstar ζ εBal ζBal εNbr ζNbr Bload εLoad Kload ζLoad ζLocal ζConfig ρstar sstar kstar τ
      P π f g ρi A Bset Scale D Dload b weight q s a j z)
    (hγ:0≤γ) (hp:0≤p) (hk:0≤k):
    ∀ i≤L,
      let σi:=rawMarkedRestrictPair (f i) (g i) z.1
      let Hi:=fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
        (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j b (f i x) (g i u);
      MarkedReferenceStatistics (P.comap (f i)) (ρi i) d a j (D i) εRef δRef (γ/2) p k s₀
        (s₀/((r+4:ℕ):ℝ)) σi ∧
      MarkedReferenceCutFamilies (P.comap (f i)) (ρi i) d a j (γ/2) p k tstar σi ∧
      MarkedReferenceConfigurations r (P.comap (f i)) (ρi i) d a j β σi ∧
      MarkedLevelFiniteBalanceBound (P.comap (f i)) (ρi i) d (r+4) (A i) (Bset i)
        ((εBal+((r+4)+2:ℕ)*ζBal)*Scale i) σi Hi ∧
      MarkedCommonConfigurationsWithSpokes r (P.comap (f i)) (ρi i) d βCommon ζ σi Hi ∧
      MarkedLocalConfigurationsWithSpokes r (P.comap (f i)) (ρi i) d (A i)
        (markedLocalCycleCoefficient r γ (tstar/2) kstar-(r+5:ℕ)*ζConfig)
        (markedLocalPathCoefficient r γ (tstar/2) kstar-(r+4:ℕ)*ζConfig) σi Hi ∧
      MarkedLocalSpokeLoadsWithSpokes (P.comap (f i)) (ρi i) d (r+4) (Dload i) p k s₀ (weight i)
        (τ+εLoad+5*(((r+4):ℝ)+1)^4*(2*Bload/(ρstar*sstar/(2*((r+4:ℕ):ℝ)))^(2*(r+4)+1))*Kload*ζLocal) σi Hi := by
  have href:=marked_adaptive_agreement_reference_fields r d size a₀ b₀ e₀ aRob bRob eRob f₀ L hNbr
    β βCommon εAbs εRob ζRob εRef δRef γ p k s₀ tstar ζ εBal ζBal εNbr ζNbr Bload εLoad Kload ζLoad ζLocal ζConfig ρstar sstar kstar τ
    P π f g ρi A Bset Scale D Dload b weight q s a j z hEvent hγ hp hk
  have hcommon:=marked_adaptive_agreement_base_common_configurations r d size a₀ b₀ e₀ aRob bRob eRob f₀ L hNbr
    β βCommon εAbs εRob ζRob εRef δRef γ p k s₀ tstar ζ εBal ζBal εNbr ζNbr Bload εLoad Kload ζLoad ζLocal ζConfig ρstar sstar kstar τ
    P π f g ρi A Bset Scale D Dload b weight q s a j z hEvent
  dsimp only [MarkedAdaptiveAgreementProperty] at hEvent
  intro i hi
  refine ⟨(href i hi).1,(href i hi).2,?_,?_,hcommon i hi,?_,?_⟩
  · first
      | exact (hEvent.1 i hi).1
      | exact (hEvent.1.1 i hi).1
      | exact (hEvent.1.1.1 i hi).1
      | exact (hEvent.1.1.1.1 i hi).1
      | exact (hEvent.1.1.1.1.1 i hi).1
      | exact (hEvent.1.1.1.1.1.1 i hi).1
      | exact (hEvent.1.1.1.1.1.1.1 i hi).1
      | exact (hEvent.1.1.1.1.1.1.1.1 i hi).1
      | exact (hEvent.1.1.1.1.1.1.1.1.1 i hi).1
      | exact (hEvent.1.1.1.1.1.1.1.1.1.1 i hi).1
      | exact (hEvent.1.1.1.1.1.1.1.1.1.1.1 i hi).1
      | exact (hEvent.2 i hi).1
      | exact (hEvent.1.2 i hi).1
      | exact (hEvent.1.1.2 i hi).1
      | exact (hEvent.1.1.1.2 i hi).1
      | exact (hEvent.1.1.1.1.2 i hi).1
      | exact (hEvent.1.1.1.1.1.2 i hi).1
      | exact (hEvent.1.1.1.1.1.1.2 i hi).1
      | exact (hEvent.1.1.1.1.1.1.1.2 i hi).1
      | exact (hEvent.1.1.1.1.1.1.1.1.2 i hi).1
      | exact (hEvent.1.1.1.1.1.1.1.1.1.2 i hi).1
      | exact (hEvent.1.1.1.1.1.1.1.1.1.1.2 i hi).1
      | exact (hEvent.1.1.1.1.1.1.1.1.1.1.1.2 i hi).1
      | exact (hEvent.1.1.1.1.1.1.1.1.1.1.1.1.2 i hi).1
      | exact (hEvent.1.1.1.1.1.1.1.1.1.1.1.1.1.2 i hi).1
      | exact (hEvent.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2 i hi).1
      | exact (hEvent.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2 i hi).1
      | exact (hEvent.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1 i hi).1
  · first
      | exact (hEvent.1 i hi).1
      | exact (hEvent.1.1 i hi).1
      | exact (hEvent.1.1.1 i hi).1
      | exact (hEvent.1.1.1.1 i hi).1
      | exact (hEvent.1.1.1.1.1 i hi).1
      | exact (hEvent.1.1.1.1.1.1 i hi).1
      | exact (hEvent.1.1.1.1.1.1.1 i hi).1
      | exact (hEvent.1.1.1.1.1.1.1.1 i hi).1
      | exact (hEvent.1.1.1.1.1.1.1.1.1 i hi).1
      | exact (hEvent.1.1.1.1.1.1.1.1.1.1 i hi).1
      | exact (hEvent.1.1.1.1.1.1.1.1.1.1.1 i hi).1
      | exact (hEvent.2 i hi).1
      | exact (hEvent.1.2 i hi).1
      | exact (hEvent.1.1.2 i hi).1
      | exact (hEvent.1.1.1.2 i hi).1
      | exact (hEvent.1.1.1.1.2 i hi).1
      | exact (hEvent.1.1.1.1.1.2 i hi).1
      | exact (hEvent.1.1.1.1.1.1.2 i hi).1
      | exact (hEvent.1.1.1.1.1.1.1.2 i hi).1
      | exact (hEvent.1.1.1.1.1.1.1.1.2 i hi).1
      | exact (hEvent.1.1.1.1.1.1.1.1.1.2 i hi).1
      | exact (hEvent.1.1.1.1.1.1.1.1.1.1.2 i hi).1
      | exact (hEvent.1.1.1.1.1.1.1.1.1.1.1.2 i hi).1
      | exact (hEvent.1.1.1.1.1.1.1.1.1.1.1.1.2 i hi).1
      | exact (hEvent.1.1.1.1.1.1.1.1.1.1.1.1.1.2 i hi).1
      | exact (hEvent.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2 i hi).1
      | exact (hEvent.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2 i hi).1
      | exact (hEvent.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1 i hi).1
  · first
      | exact hEvent.2 i hi
      | exact hEvent.1.2 i hi
      | exact hEvent.1.1.2 i hi
      | exact hEvent.1.1.1.2 i hi
      | exact hEvent.1.1.1.1.2 i hi
      | exact hEvent.1.1.1.1.1.2 i hi
      | exact hEvent.1.1.1.1.1.1.2 i hi
      | exact hEvent.1.1.1.1.1.1.1.2 i hi
      | exact hEvent.1.1.1.1.1.1.1.1.2 i hi
      | exact hEvent.1.1.1.1.1.1.1.1.1.2 i hi
      | exact hEvent.1.1.1.1.1.1.1.1.1.1.2 i hi
      | exact hEvent.1.1.1.1.1.1.1.1.1.1.1.2 i hi
      | exact hEvent.1.1.1.1.1.1.1.1.1.1.1.1.2 i hi
      | exact hEvent.1.1.1.1.1.1.1.1.1.1.1.1.1.2 i hi
      | exact hEvent.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2 i hi
      | exact hEvent.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2 i hi
      | exact hEvent.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1 i hi
  · first
      | exact hEvent.2 i hi
      | exact hEvent.1.2 i hi
      | exact hEvent.1.1.2 i hi
      | exact hEvent.1.1.1.2 i hi
      | exact hEvent.1.1.1.1.2 i hi
      | exact hEvent.1.1.1.1.1.2 i hi
      | exact hEvent.1.1.1.1.1.1.2 i hi
      | exact hEvent.1.1.1.1.1.1.1.2 i hi
      | exact hEvent.1.1.1.1.1.1.1.1.2 i hi
      | exact hEvent.1.1.1.1.1.1.1.1.1.2 i hi
      | exact hEvent.1.1.1.1.1.1.1.1.1.1.2 i hi
      | exact hEvent.1.1.1.1.1.1.1.1.1.1.1.2 i hi
      | exact hEvent.1.1.1.1.1.1.1.1.1.1.1.1.2 i hi
      | exact hEvent.1.1.1.1.1.1.1.1.1.1.1.1.1.2 i hi
      | exact hEvent.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2 i hi
      | exact hEvent.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2 i hi
      | exact hEvent.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1 i hi
end Oberwolfach
