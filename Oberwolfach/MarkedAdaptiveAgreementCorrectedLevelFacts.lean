module

public import Oberwolfach.MarkedAdaptiveAgreementBaseLevelFacts
public import Oberwolfach.MarkedVortexCorrectionLevelFacts

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [Nonempty V] [DecidableEq U]

theorem marked_adaptive_agreement_corrected_level_facts
    (r d size a₀ b₀ e₀ aRob bRob eRob f₀ L hNbr:ℕ)
    (β βCommon εAbs εRob ζRob εRef δRef γ p k s₀ tstar ζ εBal ζBal εNbr ζNbr Bload εLoad Kload ζLoad ζLocal ζConfig ρstar sstar kstar τ:ℝ)
    (P:SimpleGraph V) (π:Equiv.Perm V)
    (Dnat vsize:ℕ) (βQ εQ:ℝ) (Q:Vortex U P Dnat βQ εQ vsize)
    (hpres:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (Scale:ℕ→ℕ) (D Dload:ℕ→ℝ)
    (weight:∀ i,(Fin ((r+4)+1)→markedVortexVertexType Q i)→ℝ)
    (q:U→Γ→ℝ) (s:U→Color→ℝ) (a:Γ) (j:Color)
    (z:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a)
    (hEvent:
      let f:=markedVortexVertexEmbedding Q
      let g:=markedVortexHubEmbedding Q
      let ρi:=markedVortexPermutation Q π hpres
      let A:=markedVortexInnerVertices Q
      let B:=markedVortexInnerHubs Q
      let b:=fun i=>Function.Embedding.refl (markedVortexHubType Q i);
      MarkedAdaptiveAgreementProperty r d size a₀ b₀ e₀ aRob bRob eRob f₀ L hNbr
        β βCommon εAbs εRob ζRob εRef δRef γ p k s₀ tstar ζ εBal ζBal εNbr ζNbr Bload εLoad Kload ζLoad ζLocal ζConfig ρstar sstar kstar τ
        P π f g ρi A B Scale D Dload b weight q s a j z)
    (hγ:0≤γ) (hp:0≤p) (hk:0≤k)
    (hcor:
      let H:=retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
        (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j;
      MarkedVortexAbsorbableCorrectionWithRestrictions P π d r size aRob bRob eRob f₀ εRob ζRob z.1 H Dnat vsize βQ εQ Q):
    let H:=retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
      (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j
    let C:=fun i (σi:RawMarkedOutcome (markedVortexVertexType Q i) (markedVortexHubType Q i) Γ Color)
      (Hi:Bool→markedVortexVertexType Q i→markedVortexHubType Q i→Prop)=>
      MarkedReferenceStatistics (P.comap (markedVortexVertexEmbedding Q i)) (markedVortexPermutation Q π hpres i) d a j (D i) εRef δRef (γ/2) p k s₀
        (s₀/((r+4:ℕ):ℝ)) σi ∧
      MarkedReferenceCutFamilies (P.comap (markedVortexVertexEmbedding Q i)) (markedVortexPermutation Q π hpres i) d a j (γ/2) p k tstar σi ∧
      MarkedReferenceConfigurations r (P.comap (markedVortexVertexEmbedding Q i)) (markedVortexPermutation Q π hpres i) d a j β σi ∧
      MarkedLevelFiniteBalanceBound (P.comap (markedVortexVertexEmbedding Q i)) (markedVortexPermutation Q π hpres i) d (r+4)
        (markedVortexInnerVertices Q i) (markedVortexInnerHubs Q i) ((εBal+((r+4)+2:ℕ)*ζBal)*Scale i) σi Hi ∧
      MarkedCommonConfigurationsWithSpokes r (P.comap (markedVortexVertexEmbedding Q i)) (markedVortexPermutation Q π hpres i) d βCommon ζ σi Hi ∧
      MarkedLocalConfigurationsWithSpokes r (P.comap (markedVortexVertexEmbedding Q i)) (markedVortexPermutation Q π hpres i) d (markedVortexInnerVertices Q i)
        (markedLocalCycleCoefficient r γ (tstar/2) kstar-(r+5:ℕ)*ζConfig)
        (markedLocalPathCoefficient r γ (tstar/2) kstar-(r+4:ℕ)*ζConfig) σi Hi ∧
      MarkedLocalSpokeLoadsWithSpokes (P.comap (markedVortexVertexEmbedding Q i)) (markedVortexPermutation Q π hpres i) d (r+4) (Dload i) p k s₀ (weight i)
        (τ+εLoad+5*(((r+4):ℝ)+1)^4*(2*Bload/(ρstar*sstar/(2*((r+4:ℕ):ℝ)))^(2*(r+4)+1))*Kload*ζLocal) σi Hi;
    MarkedVortexAbsorbableCorrectionWithLevelFacts P π d r size aRob bRob eRob f₀ εRob ζRob z.1 H Dnat vsize βQ εQ Q L C := by
  intro H C
  apply marked_vortex_correction_preserves_level_facts P π d r size aRob bRob eRob f₀ εRob ζRob z.1 H Dnat vsize βQ εQ Q L C ?_ hcor
  intro i hi hL
  exact marked_adaptive_agreement_base_level_facts r d size a₀ b₀ e₀ aRob bRob eRob f₀ L hNbr
      β βCommon εAbs εRob ζRob εRef δRef γ p k s₀ tstar ζ εBal ζBal εNbr ζNbr Bload εLoad Kload ζLoad ζLocal ζConfig ρstar sstar kstar τ
      P π (markedVortexVertexEmbedding Q) (markedVortexHubEmbedding Q) (markedVortexPermutation Q π hpres)
      (markedVortexInnerVertices Q) (markedVortexInnerHubs Q) Scale D Dload
      (fun i=>Function.Embedding.refl (markedVortexHubType Q i)) weight q s a j z hEvent hγ hp hk i hL
end Oberwolfach
