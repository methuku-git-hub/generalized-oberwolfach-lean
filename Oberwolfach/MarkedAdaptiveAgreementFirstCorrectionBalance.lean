module

public import Oberwolfach.MarkedAdaptiveAgreementBaseLevelFacts
public import Oberwolfach.MarkedVortexCorrectionFirstBalance

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

theorem marked_adaptive_agreement_first_correction_balance
    (r d size a₀ b₀ e₀ aRob bRob eRob f₀ L hNbr:ℕ)
    (β βCommon εAbs εRob ζRob εRef δRef γ p k s₀ tstar ζ εBal ζBal εNbr ζNbr Bload εLoad Kload ζLoad ζLocal ζConfig ρstar sstar kstar τ:ℝ)
    (P:SimpleGraph V) (π:Equiv.Perm V)
    (Dnat vsize:ℕ) (βQ εQ:ℝ) (Q:Vortex U P Dnat βQ εQ vsize)
    (hpres:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (Scale:ℕ→ℕ) (D Dload:ℕ→ℝ)
    (weight:∀ i,(Fin ((r+4)+1)→markedVortexVertexType Q i)→ℝ)
    (q:U→Γ→ℝ) (s:U→Color→ℝ) (a:Γ) (j:Color)
    (z:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a)
    (C:∀i, RawMarkedOutcome (markedVortexVertexType Q i) (markedVortexHubType Q i) Γ Color →
      (Bool→markedVortexVertexType Q i→markedVortexHubType Q i→Prop)→Prop)
    (hζRob:0≤ζRob)
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
      MarkedVortexAbsorbableCorrectionWithLevelFacts P π d r size aRob bRob eRob f₀ εRob ζRob z.1 H Dnat vsize βQ εQ Q L C):
    let H:=retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
      (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j;
    MarkedVortexCorrectionWithFirstBalance P π d r size aRob bRob eRob f₀ εRob ζRob z.1 H Dnat vsize βQ εQ Q L C
      ((εBal+((r+4)+2:ℕ)*ζBal)*Scale 0) := by
  intro H
  have hfacts:=marked_adaptive_agreement_base_level_facts r d size a₀ b₀ e₀ aRob bRob eRob f₀ L hNbr
      β βCommon εAbs εRob ζRob εRef δRef γ p k s₀ tstar ζ εBal ζBal εNbr ζNbr Bload εLoad Kload ζLoad ζLocal ζConfig ρstar sstar kstar τ
      P π (markedVortexVertexEmbedding Q) (markedVortexHubEmbedding Q) (markedVortexPermutation Q π hpres)
      (markedVortexInnerVertices Q) (markedVortexInnerHubs Q) Scale D Dload
      (fun i=>Function.Embedding.refl (markedVortexHubType Q i)) weight q s a j z hEvent hγ hp hk 0 (Nat.zero_le L)
  exact marked_vortex_correction_first_balance_from_event P π d r size aRob bRob eRob f₀ εRob ζRob z.1 H
    Dnat vsize βQ εQ Q L hpres hζRob ((εBal+((r+4)+2:ℕ)*ζBal)*Scale 0) C hfacts.2.2.2.1 hcor
end Oberwolfach
