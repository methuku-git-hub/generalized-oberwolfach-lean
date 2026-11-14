module

public import Oberwolfach.MarkedActualCommonCorrectionBudgeted
public import Oberwolfach.MarkedVortexParentRecordEvent

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 60000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance namedBudgetCorrectionFinDecidable (n:ℕ):DecidableEq (Fin n):=Classical.decEq _
theorem marked_named_parent_budgeted_correction_selection
    (r:ℕ) (ρ₀ γRich kstar tstar ζEvent εRob gammaLoss sigmaLoss κmax:ℝ)
    (hρ₀:0<ρ₀) (hγ:0<γRich) (hkstar:0<kstar)
    (htstar:0<tstar) (htstar1:tstar≤1) (hζEvent:0<ζEvent)
    (hGamma:0<gammaLoss) (hSigma:0<sigmaLoss) (hκmax:0<κmax):
    ∃ ζRob:ℝ,0<ζRob ∧ ζRob≤ζEvent ∧
    ∃ ξCorr:ℝ,0<ξCorr ∧ 16*(((r+4:ℕ):ℝ)+1)*ξCorr≤ζRob ∧
      (∀ n:ℕ,6*(8*((((r+4):ℕ):ℝ)+1)*ξCorr*n)≤min (gammaLoss*n) (sigmaLoss*n)) ∧
    ∃ η₀:ℝ,0<η₀ ∧ ∃ κ εRef εNbr:ℝ,0<κ ∧ κ≤κmax ∧ εRef=κ/4 ∧ 0<εRef ∧ 0<εNbr ∧
    ∃ N:ℕ,∀(n:ℕ),N≤n→1≤n→
    ∀(U:Type) [Fintype U] [DecidableEq U] [Nonempty (Fin n)]
    (hU:Fintype.card U≤n)
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (Dnat vsize:ℕ) (βQ εQ:ℝ) (Q:Vortex U P Dnat βQ εQ vsize)
    (hpres:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (K d size a₀ b₀ e₀ aRob bRob eRob f₀ L hNbr:ℕ) (hh:1≤hNbr)
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (θ ρ:ℝ) (hρlo:ρ₀≤ρ) (hρhi:ρ≤1)
    (hDlo:(n:ℝ)/2≤Dnat) (hDhi:(Dnat:ℝ)≤2*n) (hsize:ρ*Dnat=2*Fintype.card U)
    (hεQ:0≤εQ) (hεQsmall:εQ≤min ((γRich/2)*kstar) tstar/128)
    (β βCommon εAbs ζ εBal ζBal ζNbr Bload εLoad ζLoad ζLocal ζConfig sstar τLevel:ℝ)
    (levelWeight:∀i,(Fin ((r+4)+1)→markedVortexVertexType Q i)→ℝ)
    (k₀ aParent bParent eParent:ℕ) (αP εAbsP ζAbsP βconfigP βCommonP δparent:ℝ)
    (weightParent:∀i,(Fin (r+4+1)→markedVortexVertexType Q i)→ℝ)
    (weightActive:∀i,(Fin (r+4+1)→↥((Finset.univ\markedVortexInnerVertices Q i):Finset (markedVortexVertexType Q i)))→ℝ)
    (hpmin:kstar≤ρ*(1/100)/2) (hkmin:kstar≤ρ*((1/100)/(((r+4):ℕ):ℝ))/2)
    (mass:MarkedExpandedActualOutcome (U:=U) π d→ℝ)
    (Matching:MarkedExpandedActualOutcome (U:=U) π d→Prop)
    (hSelect:∃ outcome,0<mass outcome ∧ Matching outcome ∧ (MarkedVortexParentRecordEvent r (r+12) k₀ d αP ρ₀ sstar tstar kstar
      εAbsP ζAbsP βconfigP βCommonP εRef κ δparent δparent δparent δparent δparent δparent δparent δparent
      εBal ζBal δparent δparent δparent δparent δparent δparent
      size aParent bParent eParent f₀ P Dnat vsize βQ εQ Q π hpres L (1/100)
      (initialIndexDensity U Dnat*(1/100)/2) ((initialIndexDensity U Dnat*(1/100)/2)/(((r+4):ℕ):ℝ))
      (longAssignedIntervalProbability F hF K (r+4) θ) (longAssignedSpokeProbability F hF K (r+4) θ)
      false false weightParent weightActive (markedExpandedActualSelected π d outcome)) ∧ 
      let fV:=markedVortexVertexEmbedding Q
      let gV:=markedVortexHubEmbedding Q
      let ρi:=markedVortexPermutation Q π hpres
      let Aset:=markedVortexInnerVertices Q
      let Bset:=markedVortexInnerHubs Q
      let Scale:=fun i=>Fintype.card (markedVortexVertexType Q i)
      let Dlevel:=fun i=>2*(Fintype.card (markedVortexHubType Q i):ℝ)/ρ
      let bdom:=fun i=>Function.Embedding.refl (markedVortexHubType Q i);
      MarkedAdaptiveAgreementProperty r d size a₀ b₀ e₀ aRob bRob eRob f₀ L hNbr
        β βCommon εAbs εRob ζEvent εRef κ γRich (ρ*(1/100)/2)
        (ρ*((1/100)/(((r+4):ℕ):ℝ))/2) (1/100) tstar ζ εBal ζBal εNbr ζNbr Bload εLoad 1 ζLoad ζLocal ζConfig ρ₀ sstar kstar τLevel
        P π fV gV ρi Aset Bset Scale Dlevel Dlevel bdom levelWeight
        (longAssignedIntervalProbability F hF K (r+4) θ) (longAssignedSpokeProbability F hF K (r+4) θ) false false (markedExpandedActualSelected π d outcome)),
    ∃ outcome,0<mass outcome ∧ Matching outcome ∧ (MarkedVortexParentRecordEvent r (r+12) k₀ d αP ρ₀ sstar tstar kstar
      εAbsP ζAbsP βconfigP βCommonP εRef κ δparent δparent δparent δparent δparent δparent δparent δparent
      εBal ζBal δparent δparent δparent δparent δparent δparent
      size aParent bParent eParent f₀ P Dnat vsize βQ εQ Q π hpres L (1/100)
      (initialIndexDensity U Dnat*(1/100)/2) ((initialIndexDensity U Dnat*(1/100)/2)/(((r+4):ℕ):ℝ))
      (longAssignedIntervalProbability F hF K (r+4) θ) (longAssignedSpokeProbability F hF K (r+4) θ)
      false false weightParent weightActive (markedExpandedActualSelected π d outcome)) ∧ (
      let fV:=markedVortexVertexEmbedding Q
      let gV:=markedVortexHubEmbedding Q
      let ρi:=markedVortexPermutation Q π hpres
      let Aset:=markedVortexInnerVertices Q
      let Bset:=markedVortexInnerHubs Q
      let Scale:=fun i=>Fintype.card (markedVortexVertexType Q i)
      let Dlevel:=fun i=>2*(Fintype.card (markedVortexHubType Q i):ℝ)/ρ
      let bdom:=fun i=>Function.Embedding.refl (markedVortexHubType Q i);
      MarkedAdaptiveAgreementProperty r d size a₀ b₀ e₀ aRob bRob eRob f₀ L hNbr
        β βCommon εAbs εRob ζEvent εRef κ γRich (ρ*(1/100)/2)
        (ρ*((1/100)/(((r+4):ℕ):ℝ))/2) (1/100) tstar ζ εBal ζBal εNbr ζNbr Bload εLoad 1 ζLoad ζLocal ζConfig ρ₀ sstar kstar τLevel
        P π fV gV ρi Aset Bset Scale Dlevel Dlevel bdom levelWeight
        (longAssignedIntervalProbability F hF K (r+4) θ) (longAssignedSpokeProbability F hF K (r+4) θ) false false (markedExpandedActualSelected π d outcome)) ∧ (MarkedProtectedAbsorbableCorrectionWithBounds P π d r size aRob bRob eRob f₀ εRob ζRob ξCorr (markedExpandedActualSelected π d outcome).1 (retainedRawMarkedSpokes π d (fun e=>(markedExpandedActualSelected π d outcome).1 (Sum.inr e)) false
      (startRetentionMinimum (rawStartHubSet π d (fun e=>(markedExpandedActualSelected π d outcome).1 (Sum.inr e)) false)) (markedExpandedActualSelected π d outcome).2 false false)
      (Q.extendedVertices 1) (Q.extendedIndices 1)) := by
  obtain ⟨ζRob,hζRob,hζScale,ξCorr,hξCorr,hξscale,hinc,η₀,hη₀,κ,εRef,εNbr,hκ,hκmax',hεRef,hεRefpos,hεNbr,N,hW⟩:=
    marked_actual_common_correction_budgeted_selection r ρ₀ γRich kstar tstar ζEvent εRob gammaLoss sigmaLoss κmax
      hρ₀ hγ hkstar htstar htstar1 hζEvent hGamma hSigma hκmax
  refine ⟨ζRob,hζRob,hζScale,ξCorr,hξCorr,hξscale,hinc,η₀,hη₀,κ,εRef,εNbr,hκ,hκmax',hεRef,hεRefpos,hεNbr,N,?_⟩
  intro n hn hn1 U _ _ _ hU P π Dnat vsize βQ εQ Q hpres K d size a₀ b₀ e₀ aRob bRob eRob f₀ L hNbr hh F hF θ ρ hρlo hρhi hDlo hDhi hsize hεQ hεQsmall β βCommon εAbs ζ εBal ζBal ζNbr Bload εLoad ζLoad ζLocal ζConfig sstar τLevel levelWeight k₀ aParent bParent eParent αP εAbsP ζAbsP βconfigP βCommonP δparent weightParent weightActive hpmin hkmin mass Matching hSelect
  apply hW n hn hn1 U hU P π Dnat vsize βQ εQ Q hpres K d size a₀ b₀ e₀ aRob bRob eRob f₀ L hNbr hh F hF θ ρ hρlo hρhi hDlo hDhi hsize hεQ hεQsmall β βCommon εAbs κ ζ εBal ζBal ζNbr Bload εLoad ζLoad ζLocal ζConfig sstar τLevel levelWeight hpmin hkmin mass Matching
    (fun z=>MarkedVortexParentRecordEvent r (r+12) k₀ d αP ρ₀ sstar tstar kstar
      εAbsP ζAbsP βconfigP βCommonP εRef κ δparent δparent δparent δparent δparent δparent δparent δparent
      εBal ζBal δparent δparent δparent δparent δparent δparent
      size aParent bParent eParent f₀ P Dnat vsize βQ εQ Q π hpres L (1/100)
      (initialIndexDensity U Dnat*(1/100)/2) ((initialIndexDensity U Dnat*(1/100)/2)/(((r+4):ℕ):ℝ))
      (longAssignedIntervalProbability F hF K (r+4) θ) (longAssignedSpokeProbability F hF K (r+4) θ)
      false false weightParent weightActive z)
  exact hSelect
end Oberwolfach
