module

public import Oberwolfach.MarkedLongCommonMatchingCorrection
public import Oberwolfach.MarkedExpandedActualSample

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 50000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance actualCommonCorrectionFinDecidable (n:ℕ):DecidableEq (Fin n):=Classical.decEq _
theorem marked_actual_common_matching_correction_selection
    (r:ℕ) (ρ₀ γRich kstar tstar ζRob εRob:ℝ)
    (hρ₀:0<ρ₀) (hγ:0<γRich) (hkstar:0<kstar)
    (htstar:0<tstar) (htstar1:tstar≤1) (hζRob:0<ζRob):
    ∃ξCorr:ℝ,0<ξCorr ∧ 16*(((r+4:ℕ):ℝ)+1)*ξCorr≤ζRob ∧ ∃η₀:ℝ,0<η₀ ∧ ∃N:ℕ,∀(n:ℕ),N≤n→1≤n→
    ∀(U:Type) [Fintype U] [DecidableEq U] [Nonempty (Fin n)]
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (Dnat vsize:ℕ) (βQ εQ:ℝ) (Q:Vortex U P Dnat βQ εQ vsize)
    (hpres:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (K d size a₀ b₀ e₀ aRob bRob eRob f₀ L hNbr:ℕ) (hh:1≤hNbr)
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (θ ρ:ℝ) (hρlo:ρ₀≤ρ) (hρhi:ρ≤1)
    (hDlo:(n:ℝ)/2≤Dnat) (hDhi:(Dnat:ℝ)≤2*n) (hsize:ρ*Dnat=2*Fintype.card U)
    (hεQ:0≤εQ) (hεQsmall:εQ≤min ((γRich/2)*kstar) tstar/128)
    (β βCommon εAbs εRef δRef ζ εBal ζBal εNbr ζNbr Bload εLoad ζLoad ζLocal ζConfig sstar τLevel:ℝ)
    (levelWeight:∀i,(Fin ((r+4)+1)→markedVortexVertexType Q i)→ℝ)
    (ζEvent:ℝ) (hζScale:ζRob≤ζEvent)
    (hεNbr:0≤εNbr)
    (hpmin:kstar≤ρ*(1/100)/2) (hkmin:kstar≤ρ*((1/100)/(((r+4):ℕ):ℝ))/2)
    (hcutBudget:εNbr/(2*((hNbr:ℝ)+1))≤14*(min ((γRich/2)*kstar) tstar/128))
    (hbudget:2*(εRef*n)+2*(εNbr*Fintype.card U)≤η₀*n)
    (hmarked:εRef*n+εNbr*Fintype.card U≤η₀*n)
    (hcolumn:((((r+4):ℕ):ℝ)+1)*(εNbr*n)≤η₀*n)
    (mass:MarkedExpandedActualOutcome (U:=U) π d→ℝ)
    (Matching:MarkedExpandedActualOutcome (U:=U) π d→Prop)
    (Parent:RawMarkedRetainedOutcome (U:=U) (Color:=Bool) π d false→Prop)
    (hSelect:∃ outcome,0<mass outcome ∧ Matching outcome ∧ Parent (markedExpandedActualSelected π d outcome) ∧ 
      let fV:=markedVortexVertexEmbedding Q
      let gV:=markedVortexHubEmbedding Q
      let ρi:=markedVortexPermutation Q π hpres
      let Aset:=markedVortexInnerVertices Q
      let Bset:=markedVortexInnerHubs Q
      let Scale:=fun i=>Fintype.card (markedVortexVertexType Q i)
      let Dlevel:=fun i=>2*(Fintype.card (markedVortexHubType Q i):ℝ)/ρ
      let bdom:=fun i=>Function.Embedding.refl (markedVortexHubType Q i);
      MarkedAdaptiveAgreementProperty r d size a₀ b₀ e₀ aRob bRob eRob f₀ L hNbr
        β βCommon εAbs εRob ζEvent εRef δRef γRich (ρ*(1/100)/2)
        (ρ*((1/100)/(((r+4):ℕ):ℝ))/2) (1/100) tstar ζ εBal ζBal εNbr ζNbr Bload εLoad 1 ζLoad ζLocal ζConfig ρ₀ sstar kstar τLevel
        P π fV gV ρi Aset Bset Scale Dlevel Dlevel bdom levelWeight
        (longAssignedIntervalProbability F hF K (r+4) θ) (longAssignedSpokeProbability F hF K (r+4) θ) false false (markedExpandedActualSelected π d outcome)),
    ∃ outcome,0<mass outcome ∧ Matching outcome ∧ Parent (markedExpandedActualSelected π d outcome) ∧ (
      let fV:=markedVortexVertexEmbedding Q
      let gV:=markedVortexHubEmbedding Q
      let ρi:=markedVortexPermutation Q π hpres
      let Aset:=markedVortexInnerVertices Q
      let Bset:=markedVortexInnerHubs Q
      let Scale:=fun i=>Fintype.card (markedVortexVertexType Q i)
      let Dlevel:=fun i=>2*(Fintype.card (markedVortexHubType Q i):ℝ)/ρ
      let bdom:=fun i=>Function.Embedding.refl (markedVortexHubType Q i);
      MarkedAdaptiveAgreementProperty r d size a₀ b₀ e₀ aRob bRob eRob f₀ L hNbr
        β βCommon εAbs εRob ζEvent εRef δRef γRich (ρ*(1/100)/2)
        (ρ*((1/100)/(((r+4):ℕ):ℝ))/2) (1/100) tstar ζ εBal ζBal εNbr ζNbr Bload εLoad 1 ζLoad ζLocal ζConfig ρ₀ sstar kstar τLevel
        P π fV gV ρi Aset Bset Scale Dlevel Dlevel bdom levelWeight
        (longAssignedIntervalProbability F hF K (r+4) θ) (longAssignedSpokeProbability F hF K (r+4) θ) false false (markedExpandedActualSelected π d outcome)) ∧ (MarkedProtectedAbsorbableCorrectionWithBounds P π d r size aRob bRob eRob f₀ εRob ζRob ξCorr (markedExpandedActualSelected π d outcome).1 (retainedRawMarkedSpokes π d (fun e=>(markedExpandedActualSelected π d outcome).1 (Sum.inr e)) false
      (startRetentionMinimum (rawStartHubSet π d (fun e=>(markedExpandedActualSelected π d outcome).1 (Sum.inr e)) false)) (markedExpandedActualSelected π d outcome).2 false false)
      (Q.extendedVertices 1) (Q.extendedIndices 1)) := by
  obtain ⟨ξCorr,hξCorr,hξscale,η₀,hη₀,N,hW⟩:=marked_long_common_matching_correction_selection
    r ρ₀ γRich kstar tstar ζRob εRob hρ₀ hγ hkstar htstar htstar1 hζRob
  refine ⟨ξCorr,hξCorr,hξscale,η₀,hη₀,N,?_⟩
  intro n hn hn1 U _ _ _ P π Dnat vsize βQ εQ Q hpres K d size a₀ b₀ e₀ aRob bRob eRob f₀ L hNbr hh F hF θ ρ hρlo hρhi hDlo hDhi hsize hεQ hεQsmall β βCommon εAbs εRef δRef ζ εBal ζBal εNbr ζNbr Bload εLoad ζLoad ζLocal ζConfig sstar τLevel levelWeight ζEvent hζScale hεNbr hpmin hkmin hcutBudget hbudget hmarked hcolumn mass Matching Parent hSelect
  exact hW n hn hn1 U P π Dnat vsize βQ εQ Q hpres K d size a₀ b₀ e₀ aRob bRob eRob f₀ L hNbr hh F hF θ ρ hρlo hρhi hDlo hDhi hsize hεQ hεQsmall β βCommon εAbs εRef δRef ζ εBal ζBal εNbr ζNbr Bload εLoad ζLoad ζLocal ζConfig sstar τLevel levelWeight ζEvent hζScale hεNbr hpmin hkmin hcutBudget hbudget hmarked hcolumn
    (MarkedExpandedActualOutcome (U:=U) π d) mass (markedExpandedActualSelected π d) Matching Parent hSelect
end Oberwolfach
