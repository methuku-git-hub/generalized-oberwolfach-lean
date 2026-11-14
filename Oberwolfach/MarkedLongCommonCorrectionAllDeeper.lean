module

public import Oberwolfach.MarkedLongCommonCorrectionAllLevelsBalance
public import Oberwolfach.MarkedCorrectionAllDeeperBalances
public import Oberwolfach.MarkedAdaptiveAgreementRobustScaleMono
public import Oberwolfach.MarkedAdaptiveAgreementFirstCorrectionBalance
public import Oberwolfach.MarkedVortexCorrectionAllLevelsBalance
public import Oberwolfach.MarkedLongCommonProtectedCorrection
public import Oberwolfach.MarkedCommonCorrectionErrorChoices
public import Oberwolfach.MarkedProtectedCorrectionAbsorbable
public import Oberwolfach.MarkedLongCommonAgreementGlobalBalance
public import Oberwolfach.MarkedLongCommonAgreementInitialCuts
public import Oberwolfach.MarkedAdaptiveAgreementRobustAbsorber
public import Oberwolfach.VortexFirstPairProtectedSize

@[expose] public section
/-! Assemble the common event, protected correction and robust absorber on
one retained sample, with the correction threshold chosen first. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 50000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance commonCorrectionVortexAllDeeperFinDecidable (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem marked_long_common_event_correction_all_deeper_balances
    (r:ℕ) (ρ₀ γRich kstar tstar ζCor εRob:ℝ)
    (hρ₀:0<ρ₀) (hγ:0<γRich) (hkstar:0<kstar)
    (htstar:0<tstar) (htstar1:tstar≤1) (hζCor:0<ζCor):
    ∃η₀:ℝ,0<η₀ ∧ ∃εRef εNbr:ℝ,0<εRef ∧ 0<εNbr ∧ ∃N:ℕ,∀(n:ℕ),N≤n→1≤n→
    ∀(U:Type) [Fintype U] [DecidableEq U] [Nonempty (Fin n)]
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (Dnat vsize:ℕ) (βQ εQ:ℝ) (Q:Vortex U P Dnat βQ εQ vsize)
    (hpres:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (K d size a₀ b₀ e₀ aRob bRob eRob f₀ L hNbr:ℕ) (hh:1≤hNbr)
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (θ ρ:ℝ) (hρlo:ρ₀≤ρ) (hρhi:ρ≤1)
    (hDlo:(n:ℝ)/2≤Dnat) (hDhi:(Dnat:ℝ)≤2*n) (hsize:ρ*Dnat=2*Fintype.card U)
    (hεQ:0<εQ) (hsizePos:0<vsize) (hL:L<Q.length) (hterminal:L+1=Q.length) (hεQsmall:εQ≤min ((γRich/2)*kstar) tstar/128)
    (β βCommon εAbs δRef ζ εBal ζBal ζNbr Bload εLoad ζLoad ζLocal ζConfig sstar τLevel:ℝ)
    (levelWeight:∀i,(Fin ((r+4)+1)→markedVortexVertexType Q i)→ℝ)
    (ηBal:ℝ) (hηBal:0≤ηBal)
    (hbudget:εBal+((r+4)+2:ℕ)*ζBal+((r+4)+2:ℕ)*(4*ζCor)≤ηBal*εQ/2)
    (hεBal:0≤εBal) (hζBal:0≤ζBal)
    (hdeepBase:εBal+((r+4)+2:ℕ)*ζBal≤ηBal/2)
    (hdeepCor:((r+4)+2:ℕ)*(4*ζCor)≤ηBal*εQ^2/8)
    (ζEvent:ℝ) (hEventScale:ζCor≤ζEvent)
    (z:RawMarkedRetainedOutcome (U:=U) (Color:=Bool) π d false)
    (hEvent:
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
        (longAssignedIntervalProbability F hF K (r+4) θ) (longAssignedSpokeProbability F hF K (r+4) θ) false false z)
    (hDeep:L=0 ∨ MarkedActualVortexBalanceProperty Q π hpres d (r+4) (L-1) false false εBal ζBal
      (markedVortexDeeperVertices Q) (markedVortexDeeperHubs Q) z)
    (hpmin:kstar≤ρ*(1/100)/2) (hkmin:kstar≤ρ*((1/100)/(((r+4):ℕ):ℝ))/2),
    let H:=retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) false
      (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false)) z.2 false false;
    let C:=fun i (σi:RawMarkedOutcome (markedVortexVertexType Q i) (markedVortexHubType Q i) Bool Bool)
      (Hi:Bool→markedVortexVertexType Q i→markedVortexHubType Q i→Prop)=>
      MarkedReferenceStatistics (P.comap (markedVortexVertexEmbedding Q i)) (markedVortexPermutation Q π hpres i) d false false (2*(Fintype.card (markedVortexHubType Q i):ℝ)/ρ) εRef δRef (γRich/2) (ρ*(1/100)/2) (ρ*((1/100)/(((r+4):ℕ):ℝ))/2) (1/100)
        ((1/100)/((r+4:ℕ):ℝ)) σi ∧
      MarkedReferenceCutFamilies (P.comap (markedVortexVertexEmbedding Q i)) (markedVortexPermutation Q π hpres i) d false false (γRich/2) (ρ*(1/100)/2) (ρ*((1/100)/(((r+4):ℕ):ℝ))/2) tstar σi ∧
      MarkedReferenceConfigurations r (P.comap (markedVortexVertexEmbedding Q i)) (markedVortexPermutation Q π hpres i) d false false β σi ∧
      MarkedLevelFiniteBalanceBound (P.comap (markedVortexVertexEmbedding Q i)) (markedVortexPermutation Q π hpres i) d (r+4)
        (markedVortexInnerVertices Q i) (markedVortexInnerHubs Q i)
        ((εBal+((r+4)+2:ℕ)*ζBal)*Fintype.card (markedVortexVertexType Q i)) σi Hi ∧
      MarkedCommonConfigurationsWithSpokes r (P.comap (markedVortexVertexEmbedding Q i)) (markedVortexPermutation Q π hpres i) d βCommon ζ σi Hi ∧
      MarkedLocalConfigurationsWithSpokes r (P.comap (markedVortexVertexEmbedding Q i)) (markedVortexPermutation Q π hpres i) d (markedVortexInnerVertices Q i)
        (markedLocalCycleCoefficient r γRich (tstar/2) kstar-(r+5:ℕ)*ζConfig)
        (markedLocalPathCoefficient r γRich (tstar/2) kstar-(r+4:ℕ)*ζConfig) σi Hi ∧
      MarkedLocalSpokeLoadsWithSpokes (P.comap (markedVortexVertexEmbedding Q i)) (markedVortexPermutation Q π hpres i) d (r+4) (2*(Fintype.card (markedVortexHubType Q i):ℝ)/ρ) (ρ*(1/100)/2) (ρ*((1/100)/(((r+4):ℕ):ℝ))/2) (1/100) (levelWeight i)
        (τLevel+εLoad+5*(((r+4):ℝ)+1)^4*(2*Bload/(ρ₀*sstar/(2*((r+4:ℕ):ℝ)))^(2*(r+4)+1))*1*ζLocal) σi Hi;
    let G:=fun i σi Hi=>C i σi Hi ∧
      MarkedLevelFiniteBalanceBound (P.comap (markedVortexVertexEmbedding Q i))
        (markedVortexPermutation Q π hpres i) d (r+4) (markedVortexInnerVertices Q i)
        (markedVortexInnerHubs Q i) (ηBal*(markedVortexInnerVertices Q i).card) σi Hi;
    let B:=fun i σi Hi=>G i σi Hi ∧
      MarkedLevelFiniteBalanceBound (P.comap (markedVortexVertexEmbedding Q i))
        (markedVortexPermutation Q π hpres i) d (r+4)
        (markedVortexDeeperVertices Q i) (markedVortexDeeperHubs Q i)
        ((εBal+((r+4)+2:ℕ)*ζBal)*(markedVortexDeeperVertices Q i).card) σi Hi;
    MarkedVortexCorrectionWithBothScaledBalances P π d r size aRob bRob eRob f₀ εRob ζCor z.1 H
      Dnat vsize βQ εQ Q L B ηBal εBal ζBal:=by
  obtain ⟨η₀,hη₀,εRef,εNbr,hεRef,hεNbr,N,hN⟩:=
    marked_long_common_event_correction_all_levels_balance r ρ₀ γRich kstar tstar ζCor εRob
      hρ₀ hγ hkstar htstar htstar1 hζCor
  refine ⟨η₀,hη₀,εRef,εNbr,hεRef,hεNbr,N,?_⟩
  intro n hnN hn1 U _ _ _ P π Dnat vsize βQ εQ Q hpres K d size a₀ b₀ e₀ aRob bRob eRob f₀ L hNbr hh F hF θ ρ hρlo hρhi hDlo hDhi hsize hεQ hsizePos hL hterminal hεQsmall β βCommon εAbs δRef ζ εBal ζBal ζNbr Bload εLoad ζLoad ζLocal ζConfig sstar τLevel levelWeight ηBal hηBal hbudget hεBal hζBal hdeepBase hdeepCor ζEvent hEventScale z hEvent hDeep hpmin hkmin H C G B
  have hcore:=hN n hnN hn1 U P π Dnat vsize βQ εQ Q hpres K d size a₀ b₀ e₀ aRob bRob eRob f₀ L hNbr hh F hF θ ρ hρlo hρhi hDlo hDhi hsize hεQ hsizePos hL hεQsmall β βCommon εAbs δRef ζ εBal ζBal ζNbr Bload εLoad ζLoad ζLocal ζConfig sstar τLevel levelWeight ηBal hηBal hbudget ζEvent hEventScale z hEvent hpmin hkmin
  exact marked_correction_all_deeper_balances P π d r size aRob bRob eRob f₀ εRob ζCor hζCor.le
    Dnat vsize βQ εQ Q L hpres hterminal hεQ hsizePos ηBal εBal ζBal hηBal hεBal hζBal hdeepBase hdeepCor
    false false z hDeep G hcore
end Oberwolfach
