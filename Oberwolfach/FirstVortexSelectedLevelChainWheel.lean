module

public import Oberwolfach.FirstVortexSelectedLevelChainAllRates
public import Oberwolfach.FirstVortexGeometricChainInputs
public import Oberwolfach.FirstVortexDensityParentLowerCard
public import Oberwolfach.FirstVortexSelectedParentProbabilities
public import Oberwolfach.FirstVortexExactParentCapBound
public import Oberwolfach.FirstVortexSelectedParentChainRates
public import Oberwolfach.LongAssignedSamplingRecipe

@[expose] public section
/-! Specialize the level-chain continuation to the actual parent event,
weights and sampling probabilities selected by the original hierarchy. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
set_option maxHeartbeats 120000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance selectedLevelWheelFin (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n
local instance (priority := 2000) selectedLevelWheelSix:DecidableEq (Fin 6):=instDecidableEqFin 6
local instance selectedLevelWheelArc {n:ℕ} (P:(Fin n×Fin n)→Prop):DecidableEq {e:Fin n×Fin n // P e}:=Classical.decEq _
attribute [local instance] partitionedDivisibleArcFinite partitionedDivisibleOrdFinite partitionedDivisibleMarkFinite

theorem first_vortex_selected_level_chain_wheel
    {n K:ℕ} [Nonempty (Fin n)] {U:Type} [Fintype U] [DecidableEq U]
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d r Dv mm:ℕ) (β ε:ℝ)
    (Vort:Vortex U P Dv β ε mm)
    (hπ:∀i v,π v∈Vort.extendedVertices i↔v∈Vort.extendedVertices i)
    (L:ℕ) (z:MarkedExpandedActualOutcome (U:=U) π d)
    (τ:RawMarkedOutcome (Fin n) U Bool Bool) (Hnew:Bool→Fin n→U→Prop)
    (active cLocal ζChange εStable:ℝ) (sizeStable eStable:ℕ)
    (hNext:FirstVortexNamedLevelChainContinuation P π d r Dv mm β ε Vort hπ L z τ Hnew active cLocal ζChange εStable sizeStable eStable)
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2) (θ:ℝ)
    (k₀ N NI Kgeom sizeParent aParent bParent eParent fParent:ℕ)
    (αRef ρ₀ δSelected εSelected ζSelected εAbsP ζAbsP βconfigP βCommonP εRef:ℝ)
    (βA βrec κ ξ thetaDeep ω xiDeep etaBal x eta deltaI hIcut:ℝ)
    (weightParent:∀i,(Fin (r+4+1)→markedVortexVertexType Vort i)→ℝ)
    (weightActive:∀i,(Fin (r+4+1)→↥((Finset.univ\markedVortexInnerVertices Vort i):Finset (markedVortexVertexType Vort i)))→ℝ)
    (hα:0<αRef) (hρ₀:0<ρ₀) (hρlo:ρ₀≤ initialIndexDensity U Dv)
    (hκ:0<κ) (hx:0<x) (hθDeep:0<thetaDeep) (heta:0<eta) (hd:2≤d) (hε:0<ε)
    (hxi0:0≤xiDeep)
    (hXiScale:(4*(Kgeom:ℝ)+((3*r+50:ℕ):ℝ))*xiDeep≤κ/2)
    (hTstar:1/(200*((r+4:ℕ):ℝ))≤(1/100)/(((r+4):ℕ):ℝ))
    (hDeepSource:∀ρ t:ℝ,ρ₀≤ρ→1/(200*((r+4:ℕ):ℝ))≤t→(1+2/ρ)*xiDeep≤t*ω/32)
    (δbase ζFixed ζCut cap₁ cap₂:ℝ)
    (hAt:FirstVortexActualParentAlignedAt r ρ₀ (1/100) (1/(200*((r+4:ℕ):ℝ)))
      (successorWeightUpper k₀ ((2*αRef)/4)) δbase ζFixed κ x thetaDeep eta ε etaBal cap₁ cap₂ βA
      (markedLocalCycleCoefficient r αRef ((1/(200*((r+4:ℕ):ℝ)))/2) (ρ₀/(800*((r+4:ℕ):ℝ))))
      (markedLocalPathCoefficient r αRef ((1/(200*((r+4:ℕ):ℝ)))/2) (ρ₀/(800*((r+4:ℕ):ℝ)))) δSelected εSelected ζSelected)
    (hβA:βA≤βCommonP) (hrec:βrec≤βA) (hεRef:εRef≤(κ/2)/4)
    (hL:L+1=Vort.length) (hβ:β≤1/4) (hIcut0:0≤hIcut) (hEtaBal:0<etaBal)
    (hδAlpha:deltaI≤αRef/32) (hδStar:deltaI≤(ρ₀/(800*((r+4:ℕ):ℝ)))/32)
    (hδTime:2*deltaI≤(1/(200*((r+4:ℕ):ℝ)))/8)
    (hIStar:2*hIcut≤αRef*(ρ₀/(800*((r+4:ℕ):ℝ)))/4)
    (hδbaseCut:δbase≤ζCut) (hCut:2*hIcut≤(1/(200*((r+4:ℕ):ℝ)))/8-ζCut)
    (hN:1≤N) (hn:0<n) (hU:Fintype.card U≤n) (hDpos:0<Dv) (hDlo:(n:ℝ)/2≤Dv)
    (hρhi:initialIndexDensity U Dv≤1) (hζChange:0≤ζChange) (hζFixed:0<ζFixed)
    (hCycleFixed:3*βA≤markedLocalCycleCoefficient r αRef ((1/(200*((r+4:ℕ):ℝ)))/2) (ρ₀/(800*((r+4:ℕ):ℝ)))-(r+5:ℕ)*ζFixed)
    (hPathFixed:3*βA≤markedLocalPathCoefficient r αRef ((1/(200*((r+4:ℕ):ℝ)))/2) (ρ₀/(800*((r+4:ℕ):ℝ)))-(r+4:ℕ)*ζFixed)
    (hβrecT:βrec≤(1/(200*((r+4:ℕ):ℝ)))/4)
    (hActiveCap:active≤Classical.choose (marked_vortex_active_transfer_from_parent_fixed_margin r (2*αRef)
      (1/(200*((r+4:ℕ):ℝ))) (ρ₀/(800*((r+4:ℕ):ℝ))) ζFixed eta
      (successorWeightUpper k₀ ((2*αRef)/4)) (ρ₀/(800*((r+4:ℕ):ℝ))) hζFixed heta
      (successorWeightConstants_pos k₀ ((2*αRef)/4) (by positivity)).2.le (by positivity) (by positivity)))
    (hLocalEq:cLocal=markedExplicitJointLocalCap (r+4) (r+12) etaBal x)
    (hParentCap:FirstVortexExactParentCapBound r αRef ρ₀ κ ζFixed thetaDeep
      (successorWeightUpper k₀ ((2*αRef)/4)) ζChange hα hρ₀)
    (γLevel σLevel:ℝ) (hγ:0<γLevel) (hσ:0<σLevel):
    let chain_k₀:=k₀
    let chain_α:=αRef
    let chain_ρ₀:=ρ₀
    let chain_sstar:=(1/100:ℝ)
    let chain_tstar:=(1/(200*((r+4:ℕ):ℝ)))
    let chain_kstar:=(ρ₀/(800*((r+4:ℕ):ℝ)))
    let chain_εAbs:=εAbsP
    let chain_ζAbs:=ζAbsP
    let chain_βconfig:=βconfigP
    let chain_βCommon:=βCommonP
    let chain_εref:=εRef
    let chain_δref:=κ/2
    let chain_tolRef:=δSelected
    let chain_ζActive:=δSelected
    let chain_τ:=δSelected
    let chain_tolLocal:=δSelected
    let chain_ζLocal:=δSelected
    let chain_τParent:=δSelected
    let chain_tolParent:=δSelected
    let chain_ζParent:=δSelected
    let chain_epsBal:=εSelected
    let chain_ζBal:=ζSelected
    let chain_ζCut:=δSelected
    let chain_ζCfg:=δSelected
    let chain_rowErr:=δSelected
    let chain_ζCommon:=δSelected
    let chain_ζWide:=δSelected
    let chain_ζRow:=δSelected
    let chain_size:=sizeParent
    let chain_a₀:=aParent
    let chain_b₀:=bParent
    let chain_e₀:=eParent
    let chain_f₀:=fParent
    let chain_s₀:=(1/100:ℝ)
    let chain_p:=(initialIndexDensity U Dv*(1/100:ℝ)/2)
    let chain_kval:=(initialIndexDensity U Dv*(1/100:ℝ)/2/((r+4:ℕ):ℝ))
    let chain_q:=(longAssignedIntervalProbability F hF K (r+4) θ)
    let chain_s:=(longAssignedSpokeProbability F hF K (r+4) θ)
    let chain_weightParent:=weightParent
    let chain_weight:=weightActive
    let chain_βA:=βA
    let chain_βrec:=βrec
    let chain_κ:=κ
    let chain_ξ:=ξ
    let chain_thetaDeep:=thetaDeep
    let chain_ω:=ω
    let chain_xiDeep:=xiDeep
    let chain_etaBal:=etaBal
    let chain_x:=x
    let chain_eta:=eta
    let chain_deltaI:=deltaI
    let chain_hIcut:=hIcut
    let chain_αParent:=2*αRef
    let chain_κold:=κ/2
    let chain_xold:=x/2
    let chain_thetaOld:=thetaDeep/2
    let chain_etaOld:=eta/2
    let chain_N:=N
    let chain_NI:=NI
    let chain_Kgeom:=Kgeom;
  ∀(chain_hParentWeight:∀i ≤ L,SuccessorSequenceWeightConditions (P.comap (markedVortexVertexEmbedding Vort i))
      (markedVortexPermutation Vort π hπ i) (3*d) (2*(Fintype.card (markedVortexHubType Vort i):ℝ)/initialIndexDensity U Dv)
      chain_τParent (successorWeightLower chain_k₀ (chain_αParent/4)) (successorWeightUpper chain_k₀ (chain_αParent/4)) (chain_weightParent i)),
  ∀(chain_hActiveWeight:∀i ≤ L+1,SuccessorSequenceWeightConditions (P.comap (markedVortexActiveVertexEmbedding Vort i))
      (markedVortexActivePermutation Vort π hπ i) (3*d)
      (2*((((Finset.univ\markedVortexInnerHubs Vort i):Finset (markedVortexHubType Vort i)).card):ℝ)/initialIndexDensity U Dv)
      chain_τ (successorWeightLower chain_k₀ (chain_αParent/4)) (successorWeightUpper chain_k₀ (chain_αParent/4)) (chain_weight i)),
  ∀(chain_hGeo:MarkedVortexGeometricRecordEvent Vort chain_α chain_ρ₀ chain_κ chain_hIcut chain_ξ chain_xiDeep chain_ω chain_x chain_N chain_NI L),
  ∀(chain_hGood:MarkedVortexParentRecordSmallerReferenceEvent r (r+12) chain_k₀ d chain_αParent chain_ρ₀ chain_sstar chain_tstar chain_kstar
      chain_εAbs chain_ζAbs chain_βconfig chain_βCommon chain_εref chain_δref chain_tolRef chain_ζActive chain_τ chain_tolLocal chain_ζLocal chain_τParent chain_tolParent chain_ζParent chain_epsBal chain_ζBal chain_ζCut chain_ζCfg chain_rowErr chain_ζCommon chain_ζWide chain_ζRow
      chain_size chain_a₀ chain_b₀ chain_e₀ chain_f₀ P Dv mm β ε Vort π hπ L chain_s₀ chain_p chain_kval chain_q chain_s false false chain_weightParent chain_weight (markedExpandedActualSelected π d z)),
        (∀rho omega t:ℝ,chain_ρ₀ ≤ rho → rho ≤ 1 → chain_ρ₀/8 ≤ omega → omega ≤ 1 → chain_tstar ≤ t → (r+4:ℝ)*t ≤ 1 → 
      chain_ρ₀/400 ≤ rho*(r+4:ℝ)*t/2 → chain_kstar ≤ rho*(r+4:ℝ)*t/2 → chain_kstar ≤ rho*t/2 → chain_kstar ≤ t → 
      ∀(Gamma Shade:Type) [Fintype Gamma] [Fintype Shade],
      ∀level:MarkedReferenceLevelData Gamma Shade r d chain_N chain_NI chain_Kgeom (chain_α/16) rho omega t chain_kstar chain_βA
        (successorWeightLower chain_k₀ (chain_α/4)) (successorWeightUpper chain_k₀ (chain_α/4))
        chain_κ chain_ξ chain_thetaDeep (chain_α/8) chain_ω (ε/4) chain_βrec (successorWeightLower chain_k₀ (chain_α/4)) (successorWeightUpper chain_k₀ (chain_α/4))
        chain_eta chain_x (chain_ρ₀/16) chain_hIcut chain_deltaI chain_etaBal,
      MarkedReferenceLevelStepProperty level γLevel σLevel) → ε≤εStable → 2*mm≤sizeStable →
    Classical.choose (marked_vortex_terminal_budget eStable γLevel σLevel hγ hσ)≤Fintype.card (Fin n) →
    let Earc:=MarkedSampleArc P π (3*d) (fun e=>τ (Sum.inl e)) false
    let Karc:=MarkedSampleArc P π (3*d) (fun e=>τ (Sum.inl e)) true;
    HasResourceDecomposition (fun W:MarkedWheel (fun e:Earc=>e.val.1) (fun e=>e.val.2)
      (fun e:Karc=>e.val.1) (fun e=>e.val.2) (r+4) π (3*d) (Hnew false) (Hnew true)=>markedWheelPhysicalResources W)
      (markedDecompositionTarget (markedPhysicalRimSet (fun e:Earc=>e.val.1) (fun e=>e.val.2)
        (fun e:Karc=>e.val.1) (fun e=>e.val.2) π) (Hnew false) (Hnew true)) :=by
  dsimp only []
  intro hParentWeight hActiveWeight hGeo hGood hSteps hStable hSize hBudget
  exact first_vortex_selected_level_chain_all_rates (K:=K) P π d r Dv mm β ε Vort hπ L z τ Hnew active cLocal ζChange εStable sizeStable eStable hNext
    F hF θ k₀ N NI Kgeom sizeParent aParent bParent eParent fParent αRef ρ₀ δSelected εSelected ζSelected εAbsP ζAbsP βconfigP βCommonP εRef
    βA βrec κ ξ thetaDeep ω xiDeep etaBal x eta deltaI hIcut weightParent weightActive hα hρ₀ hρlo hκ hx hθDeep heta hd hε hxi0 hXiScale hTstar hDeepSource
    δbase ζFixed ζCut cap₁ cap₂ hAt hβA hrec hεRef hL hβ hIcut0 hEtaBal hδAlpha hδStar hδTime hIStar hδbaseCut hCut
    hN hn hU hDpos hDlo hρhi hζChange hζFixed hCycleFixed hPathFixed hβrecT hActiveCap hLocalEq hParentCap
    hParentWeight hActiveWeight hGeo hGood γLevel σLevel hSteps hStable hSize hγ hσ hBudget
end Oberwolfach
