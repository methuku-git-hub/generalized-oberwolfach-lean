module

public import Oberwolfach.FirstVortexLevelChainAtParent
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
local instance selectedLevelChainFin (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n
local instance (priority := 2000) selectedLevelChainSix:DecidableEq (Fin 6):=instDecidableEqFin 6
local instance selectedLevelChainArc {n:ℕ} (P:(Fin n×Fin n)→Prop):DecidableEq {e:Fin n×Fin n // P e}:=Classical.decEq _
attribute [local instance] partitionedDivisibleArcFinite partitionedDivisibleOrdFinite partitionedDivisibleMarkFinite

theorem first_vortex_level_chain_at_selected_parent
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
    (weightActive:∀i,(Fin (r+4+1)→↥((Finset.univ\markedVortexInnerVertices Vort i):Finset (markedVortexVertexType Vort i)))→ℝ):
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
  ∀(chain_hα:0<chain_α),
  ∀(chain_hαle:chain_α ≤ chain_αParent),
  ∀(chain_hκle:chain_κold ≤ chain_κ),
  ∀(chain_hxle:chain_xold ≤ chain_x),
  ∀(chain_hθle:chain_thetaOld ≤ chain_thetaDeep),
  ∀(chain_hηle:chain_etaOld ≤ chain_eta),
  ∀(chain_hρ:0  ≤  initialIndexDensity U Dv),
  ∀(chain_hs₀:0 ≤ chain_s₀),
  ∀(chain_hd:1 ≤ d),
  ∀(chain_he:0 ≤ ε),
  ∀(chain_hp:chain_p=initialIndexDensity U Dv*chain_s₀/2),
  ∀(chain_hk:chain_kval=chain_p/(((r+4):ℕ):ℝ)),
  ∀(chain_hq0:∀u,chain_q u false=chain_s₀/(((r+4):ℕ):ℝ)),
  ∀(chain_hs0:∀u,chain_s u false=chain_s₀),
  ∀(chain_hXi0:0 ≤ chain_xiDeep),
  ∀(chain_hXiScale:(4*chain_Kgeom+3*r+50:ℝ)*chain_xiDeep ≤ chain_κ/2),
  ∀(chain_hDeepGap:(1+2/initialIndexDensity U Dv)*chain_xiDeep ≤ (chain_s₀/(((r+4):ℕ):ℝ))*chain_ω/32),
  ∀(chain_hβA:chain_βA ≤ chain_βCommon),
  ∀(chain_hζκ:chain_ζCommon ≤ chain_κold/4),
  ∀(chain_hC:3*chain_βA ≤ markedLocalCycleCoefficient r (chain_αParent/2) (chain_tstar/2) chain_kstar-(r+5:ℕ)*chain_ζCfg),
  ∀(chain_hP:3*chain_βA ≤ markedLocalPathCoefficient r (chain_αParent/2) (chain_tstar/2) chain_kstar-(r+4:ℕ)*chain_ζCfg),
  ∀(chain_hrec:chain_βrec ≤ chain_βA),
  ∀(chain_herr:chain_tolRef+(r+12:ℕ)*chain_ζActive ≤ chain_κold/4),
  ∀(chain_hζActiveK:chain_ζActive ≤ chain_κold/4),
  ∀(chain_hεeq:chain_εref ≤ chain_κold/4),
  ∀(chain_hδeq:chain_δref=chain_κold),
  ∀(chain_hpot:chain_τParent+chain_tolParent+11*(((r+4:ℕ):ℝ)+1)^4*(2*successorWeightUpper chain_k₀ (chain_αParent/4)/(chain_ρ₀*chain_sstar/(2*((r+4:ℕ):ℝ)))^(2*(r+4)+1))*chain_ζParent ≤ chain_κold/4),
  ∀(chain_hdeep:chain_τParent+chain_tolParent+11*(((r+4:ℕ):ℝ)+1)^4*(2*successorWeightUpper chain_k₀ (chain_αParent/4)/(chain_ρ₀*chain_sstar/(2*((r+4:ℕ):ℝ)))^(2*(r+4)+1))*chain_ζParent ≤ chain_thetaOld/4),
  ∀(chain_hxold:0 ≤ chain_xold),
  ∀(chain_hbal:chain_epsBal+((r+4)+2:ℕ)*chain_ζBal ≤ chain_etaBal),
  ∀(chain_hmargin:chain_epsBal+((r+4)+2:ℕ)*chain_ζBal ≤ chain_xold/2),
  ∀(chain_hterminal:L+1=Vort.length),
  ∀(chain_hrowmargin:chain_rowErr+chain_ζRow ≤ (chain_s₀/((r+4:ℕ):ℝ))/8),
  ∀(chain_hloadmargin:chain_τ+chain_tolLocal+5*(((r+4:ℕ):ℝ)+1)^4*(2*successorWeightUpper chain_k₀ (chain_αParent/4)/(chain_ρ₀*chain_sstar/(2*((r+4:ℕ):ℝ)))^(2*(r+4)+1))*(4/ε)*chain_ζWide ≤ chain_etaOld/4),
  ∀(chain_hbquarter:β ≤ 1/4),
  ∀(chain_hh:0 ≤ chain_hIcut),
  ∀(chain_hδα:chain_deltaI ≤ (chain_αParent/2)/32),
  ∀(chain_hδstar:chain_deltaI ≤ chain_kstar/32),
  ∀(chain_hδt:2*chain_deltaI ≤ chain_tstar/8),
  ∀(chain_hhstar:2*chain_hIcut ≤ (chain_αParent/2)*chain_kstar/4),
  ∀(chain_hhs:2*chain_hIcut ≤ chain_tstar/8-chain_ζCut),
  ∀(chain_hEndpoint:chain_tolRef+(r+12:ℕ)*chain_ζActive ≤ chain_xold/2),
  ∀(chain_iota:ℝ),
  ∀(chain_hηBalPos:0<chain_etaBal),
  ∀(chain_hxPos:0<chain_x),
  ∀(chain_hiota:0 < chain_iota),
  ∀(chain_hζchange:0 ≤ ζChange),
  ∀(chain_hepsBal:0 ≤ chain_epsBal),
  ∀(chain_hζBal:0 ≤ chain_ζBal),
  ∀(chain_hBalRelative:chain_epsBal+((r+4)+2:ℕ)*chain_ζBal ≤ chain_etaBal/2),
  ∀(chain_hBalAmbient:chain_epsBal+((r+4)+2:ℕ)*chain_ζBal ≤ chain_x/4),
  ∀(chain_hsize:chain_iota*Fintype.card (markedVortexVertexType Vort 0) ≤ ((markedVortexInnerVertices Vort 0).card:ℝ)),
  ∀(chain_hn:0<Fintype.card (Fin n)),
  ∀(chain_hu:Fintype.card U ≤ Fintype.card (Fin n)),
  ∀(chain_pstar:ℝ),
  ∀(chain_hpstar:0<chain_pstar),
  ∀(chain_hplo:chain_pstar ≤ chain_p),
  ∀(chain_hklo:chain_pstar ≤ chain_kval),
  ∀(chain_hslo:chain_pstar ≤ chain_s₀),
  ∀(chain_hp1:chain_p ≤ 1),
  ∀(chain_hk1:chain_kval ≤ 1),
  ∀(chain_hs1:chain_s₀ ≤ 1),
  ∀(chain_hDlo:(Fintype.card (markedVortexVertexType Vort 0):ℝ)/2 ≤ 2*(Fintype.card (markedVortexHubType Vort 0):ℝ)/initialIndexDensity U Dv),
  ∀(chain_hDhi:2*(Fintype.card (markedVortexHubType Vort 0):ℝ)/initialIndexDensity U Dv ≤ 2*Fintype.card (markedVortexVertexType Vort 0)),
  ∀(chain_hboundaryHalf:chain_xold ≤ chain_x/2),
  ∀(chain_hκPos:0<chain_κ),
  ∀(chain_ωParent:ℝ),
  ∀(chain_hωPos:0<chain_ωParent),
  ∀(chain_plo chain_klo:ℝ),
  ∀(chain_hploPos:0<chain_plo),
  ∀(chain_hkloPos:0<chain_klo),
  ∀(chain_hαeq:chain_αParent=2*chain_α),
  ∀(chain_hκoldEq:chain_κold=chain_κ/2),
  ∀(chain_hUlower:chain_ωParent*Fintype.card (Fin n) ≤ (Fintype.card U:ℝ)),
  ∀(chain_hpLower:chain_plo ≤ chain_p),
  ∀(chain_hkLower:chain_klo ≤ chain_kval),
  ∀(chain_ζFixed:ℝ),
  ∀(chain_hζFixed:0<chain_ζFixed),
  ∀(chain_hCfg:2*chain_ζCfg ≤ chain_ζFixed),
  ∀(chain_hθDeepPos:0<chain_thetaDeep),
  ∀(chain_hθoldHalf:chain_thetaOld ≤ chain_thetaDeep/2),
  ∀(chain_hcycleDeep:3*chain_βA ≤ markedLocalCycleCoefficient r (chain_αParent/2) (chain_tstar/2) chain_kstar-(r+5:ℕ)*chain_ζFixed),
  ∀(chain_hpathDeep:3*chain_βA ≤ markedLocalPathCoefficient r (chain_αParent/2) (chain_tstar/2) chain_kstar-(r+4:ℕ)*chain_ζFixed),
  ∀(chain_hηPos:0<chain_eta),
  ∀(chain_htstarPos:0<chain_tstar),
  ∀(chain_hnactive:0<Fintype.card ↥((Finset.univ\markedVortexInnerVertices Vort 1):Finset (markedVortexVertexType Vort 1))),
  ∀(chain_hβrect:chain_βrec ≤ (chain_s₀/((r+4:ℕ):ℝ))/4),
  ∀(chain_htt:chain_tstar ≤ chain_s₀/((r+4:ℕ):ℝ)),
  ∀(chain_hactiveErr:chain_τ+chain_tolLocal+5*(((r+4:ℕ):ℝ)+1)^4*(2*successorWeightUpper chain_k₀ (chain_αParent/4)/(chain_ρ₀*chain_sstar/(2*((r+4:ℕ):ℝ)))^(2*(r+4)+1))*(4/ε)*chain_ζWide ≤ chain_eta/8),
  ∀(chain_hactiveRow:chain_rowErr+chain_ζRow ≤ chain_tstar/16),
  ∀(chain_hDactiveLo:(Fintype.card ↥((Finset.univ\markedVortexInnerVertices Vort 1):Finset (markedVortexVertexType Vort 1)):ℝ)/2 ≤ 
      2*((((Finset.univ\markedVortexInnerHubs Vort 1):Finset (markedVortexHubType Vort 1)).card):ℝ)/initialIndexDensity U Dv),
  ∀(chain_hDactiveHi:2*((((Finset.univ\markedVortexInnerHubs Vort 1):Finset (markedVortexHubType Vort 1)).card):ℝ)/initialIndexDensity U Dv ≤ 
      2*Fintype.card ↥((Finset.univ\markedVortexInnerVertices Vort 1):Finset (markedVortexVertexType Vort 1))),
  ∀(chain_hρ₀Pos:0<chain_ρ₀),
  ∀(chain_hρlo:chain_ρ₀ ≤ initialIndexDensity U Dv),
  ∀(chain_hρhi:initialIndexDensity U Dv ≤ 1),
  ∀(chain_htstarCap:chain_tstar ≤ (1/100)/(((r+4):ℕ):ℝ)),
  ∀(chain_hkstarPos:0<chain_kstar),
  ∀(chain_hkstarCap:chain_kstar ≤ initialIndexDensity U Dv*((1/100)/(((r+4):ℕ):ℝ))/2),
  ∀(chain_hs₀Eq:chain_s₀=(1/100:ℝ)),
  ∀(chain_hζactiveCap:active≤Classical.choose (marked_vortex_active_transfer_from_parent_fixed_margin r chain_αParent chain_tstar chain_kstar chain_ζFixed chain_eta
      (successorWeightUpper chain_k₀ (chain_αParent/4)) chain_pstar chain_hζFixed chain_hηPos
      (successorWeightConstants_pos chain_k₀ (chain_αParent/4) (by have hh:=lt_of_lt_of_le chain_hα chain_hαle;positivity)).2.le chain_hpstar chain_htstarPos)),
  ∀(chain_hcLocalEq:cLocal=markedExplicitJointLocalCap (r+4) (r+12) chain_etaBal chain_x),
  ∀(chain_hζFinal:ζChange ≤ Classical.choose (marked_vortex_fixed_margin_local_correction_cap r chain_κ chain_αParent chain_ωParent chain_plo chain_klo chain_tstar chain_kstar chain_ζFixed chain_thetaDeep (1:ℝ)
      (successorWeightUpper chain_k₀ (chain_αParent/4)) chain_pstar (1:ℝ) (1:ℝ) (1:ℝ)
      chain_hκPos (lt_of_lt_of_le chain_hα chain_hαle) chain_hωPos chain_hploPos chain_hkloPos chain_htstarPos chain_hζFixed chain_hθDeepPos (by norm_num)
      (successorWeightConstants_pos chain_k₀ (chain_αParent/4) (by have chain_hh:=lt_of_lt_of_le chain_hα chain_hαle;positivity)).2.le
      chain_hpstar (by norm_num) (by norm_num) (by norm_num))),
        ∀(γLevel σLevel:ℝ), (∀rho omega t:ℝ,chain_ρ₀ ≤ rho → rho ≤ 1 → chain_ρ₀/8 ≤ omega → omega ≤ 1 → chain_tstar ≤ t → (r+4:ℝ)*t ≤ 1 → 
      chain_ρ₀/400 ≤ rho*(r+4:ℝ)*t/2 → chain_kstar ≤ rho*(r+4:ℝ)*t/2 → chain_kstar ≤ rho*t/2 → chain_kstar ≤ t → 
      ∀(Gamma Shade:Type) [Fintype Gamma] [Fintype Shade],
      ∀level:MarkedReferenceLevelData Gamma Shade r d chain_N chain_NI chain_Kgeom (chain_α/16) rho omega t chain_kstar chain_βA
        (successorWeightLower chain_k₀ (chain_α/4)) (successorWeightUpper chain_k₀ (chain_α/4))
        chain_κ chain_ξ chain_thetaDeep (chain_α/8) chain_ω (ε/4) chain_βrec (successorWeightLower chain_k₀ (chain_α/4)) (successorWeightUpper chain_k₀ (chain_α/4))
        chain_eta chain_x (chain_ρ₀/16) chain_hIcut chain_deltaI chain_etaBal,
      MarkedReferenceLevelStepProperty level γLevel σLevel) → ε≤εStable → 2*mm≤sizeStable →
    ∀(hγ:0<γLevel) (hσ:0<σLevel),
    Classical.choose (marked_vortex_terminal_budget eStable γLevel σLevel hγ hσ)≤Fintype.card (Fin n) →
    let Earc:=MarkedSampleArc P π (3*d) (fun e=>τ (Sum.inl e)) false
    let Karc:=MarkedSampleArc P π (3*d) (fun e=>τ (Sum.inl e)) true;
    HasResourceDecomposition (fun W:MarkedWheel (fun e:Earc=>e.val.1) (fun e=>e.val.2)
      (fun e:Karc=>e.val.1) (fun e=>e.val.2) (r+4) π (3*d) (Hnew false) (Hnew true)=>markedWheelPhysicalResources W)
      (markedDecompositionTarget (markedPhysicalRimSet (fun e:Earc=>e.val.1) (fun e=>e.val.2)
        (fun e:Karc=>e.val.1) (fun e=>e.val.2) π) (Hnew false) (Hnew true)) :=by
  dsimp only []
  intro hParentWeight hActiveWeight hGeo hGood
  exact first_vortex_level_chain_at_parent P π d r Dv mm β ε Vort hπ L z τ Hnew active cLocal ζChange εStable sizeStable eStable hNext
    (k₀) (αRef) (ρ₀) ((1/100:ℝ)) ((1/(200*((r+4:ℕ):ℝ)))) ((ρ₀/(800*((r+4:ℕ):ℝ)))) (εAbsP) (ζAbsP) (βconfigP) (βCommonP) (εRef) (κ/2) (δSelected) (δSelected) (δSelected) (δSelected) (δSelected) (δSelected) (δSelected) (δSelected) (εSelected) (ζSelected) (δSelected) (δSelected) (δSelected) (δSelected) (δSelected) (δSelected) (sizeParent) (aParent) (bParent) (eParent) (fParent) ((1/100:ℝ)) ((initialIndexDensity U Dv*(1/100:ℝ)/2)) ((initialIndexDensity U Dv*(1/100:ℝ)/2/((r+4:ℕ):ℝ))) ((longAssignedIntervalProbability F hF K (r+4) θ)) ((longAssignedSpokeProbability F hF K (r+4) θ)) (weightParent) (weightActive) (βA) (βrec) (κ) (ξ) (thetaDeep) (ω) (xiDeep) (etaBal) (x) (eta) (deltaI) (hIcut) (2*αRef) (κ/2) (x/2) (thetaDeep/2) (eta/2) (N) (NI) (Kgeom) hParentWeight hActiveWeight hGeo hGood
end Oberwolfach
