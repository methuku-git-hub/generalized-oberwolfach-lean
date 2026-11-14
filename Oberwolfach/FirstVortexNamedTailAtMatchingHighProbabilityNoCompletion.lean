module

public import Oberwolfach.LongExpandedGlobalTests
public import Oberwolfach.LongCorrectionUniversalMatchingReserveEvent
public import Oberwolfach.FirstVortexNamedTailAtMatchingSelectedLossNoCompletion
public import Oberwolfach.LongSelectorCommonFailureChoiceArbitrary

@[expose] public section
/-! Choose the common positive probability and seven failure budgets while
retaining the selected correction loss and joint host thresholds. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
set_option maxHeartbeats 120000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
attribute [local instance] referenceWitnessFinDecidable
attribute [local instance 100000] Finset.decidableDforallFinset

def FirstVortexNamedTailAtMatchingHighProbabilityNoCompletion
    (r h k₀ Qpow:ℕ) (αRef sstar ω γRich tstar kstar ρ₀:ℝ) (hρ₀:0<ρ₀)
    (β βCommon εAbs εRob ζRob δAbs εAbsP ζAbsP δAbsP βconfigP βCommonP εStable ζStable capStable:ℝ)
    (εQ:ℝ) (hεQ:0<εQ) (hεQ1:εQ<1/4) (hεQAbs:εQ≤εAbs) (hεQRob:εQ≤εRob)
      (hεQsmall:εQ≤min ((γRich/2)*kstar) tstar/128)
    (K:ℕ) (hK3:3≤K) (hm:7≤(r+4))
    (θ:ℝ) (hθpos:0<θ) (hθ:θ≤1/100)
    (htstarBound:tstar≤(1/100)/(((r+4):ℕ):ℝ))
    (d:ℕ) (hd:2≤d) (cBoundary:ℝ) (hcBoundary:0<cBoundary) (hspacing:4/(d:ℝ)≤cBoundary) (hcut:(1/((((r+4):ℕ):ℝ)+1))/(d:ℝ)≤θ)
    (BM:ℝ) (hBM:0<BM) (BO:Fin K→ℝ) (hBO:∀i,0<BO i)
    (lam:ℝ) (hlam:0<lam) (hlamθ:lam≤θ) (ξCap:ℝ) (hξCap:0<ξCap)
    (α cLocal chainCap active lamAssign δglobal δold δlocal bmatch ζret ηBalance κPack βfinal cap rho eta δLoss εInner:ℝ) (hζret:0<ζret)
    (gammaStep sigmaStep:ℝ):Prop :=
    let ni:=@longPaddedSeedExponent K
    let hni:=@long_padded_seed_exponent_positive K
    let hpadded:=@long_padded_seed_length_eq_exponent K
    let pstar₀:=min (1/4:ℝ) (min (ρ₀/8) (ρ₀/(6*((((r+4):ℕ):ℝ)+1))))
    let BMseed₀:=2*BM/pstar₀^(2*(r+4)+1)
    let BOseed₀:=fun i=>2*BO i/pstar₀^(2*(ni i+2))
    let Kpair₀:=1+((((r+4):ℕ):ℝ)+1)^4*BMseed₀+∑i:Fin K,((ni i:ℝ)+2)^3*BOseed₀ i
    let C₀:=10*(((((r+4):ℕ):ℝ)+1)^4*BMseed₀+∑i:Fin K,((ni i:ℝ)+2)^4*BOseed₀ i)
    ∃epsOrd:ℝ,0<epsOrd ∧ epsOrd≤1 ∧ 3*epsOrd≤lam*(θ/(100*(K:ℝ)^2)) ∧
    let alphaOrd:=min (lam/(10*(d:ℝ))) (θ/(200*(K:ℝ)^2))
    let γOrd:=min (epsOrd/2) (min (1/2:ℝ) (min (lam/(10*(d:ℝ))) (lam/10)))
    0<alphaOrd ∧ alphaOrd≤θ/(200*(K:ℝ)^2) ∧ 0<γOrd ∧ γOrd≤epsOrd ∧
    let ni:=@longPaddedSeedExponent K
    let hni:=@long_padded_seed_exponent_positive K
    let hpadded:=@long_padded_seed_length_eq_exponent K
    let pstar₀:=min (1/4:ℝ) (min (ρ₀/8) (ρ₀/(6*(((r+4:ℕ):ℝ)+1))))
    let BMseed₀:=2*BM/pstar₀^(2*(r+4)+1)
    let BOseed₀:=fun i=>2*BO i/pstar₀^(2*(ni i+2))
    let Kpair₀:=1+(((r+4:ℕ):ℝ)+1)^4*BMseed₀+∑i:Fin K,((ni i:ℝ)+2)^3*BOseed₀ i
    let C₀:=10*((((r+4:ℕ):ℝ)+1)^4*BMseed₀+∑i:Fin K,((ni i:ℝ)+2)^4*BOseed₀ i)
    ∃ηSeed:ℝ,0<ηSeed ∧ ∃tSeed τSeed ΔSeed ξSeed:ℝ,0<tSeed ∧ 0<τSeed ∧ τSeed≤1/16 ∧ 0<ΔSeed ∧ 0<ξSeed ∧ 4*ξSeed≤epsOrd/2 ∧
    ∃ηOrd:ℝ,0<ηOrd ∧ ∃tOrd τOrd ΔOrd ξOrd:ℝ,0<tOrd ∧ 0<τOrd ∧ τOrd≤1/16 ∧ 0<ΔOrd ∧ 0<ξOrd ∧ 4*ξOrd≤epsOrd/2 ∧
    ∃lamOrd ηListOrd ζOrd:ℝ,0<lamOrd ∧ 0<ηListOrd ∧ 0<ζOrd ∧ ζOrd≤ΔOrd ∧ ζOrd≤epsOrd/8 ∧ ζOrd≤ΔSeed ∧
    ∃NListOrd:ℕ,
      (∀n≥NListOrd,
        let βList:ℝ:=(min (2*αRef) (1/4:ℝ))*(ρ₀/200)^2*(1/100)/16;
        (n:ℝ)^(3/4:ℝ)+2*(2*((3*d:ℕ):ℝ)+1)≤(2*αRef)*(ρ₀/200)^2*n ∧
        βList*n+(n:ℝ)^(3/4:ℝ)≤(2*αRef)*(ρ₀/200)^2*n*(1/100:ℝ) ∧
        (lamOrd+2*ζOrd)*n≤βList*n ∧ (n:ℝ)^(3/4:ℝ)≤ηListOrd*n ∧
        ∀(m:ℕ) (εQ:ℝ),εQ≤βList/32→1/(100*(m:ℝ))≤βList/16→
          βList/2+εQ+1/(100*(m:ℝ))+ηListOrd≤lamOrd) ∧
    ∃cOrd ξClassOrd:ℝ,0<cOrd ∧ 0<ξClassOrd ∧ ξClassOrd≤ξCap ∧
      ξClassOrd≤min (min (cOrd/4) ((ζOrd/4)/16)) ((2*αRef)*(ρ₀/200)^2/4) ∧
      ζOrd/2+ξClassOrd+ζOrd/4≤ζOrd ∧
      LongEveryClassOrientationCap (2*αRef) ρ₀ (ζOrd/4) cOrd ∧
    (∃hδ:0<δglobal,∃hθ':0<θ,∃hθδ:10*θ≤δglobal,∃hspacing':1/(d:ℝ)≤θ/1024,
      FirstVortexActualCallerNumericResult r d K ρ₀ cap rho eta δLoss εInner δglobal
        εQ cLocal active θ lamAssign lam epsOrd ζOrd ξClassOrd ζret ηBalance κPack βfinal hδ hθ' hθδ hspacing' ∧
      ∀ξPrep:ℝ,0≤ξPrep→4*ξPrep≤epsOrd/2→∀e:ℕ,∃Nchain:ℕ,
      FirstVortexFixedTerminalChainAt α lam lamAssign εQ δold δlocal δglobal θ epsOrd ξPrep ρ₀ bmatch ξClassOrd ζret d K r ζOrd rho δLoss εInner eta e
        cap chainCap active ηBalance κPack βfinal Nchain) ∧
    ∃eps:ℝ,0<eps ∧ eps≤1 ∧ 3*eps≤(min lam epsOrd)*(θ/(100*(K:ℝ)^2)) ∧ eps≤epsOrd ∧
    let alpha:=min ((min lam epsOrd)/(10*(d:ℝ))) (θ/(200*(K:ℝ)^2))
    let γ:=min (eps/2) (min (1/2:ℝ) (min ((min lam epsOrd)/(10*(d:ℝ))) ((min lam epsOrd)/10)))
    0<alpha ∧ alpha≤θ/(200*(K:ℝ)^2) ∧ 0<γ ∧ γ≤eps ∧
    ∀χTarget:ℝ,0<χTarget→
    ∃ε₀ ηEvent:ℝ,0<ε₀ ∧ ε₀<1 ∧ 0<ηEvent ∧ 0<1-(36*(ε₀+6*ηEvent)+ηEvent) ∧
      36*(ε₀+6*ηEvent)+ηEvent≤χTarget ∧
    ∀ (αHost rPart:ℝ) (hαHost:0<αHost) (hrPart:0<rPart)
      (hεQHost:εQ≤αHost/100000),
    ∃ εExtra:ℝ,0<εExtra ∧ (0<ε₀→4*εExtra≤ε₀) ∧
    ∃gammaLoss sigmaLoss extra:ℝ,0<gammaLoss ∧ 0<sigmaLoss ∧ 0<extra ∧ gammaLoss≤ζOrd/2 ∧
      gammaLoss+extra≤gammaStep ∧ sigmaLoss+extra≤sigmaStep ∧
    ∀ (κmax κauxCap ζCap:ℝ),0<κmax→0<κauxCap→0<ζCap →
    ∃ ζCorr ξCorr η₀ κ εRef εNbr:ℝ,0<ζCorr ∧ ζCorr≤ζRob ∧ ζCorr≤ζCap ∧ 0<ξCorr ∧
      16*((((r+4):ℕ):ℝ)+1)*ξCorr≤ζCorr ∧
      (∀n:ℕ,6*(8*((((r+4):ℕ):ℝ)+1)*ξCorr*n)≤min (gammaLoss*n) (sigmaLoss*n)) ∧
      0<η₀ ∧ 0<κ ∧ κ≤κmax ∧ κ≤κauxCap ∧ εRef=κ/4 ∧ εRef≤κmax/4 ∧ 0<εRef ∧ 0<εNbr ∧ εNbr≤κauxCap ∧
    ∃χ χCommon χBal χNbr χLoad χLocal χConfig:ℝ,
      0<χ ∧ 0<χCommon ∧ 0<χBal ∧ 0<χNbr ∧ 0<χLoad ∧ 0<χLocal ∧ 0<χConfig ∧
      χ+χCommon+χBal+2*χNbr+χLoad+χLocal+χConfig+εExtra<ε₀ ∧
    ∀ (Qreal pstarRef ζ εBal ζBal ζNbr εLoad ζLoad ζLocal ζConfig τLevel:ℝ)
    (hpstarRef:0<pstarRef) (hζ:0<ζ) (hεBal:0<εBal) (hζBal:0<ζBal)
    (hζNbr:0<ζNbr) (hεLoad:0<εLoad) (hζLoad:0<ζLoad) (hζLocal:0<ζLocal)
    (hζConfig:0<ζConfig) (hτLevel:0<τLevel) (hQreal:0<Qreal)
    (hNbr:ℕ) (hhNbr:1≤hNbr) (hpstarBound:4*(((r+4):ℕ):ℝ)*pstarRef≤ρ₀*(1/100)),
    ∀ δparent:ℝ,0<δparent→∃βmax:ℝ,0<βmax ∧ ∀βQ:ℝ,0≤βQ→βQ≤1/4→βQ≤αRef/4→βQ≤βmax→βQ≤εBal/4→βQ≤εRef/4→
    ∃MLevel:ℕ,1≤MLevel ∧
    ∃mLevel:ℕ,1≤mLevel ∧ ∃η:ℝ,0<η ∧ ∃t₀ τ₀ Δ ξ:ℝ,0<t₀ ∧ 0<τ₀ ∧ τ₀≤1/16 ∧ 0<Δ ∧ 0<ξ ∧ 4*ξ≤eps/2 ∧
    ∃ξResidual:ℝ,0≤ξResidual ∧ 4*ξResidual≤epsOrd/2 ∧ ζOrd≤ξResidual ∧ ξ≤ξResidual ∧ ξSeed≤ξResidual ∧
      (∀n:ℕ,ζOrd*n≤ξResidual*n ∧ ξ*n≤ξResidual*n ∧ ξSeed*n≤ξResidual*n) ∧
    ∃ζList:ℝ,0<ζList ∧ ζList≤Δ ∧ ∃N:ℕ,
    ∀size:ℕ,∃a₀ b₀ e₀ aRob bRob eRob aParent bParent eParent aStable bStable eStable:ℕ,
    ∃Nchain:ℕ,FirstVortexFixedTerminalChainAt α lam lamAssign εQ δold δlocal δglobal θ epsOrd ξResidual ρ₀ bmatch ξClassOrd ζret d K r ζOrd rho δLoss εInner eta eRob
      cap chainCap active ηBalance κPack βfinal Nchain ∧
    ∃Nprep:ℕ,FirstVortexPreparedBoundarySolverAt r d K Nprep α εQ δlocal δglobal θ epsOrd ξResidual ρ₀ bmatch ξClassOrd ζret lamAssign lam ∧
    ∀f₀ B:ℕ,eRob≤B→∃NHost:ℕ,Nchain≤NHost ∧ Nprep≤NHost ∧
      (∀n:ℕ,NHost≤n→(eRob:ℝ)≤extra*n) ∧
    ∀n:ℕ,∀hn:max (max N NHost) 1≤n,∀(U:Type) [Fintype U] [DecidableEq U],
    ∀(F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (Allowed:Set ℕ) (hAllowed:∀u,AllowedCycleLengths (F u) Allowed)
    (ρ D:ℝ) (hρlo:ρ₀≤ρ) (hρ1:ρ≤1) (hD:0<D)
    (hsize:ρ*D=2*Fintype.card U)
    (hclass:∀u,factorPreparationClass (F u) K=none)
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (τ A:ℝ) (weight:(Fin ((r+4)+1)→Fin n)→ℝ)
    (hw:SuccessorSequenceWeightConditions P π (3*d) D τ A BM weight)
    (hDlo:(n:ℝ)/2≤D) (hDhi:D≤2*n)
    (w:∀i,OrdinaryCycle P (ni i+2)→ℝ) (hw0:∀i C,0≤w i C)
    (hwupper:∀i C,w i C≤BO i/(n:ℝ)^(ni i))
    (huv:Fintype.card U≤n)
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (εHost:ℝ)
    (he:∀i∈longRetainedSeedIndices F hF K θ,∀x y,
      (∑C:OrdinaryCycle P (ni i+2),if C.val.val.Adj x y then w i C else 0)=if P.Adj x y then 1 else 0)
    (hdeg:∀x,|(P.degree x:ℝ)-D|≤εHost*n)
    (hbudgetV:∀i∈longRetainedSeedIndices F hF K θ,
      6*((ni i+2:ℕ):ℝ)^4*BO i*(2*(3*d))+εHost*n≤τ*D)
    (hbudgetE:∀i∈longRetainedSeedIndices F hF K θ,
      5*((ni i+2:ℕ):ℝ)^4*BO i*(2*(3*d))/n≤τ)
    (hτnonneg:0≤τ) (hτbound:τ≤min τ₀ (min τSeed τOrd)),
    εHost≤δAbs →
    ∀ (Dnat vsize:ℕ), (Dnat:ℝ)=D → ρ=initialIndexDensity U Dnat →
      P.IsRegularOfDegree Dnat → (1/2+2*αRef)*n≤D → mLevel≤vsize → vsize≤n →
    ∀ (Q:Vortex U P Dnat βQ εQ vsize)
      (hAbsSize:2*vsize≤size)
      (hεQcap:εQ≤((min (2*αRef) (1/4:ℝ))*(ρ₀/200)^2*(1/100)/16)/32)
      (htrim:1/(100*((r+4:ℕ):ℝ))≤((min (2*αRef) (1/4:ℝ))*(ρ₀/200)^2*(1/100)/16)/16)
      (hpres:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
      (L:ℕ),L<Q.length →
    kstar≤ρ*(1/100)/2 → kstar≤ρ*((1/100)/(((r+4):ℕ):ℝ))/2 → tstar≤(1/100)/(((r+4):ℕ):ℝ) →
      Even Dnat → (1/2+αHost)*(n:ℝ)≤D →
    let W:=markedVortexVertexType Q
    let Z:=markedVortexHubType Q
    let Hdom:=Z
    let fV:=markedVortexVertexEmbedding Q
    let gV:=markedVortexHubEmbedding Q
    let ρi:=markedVortexPermutation Q π hpres
    let Aset:=markedVortexInnerVertices Q
    let Bset:=markedVortexInnerHubs Q
    let Scale:=fun i=>Fintype.card (W i)
    let Dbal:=fun i=>2*((Bset i).card:ℝ)/ρ
    let Dlevel:=fun i=>2*(Fintype.card (Z i):ℝ)/ρ
    let bdom:=fun i=>Function.Embedding.refl (Z i)
    let Dload:=Dlevel
    let Aload:=successorWeightLower k₀ ((2*αRef)/4)
    let Bload:=successorWeightUpper k₀ ((2*αRef)/4)
    let AP:∀i,Finset (W i):=fun i=>Finset.univ\markedVortexInnerVertices Q i
    let BP:∀i,Finset (Z i):=fun i=>Finset.univ\markedVortexInnerHubs Q i
    let XP:=fun i=>↥(AP i)
    let fActiveP:=fun i=>markedVortexActiveVertexEmbedding Q i
    let gActiveP:=fun i=>markedVortexActiveHubEmbedding Q i
    let ρActiveP:=fun i=>markedVortexActivePermutation Q π hpres i
    let DactiveP:=fun i=>2*((BP i).card:ℝ)/initialIndexDensity U Dnat
    let pstarLocalP:=ρ₀*sstar/(2*((r+4:ℕ):ℝ))
    let fParentP:=markedVortexVertexEmbedding Q
    let gParentP:=markedVortexHubEmbedding Q
    let gWideP:=markedVortexNonDeeperHubToPhysical Q
    let ρParentP:=markedVortexPermutation Q π hpres
    let DparentP:=fun i=>2*(Fintype.card (Z i):ℝ)/initialIndexDensity U Dnat
    let GP:=P
    let αP:ℝ:=2*αRef
    let Color:=Bool
    let aP:Bool:=false
    let jP:Bool:=false
    let sParent:ℝ:=1/100
    let pParent:=initialIndexDensity U Dnat*sParent/2
    let kParent:=pParent/(((r+4):ℕ):ℝ);
    ∃ weightParentP:∀i,(Fin ((r+4)+1)→W i)→ℝ,
    ∃ weightActiveP:∀i,(Fin ((r+4)+1)→XP i)→ℝ,
    (∀i≤L,SuccessorSequenceWeightConditions (P.comap (fParentP i)) (ρParentP i) (3*d)
      (DparentP i) δparent (successorWeightLower k₀ (αP/4)) (successorWeightUpper k₀ (αP/4)) (weightParentP i)) ∧
    (∀i≤L+1,SuccessorSequenceWeightConditions (P.comap (fActiveP i)) (ρActiveP i) (3*d)
      (DactiveP i) δparent (successorWeightLower k₀ (αP/4)) (successorWeightUpper k₀ (αP/4)) (weightActiveP i)) ∧
    ∃levelWeight:∀i,(Fin ((r+4)+1)→W i)→ℝ,
    (∀i≤L,SuccessorSequenceWeightConditions (P.comap (fV i)) (ρi i) (3*d) (Dload i) τLevel Aload Bload (levelWeight i)) ∧
    let t:=t₀
    let tHub:=ξ*(n:ℝ)
    let b:=longAssignedApproxOrdinaryWeight F hF K (r+4) θ
    let a:=longAssignedApproxMarkedWeight F hF K (r+4) θ
    let p₁:=ρ*(1/100)/2
    let k₁:=ρ*((1/100)/(((r+4):ℕ):ℝ))/2
    let p₂:=(∑u,b u)/D
    let k₂:=(∑u,a u)/D
    let udens:=2*(∑u,(1-1/100-(1/100)/(((r+4):ℕ):ℝ)-a u-b u))/D
    let q:=longAssignedIntervalProbability F hF K (r+4) θ
    let s:=longAssignedSpokeProbability F hF K (r+4) θ
    let hLaw:=long_assigned_actual_raw_law_parameters (by omega) F hF Allowed hAllowed K (by omega) (r+4) d hm hd θ ρ₀ ρ D
      hθpos.le hθ hρ₀ hρlo hρ1 hD hsize hcut hclass
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=Fin n) p₁ k₁ p₂ k₂ udens
      hLaw.1 hLaw.2.1 hLaw.2.2.1 hLaw.2.2.2.1 hLaw.2.2.2.2.1 hLaw.2.2.2.2.2.1
      d hd q hLaw.2.2.2.2.2.2.1 hLaw.2.2.2.2.2.2.2.1 s
      hLaw.2.2.2.2.2.2.2.2.1 hLaw.2.2.2.2.2.2.2.2.2)
    let f:=fun (ω:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e) e=>
      rawExpandedMarkedCollapse e (ω e)
    let pstar:=min (1/4:ℝ) (min (ρ₀/8) (ρ₀/(6*((((r+4):ℕ):ℝ)+1))))
    let BMseed:=2*BM/pstar^(2*(r+4)+1)
    let BOseed:=fun i=>2*BO i/pstar^(2*(ni i+2))
    let Wm:=longAssignedMarkedSeed F hF K (r+4) d θ D π weight
    let Wo:=longAssignedOrdinarySeed F hF K (r+4) d θ D P π ni hni w
    let C:=10*(((((r+4):ℕ):ℝ)+1)^4*BMseed+∑i:Fin K,((ni i:ℝ)+2)^4*BOseed i)
    let ℓ:=fun i=>ni i+2
    let Wmix:=longMixedSeedWeight Wm Wo
    let R:=longRawHubResources (U:=U) π d (r+4) ℓ
    let Pair:Option (Fin K)→ℝ:=fun i=>match i with
      | none=>((((r+4):ℕ):ℝ)+1)^4*BMseed
      | some i=>((ni i:ℝ)+2)^3*BOseed i
    let Kpair:=1+((((r+4):ℕ):ℝ)+1)^4*BMseed+∑i:Fin K,((ni i:ℝ)+2)^3*BOseed i
    let failure:=4*(Fintype.card U:ℝ)*Real.exp (-2*tHub^2/((4*(d:ℝ)+3)^2*(n:ℝ)))
    letI : Nonempty (Fin n):=⟨⟨0,by omega⟩⟩
    let ParentGood:=fun z=>MarkedVortexParentRecordSmallerReferenceEvent r h k₀ d αP ρ₀ sstar tstar kstar
      εAbsP ζAbsP βconfigP βCommonP εRef κmax δparent δparent δparent δparent δparent δparent δparent δparent
      εBal ζBal δparent δparent δparent δparent δparent δparent
      size aParent bParent eParent f₀ GP Dnat vsize βQ εQ Q π hpres L sParent pParent kParent q s aP jP weightParentP weightActiveP z;
    let Ret:=fun raw:RawMarkedOutcome (Fin n) U Bool Bool=>
      StartRetentionOutcome (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false)
        (startRetentionMinimum (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false))
    let ν:=fun raw:RawMarkedOutcome (Fin n) U Bool Bool=>
      startRetentionLaw (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false)
        (startRetentionMinimum (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false)) (startRetentionMinimum_le _)
    let Prior:=MarkedAdaptiveAgreementProperty r d size a₀ b₀ e₀ aRob bRob eRob f₀ L hNbr
      β βCommon εAbs εRob ζRob εRef κmax γRich p₁ k₁ (1/100) tstar ζ εBal ζBal εNbr ζNbr Bload εLoad 1 ζLoad ζLocal ζConfig ρ₀ sstar kstar τLevel
      P π fV gV ρi Aset Bset Scale Dlevel Dload bdom levelWeight q s false false;
    let ExpandedGood:=fun z:(Σω:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e,Ret (f ω))=>LongExpandedGlobalTests P π d ζret p₁ k₁ p₂ k₂ udens q z;
    1-(36*(ε₀+6*ηEvent)+ηEvent)≤(μ.sigma (fun ω=>ν (f ω))).probability (fun z=>(
      Prior ⟨f z.1,z.2⟩ ∧ ParentGood ⟨f z.1,z.2⟩ ∧ ExpandedGood z ∧
      MarkedRetainedRobustChangeEvent P π d r false false εStable ζStable capStable size aStable bStable eStable f₀ ⟨f z.1,z.2⟩ ∧
      MarkedProtectedAbsorbableCorrectionWithBounds P π d r size aRob bRob eRob f₀ εRob ζCorr ξCorr (f z.1)
        (retainedRawMarkedSpokes π d (fun e=>f z.1 (Sum.inr e)) false
          (startRetentionMinimum (rawStartHubSet π d (fun e=>f z.1 (Sum.inr e)) false)) z.2 false false)
        (Q.extendedVertices 1) (Q.extendedIndices 1) ∧
      LongEveryClassValidDeletionEvent ζOrd P π d r gammaLoss sigmaLoss ξClassOrd z
        (Q.extendedVertices 1) (Q.extendedIndices 1) K B θ D alphaOrd γOrd epsOrd
        ((min (2*αRef) (1/4:ℝ))*(ρ₀/200)^2*(1/100)/16) F hF weight w ∧
      LongCorrectionUniversalMatchingReserveEvent P π d r Dnat vsize βQ εQ Q (Q.length-1) aRob bRob eRob
        gammaLoss sigmaLoss extra ξClassOrd ζOrd z θ alphaOrd γOrd epsOrd
        ((min (2*αRef) (1/4:ℝ))*(ρ₀/200)^2*(1/100)/16) F hF weight w ∅ ∧
      FirstVortexConcreteBoundaryEvent P π d r Dnat vsize βQ εQ Q θ ρ₀ BM BO F hF weight w
        alphaOrd γOrd epsOrd ζOrd ξSeed ΔSeed ζret ζ
        ((min (2*αRef) (1/4:ℝ))*(ρ₀/200)^2*(1/100)/16) tSeed τ z (Q.extendedVertices 1)) ∧
      ∀v,((rawIntervalBoundaryHubSet π d (fun e=>z.1 (Sum.inr e)) (Q.extendedIndices 1) v).card:ℝ)≤cBoundary*((Q.extendedVertices 1).card:ℝ))

theorem first_vortex_named_tail_at_matching_high_probability_no_completion
    (r h k₀ Qpow:ℕ) (αRef sstar ω γRich tstar kstar ρ₀:ℝ) (hρ₀:0<ρ₀)
    (β βCommon εAbs εRob ζRob δAbs εAbsP ζAbsP δAbsP βconfigP βCommonP εStable ζStable capStable:ℝ)
    (εQ:ℝ) (hεQ:0<εQ) (hεQ1:εQ<1/4) (hεQAbs:εQ≤εAbs) (hεQRob:εQ≤εRob)
      (hεQsmall:εQ≤min ((γRich/2)*kstar) tstar/128)
    (K:ℕ) (hK3:3≤K) (hm:7≤(r+4))
    (θ:ℝ) (hθpos:0<θ) (hθ:θ≤1/100)
    (htstarBound:tstar≤(1/100)/(((r+4):ℕ):ℝ))
    (d:ℕ) (hd:2≤d) (cBoundary:ℝ) (hcBoundary:0<cBoundary) (hspacing:4/(d:ℝ)≤cBoundary) (hcut:(1/((((r+4):ℕ):ℝ)+1))/(d:ℝ)≤θ)
    (BM:ℝ) (hBM:0<BM) (BO:Fin K→ℝ) (hBO:∀i,0<BO i)
    (lam:ℝ) (hlam:0<lam) (hlamθ:lam≤θ) (ξCap:ℝ) (hξCap:0<ξCap)
    (α cLocal chainCap active lamAssign δglobal δold δlocal bmatch ζret ηBalance κPack βfinal cap rho eta δLoss εInner:ℝ) (hζret:0<ζret)
    (gammaStep sigmaStep:ℝ)    (hTail:FirstVortexNamedTailAtMatchingSelectedLossNoCompletion r h k₀ Qpow αRef sstar ω γRich tstar kstar ρ₀ hρ₀
      β βCommon εAbs εRob ζRob δAbs εAbsP ζAbsP δAbsP βconfigP βCommonP εStable ζStable capStable
      εQ hεQ hεQ1 hεQAbs hεQRob hεQsmall K hK3 hm θ hθpos hθ htstarBound
      d hd cBoundary hcBoundary hspacing hcut BM hBM BO hBO lam hlam hlamθ ξCap hξCap
      α cLocal chainCap active lamAssign δglobal δold δlocal bmatch ζret ηBalance κPack βfinal cap rho eta δLoss εInner hζret gammaStep sigmaStep):
    FirstVortexNamedTailAtMatchingHighProbabilityNoCompletion r h k₀ Qpow αRef sstar ω γRich tstar kstar ρ₀ hρ₀
      β βCommon εAbs εRob ζRob δAbs εAbsP ζAbsP δAbsP βconfigP βCommonP εStable ζStable capStable
      εQ hεQ hεQ1 hεQAbs hεQRob hεQsmall K hK3 hm θ hθpos hθ htstarBound
      d hd cBoundary hcBoundary hspacing hcut BM hBM BO hBO lam hlam hlamθ ξCap hξCap
      α cLocal chainCap active lamAssign δglobal δold δlocal bmatch ζret ηBalance κPack βfinal cap rho eta δLoss εInner hζret gammaStep sigmaStep :=by
  obtain ⟨epsOrd,hepsOrd,hepsOrd1,hepsOrdRate,haOrd,haOrdBound,hγOrd,hγOrdBound,
    ηSeed,hηSeed,tSeed,τSeed,ΔSeed,ξSeed,htSeed,hτSeed,hτSeedBound,hΔSeed,hξSeed,hξSeedBound,
    ηOrd,hηOrd,tOrd,τOrd,ΔOrd,ξOrd,htOrd,hτOrd,hτOrdBound,hΔOrd,hξOrd,hξOrdBound,
    lamOrd,ηListOrd,ζOrd,hlamOrd,hηListOrd,hζOrd,hζOrdΔ,hζOrdE,hζOrdSeed,NListOrd,hList,
    cOrd,ξClassOrd,hcOrd,hξClassOrd,hξCapOrd,hξClassBound,hζSum,hOrient,hNumeric,hRest⟩:=hTail
  refine ⟨epsOrd,hepsOrd,hepsOrd1,hepsOrdRate,haOrd,haOrdBound,hγOrd,hγOrdBound,
    ηSeed,hηSeed,tSeed,τSeed,ΔSeed,ξSeed,htSeed,hτSeed,hτSeedBound,hΔSeed,hξSeed,hξSeedBound,
    ηOrd,hηOrd,tOrd,τOrd,ΔOrd,ξOrd,htOrd,hτOrd,hτOrdBound,hΔOrd,hξOrd,hξOrdBound,
    lamOrd,ηListOrd,ζOrd,hlamOrd,hηListOrd,hζOrd,hζOrdΔ,hζOrdE,hζOrdSeed,NListOrd,hList,
    cOrd,ξClassOrd,hcOrd,hξClassOrd,hξCapOrd,hξClassBound,hζSum,hOrient,hNumeric,?_⟩
  obtain ⟨eps,heps,heps1,hepsRate,hepsLe,ha,haBound,hγ,hγBound,hRest⟩:=hRest
  refine ⟨eps,heps,heps1,hepsRate,hepsLe,ha,haBound,hγ,hγBound,?_⟩
  intro χTarget hχTarget
  obtain ⟨ε₀,ηEvent,hε₀,hε₀one,hηEvent,hprob,hχBudget,hchoose⟩:=long_selector_common_failure_choice_arbitrary χTarget hχTarget
  refine ⟨ε₀,ηEvent,hε₀,hε₀one,hηEvent,hprob,hχBudget,?_⟩
  intro αHost rPart hαHost hrPart hεQHost
  obtain ⟨εExtra,hExtra,hExtraBound,hRest⟩:=hRest αHost rPart hαHost hrPart hεQHost ε₀ ηEvent hε₀ hε₀one hηEvent hprob
  refine ⟨εExtra,hExtra,hExtraBound,?_⟩
  obtain ⟨gammaLoss,sigmaLoss,extra,hγLoss,hσLoss,hextra,hγOrd,hγBudget,hσBudget,hRest⟩:=hRest
  refine ⟨gammaLoss,sigmaLoss,extra,hγLoss,hσLoss,hextra,hγOrd,hγBudget,hσBudget,?_⟩
  intro κmax κauxCap ζCap hκmax hκauxCap hζCap
  obtain ⟨ζCorr,ξCorr,η₀,κ,εRef,εNbr,hζCorr,hζRob,hζCap',hξCorr,hξCorrRate,hbudget,
    hη₀,hκ,hκmax',hκaux',hεRefEq,hεRefMax,hεRef,hεNbr,hεNbrCap,hRest⟩:=
      hRest κmax κauxCap ζCap hκmax hκauxCap hζCap
  refine ⟨ζCorr,ξCorr,η₀,κ,εRef,εNbr,hζCorr,hζRob,hζCap',hξCorr,hξCorrRate,hbudget,
    hη₀,hκ,hκmax',hκaux',hεRefEq,hεRefMax,hεRef,hεNbr,hεNbrCap,?_⟩
  obtain ⟨χ,χCommon,χBal,χNbr,χLoad,χLocal,χConfig,hχ,hχCommon,hχBal,hχNbr,hχLoad,hχLocal,hχConfig,hgap⟩:=hchoose εExtra (hExtraBound hε₀)
  refine ⟨χ,χCommon,χBal,χNbr,χLoad,χLocal,χConfig,hχ,hχCommon,hχBal,hχNbr,hχLoad,hχLocal,hχConfig,hgap,?_⟩
  intro Qreal pstarRef ζ εBal ζBal ζNbr εLoad ζLoad ζLocal ζConfig τLevel
    hpstarRef hζ hεBal hζBal hζNbr hεLoad hζLoad hζLocal hζConfig hτLevel hQreal hNbr hhNbr hpstarBound
  exact hRest χ χCommon Qreal pstarRef ζ εBal ζBal χBal ζNbr χNbr εLoad ζLoad χLoad ζLocal χLocal ζConfig χConfig τLevel
    hχ hχCommon hpstarRef hζ hεBal hζBal hχBal hζNbr hχNbr hεLoad hζLoad hχLoad hζLocal hχLocal hζConfig hχConfig hτLevel hQreal hNbr hhNbr hpstarBound hgap
end Oberwolfach
