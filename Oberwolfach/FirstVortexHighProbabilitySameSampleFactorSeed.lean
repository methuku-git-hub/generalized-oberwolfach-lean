module

public import Oberwolfach.FirstVortexHighProbabilityNumericWithFixedChain
public import Oberwolfach.FirstVortexFixedClassFactorSeedProjection

@[expose] public section
/-! On every outcome of the high-probability event, obtain the factor seed,
    the edited-target matching and the level continuation on that same outcome. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 65536
set_option maxRecDepth 32768
set_option maxHeartbeats 120000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
attribute [local instance] referenceWitnessFinDecidable
attribute [local instance 100000] Finset.decidableDforallFinset
attribute [local instance] partitionedDivisibleArcFinite partitionedDivisibleOrdFinite partitionedDivisibleMarkFinite

def FirstVortexHighProbabilitySameSampleFactorSeed
    (r h k₀ Qpow:ℕ) (αRef sstar ω γRich tstar kstar ρ₀:ℝ) (hρ₀:0<ρ₀)
    (β βCommon εAbs εRob ζRob δAbs εAbsP ζAbsP δAbsP βconfigP βCommonP εStable ζStable capStable:ℝ)
    (cap rho eta δLoss εInner δglobal cSmall active lamAssign ηBalance κPack βfinal:ℝ)
    (εQ:ℝ) (hεQ:0<εQ) (hεQ1:εQ<1/4) (hεQAbs:εQ≤εAbs) (hεQRob:εQ≤εRob)
      (hεQsmall:εQ≤min ((γRich/2)*kstar) tstar/128)
    (αHost rPart ζret:ℝ) (hαHost:0<αHost) (hrPart:0<rPart) (hζret:0<ζret)
      (hεQHost:εQ≤αHost/100000)
    (K:ℕ) (hK3:3≤K) (hm:7≤(r+4))
    (θ:ℝ) (hθpos:0<θ) (hθ:θ≤1/100)
    (htstarBound:tstar≤(1/100)/(((r+4):ℕ):ℝ))
    (d:ℕ) (hd:2≤d) (cBoundary:ℝ) (hcBoundary:0<cBoundary) (hspacing:4/(d:ℝ)≤cBoundary) (hcut:(1/((((r+4):ℕ):ℝ)+1))/(d:ℝ)≤θ)
    (BM:ℝ) (hBM:0<BM) (BO:Fin K→ℝ) (hBO:∀i,0<BO i)
    (lam:ℝ) (hlam:0<lam) (hlamθ:lam≤θ) (ξCap:ℝ) (hξCap:0<ξCap)
    (α δold δlocal bmatch cLocal ρreserve κaux:ℝ):Prop :=
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
      (∃hδ:0<δglobal,∃hθ:0<θ,∃hθδ:10*θ≤δglobal,∃hspacing:1/(d:ℝ)≤θ/1024,
        FirstVortexActualCallerNumericResult r d K ρ₀ cap rho eta δLoss εInner δglobal
          εQ cSmall active θ lamAssign lam epsOrd ζOrd ξClassOrd ζret ηBalance κPack βfinal hδ hθ hθδ hspacing) ∧
    ∃eps:ℝ,0<eps ∧ eps≤1 ∧ 3*eps≤(min lam epsOrd)*(θ/(100*(K:ℝ)^2)) ∧ eps≤epsOrd ∧
    let alpha:=min ((min lam epsOrd)/(10*(d:ℝ))) (θ/(200*(K:ℝ)^2))
    let γ:=min (eps/2) (min (1/2:ℝ) (min ((min lam epsOrd)/(10*(d:ℝ))) ((min lam epsOrd)/10)))
    0<alpha ∧ alpha≤θ/(200*(K:ℝ)^2) ∧ 0<γ ∧ γ≤eps ∧
    ∀(ε₀ ηEvent:ℝ),0<ε₀→ε₀<1→0<ηEvent→0<1-(36*(ε₀+6*ηEvent)+ηEvent)→
    ∃ εExtra:ℝ,0<εExtra ∧ (0<ε₀→4*εExtra≤ε₀) ∧
    ∀ (gammaLoss sigmaLoss κmax κauxCap ζCap:ℝ),0<gammaLoss→0<sigmaLoss→0<κmax→0<κauxCap→0<ζCap → gammaLoss≤ζOrd/2 →
    ∃ ζCorr ξCorr η₀ κ εRef εNbr:ℝ,0<ζCorr ∧ ζCorr≤ζRob ∧ ζCorr≤ζCap ∧ 0<ξCorr ∧
      16*((((r+4):ℕ):ℝ)+1)*ξCorr≤ζCorr ∧
      (∀n:ℕ,6*(8*((((r+4):ℕ):ℝ)+1)*ξCorr*n)≤min (gammaLoss*n) (sigmaLoss*n)) ∧
      0<η₀ ∧ 0<κ ∧ κ≤κmax ∧ κ≤κauxCap ∧ εRef=κ/4 ∧ εRef≤κmax/4 ∧ 0<εRef ∧ 0<εNbr ∧ εNbr≤κauxCap ∧
    ∀ (χ χCommon Qreal pstarRef ζ εBal ζBal χBal ζNbr χNbr εLoad ζLoad χLoad ζLocal χLocal ζConfig χConfig τLevel:ℝ)
    (hχ:0<χ)
    (hχCommon:0<χCommon) (hpstarRef:0<pstarRef) (hζ:0<ζ) (hεBal:0<εBal) (hζBal:0<ζBal) (hχBal:0<χBal)
    (hζNbr:0<ζNbr) (hχNbr:0<χNbr) (hεLoad:0<εLoad)
    (hζLoad:0<ζLoad) (hχLoad:0<χLoad) (hζLocal:0<ζLocal) (hχLocal:0<χLocal) (hζConfig:0<ζConfig) (hχConfig:0<χConfig) (hτLevel:0<τLevel)
    (hQreal:0<Qreal) (hNbr:ℕ) (hhNbr:1≤hNbr) (hpstarBound:4*(((r+4):ℕ):ℝ)*pstarRef≤ρ₀*(1/100))
    (hgap:χ+χCommon+χBal+2*χNbr+χLoad+χLocal+χConfig+εExtra<ε₀),
    ∀ δparent:ℝ,0<δparent→∃βmax:ℝ,0<βmax ∧ ∀βQ:ℝ,0≤βQ→βQ≤1/4→βQ≤αRef/4→βQ≤βmax→βQ≤εBal/4→βQ≤εRef/4→
    ∃MLevel:ℕ,1≤MLevel ∧
    ∃mLevel:ℕ,1≤mLevel ∧ ∃η:ℝ,0<η ∧ ∃t₀ τ₀ Δ ξ:ℝ,0<t₀ ∧ 0<τ₀ ∧ τ₀≤1/16 ∧ 0<Δ ∧ 0<ξ ∧ 4*ξ≤eps/2 ∧
    ∃ξResidual:ℝ,0≤ξResidual ∧ 4*ξResidual≤epsOrd/2 ∧ ζOrd≤ξResidual ∧ ξ≤ξResidual ∧ ξSeed≤ξResidual ∧
      (∀n:ℕ,ζOrd*n≤ξResidual*n ∧ ξ*n≤ξResidual*n ∧ ξSeed*n≤ξResidual*n) ∧
    ∃ζList:ℝ,0<ζList ∧ ζList≤Δ ∧ ∃N:ℕ,
    ∀size:ℕ,∃a₀ b₀ e₀ aRob bRob eRob aParent bParent eParent aStable bStable eStable:ℕ,
    ∃Nchain:ℕ,FirstVortexSameSampleFixedClassChainAt α lam lamAssign εQ δold δlocal δglobal θ epsOrd ξResidual ρ₀ bmatch ξClassOrd ζret d K r ζOrd rho δLoss εInner eta eRob
      cap cLocal active ηBalance κPack βfinal Nchain ∧
    ∀f₀ B:ℕ,eRob≤B→∀extra:ℝ,0<extra→∃NHost:ℕ,Nchain≤NHost ∧
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
    ∀ (Itype:Type) [Fintype Itype] (density:Itype→ℝ) (iclass:Itype),
      (∀j,0≤density j) → (∑j,density j=1) →
      (∀j,density j=0 ∨ rPart≤density j) → rPart≤density iclass → ρ=density iclass →
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
    let ExpandedGood:=fun z:(Σω:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e,Ret (f ω))=>
      (∀A:SimpleGraph (Fin n),(∀v,A.degree v≤B)→
        ∃S:SimpleGraph (Fin n),S≤P ∧ S.IsRegularOfDegree (2*Fintype.card U) ∧
          (∀x y,((spanningRestriction (⊤:SimpleGraph (Fin n)) (Q.extendedVertices 1))⊔A).Adj x y→(S.Adj x y↔(longPhysicalStateGraph P z.1 {0,1,2,3,4}).Adj x y)) ∧
          (∀v,((changed ((longPhysicalStateGraph P z.1 {0,1,2,3,4}).neighborFinset v) (S.neighborFinset v)).card:ℝ)≤ξClassOrd*n)) ∧
      (((RetainedRestrictionGood π d (fun e=>z.1 (Sum.inr e)) false
        (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false))
        (fun _:Unit=>Finset.univ) (fun _:Unit=>Finset.univ) ζret z.2 ∧
        (∀v,((rawIntervalBoundaryHubSet π d (fun e=>z.1 (Sum.inr e)) Finset.univ v).card:ℝ)≤
          4*(Fintype.card U:ℝ)/d+4*(n:ℝ)^(3/4:ℝ))) ∧
       (∀j x,
        |((∑y,sampledColourOrientation P (fun e=>z.1 (Sum.inl e)) j x y:ℕ):ℝ)-markedExpandedPhysicalProbability p₁ k₁ p₂ k₂ udens j/2*P.degree x|<(n:ℝ)^(3/5:ℝ) ∧
        |((∑y,sampledColourOrientation P (fun e=>z.1 (Sum.inl e)) j y x:ℕ):ℝ)-markedExpandedPhysicalProbability p₁ k₁ p₂ k₂ udens j/2*P.degree x|<(n:ℝ)^(3/5:ℝ) ∧
        |(sampledColourDegree P (fun e=>(z.1 (Sum.inl e)).1) j x:ℝ)-markedExpandedPhysicalProbability p₁ k₁ p₂ k₂ udens j*P.degree x|<(n:ℝ)^(3/5:ℝ))) ∧
       (∀g x,|((rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) g x).card:ℝ)-(∑w,q w g/(d:ℝ))|<(n:ℝ)^(3/5:ℝ)));
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
      LongCorrectionReserveConcreteClassEvent P π d r Dnat vsize βQ εQ Q (Q.length-1) aRob bRob eRob
        gammaLoss sigmaLoss extra ξClassOrd ζOrd z θ alphaOrd γOrd epsOrd
        ((min (2*αRef) (1/4:ℝ))*(ρ₀/200)^2*(1/100)/16) F hF weight w ∅ ∧
      LongEveryReserveConcreteClassEvent P π d r Dnat vsize βQ εQ Q B gammaLoss sigmaLoss ξClassOrd ζOrd z
        θ Dnat alphaOrd γOrd epsOrd ((min (2*αRef) (1/4:ℝ))*(ρ₀/200)^2*(1/100)/16) F hF weight w ∧
      FirstVortexConcreteBoundaryEvent P π d r Dnat vsize βQ εQ Q θ ρ₀ BM BO F hF weight w
        alphaOrd γOrd epsOrd ζOrd ξSeed ΔSeed ζret ζ
        ((min (2*αRef) (1/4:ℝ))*(ρ₀/200)^2*(1/100)/16) tSeed τ z (Q.extendedVertices 1)) ∧
      (∀v,((rawIntervalBoundaryHubSet π d (fun e=>z.1 (Sum.inr e)) (Q.extendedIndices 1) v).card:ℝ)≤cBoundary*((Q.extendedVertices 1).card:ℝ)) ∧
      (L+1=Q.length → (eRob:ℝ)≤ρreserve*n → κauxCap≤κaux → ζ≤ζret →
        let γLoss:=gammaLoss
        let σLoss:=sigmaLoss
        let sizeStable:=size
        let fStable:=f₀
        let Vort:=Q
        let Dv:=Dnat
        let mm:=vsize
        let β:=βQ
        let ε:=εQ
        let Δ:=ζOrd
        let ξ:=ξResidual
        let ξPart:=ξClassOrd
        let a:=alphaOrd
        let γ:=γOrd
        let eps:=epsOrd
        let βList:ℝ:=(min (2*αRef) (1/4:ℝ))*(ρ₀/200)^2*(1/100)/16
        let e₀:=eRob
        let αAssign:=2*α
        let hπ:=hpres;
        ∃boundary lossInside inside loc:ℝ,
      boundary=4*(Fintype.card U:ℝ)/d+4*(n:ℝ)^(3/4:ℝ) ∧
      FirstVortexSummedLossAt n d ((markedVortexInnerVertices Vort 0).card:ℝ)
        cLocal rho eta θ a γ ξPart κPack Δ ζret ηBalance boundary lossInside inside loc ∧
    let κ:=κPack
    let δsmall:=δglobal
    let ρsmall:=θ/4096
    let δspoke:=δglobal;
    ∃D₀:MarkedReferenceDeletion P π d (fun x=>rawExpandedMarkedCollapse x (z.1 x)),
    ∃C:Finset (Finset (Fin n)⊕(Fin n×U)), longTerminalProtectedReserve P π d r z z.2 (Vort.extendedVertices 1) (Vort.extendedIndices 1) γLoss σLoss e₀ (Vort.extendedVertices (L+1)) (Vort.extendedIndices (L+1)) D₀ C ∧
    ∀S:SimpleGraph (Fin n),S≤P → S.IsRegularOfDegree (2*Fintype.card U) →
      (∀v,((changed ((longPhysicalStateGraph P z.1 {0,1,2,3,4}).neighborFinset v) (S.neighborFinset v)).card:ℝ)≤ξPart*n) →
      (∀x∈Vort.extendedVertices 1,∀y∈Vort.extendedVertices 1,S.Adj x y↔(longPhysicalStateGraph P z.1 {0,1,2,3,4}).Adj x y) → markedResourceRimGraph C≤S →
    ∃Mhost:Fin n→Fin n→ℕ, ∃Del:SimpleGraph (Fin n),
      S≤P ∧ S.IsRegularOfDegree (2*Fintype.card U) ∧
      (∀v,((changed ((longPhysicalStateGraph P z.1 {0,1,2,3,4}).neighborFinset v) (S.neighborFinset v)).card:ℝ)≤ξPart*n) ∧
      (∀x∈(Vort.extendedVertices 1),∀y∈(Vort.extendedVertices 1),S.Adj x y↔(longPhysicalStateGraph P z.1 {0,1,2,3,4}).Adj x y) ∧
      markedResourceRimGraph C≤S ∧
      (∀x∈(Vort.extendedVertices 1),∀y∈(Vort.extendedVertices 1),(longSelectedPhysicalGraph P π d z.1).Adj x y→S.Adj x y) ∧
      LongClassMatchingDeletionWitness Δ P π d r z (Vort.extendedVertices 1) K θ Dv a γ eps βList F hF weight w D₀ C S Mhost Del ∧
      FirstVortexClassPreparedRetainedFullPackingOutcomeWithAllHubLoad P S π Dv mm d (r+4) β ε Vort F hF θ lamAssign eps δlocal δglobal (αAssign/2) bmatch ρ₀ ξ Δ a γ weight w z.1
        (startRetentionMinimum (rawStartHubSet π d (fun x=>z.1 (Sum.inr x)) false)) z.2 ∧
    let t:=startRetentionMinimum (rawStartHubSet π d (fun x=>z.1 (Sum.inr x)) false)
    let raw:RawMarkedOutcome (Fin n) U Bool Bool:=fun x=>rawExpandedApproximateCollapse x (z.1 x)
    let ℓ:=fun i:Fin K=>longPaddedSeedExponent i+2
    let R:=mixedCandidateResources (longRawSeedResources (U:=U) π d (r+4) ℓ)
    let Tmix:=bernoulliVertexSet (longRawHubState P π d raw true true)
    let Q:=longRawSurvivingResources P π d raw true true Del.edgeFinset
    let q:=survivingCandidateEmbedding R Q Tmix (long_raw_surviving_resources_subset P π d raw true true Del.edgeFinset)
    let φ:=markedRawSampledPhysicalEmbedding P π d raw true true;
    0<K→θ≤1→∀ζRet:ℝ,
    0<active→0<ε→ε≤1/4→0<mm→0≤ζRet→ζRet≤active/128→ζret≤ζRet*ε/2→
    ∀p₂ k₂ u:ℝ,
    (∀v,|((rawStartHubSet π d (fun x=>z.1 (Sum.inr x)) false v).card:ℝ)-
      (∑w,longAssignedIntervalProbability F hF K (r+4) θ w false/(d:ℝ))|<(n:ℝ)^(3/5:ℝ))→
    (∀j v,|((∑x,sampledColourOrientation P (fun x=>z.1 (Sum.inl x)) j x v:ℕ):ℝ)-
      markedExpandedPhysicalProbability (initialIndexDensity U Dv*(1/100:ℝ)/2) (initialIndexDensity U Dv*((1/100:ℝ)/((r+4:ℕ):ℝ))/2) p₂ k₂ u j/2*P.degree v|<(n:ℝ)^(3/5:ℝ))→
    0≤γ→0≤θ→u≤2*θ→
    (∀v,|((sampledColourDegree P (fun e=>(z.1 (Sum.inl e)).1) 4 v):ℝ)-u*(P.degree v:ℝ)|≤(n:ℝ)^(3/5:ℝ))→
    ∀(ζChange:ℝ),0≤ζChange→ζChange≤capStable→
    active≤ζChange→(min cap (1:ℝ))/2≤ζChange→0≤cLocal→active≤cLocal→
    let σ:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedMarkedCollapse e (z.1 e)
    let Hraw:=retainedRawMarkedSpokes π d (fun e=>raw (Sum.inr e)) false t z.2 false false;
    ∃(Pack:Finset (Sym2 (Fin n))) (E:U→Finset (Sym2 (Fin n))) (Spokes:U→Finset (Fin n))
      (A:Finset (Fin n×Fin n)),
      let Small:=SimpleGraph.fromEdgeSet (↑Pack:Set (Sym2 (Fin n)))⊔prescribedPhysicalUnion E;
      Small.edgeFinset=A.image (fun a=>s(a.1,a.2)) ∧
      LongFactorComplementProvenance F S P π d (r+4) raw t z.2 Pack E A Spokes ∧
      ∃T:Finset {a:Fin n×Fin n // longEligibleResidualArc Mhost Small ⊥ a},
      ∃τnew:RawMarkedOutcome (Fin n) U Bool Bool,
      (∀mark x y,markedPhysicalRim P π (3*d) (fun e=>τnew (Sum.inl e)) mark x y=1 ↔
        if mark then ∃e:residualMarkedArc (longEligibleResidualArc Mhost Small ⊥) T,e.val.val.1=x∧π.symm e.val.val.2=y
        else ∃e:residualOrdinaryArc (longEligibleResidualArc Mhost Small ⊥) T,e.val.val.1=x∧e.val.val.2=y) ∧
      let Y:=fun w=>markedIntervalRootSet π (fun _:retainedMarkedIndex π d (fun x=>raw (Sum.inr x)) false t z.2 w=>d) Subtype.val
      let Hnew:Bool→Fin n→U→Prop:=fun b v w=>if b then retainedRawMarkedSpokes π d (fun e=>raw (Sum.inr e)) false t z.2 false true true v w else v∈Spokes w\Y w;
      FirstVortexNamedLevelChainContinuation P π d r Dv mm β ε Vort hπ L z τnew Hnew active cLocal ζChange εStable sizeStable eStable
))
theorem first_vortex_high_probability_same_sample_factor_seed
    (r h k₀ Qpow:ℕ) (αRef sstar ω γRich tstar kstar ρ₀:ℝ) (hρ₀:0<ρ₀)
    (β βCommon εAbs εRob ζRob δAbs εAbsP ζAbsP δAbsP βconfigP βCommonP εStable ζStable capStable:ℝ)
    (cap rho eta δLoss εInner δglobal cSmall active lamAssign ηBalance κPack βfinal:ℝ)
    (εQ:ℝ) (hεQ:0<εQ) (hεQ1:εQ<1/4) (hεQAbs:εQ≤εAbs) (hεQRob:εQ≤εRob)
      (hεQsmall:εQ≤min ((γRich/2)*kstar) tstar/128)
    (αHost rPart ζret:ℝ) (hαHost:0<αHost) (hrPart:0<rPart) (hζret:0<ζret)
      (hεQHost:εQ≤αHost/100000)
    (K:ℕ) (hK3:3≤K) (hm:7≤(r+4))
    (θ:ℝ) (hθpos:0<θ) (hθ:θ≤1/100)
    (htstarBound:tstar≤(1/100)/(((r+4):ℕ):ℝ))
    (d:ℕ) (hd:2≤d) (cBoundary:ℝ) (hcBoundary:0<cBoundary) (hspacing:4/(d:ℝ)≤cBoundary) (hcut:(1/((((r+4):ℕ):ℝ)+1))/(d:ℝ)≤θ)
    (BM:ℝ) (hBM:0<BM) (BO:Fin K→ℝ) (hBO:∀i,0<BO i)
    (lam:ℝ) (hlam:0<lam) (hlamθ:lam≤θ) (ξCap:ℝ) (hξCap:0<ξCap)
    (α δold δlocal bmatch cLocal:ℝ)
    (ρreserve κaux ζlocal s c:ℝ)
    (βListInit εLevelInit hostCapInit:ℝ)
    (hInitial:FirstVortexInitialMatchingVortexRates ρ₀ δglobal βListInit βfinal εLevelInit εInner εAbs εRob γRich kstar tstar hostCapInit bmatch α εQ)
    (hRet:FirstVortexRetentionBalanceRates r d εQ active θ s c ζret ζlocal ηBalance κaux)
    (hcutHost:5/((((r+4):ℝ)+1)*(d:ℝ)+5)+(((r+4):ℝ)+1)*(d:ℝ)/(K:ℝ)≤θ/2)
    (hlamhi:lam≤α/128) (hρreserve:0≤ρreserve)
    (hListMargin:βfinal+2*ρreserve≤((min (2*αRef) (1/4:ℝ))*(ρ₀/200)^2*(1/100)/16)/2)
    (hγRich:0≤γRich) (hζStable:0≤ζStable)
    (hSel:FirstVortexHighProbabilityNumericWithFixedChain r h k₀ Qpow αRef sstar ω γRich tstar kstar ρ₀ hρ₀
      β βCommon εAbs εRob ζRob δAbs εAbsP ζAbsP δAbsP βconfigP βCommonP εStable ζStable capStable
      cap rho eta δLoss εInner δglobal cSmall active lamAssign ηBalance κPack βfinal
      εQ hεQ hεQ1 hεQAbs hεQRob hεQsmall αHost rPart ζret hαHost hrPart hζret hεQHost
      K hK3 hm θ hθpos hθ htstarBound d hd cBoundary hcBoundary hspacing hcut BM hBM BO hBO lam hlam hlamθ ξCap hξCap α δold δlocal bmatch cLocal):
    FirstVortexHighProbabilitySameSampleFactorSeed r h k₀ Qpow αRef sstar ω γRich tstar kstar ρ₀ hρ₀
      β βCommon εAbs εRob ζRob δAbs εAbsP ζAbsP δAbsP βconfigP βCommonP εStable ζStable capStable
      cap rho eta δLoss εInner δglobal cSmall active lamAssign ηBalance κPack βfinal
      εQ hεQ hεQ1 hεQAbs hεQRob hεQsmall αHost rPart ζret hαHost hrPart hζret hεQHost
      K hK3 hm θ hθpos hθ htstarBound d hd cBoundary hcBoundary hspacing hcut BM hBM BO hBO lam hlam hlamθ ξCap hξCap α δold δlocal bmatch cLocal ρreserve κaux :=by
  obtain ⟨epsOrd,hepsOrd,hepsOrd1,hepsOrdRate,haOrd,haOrdBound,hγOrd,hγOrdBound,
    ηSeed,hηSeed,tSeed,τSeed,ΔSeed,ξSeed,htSeed,hτSeed,hτSeedBound,hΔSeed,hξSeed,hξSeedBound,
    ηOrd,hηOrd,tOrd,τOrd,ΔOrd,ξOrd,htOrd,hτOrd,hτOrdBound,hΔOrd,hξOrd,hξOrdBound,
    lamOrd,ηListOrd,ζOrd,hlamOrd,hηListOrd,hζOrd,hζOrdΔ,hζOrdE,hζOrdSeed,NListOrd,hList,
    cOrd,ξClassOrd,hcOrd,hξClassOrd,hξCapOrd,hξClassBound,hζSum,hOrient,hNum,
    eps,heps,heps1,hepsRate,hepsLe,ha,haBound,hγ,hγBound,hh⟩:=hSel
  refine ⟨epsOrd,hepsOrd,hepsOrd1,hepsOrdRate,haOrd,haOrdBound,hγOrd,hγOrdBound,
    ηSeed,hηSeed,tSeed,τSeed,ΔSeed,ξSeed,htSeed,hτSeed,hτSeedBound,hΔSeed,hξSeed,hξSeedBound,
    ηOrd,hηOrd,tOrd,τOrd,ΔOrd,ξOrd,htOrd,hτOrd,hτOrdBound,hΔOrd,hξOrd,hξOrdBound,
    lamOrd,ηListOrd,ζOrd,hlamOrd,hηListOrd,hζOrd,hζOrdΔ,hζOrdE,hζOrdSeed,NListOrd,hList,
    cOrd,ξClassOrd,hcOrd,hξClassOrd,hξCapOrd,hξClassBound,hζSum,hOrient,hNum,
    eps,heps,heps1,hepsRate,hepsLe,ha,haBound,hγ,hγBound,?_⟩
  intro ε₀ ηEvent hε₀ hε₀one hηEvent hprob
  obtain ⟨εExtra,hExtra,hExtraBound,hh⟩:=hh ε₀ ηEvent hε₀ hε₀one hηEvent hprob
  refine ⟨εExtra,hExtra,hExtraBound,?_⟩
  intro gammaLoss sigmaLoss κmax κauxCap ζCap hGamma hSigma hκmax hκaux hζCap hGammaOrd
  obtain ⟨ζCorr,ξCorr,η₀,κ,εRef,εNbr,hζCorr,hζRob,hζCap',hξCorr,hξCorrRate,hbudget,
    hη₀,hκ,hκmax',hκaux',hεRefEq,hεRefMax,hεRef,hεNbr,hεNbrCap,hh⟩:=
    hh gammaLoss sigmaLoss κmax κauxCap ζCap hGamma hSigma hκmax hκaux hζCap hGammaOrd
  refine ⟨ζCorr,ξCorr,η₀,κ,εRef,εNbr,hζCorr,hζRob,hζCap',hξCorr,hξCorrRate,hbudget,
    hη₀,hκ,hκmax',hκaux',hεRefEq,hεRefMax,hεRef,hεNbr,hεNbrCap,?_⟩
  intro χ χCommon Qreal pstarRef ζ εBal ζBal χBal ζNbr χNbr εLoad ζLoad χLoad ζLocal χLocal ζConfig χConfig τLevel
    hχ hχCommon hpstarRef hζ hεBal hζBal hχBal hζNbr hχNbr hεLoad hζLoad hχLoad hζLocal hχLocal hζConfig hχConfig hτLevel hQreal hNbr hhNbr hpstarBound hgap
  have hh:=hh χ χCommon Qreal pstarRef ζ εBal ζBal χBal ζNbr χNbr εLoad ζLoad χLoad ζLocal χLocal ζConfig χConfig τLevel
    hχ hχCommon hpstarRef hζ hεBal hζBal hχBal hζNbr hχNbr hεLoad hζLoad hχLoad hζLocal hχLocal hζConfig hχConfig hτLevel hQreal hNbr hhNbr hpstarBound hgap
  intro δparent hδparent
  obtain ⟨βmax,hβmax,hh⟩:=hh δparent hδparent
  refine ⟨βmax,hβmax,?_⟩
  intro βQ hβQ hβquarter hβα4 hβmax' hβbal hβref
  obtain ⟨MLevel,hMLevel,mLevel,hmLevel,η,hη,t₀,τ₀,Δ,ξ,ht₀,hτ₀,hτ₀cap,hΔ,hξ,hξrate,
    ξResidual,hξResidual,hξResidualBound,hζOrdResidual,hξResidualBound2,hξSeedResidual,hResidualScales,
    ζList,hζList,hζListCap,N,hSelect⟩:=hh βQ hβQ hβquarter hβα4 hβmax' hβbal hβref
  refine ⟨MLevel,hMLevel,mLevel,hmLevel,η,hη,t₀,τ₀,Δ,ξ,ht₀,hτ₀,hτ₀cap,hΔ,hξ,hξrate,
    ξResidual,hξResidual,hξResidualBound,hζOrdResidual,hξResidualBound2,hξSeedResidual,hResidualScales,
    ζList,hζList,hζListCap,N,?_⟩
  intro size
  obtain ⟨a₀,b₀,e₀,aRob,bRob,eRob,aParent,bParent,eParent,aStable,bStable,eStable,hSelect⟩:=hSelect size
  obtain ⟨Nchain,hChain,hSelect⟩:=hSelect
  refine ⟨a₀,b₀,e₀,aRob,bRob,eRob,aParent,bParent,eParent,aStable,bStable,eStable,Nchain,hChain,?_⟩
  intro f₀ B heB extra hextra
  obtain ⟨NHost,hNchain,hFor⟩:=hSelect f₀ B heB extra hextra
  refine ⟨NHost,hNchain,?_⟩
  intro n hn U _ _ F hF Allowed hAllowed ρ D hρlo hρ1 hD hsize hclass P π τ A weight hw hDlo hDhi w hw0 hwupper hU hnoshort εHost hedges hdeg hbudgetV hbudgetE hτnonneg hτbound hεHost
    Dnat vsize hDnat hρactual hreg hmargin hmLevelSize hvsize Q hAbsSize hεQcap htrim hpres L hLQ hk₁ hk₂ htstar Itype _ density iclass hdensity hsum hparts hiclass hρeq hEven hmarginHost
  have hnChain:Nchain≤n:=by omega
  letI : Nonempty (Fin n):=⟨⟨0,by omega⟩⟩
  have hSelected:=hFor n hn U F hF Allowed hAllowed ρ D hρlo hρ1 hD hsize hclass P π τ A weight hw hDlo hDhi w hw0 hwupper hU hnoshort εHost hedges hdeg hbudgetV hbudgetE hτnonneg hτbound hεHost
    Dnat vsize hDnat hρactual hreg hmargin hmLevelSize hvsize Q hAbsSize hεQcap htrim hpres L hLQ hk₁ hk₂ htstar Itype density iclass hdensity hsum hparts hiclass hρeq hEven hmarginHost
  obtain ⟨weightParent,weightActive,hParentWeight,hActiveWeight,levelWeight,hLevelWeight,hProb⟩:=hSelected
  refine ⟨weightParent,weightActive,hParentWeight,hActiveWeight,levelWeight,hLevelWeight,?_⟩
  apply le_trans hProb
  apply finiteLaw_probability_mono
  intro z hz
  obtain ⟨⟨hPrior,hParent,hExpanded,hStable,hProtected,hEvery,hCorrReserve,hEveryReserve,hBoundary⟩,hBound⟩:=hz
  refine ⟨⟨hPrior,hParent,hExpanded,hStable,hProtected,hEvery,hCorrReserve,hEveryReserve,hBoundary⟩,hBound,?_⟩
  intro hL hReserve hκcap hζcap
  have hDnatPos:0<Dnat:=by
    have hdpos:0<(Dnat:ℝ):=by linarith
    exact_mod_cast hdpos
  have hρactualPos:0 < initialIndexDensity U Dnat:=by rw [←hρactual]; exact lt_of_lt_of_le hρ₀ hρlo
  have hUreal:0<(Fintype.card U:ℝ):=by nlinarith [mul_pos (lt_of_lt_of_le hρ₀ hρlo) hD]
  have hUpos:0<Fintype.card U:=by exact_mod_cast hUreal
  have hDlo':(n:ℝ)/2≤Dnat:=by simpa [hDnat] using hDlo
  have hDhi':(Dnat:ℝ)≤2*n:=by simpa [hDnat] using hDhi
  have hvpos:0<vsize:=by omega
  have hεα:εQ≤α/1000:=by rcases hInitial with ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,hh,_⟩;exact hh
  have hεδ:εQ≤δglobal:=by rcases hInitial with ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,hh,_⟩;exact hh
  have hζretRate:ζret≤θ/4096:=hRet.2.2.2.2.2.2.1
  have hηBalance:0<ηBalance:=hRet.2.2.1
  have hκauxPos:0<κaux:=hRet.2.2.2.1
  have hκauxRet:κaux≤ζret:=hRet.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hκauxRate:κaux≤ηBalance/(8*((((r+4):ℕ):ℝ)+1)):=hRet.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hcutMatch:(1/((r:ℝ)+4+1))/(d:ℝ)≤θ:=by simpa only [Nat.cast_add,Nat.cast_ofNat] using hcut
  have hChainSelected:=first_vortex_fixed_class_chain_at_selected_sample α lam lamAssign εQ δold δlocal δglobal θ epsOrd ξResidual ρ₀ bmatch ξClassOrd ζret d K r ζOrd rho δLoss εInner eta eRob
    cap cLocal active ηBalance κPack βfinal Nchain hChain
  have hChainSeed:=first_vortex_fixed_class_factor_seed_at_selected_sample α lam lamAssign εQ δold δlocal δglobal θ epsOrd ξResidual ρ₀ bmatch ξClassOrd ζret d K r ζOrd rho δLoss εInner eta eRob
    cap cLocal active ηBalance κPack βfinal Nchain hChainSelected
  have hNumMatch:=hChainSeed n hnChain U P π Dnat vsize βQ Q hreg hDnatPos (by simpa [hρactual] using hρ1) (by simpa [hρactual] using hρlo) hDlo' hDhi' hvpos F hF Allowed hAllowed hclass hcutMatch hcutHost hnoshort
    hεα hlamhi (min (lam/(10*(d:ℝ))) (θ/(200*(K:ℝ)^2))) (min (epsOrd/2) (min (1/2:ℝ) (min (lam/(10*(d:ℝ))) (lam/10)))) (θ/4096) ξSeed ΔSeed rfl rfl rfl hζOrdE hξSeedResidual hζOrdSeed hepsOrd1 hζretRate hζret.le
    τ A BM hBM weight (by simpa [hDnat] using hw) BO hBO w hw0 hwupper z (fun _=>True) trivial ζ hζcap (Q.extendedVertices 1)
    ((min (2*αRef) (1/4:ℝ))*(ρ₀/200)^2*(1/100)/16) tSeed τ hτnonneg hBoundary
    gammaLoss sigmaLoss size aRob bRob eRob f₀ L B εRob ζCorr ξCorr hAbsSize hL hpres hξCorr.le (hbudget n) hεQRob heB (by simpa only [hDnat] using hEvery) hProtected
    (2*α) ρreserve (by ring) hReserve (le_refl _) hUpos hεδ hU hρreserve hListMargin hζOrdResidual
    hNbr hhNbr size a₀ b₀ e₀ aRob bRob eRob f₀ (initialIndexDensity U Dnat) hρactualPos (by simpa [hDnat,hρactual] using hsize)
    β βCommon εAbs εRob ζRob εRef κmax γRich tstar ζ εBal ζBal εNbr ζNbr (successorWeightUpper k₀ ((2*αRef)/4)) εLoad ζLoad ζLocal ζConfig ρ₀ sstar kstar τLevel hγRich levelWeight (by simpa only [LongMatchingCommonEvent, markedExpandedActualSelected, hρactual] using hPrior)
    κaux κ hηBalance hκauxPos hκ.le (hκaux'.trans hκcap) hεRefEq hεNbr.le (hεNbrCap.trans hκcap) hκauxRate hκauxRet
    εStable ζStable capStable size aStable bStable eStable f₀ hζStable hStable
  obtain ⟨boundary,lossInside,inside,loc,hboundary,hSum,D₀,C,hTerminal,hFor⟩:=hNumMatch.2
  refine ⟨boundary,lossInside,inside,loc,hboundary,hSum,D₀,C,hTerminal,?_⟩
  have hStateSets :
      (letI:DecidableEq (Fin 6):=referenceWitnessFinDecidable 6; ({0,1,2,3,4}:Finset (Fin 6))) =
      (letI:DecidableEq (Fin 6):=instDecidableEqFin 6; ({0,1,2,3,4}:Finset (Fin 6))) := by
    ext i
    simp
  rw [←hStateSets] at hFor
  intro S hSP hRegS hEditS hInnerS hReserveS
  exact hFor S hSP hRegS hEditS hInnerS hReserveS
end Oberwolfach
