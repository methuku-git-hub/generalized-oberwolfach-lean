module

public import Oberwolfach.FirstVortexSelectorFailureIntegratedTail

@[expose] public section
/-! The complete positive-sample selector continuation, named so that its
parent constants can be shared with the uniform level choice. -/
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

def FirstVortexSelectorConcreteTail
    (r h k₀ Qpow:ℕ) (αRef sstar ω γRich tstar kstar ρ₀:ℝ) (hρ₀:0<ρ₀)
    (β βCommon εAbs εRob ζRob δAbs εAbsP ζAbsP δAbsP βconfigP βCommonP εStable ζStable capStable:ℝ):Prop :=
    ∀(εQ:ℝ) (hεQ:0<εQ) (hεQ1:εQ<1/4) (hεQAbs:εQ≤εAbs) (hεQRob:εQ≤εRob)
      (hεQsmall:εQ≤min ((γRich/2)*kstar) tstar/128),
    ∀ (αHost rPart ζret:ℝ) (hαHost:0<αHost) (hrPart:0<rPart) (hζret:0<ζret)
      (hεQHost:εQ≤αHost/100000),
    ∀ (K:ℕ) (hK3:3≤K) (hm:7≤(r+4))
    (θ:ℝ) (hθpos:0<θ) (hθ:θ≤1/100)
    (htstarBound:tstar≤(1/100)/(((r+4):ℕ):ℝ))
    (d:ℕ) (hd:2≤d) (cBoundary:ℝ) (hcBoundary:0<cBoundary) (hspacing:4/(d:ℝ)≤cBoundary) (hcut:(1/((((r+4):ℕ):ℝ)+1))/(d:ℝ)≤θ)
    (BM:ℝ) (hBM:0<BM) (BO:Fin K→ℝ) (hBO:∀i,0<BO i),
    let ni:=@longPaddedSeedExponent K
    let hni:=@long_padded_seed_exponent_positive K
    let hpadded:=@long_padded_seed_length_eq_exponent K
    let pstar₀:=min (1/4:ℝ) (min (ρ₀/8) (ρ₀/(6*((((r+4):ℕ):ℝ)+1))))
    let BMseed₀:=2*BM/pstar₀^(2*(r+4)+1)
    let BOseed₀:=fun i=>2*BO i/pstar₀^(2*(ni i+2))
    let Kpair₀:=1+((((r+4):ℕ):ℝ)+1)^4*BMseed₀+∑i:Fin K,((ni i:ℝ)+2)^3*BOseed₀ i
    let C₀:=10*(((((r+4):ℕ):ℝ)+1)^4*BMseed₀+∑i:Fin K,((ni i:ℝ)+2)^4*BOseed₀ i)
    ∀(lam:ℝ) (hlam:0<lam) (hlamθ:lam≤θ) (ξCap:ℝ) (hξCap:0<ξCap),
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
    ∃eps:ℝ,0<eps ∧ eps≤1 ∧ 3*eps≤(min lam epsOrd)*(θ/(100*(K:ℝ)^2)) ∧ eps≤epsOrd ∧
    let alpha:=min ((min lam epsOrd)/(10*(d:ℝ))) (θ/(200*(K:ℝ)^2))
    let γ:=min (eps/2) (min (1/2:ℝ) (min ((min lam epsOrd)/(10*(d:ℝ))) ((min lam epsOrd)/10)))
    0<alpha ∧ alpha≤θ/(200*(K:ℝ)^2) ∧ 0<γ ∧ γ≤eps ∧
    ∃ε₀ ηEvent:ℝ,0<ε₀ ∧ ε₀<1 ∧ 0<ηEvent ∧ 0<1-(36*(ε₀+6*ηEvent)+ηEvent) ∧
    ∃ εExtra:ℝ,0<εExtra ∧ (0<ε₀→4*εExtra≤ε₀) ∧
    ∀ (γLevel σLevel κmax κauxCap ζCap:ℝ),0<γLevel→0<σLevel→0<κmax→0<κauxCap→0<ζCap →
    ∃ gammaLoss sigmaLoss:ℝ,0<gammaLoss ∧ 0<sigmaLoss ∧ gammaLoss≤γLevel ∧ sigmaLoss≤σLevel ∧ gammaLoss≤ζOrd/2 ∧
    ∃ ζCorr ξCorr η₀ κ εRef εNbr:ℝ,0<ζCorr ∧ ζCorr≤ζRob ∧ ζCorr≤ζCap ∧ 0<ξCorr ∧
      16*((((r+4):ℕ):ℝ)+1)*ξCorr≤ζCorr ∧
      (∀n:ℕ,6*(8*((((r+4):ℕ):ℝ)+1)*ξCorr*n)≤min (gammaLoss*n) (sigmaLoss*n)) ∧
      0<η₀ ∧ 0<κ ∧ κ≤κmax ∧ κ≤κauxCap ∧ εRef=κ/4 ∧ εRef≤κmax/4 ∧ 0<εRef ∧ 0<εNbr ∧ εNbr≤κauxCap ∧
    ∃χ χCommon χBal χNbr χLoad χLocal χConfig:ℝ,
      0<χ ∧ 0<χCommon ∧ 0<χBal ∧ 0<χNbr ∧ 0<χLoad ∧ 0<χLocal ∧ 0<χConfig ∧
      χ+χCommon+χBal+2*χNbr+χLoad+χLocal+χConfig+εExtra<ε₀ ∧
    ∀ (ζ εBal ζBal:ℝ) (hζ:0<ζ) (hεBal:0<εBal) (hζBal:0<ζBal),
    let Qreal:ℝ:=1
    let pstarRef:ℝ:=kstar
    let ζNbr:ℝ:=1
    let εLoad:ℝ:=1
    let ζLoad:ℝ:=1
    let ζLocal:ℝ:=1
    let ζConfig:ℝ:=1
    let τLevel:ℝ:=1
    let hNbr:ℕ:=1;
    ∀ δparent:ℝ,0<δparent→∃βmax:ℝ,0<βmax ∧ ∀βQ:ℝ,0≤βQ→βQ≤1/4→βQ≤αRef/4→βQ≤βmax→βQ≤εBal/4→βQ≤εRef/4→
    ∃MLevel:ℕ,1≤MLevel ∧
    ∃mLevel:ℕ,1≤mLevel ∧ ∃η:ℝ,0<η ∧ ∃t₀ τ₀ Δ ξ:ℝ,0<t₀ ∧ 0<τ₀ ∧ τ₀≤1/16 ∧ 0<Δ ∧ 0<ξ ∧ 4*ξ≤eps/2 ∧
    ∃ξResidual:ℝ,0≤ξResidual ∧ 4*ξResidual≤epsOrd/2 ∧ ζOrd≤ξResidual ∧ ξ≤ξResidual ∧ ξSeed≤ξResidual ∧
      (∀n:ℕ,ζOrd*n≤ξResidual*n ∧ ξ*n≤ξResidual*n ∧ ξSeed*n≤ξResidual*n) ∧
    ∃ζList:ℝ,0<ζList ∧ ζList≤Δ ∧ ∃N:ℕ,
    ∀size:ℕ,∃a₀ b₀ e₀ aRob bRob eRob aParent bParent eParent aStable bStable eStable:ℕ,∀f₀ B:ℕ,∃NHost:ℕ,
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
    let Prior:=LongMatchingCommonEvent P π Dnat vsize βQ εQ Q hpres
      r K d size a₀ b₀ e₀ aRob bRob eRob f₀ L hNbr F hF θ ρ
      β βCommon εAbs εRob ζRob εRef κmax γRich tstar ζ εBal ζBal εNbr ζNbr Bload εLoad ζLoad ζLocal ζConfig
      ρ₀ sstar kstar τLevel levelWeight;
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
    ∃z,0<(μ.sigma (fun ω=>ν (f ω))).mass z ∧ ((fun z=>(((Prior ⟨f z.1,z.2⟩ ∧ ((ExpandedGood z ∧ MarkedRetainedRobustChangeEvent P π d r false false εStable ζStable capStable size aStable bStable eStable f₀ ⟨f z.1,z.2⟩) ∧
          ((∀v,|(((P.neighborFinset v∩Q.extendedVertices 1).filter (fun x=>(z.1 (Sum.inl s(v,x))).1=4)).card:ℝ)-
            udens*(P.neighborFinset v∩Q.extendedVertices 1).card|<(n:ℝ)^(3/4:ℝ)) ∧
          (∀u,|rawIntervalUnassignedHubCountOn π d (fun e=>z.1 (Sum.inr e)) u (Q.extendedVertices 1)-
            ((Q.extendedVertices 1).card:ℝ)*(1-(∑g,q u g)-(∑j,s u j))|<((Q.extendedVertices 1).card:ℝ)^(3/4:ℝ)) ∧
          (∀v,|rawIntervalUnassignedColumnCount π d (fun e=>z.1 (Sum.inr e)) v (Q.extendedIndices 1)-
            ∑u∈Q.extendedIndices 1,(1-(∑g,q u g)-(∑j,s u j))|<((Q.extendedVertices 1).card:ℝ)^(3/4:ℝ)) ∧
          (∀v∈Q.extendedVertices 1,((rawIntervalBoundaryHubSet π d (fun e=>z.1 (Sum.inr e)) (Q.extendedIndices 1) v).card:ℝ)≤
            4*((Q.extendedIndices 1).card:ℝ)/d+4*((Q.extendedVertices 1).card:ℝ)^(3/4:ℝ)) ∧
          RetainedRestrictionLocalGood π d (fun e=>z.1 (Sum.inr e)) false
            (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false)) (Q.extendedVertices 1) (Q.extendedIndices 1) ζ z.2 ∧
          (∀x y,x≠y→(5/8:ℝ)*(1/100:ℝ)^2*Fintype.card U-(n:ℝ)^(3/4:ℝ)≤
            (((Finset.univ:Finset U).filter (fun w=>rawIntervalFamilyState π d (fun e=>z.1 (Sum.inr e)) (x,w)=some (Sum.inr false) ∧
              rawIntervalFamilyState π d (fun e=>z.1 (Sum.inr e)) (y,w)=some (Sum.inr false))).card:ℝ))) ∧
          ((∀u,|rawIntervalUnassignedHubCountOn π d (fun e=>z.1 (Sum.inr e)) u (Q.extendedVertices 1)-
            ((Q.extendedVertices 1).card:ℝ)*(1-(∑g,q u g)-(∑j,s u j))|<(n:ℝ)^(3/4:ℝ)) ∧
           (∀v,|rawIntervalUnassignedColumnCount π d (fun e=>z.1 (Sum.inr e)) v Finset.univ-
            ∑u:U,(1-(∑g,q u g)-(∑j,s u j))|<(n:ℝ)^(3/4:ℝ)))) ∧ LongOrderedEveryClassSampleTests P π r K d θ ρ D F hF z ∧ ParentGood ⟨f z.1,z.2⟩ ∧
        (∀v,((rawIntervalExtendedAnyHubSet π d (fun e=>z.1 (Sum.inr e)) v).card:ℝ)≤
          4*(Fintype.card U:ℝ)/(((r+4):ℕ):ℝ)+4*(n:ℝ)^(3/4:ℝ)) ∧
        (∀u i,|rawIntervalReservedLabelHubCountOn π d (fun e=>z.1 (Sum.inr e)) u false
          (rawSelectedNeighbourTestSet P π d (fun e=>z.1 (Sum.inl e)) i)-
          (rawSelectedNeighbourTestSet P π d (fun e=>z.1 (Sum.inl e)) i).card*s u false|<(n:ℝ)^(3/4:ℝ)) ∧
        MarkedProtectedAbsorbableCorrectionWithBounds P π d r size aRob bRob eRob f₀ εRob ζCorr ξCorr (f z.1)
          (retainedRawMarkedSpokes π d (fun e=>f z.1 (Sum.inr e)) false
            (startRetentionMinimum (rawStartHubSet π d (fun e=>f z.1 (Sum.inr e)) false)) z.2 false false)
          (Q.extendedVertices 1) (Q.extendedIndices 1) ∧
        (∀(γList pstarList βList lamList ζList:ℝ),
          0≤γList→0≤pstarList→pstarList≤ρ*(1/100)/2→0≤βList→0≤lamList→0≤ζList→
          (∀x,(1/2+γList)*n≤(P.degree x:ℝ))→
          (n:ℝ)^(3/4:ℝ)+2*(2*((3*d:ℕ):ℝ)+1)≤γList*pstarList^2*n→
          βList*n+(n:ℝ)^(3/4:ℝ)≤γList*pstarList^2*n*(1/100:ℝ)→
          (lamList+2*ζList)*n≤βList*n→
          ∀(Del:SimpleGraph (Fin n)),(∀x,(Del.degree x:ℝ)≤ζList*n)→
          ∀(Inner:Finset (Fin n)) (βfinal εInner η:ℝ),0≤βfinal→
          (Inner.card:ℝ)≤εInner*n→(n:ℝ)^(3/4:ℝ)≤η*n→
          βfinal+εInner+1/(100*((r+4:ℕ):ℝ))+η≤lamList→
          let D:=rawSelectedPhysicalRelation P π d (fun e=>z.1 (Sum.inl e))
          let Dfree:=fun x y=>D x y ∧ ¬Del.Adj x y;
          ∀u,IsExtendingList Dfree (rawReservedSpokeList π d (fun e=>z.1 (Sum.inr e)) u\
            (Inner∪retainedFinalMarkedAt π d (fun e=>z.1 (Sum.inr e))
              (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false)) z.2 u)) βfinal) ∧
        (let βList:ℝ:=(min (2*αRef) (1/4:ℝ))*(ρ₀/200)^2*(1/100)/16;
          εQ≤βList/32→1/(100*((r+4:ℕ):ℝ))≤βList/16→
          ∀(Del:SimpleGraph (Fin n)),(∀x,(Del.degree x:ℝ)≤ζList*n)→
          ∀(Inner:Finset (Fin n)),(Inner.card:ℝ)≤εQ*n→
          let D:=rawSelectedPhysicalRelation P π d (fun e=>z.1 (Sum.inl e))
          let Dfree:=fun x y=>D x y ∧ ¬Del.Adj x y;
          ∀u,IsExtendingList Dfree (rawReservedSpokeList π d (fun e=>z.1 (Sum.inr e)) u\
            (Inner∪retainedFinalMarkedAt π d (fun e=>z.1 (Sum.inr e))
              (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false)) z.2 u)) (βList/2)) ∧
        (let βList:ℝ:=(min (2*αRef) (1/4:ℝ))*(ρ₀/200)^2*(1/100)/16;
          εQ≤βList/32→1/(100*((r+4:ℕ):ℝ))≤βList/16→
          ∀(Del:SimpleGraph (Fin n)),(∀x,(Del.degree x:ℝ)≤ζList*n)→
          ((          let raw:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedApproximateCollapse e (z.1 e)
          let S:=longRawSurvivingResources P π d raw true true Del.edgeFinset
          let T:=bernoulliVertexSet (longRawHubState P π d raw true true)
          let e:S↪LongRawHubResource n U:=Function.Embedding.subtype _
          let Cand:=RestrictedResource (mixedCandidateResources R) e
          let Q:=restrictedResourceSet (mixedCandidateResources R) e
          let fS:=survivingResourceEmbedding S T (long_raw_surviving_resources_subset P π d raw true true Del.edgeFinset)
          let φ:=fS.trans (markedRawSampledPhysicalEmbedding P π d raw true true)
          let hub:=longRawHubNames (U:=U) π d (r+4) ℓ
          let test:=fun (j:LongRetainedHubTest F hF K θ) (c:Cand)=>longRetainedHubIndicator F hF θ hub j c.val
          ∃M:Finset Cand,(∀c∈M,0<mixedCandidateWeight Wmix c.val) ∧
            (∀c∈M,∀c'∈M,c≠c'→Disjoint (Q c) (Q c')) ∧
            (∀x,alpha*n≤(rimIncidentResources φ x).card →
              ((rimIncidentResources φ x\M.biUnion Q).card:ℝ)≤γ*(rimIncidentResources φ x).card) ∧
            (∀i,((longRawIncidenceSet S i\M.biUnion Q).card:ℝ)≤max (alpha*n) (γ*(longRawIncidenceSet S i).card)) ∧
            (∀i,alpha*n≤(longRawIncidenceSet S i).card →
              ((longRawIncidenceSet S i\M.biUnion Q).card:ℝ)≤γ*(longRawIncidenceSet S i).card) ∧
            (∀j,(1-γ)*(∑c,test j c*mixedCandidateWeight Wmix c.val)≤∑c∈M,test j c) ∧
            (∀j,(∑c∈M,test j c)≤(1+γ)*(∑c,test j c*mixedCandidateWeight Wmix c.val)) ∧
            (∀x,((physicalRimResidualGraph (markedRawSampledPhysicalEmbedding P π d raw true true)
              ((M.map (survivingCandidateEmbedding (mixedCandidateResources R) S T
                (long_raw_surviving_resources_subset P π d raw true true Del.edgeFinset))).biUnion
                (restrictedResourceSet (mixedCandidateResources R) (Function.Embedding.subtype (·∈T))))).degree x:ℝ)≤max alpha γ*n+(ζList*n)) ∧
            let selected:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedMarkedCollapse e (z.1 e)
            let H:=retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) false
              (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false)) z.2 false false
            ∀(Reserve:Finset (Finset (Fin n)⊕(Fin n×U))) (X:Finset (Fin n)) (Z:Finset U),
            MarkedFixedTerminalAbsorber P π d (r+4) selected H Reserve X Z →
            let state:=longRawHubState P π d raw true true
    let T:=bernoulliVertexSet state
    let eraw:{z // z∈T}↪_:=Function.Embedding.subtype _
    let q:=survivingCandidateEmbedding (mixedCandidateResources R) S T (long_raw_surviving_resources_subset P π d raw true true Del.edgeFinset)
    let N:=M.map q
    let A:=LongRawSelectedOrdinary π d (r+4) ℓ eraw N
    let Q:=longRawSelectedOrdinaryWheel π d (r+4) ℓ eraw N
    ∃assign:A↪(Σu,(F u).ConnectedComponent),
    ∃C:∀a:A,(F (Q a).val.2).ConnectedComponent,
      (∀a,(⟨(Q a).val.2,C a⟩:Σu,(F u).ConnectedComponent)=assign a) ∧
    (∀u,Fintype.card (longRawSourceDomain F π d (r+4) ℓ eraw N C u) =
      ∑i:Fin K,(N.filter (fun c=>c.val.1=some i ∧
        longRawSeedHub π d (r+4) ℓ c.val.1 c.val.2=u)).card * ℓ i) ∧
    (∀u,Fintype.card {v:Fin n // v∉longRawSourceDomain F π d (r+4) ℓ eraw N C u} =
      n - ∑i:Fin K,(N.filter (fun c=>c.val.1=some i ∧
        longRawSeedHub π d (r+4) ℓ c.val.1 c.val.2=u)).card * ℓ i) ∧
    (∀u,|((Fintype.card (longRawSourceDomain F π d (r+4) ℓ eraw N C u):ℕ):ℝ) -
      (1-θ)*(n:ℝ)*(∑i:Fin K,longAssignedKeptFraction F hF K θ i u)| ≤
      ((max (3*eps) 0)*(n:ℝ))*(∑i:Fin K,((ℓ i:ℕ):ℝ))) ∧
    (∀u,|((Fintype.card {v:Fin n // v∉longRawSourceDomain F π d (r+4) ℓ eraw N C u}:ℕ):ℝ) -
      ((n:ℝ)-(1-θ)*(n:ℝ)*(∑i:Fin K,longAssignedKeptFraction F hF K θ i u))| ≤
      ((max (3*eps) 0)*(n:ℝ))*(∑i:Fin K,((ℓ i:ℕ):ℝ))) ∧
    (∀u, (n:ℝ)*ordinaryAssignedFraction F hF K u none -
      ((max (3*eps) 0)*(n:ℝ))*(∑i:Fin K,((ℓ i:ℕ):ℝ)) ≤
        ((Fintype.card {v:Fin n // v∉longRawSourceDomain F π d (r+4) ℓ eraw N C u}:ℕ):ℝ) ∧
      ((Fintype.card {v:Fin n // v∉longRawSourceDomain F π d (r+4) ℓ eraw N C u}:ℕ):ℝ) ≤
        (n:ℝ)*(ordinaryAssignedFraction F hF K u none+(101/100:ℝ)*θ) +
          ((max (3*eps) 0)*(n:ℝ))*(∑i:Fin K,((ℓ i:ℕ):ℝ))) ∧
    (∀u v,K<Fintype.card ((F u).connectedComponentMk v)→
      v∉longRawSourceDomain F π d (r+4) ℓ eraw N C u) ∧
    let T:=longRawSourceDomain F π d (r+4) ℓ eraw N C
    ∃ψ:∀u,(T u)↪Fin n,
      (∀u x y,(F u).Adj x.val y.val→
        rawMarkedPairRims P π d raw (Sum.inl (ψ u x,ψ u y)) ∨
        rawMarkedPairRims P π d raw (Sum.inl (ψ u y,ψ u x))) ∧
      (∀u v,u≠v→Disjoint
        (partialFactorPhysicalEdges (T u) ((F u).induce (T u)) (ψ u))
        (partialFactorPhysicalEdges (T v) ((F v).induce (T v)) (ψ v))) ∧
      (∀u x y,(F u).Adj x.val y.val→Sum.inl ({ψ u x,ψ u y}:Finset (Fin n))∉Reserve) ∧
      (∀u x y,(F u).Adj x.val y.val→s(ψ u x,ψ u y)∉Del.edgeFinset)) ∧ LongSampleReservedLists P π d z Del (Q.extendedVertices 1) (βList/2))) ∧
        (let selected:RawMarkedRetainedOutcome (U:=U) (Color:=Bool) π d false:=⟨f z.1,z.2⟩
         let H:=retainedRawMarkedSpokes π d (fun e=>selected.1 (Sum.inr e)) false
           (startRetentionMinimum (rawStartHubSet π d (fun e=>selected.1 (Sum.inr e)) false)) selected.2 false false;
         Nonempty (MarkedVortexFiniteSampleChain Q π hpres selected.1 H Q.length Q.length_pos)) ∧
        (Q.length-1=0 ∨ MarkedActualVortexBalanceProperty Q π hpres d (r+4) ((Q.length-1)-1) false false εBal ζBal
          (markedVortexDeeperVertices Q) (markedVortexDeeperHubs Q) ⟨f z.1,z.2⟩) ∧
        (∀u i,|rawIntervalUnassignedHubCountOn π d (fun e=>z.1 (Sum.inr e)) u
          (rawSelectedNeighbourTestSet P π d (fun e=>z.1 (Sum.inl e)) i)-
          (rawSelectedNeighbourTestSet P π d (fun e=>z.1 (Sum.inl e)) i).card*
          (1-(∑g,q u g)-(∑j,s u j))|<(n:ℝ)^(3/4:ℝ)) ∧
        (∀x y,x≠y→((P.neighborFinset x∩P.neighborFinset y).card:ℝ)*p₁^2-(n:ℝ)^(3/4:ℝ)-
          2*(2*((3*d:ℕ):ℝ)+1)≤((Finset.univ.filter (fun v=>
            0<markedPhysicalRim P π (3*d) (fun e=>markedExpandedPhysicalCollapse (z.1 (Sum.inl e))) false x v ∧
            0<markedPhysicalRim P π (3*d) (fun e=>markedExpandedPhysicalCollapse (z.1 (Sum.inl e))) false v y)).card:ℝ)) ∧
        (∀j v,|((∑w,sampledColourOrientation P (fun e=>z.1 (Sum.inl e)) j v w:ℕ):ℝ)-
          markedExpandedPhysicalProbability p₁ k₁ p₂ k₂ udens j/2*P.degree v|<(n:ℝ)^(3/5:ℝ)) ∧
        (∀u g,|rawIntervalHubStartCount π d g (fun e=>z.1 (Sum.inr e)) u-(n:ℝ)*q u g/d|<(n:ℝ)^(3/4:ℝ)/d) ∧
        MarkedRetainedReservoirSelection r d size a₀ b₀ e₀ f₀ εAbs P π false false ⟨f z.1,z.2⟩ ∧
        MarkedVortexFixedSelection r d size a₀ b₀ e₀ f₀ εAbs P π false false ⟨f z.1,z.2⟩ ∧
        (∀b u,|rawMarkedRestrictedSpokeCol π d (fun e=>z.1 (Sum.inr e)) true true b u Finset.univ-
          (if b then q u true else s u true)*(n:ℝ)|<tHub) ∧
        (∀u,|(((ordinaryCommonHubSpokeRoots u).filter (fun root=>
          longRawHubState P π d (fun e=>rawExpandedApproximateCollapse e (z.1 e)) true true root=true)).card:ℝ)-
          longAssignedApproxOrdinaryWeight F hF K (r+4) θ u*n|≤tHub) ∧
        rawMarkedSeedConcentrated P π d (r+4) p₂ k₂ q s true true t Wm
          (fun e=>rawExpandedApproximateCollapse e (z.1 e)) ∧
        (∀i,rawOrdinarySeedConcentrated P π d (ni i+2) p₂ k₂ q s true true t (Wo i)
          (fun e=>rawExpandedApproximateCollapse e (z.1 e))) ∧
        (∀i root,longRawHubState P π d (fun e=>rawExpandedApproximateCollapse e (z.1 e)) true true root=true→
          |resourcePatternLoad (longRawHubResources (U:=U) π d (r+4) (fun i=>ni i+2) i)
            (longMixedSeedWeight Wm Wo i) (fun _ _=>true) root
            (longRawHubState P π d (fun e=>rawExpandedApproximateCollapse e (z.1 e)) true true)-
            longAssignedMixedTarget F hF K (r+4) θ D p₂ k₂ i root|≤
          t+τ*longAssignedMixedTarget F hF K (r+4) θ D p₂ k₂ i root) ∧
        (∀(Del:SimpleGraph (Fin n)) (δ:ℝ), (∀x,(Del.degree x:ℝ)≤δ)→
          δ≤Δ*n→
          let raw:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedApproximateCollapse e (z.1 e)
          let hub:=longRawHubNames (U:=U) π d (r+4) ℓ
          let S:=longRawSurvivingResources P π d raw true true Del.edgeFinset
          let e:{v // v∈S}↪_:=Function.Embedding.subtype _
          ∀ztest:LongRetainedHubTest F hF K θ,
            θ*(n:ℝ)/(200*(K:ℝ)*(K:ℝ))≤
              ∑c:RestrictedResource (mixedCandidateResources R) e,
                longRetainedHubIndicator F hF θ hub ztest c.val*mixedCandidateWeight Wmix c.val) ∧
        (∀(Del:SimpleGraph (Fin n)) (δ:ℝ), (∀x,(Del.degree x:ℝ)≤δ)→
          δ≤Δ*n→0≤t+C*(δ/(n:ℝ))+4*τ ∧ t+C*(δ/(n:ℝ))+4*τ≤eps/2) ∧
        (∀(Del:SimpleGraph (Fin n)) (δ:ℝ), (∀x,(Del.degree x:ℝ)≤δ)→
          δ≤Δ*n→
          let raw:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedApproximateCollapse e (z.1 e)
          let S:=longRawSurvivingResources P π d raw true true Del.edgeFinset
          let T:=bernoulliVertexSet (longRawHubState P π d raw true true)
          let e:S↪LongRawHubResource n U:=Function.Embedding.subtype _
          let Cand:=RestrictedResource (mixedCandidateResources R) e
          let Q:=restrictedResourceSet (mixedCandidateResources R) e
          let fS:=survivingResourceEmbedding S T (long_raw_surviving_resources_subset P π d raw true true Del.edgeFinset)
          let φ:=fS.trans (markedRawSampledPhysicalEmbedding P π d raw true true)
          let hub:=longRawHubNames (U:=U) π d (r+4) ℓ
          let test:=fun (j:LongRetainedHubTest F hF K θ) (c:Cand)=>longRetainedHubIndicator F hF θ hub j c.val
          ∃M:Finset Cand,(∀c∈M,0<mixedCandidateWeight Wmix c.val) ∧
            (∀c∈M,∀c'∈M,c≠c'→Disjoint (Q c) (Q c')) ∧
            (∀x,alpha*n≤(rimIncidentResources φ x).card →
              ((rimIncidentResources φ x\M.biUnion Q).card:ℝ)≤γ*(rimIncidentResources φ x).card) ∧
            (∀i,((longRawIncidenceSet S i\M.biUnion Q).card:ℝ)≤max (alpha*n) (γ*(longRawIncidenceSet S i).card)) ∧
            (∀i,alpha*n≤(longRawIncidenceSet S i).card →
              ((longRawIncidenceSet S i\M.biUnion Q).card:ℝ)≤γ*(longRawIncidenceSet S i).card) ∧
            (∀j,(1-γ)*(∑c,test j c*mixedCandidateWeight Wmix c.val)≤∑c∈M,test j c) ∧
            (∀j,(∑c∈M,test j c)≤(1+γ)*(∑c,test j c*mixedCandidateWeight Wmix c.val)) ∧
            (∀x,((physicalRimResidualGraph (markedRawSampledPhysicalEmbedding P π d raw true true)
              ((M.map (survivingCandidateEmbedding (mixedCandidateResources R) S T
                (long_raw_surviving_resources_subset P π d raw true true Del.edgeFinset))).biUnion
                (restrictedResourceSet (mixedCandidateResources R) (Function.Embedding.subtype (·∈T))))).degree x:ℝ)≤max alpha γ*n+δ) ∧
            let selected:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedMarkedCollapse e (z.1 e)
            let H:=retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) false
              (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false)) z.2 false false
            ∀(Reserve:Finset (Finset (Fin n)⊕(Fin n×U))) (X:Finset (Fin n)) (Z:Finset U),
            MarkedFixedTerminalAbsorber P π d (r+4) selected H Reserve X Z →
            let state:=longRawHubState P π d raw true true
    let T:=bernoulliVertexSet state
    let eraw:{z // z∈T}↪_:=Function.Embedding.subtype _
    let q:=survivingCandidateEmbedding (mixedCandidateResources R) S T (long_raw_surviving_resources_subset P π d raw true true Del.edgeFinset)
    let N:=M.map q
    let A:=LongRawSelectedOrdinary π d (r+4) ℓ eraw N
    let Q:=longRawSelectedOrdinaryWheel π d (r+4) ℓ eraw N
    ∃assign:A↪(Σu,(F u).ConnectedComponent),
    ∃C:∀a:A,(F (Q a).val.2).ConnectedComponent,
      (∀a,(⟨(Q a).val.2,C a⟩:Σu,(F u).ConnectedComponent)=assign a) ∧
    (∀u,Fintype.card (longRawSourceDomain F π d (r+4) ℓ eraw N C u) =
      ∑i:Fin K,(N.filter (fun c=>c.val.1=some i ∧
        longRawSeedHub π d (r+4) ℓ c.val.1 c.val.2=u)).card * ℓ i) ∧
    (∀u,Fintype.card {v:Fin n // v∉longRawSourceDomain F π d (r+4) ℓ eraw N C u} =
      n - ∑i:Fin K,(N.filter (fun c=>c.val.1=some i ∧
        longRawSeedHub π d (r+4) ℓ c.val.1 c.val.2=u)).card * ℓ i) ∧
    (∀u,|((Fintype.card (longRawSourceDomain F π d (r+4) ℓ eraw N C u):ℕ):ℝ) -
      (1-θ)*(n:ℝ)*(∑i:Fin K,longAssignedKeptFraction F hF K θ i u)| ≤
      ((max (3*eps) 0)*(n:ℝ))*(∑i:Fin K,((ℓ i:ℕ):ℝ))) ∧
    (∀u,|((Fintype.card {v:Fin n // v∉longRawSourceDomain F π d (r+4) ℓ eraw N C u}:ℕ):ℝ) -
      ((n:ℝ)-(1-θ)*(n:ℝ)*(∑i:Fin K,longAssignedKeptFraction F hF K θ i u))| ≤
      ((max (3*eps) 0)*(n:ℝ))*(∑i:Fin K,((ℓ i:ℕ):ℝ))) ∧
    (∀u, (n:ℝ)*ordinaryAssignedFraction F hF K u none -
      ((max (3*eps) 0)*(n:ℝ))*(∑i:Fin K,((ℓ i:ℕ):ℝ)) ≤
        ((Fintype.card {v:Fin n // v∉longRawSourceDomain F π d (r+4) ℓ eraw N C u}:ℕ):ℝ) ∧
      ((Fintype.card {v:Fin n // v∉longRawSourceDomain F π d (r+4) ℓ eraw N C u}:ℕ):ℝ) ≤
        (n:ℝ)*(ordinaryAssignedFraction F hF K u none+(101/100:ℝ)*θ) +
          ((max (3*eps) 0)*(n:ℝ))*(∑i:Fin K,((ℓ i:ℕ):ℝ))) ∧
    (∀u v,K<Fintype.card ((F u).connectedComponentMk v)→
      v∉longRawSourceDomain F π d (r+4) ℓ eraw N C u) ∧
    let T:=longRawSourceDomain F π d (r+4) ℓ eraw N C
    ∃ψ:∀u,(T u)↪Fin n,
      (∀u x y,(F u).Adj x.val y.val→
        rawMarkedPairRims P π d raw (Sum.inl (ψ u x,ψ u y)) ∨
        rawMarkedPairRims P π d raw (Sum.inl (ψ u y,ψ u x))) ∧
      (∀u v,u≠v→Disjoint
        (partialFactorPhysicalEdges (T u) ((F u).induce (T u)) (ψ u))
        (partialFactorPhysicalEdges (T v) ((F v).induce (T v)) (ψ v))) ∧
      (∀u x y,(F u).Adj x.val y.val→Sum.inl ({ψ u x,ψ u y}:Finset (Fin n))∉Reserve) ∧
      (∀u x y,(F u).Adj x.val y.val→s(ψ u x,ψ u y)∉Del.edgeFinset))) ∧
      ((∀u,|(((ordinaryCommonHubSpokeRoots u).filter (fun root=>
        longRawHubState P π d (fun e=>rawExpandedApproximateCollapse e (z.1 e)) true true root=true)).card:ℝ)-
        longAssignedApproxOrdinaryWeight F hF K (r+4) θ u*n|≤ξSeed*n) ∧
      (∀i root,longRawHubState P π d (fun e=>rawExpandedApproximateCollapse e (z.1 e)) true true root=true→
        |resourcePatternLoad (longRawHubResources (U:=U) π d (r+4) (fun i=>ni i+2) i)
          (longMixedSeedWeight Wm Wo i) (fun _ _=>true) root
          (longRawHubState P π d (fun e=>rawExpandedApproximateCollapse e (z.1 e)) true true)-
          longAssignedMixedTarget F hF K (r+4) θ D p₂ k₂ i root|≤
        tSeed+τ*longAssignedMixedTarget F hF K (r+4) θ D p₂ k₂ i root) ∧
      (∀(Del:SimpleGraph (Fin n)) (δ:ℝ), (∀x,(Del.degree x:ℝ)≤δ)→
        δ≤ΔSeed*n→0≤tSeed+C*(δ/(n:ℝ))+4*τ ∧ tSeed+C*(δ/(n:ℝ))+4*τ≤epsOrd/2)) ∧
      (∀Del:SimpleGraph (Fin n),(∀v,(Del.degree v:ℝ)≤ζOrd*n)→
        LongEarlyMatchingListsForDeletion r K d θ D alphaOrd γOrd epsOrd ζOrd
          ((min (2*αRef) (1/4:ℝ))*(ρ₀/200)^2*(1/100)/16) P π F hF weight w z (Q.extendedVertices 1) Del)) ∧
      LongEveryClassValidDeletionEvent ζOrd P π d r gammaLoss sigmaLoss ξClassOrd z
        (Q.extendedVertices 1) (Q.extendedIndices 1) K B θ D alphaOrd γOrd epsOrd
        ((min (2*αRef) (1/4:ℝ))*(ρ₀/200)^2*(1/100)/16) F hF weight w) ∧
      FirstVortexConcreteBoundaryEvent P π d r Dnat vsize βQ εQ Q θ ρ₀ BM BO F hF weight w
        alphaOrd γOrd epsOrd ζOrd ξSeed ΔSeed ζret ζ
        ((min (2*αRef) (1/4:ℝ))*(ρ₀/200)^2*(1/100)/16) tSeed τ z (Q.extendedVertices 1))) z ∧
      ∀v,((rawIntervalBoundaryHubSet π d (fun e=>z.1 (Sum.inr e)) (Q.extendedIndices 1) v).card:ℝ)≤cBoundary*((Q.extendedVertices 1).card:ℝ)


/-- Fix the selector's auxiliary host and seed tolerances while retaining
its complete same-sample conclusion. -/
theorem first_vortex_selector_concrete_tail
    (r h k₀ Qpow:ℕ) (αRef sstar ω γRich tstar kstar ρ₀:ℝ) (hρ₀:0<ρ₀)
    (hkstar:0<kstar) (hpstar:4*(((r+4):ℕ):ℝ)*kstar≤ρ₀*(1/100))
    (β βCommon εAbs εRob ζRob δAbs εAbsP ζAbsP δAbsP βconfigP βCommonP εStable ζStable capStable:ℝ)
    (hSelector:FirstVortexSelectorFailureIntegratedTail r h k₀ Qpow αRef sstar ω γRich tstar kstar ρ₀ hρ₀
      β βCommon εAbs εRob ζRob δAbs εAbsP ζAbsP δAbsP βconfigP βCommonP εStable ζStable capStable):
    FirstVortexSelectorConcreteTail r h k₀ Qpow αRef sstar ω γRich tstar kstar ρ₀ hρ₀
      β βCommon εAbs εRob ζRob δAbs εAbsP ζAbsP δAbsP βconfigP βCommonP εStable ζStable capStable :=by
  intro εQ he he1 heAbs heRob heSmall αHost rPart ζret hHost hrPart hret heHost
    K hK hm θ hθpos hθ htstarBound d hd cBoundary hcBoundary hspacing hcut BM hBM BO hBO
    ni hni hpadded pstar BMseed BOseed Kpair C lam hlam hlamθ ξCap hξCap
  have hh:=hSelector εQ he he1 heAbs heRob heSmall αHost rPart ζret hHost hrPart hret heHost
    K hK hm θ hθpos hθ htstarBound d hd cBoundary hcBoundary hspacing hcut BM hBM BO hBO lam hlam hlamθ ξCap hξCap
  obtain ⟨epsOrd,hepsOrd,hepsOrd1,hepsOrdRate,haOrd,haOrdBound,hγOrd,hγOrdBound,
    ηSeed,hηSeed,tSeed,τSeed,ΔSeed,ξSeed,htSeed,hτSeed,hτSeedBound,hΔSeed,hξSeed,hξSeedBound,
    ηOrd,hηOrd,tOrd,τOrd,ΔOrd,ξOrd,htOrd,hτOrd,hτOrdBound,hΔOrd,hξOrd,hξOrdBound,
    lamOrd,ηListOrd,ζOrd,hlamOrd,hηListOrd,hζOrd,hζOrdΔ,hζOrdE,hζOrdSeed,NListOrd,hList,
    cOrd,ξClassOrd,hcOrd,hξClassOrd,hξCapOrd,hξClassBound,hζSum,hOrient,
    eps,heps,heps1,hepsRate,hepsLe,ha,haBound,hγ,hγBound,
    ε₀,ηEvent,hε₀,hε₀one,hηEvent,hprob,εExtra,hExtra,hExtraBound,hh⟩:=hh
  refine ⟨epsOrd,hepsOrd,hepsOrd1,hepsOrdRate,haOrd,haOrdBound,hγOrd,hγOrdBound,
    ηSeed,hηSeed,tSeed,τSeed,ΔSeed,ξSeed,htSeed,hτSeed,hτSeedBound,hΔSeed,hξSeed,hξSeedBound,
    ηOrd,hηOrd,tOrd,τOrd,ΔOrd,ξOrd,htOrd,hτOrd,hτOrdBound,hΔOrd,hξOrd,hξOrdBound,
    lamOrd,ηListOrd,ζOrd,hlamOrd,hηListOrd,hζOrd,hζOrdΔ,hζOrdE,hζOrdSeed,NListOrd,hList,
    cOrd,ξClassOrd,hcOrd,hξClassOrd,hξCapOrd,hξClassBound,hζSum,hOrient,
    eps,heps,heps1,hepsRate,hepsLe,ha,haBound,hγ,hγBound,
    ε₀,ηEvent,hε₀,hε₀one,hηEvent,hprob,εExtra,hExtra,hExtraBound,?_⟩
  intro γLevel σLevel κmax κauxCap ζCap hγLevel hσLevel hκmax hκaux hζCap
  obtain ⟨gammaLoss,sigmaLoss,hGamma,hSigma,hGammaCap,hSigmaCap,hGammaOrd,
    ζCorr,ξCorr,η₀,κ,εRef,εNbr,hζCorr,hζRob,hζCap',hξCorr,hξCorrRate,hbudget,
    hη₀,hκ,hκmax',hκaux',hεRefEq,hεRefMax,hεRef,hεNbr,hεNbrCap,
    χ,χCommon,χBal,χNbr,χLoad,χLocal,χConfig,hχ,hχCommon,hχBal,hχNbr,hχLoad,hχLocal,hχConfig,hgap,hh⟩:=
    hh γLevel σLevel κmax κauxCap ζCap hγLevel hσLevel hκmax hκaux hζCap
  refine ⟨gammaLoss,sigmaLoss,hGamma,hSigma,hGammaCap,hSigmaCap,hGammaOrd,
    ζCorr,ξCorr,η₀,κ,εRef,εNbr,hζCorr,hζRob,hζCap',hξCorr,hξCorrRate,hbudget,
    hη₀,hκ,hκmax',hκaux',hεRefEq,hεRefMax,hεRef,hεNbr,hεNbrCap,
    χ,χCommon,χBal,χNbr,χLoad,χLocal,χConfig,hχ,hχCommon,hχBal,hχNbr,hχLoad,hχLocal,hχConfig,hgap,?_⟩
  intro ζ εBal ζBal hζ hεBal hζBal Qreal pstarRef ζNbr εLoad ζLoad ζLocal ζConfig τLevel hNbr
  exact hh 1 kstar ζ εBal ζBal 1 1 1 1 1 1 hkstar hζ hεBal hζBal
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) 1 (by omega) hpstar
end Oberwolfach
