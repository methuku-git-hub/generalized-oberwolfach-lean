module

public import Oberwolfach.FirstVortexCombinedEventValidDeletionCorrection
public import Oberwolfach.FirstVortexCombinedSelectorFixedClasses
public import Oberwolfach.LongEncodedActiveFromMatchingOnFixedClass

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 80000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance (priority := 2000) firstVortexFixedEventCorrectionSix : DecidableEq (Fin 6) := instDecidableEqFin 6
local instance firstVortexFixedEventCorrectionArc {n:ℕ} (P:(Fin n×Fin n)→Prop):DecidableEq {e:Fin n×Fin n // P e}:=Classical.decEq _
attribute [local instance] partitionedDivisibleArcFinite partitionedDivisibleOrdFinite partitionedDivisibleMarkFinite
local instance firstVortexFixedEventCorrectionFin (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n

theorem first_vortex_combined_event_fixed_class_correction
    (α lam lamAssign ε δold δlocal δglobal θ eps ξ ρ₀ bmatch ξPart ζret Δ:ℝ) (d K r e:ℕ)
    (rho eta δLoss εInner:ℝ) (hrho:0<rho) (heta:0<eta) (hetaR:eta≤rho)
    (hbudget:Δ+δLoss<eta) (hsupply:rho+Δ+δLoss+εInner<ρ₀/(400*((r+4:ℕ):ℝ)))
    (hα:0<α) (hlam:0<lam) (hε:0<ε) (hδ:0<δold) (hδ1:δold≤1) (hθ:0<θ) (hepsPos:0<eps)
    (hρ₀:0<ρ₀) (hbmatch:0<bmatch) (hαb:(2*α)/16≤bmatch)
    (hbd:bmatch≤((ρ₀/4)/40000)/16) (hεsmall:ε≤(ρ₀/4)/80000)
    (hθδ:10*θ≤δold) (hθlocal:θ≤δold/32) (hθhi:θ≤1/100)
    (hlamlocal:lam≤δold*ε/32) (hspacing:1/(d:ℝ)≤θ/1024)
    (hd:3≤d) (hK:3≤K) (hm:7≤(r+4))
    (heps:3*eps≤lam*(θ/(100*(K:ℝ)^2))) (hξ:4*ξ≤eps/2) (hξ0:0≤ξ)
    (hρ₀hi:ρ₀≤1) (hδglobal:0<δglobal) (hθglobal:10*θ≤δglobal)
    (hprecise:ε≤((ρ₀/4)/40000)/8192)
    (ξCap:ℝ) (hξPartCap:ξPart≤ξCap)
    (hCap:∀ξ':ℝ,ξ'≤ξCap→lam+ξ'≤((ρ₀/4)/40000)*θ/4096 ∧
      ξ'/2≤(lamAssign-lam)*ε ∧ ξ'≤α/32 ∧
      ∀n:ℕ,∀(U:Type) [Fintype U] (G:SimpleGraph (Fin n)) (D mm:ℕ) (β:ℝ)
        (Q:Vortex U G D β ε mm),0<mm→ξ'*n≤(δlocal-δold)*((Q.extendedVertices 1).card:ℝ))
    (hlamθ:lam≤θ) (hdlarge:(r+4)+2≤d)
    (Nret:ℕ) (hNret:∀n:ℕ,Nret≤n→∀q errOrd:ℝ,
      q≤1/((((r+4):ℕ):ℝ)+1)→errOrd≤θ*n→
      (n:ℝ)*q/d+(((((r+4)+1)*d-1:ℕ):ℝ))*(2*((n:ℝ)^(3/4:ℝ)/d)+ζret*n)+errOrd≤4*θ*n):
    ∃N:ℕ,∀n:ℕ,N≤n→∀ [Nonempty (Fin n)] (U:Type) [Fintype U] [DecidableEq U]
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (Dv mm:ℕ) (β:ℝ) (Vort:Vortex U P Dv β ε mm)
    (hreg:P.IsRegularOfDegree Dv) (hDv:0<Dv) (hρhi:initialIndexDensity U Dv≤1)
    (hρlo:ρ₀ ≤ initialIndexDensity U Dv) (hDlo:(n:ℝ)/2≤Dv) (hDhi:(Dv:ℝ)≤2*n) (hmm:0<mm)
    (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (Allowed:Set ℕ) (hAllowed:∀u,AllowedCycleLengths (F u) Allowed)
    (hclass:∀u,factorPreparationClass (F u) K=none)
    (hcut:(1/(((r+4):ℝ)+1))/(d:ℝ)≤θ)
    (hcutHost:5/((((r+4):ℝ)+1)*(d:ℝ)+5)+(((r+4):ℝ)+1)*(d:ℝ)/(K:ℝ)≤θ/2)
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (hεα:ε≤α/1000) (hlamhi:lam≤α/128)
    (a γ ρ ξSeed ΔSeed:ℝ)
    (haEq:a=min (lam/(10*(d:ℝ))) (θ/(200*(K:ℝ)^2)))
    (hγEq:γ=min (eps/2) (min (1/2:ℝ) (min (lam/(10*(d:ℝ))) (lam/10))))
    (hρEq:ρ=θ/4096) (hΔeps:Δ≤eps/8)
    (hξSeed:ξSeed≤ξ) (hΔSeed:Δ≤ΔSeed) (heps1:eps≤1)
    (hζ:ζret≤θ/4096) (hζ0:0≤ζret)
    (τ Asrc BM:ℝ) (hBM:0<BM) (weight:(Fin ((r+4)+1)→Fin n)→ℝ)
    (hw:SuccessorSequenceWeightConditions P π (3*d) Dv τ Asrc BM weight)
    (BO:Fin K→ℝ) (hBO:∀i,0<BO i)
    (w:∀i:Fin K,OrdinaryCycle P (longPaddedSeedExponent i+2)→ℝ) (hw0:∀i C,0≤w i C)
    (hwupper:∀i C,w i C≤BO i/(n:ℝ)^(longPaddedSeedExponent i))
    (z:MarkedExpandedActualOutcome (U:=U) π d) (ζselect:ℝ) (hζselect:ζselect≤ζret) (Inner:Finset (Fin n)) (βList:ℝ)
    (terr τerr:ℝ) (hτerr:0≤τerr)
,
    let raw:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedApproximateCollapse e ((z.1) e)
    let σ:=fun e=>raw (Sum.inr e)
    let ni:=@longPaddedSeedExponent K
    let hni:=@long_padded_seed_exponent_positive K
    let ℓ:=fun i=>ni i+2
    let p:=(∑u,longAssignedApproxOrdinaryWeight F hF K (r+4) θ u)/(Dv:ℝ)
    let k:=(∑u,longAssignedApproxMarkedWeight F hF K (r+4) θ u)/(Dv:ℝ)
    let udens:=2*(∑u,(1-(1/100:ℝ)-(1/100:ℝ)/((r+4):ℝ)-longAssignedApproxMarkedWeight F hF K (r+4) θ u-longAssignedApproxOrdinaryWeight F hF K (r+4) θ u))/(Dv:ℝ)
    let pstar:=min (1/4:ℝ) (min (ρ₀/8) (ρ₀/(6*(((r+4):ℝ)+1))))
    let BMseed:=2*BM/pstar^(2*(r+4)+1)
    let BOseed:=fun i=>2*BO i/pstar^(2*(ni i+2))
    let C:=10*((((r+4):ℝ)+1)^4*BMseed+∑i:Fin K,((ni i:ℝ)+2)^4*BOseed i)
    let Wm:=longAssignedMarkedSeed F hF K (r+4) d θ Dv π weight
    let Wo:=longAssignedOrdinarySeed F hF K (r+4) d θ Dv P π ni hni w
    let W:=longMixedSeedWeight Wm Wo
    let Rsrc:=longRawHubResources (U:=U) π d (r+4) ℓ
    let R:=mixedCandidateResources Rsrc
    let state:=longRawHubState P π d raw true true
    let hub:=longRawHubNames (U:=U) π d (r+4) ℓ
    ((((∀w,|rawIntervalUnassignedHubCountOn π d σ w (Vort.extendedVertices 1)-
      ((Vort.extendedVertices 1).card:ℝ)*(1-(∑g,longAssignedIntervalProbability F hF K (r+4) θ w g)-
        (∑j,longAssignedSpokeProbability F hF K (r+4) θ w j))|<(n:ℝ)^(3/4:ℝ))) ∧
        ((∀v,|rawIntervalUnassignedColumnCount π d σ v Finset.univ-
      ∑w:U,(1-(∑g,longAssignedIntervalProbability F hF K (r+4) θ w g)-
        (∑j,longAssignedSpokeProbability F hF K (r+4) θ w j))|<(n:ℝ)^(3/4:ℝ)))) ∧
      (((∀v,|(((P.neighborFinset v∩Vort.extendedVertices 1).filter (fun x=>((z.1) (Sum.inl s(v,x))).1=4)).card:ℝ)-
      udens*(P.neighborFinset v∩Vort.extendedVertices 1).card|<(n:ℝ)^(3/4:ℝ))) ∧
        ((∀u∈Vort.extendedIndices 1,
      |rawIntervalUnassignedHubCountOn π d σ u (Vort.extendedVertices 1)-
      ((Vort.extendedVertices 1).card:ℝ)*(1-(∑g,longAssignedIntervalProbability F hF K (r+4) θ u g)-
        (∑k,longAssignedSpokeProbability F hF K (r+4) θ u k))|<((Vort.extendedVertices 1).card:ℝ)^(3/4:ℝ))) ∧
        ((∀v∈Vort.extendedVertices 1,
      |rawIntervalUnassignedColumnCount π d σ v (Vort.extendedIndices 1)-
      ∑u∈Vort.extendedIndices 1,(1-(∑g,longAssignedIntervalProbability F hF K (r+4) θ u g)-
        (∑k,longAssignedSpokeProbability F hF K (r+4) θ u k))|<((Vort.extendedVertices 1).card:ℝ)^(3/4:ℝ))) ∧
        ((∀v∈Vort.extendedVertices 1,
      ((rawIntervalBoundaryHubSet π d σ (Vort.extendedIndices 1) v).card:ℝ)≤
        4*((Vort.extendedIndices 1).card:ℝ)/d+4*((Vort.extendedVertices 1).card:ℝ)^(3/4:ℝ))) ∧
        (RetainedRestrictionLocalGood π d σ false (startRetentionMinimum (rawStartHubSet π d (fun e=>rawExpandedMarkedCollapse (Sum.inr e) (z.1 (Sum.inr e))) false))
      (Vort.extendedVertices 1) (Vort.extendedIndices 1) ζselect (z.2)) ∧
        ((∀x y,x≠y→(5/8:ℝ)*(1/100:ℝ)^2*Fintype.card U-(n:ℝ)^(3/4:ℝ)≤
      (((Finset.univ:Finset U).filter (fun u=>rawIntervalFamilyState π d σ (x,u)=some (Sum.inr false) ∧
        rawIntervalFamilyState π d σ (y,u)=some (Sum.inr false))).card:ℝ)))) ∧
      (((∀v,((rawIntervalExtendedAnyHubSet π d σ v).card:ℝ)≤4*(Fintype.card U:ℝ)/((r+4):ℝ)+4*(n:ℝ)^(3/4:ℝ))) ∧
        ((∀u g,|rawIntervalHubStartCount π d g σ u-(n:ℝ)*longAssignedIntervalProbability F hF K (r+4) θ u g/d|<(n:ℝ)^(3/4:ℝ)/d))) ∧
      (((∀u,|(((ordinaryCommonHubSpokeRoots u).filter (fun v=>state v=true)).card:ℝ)-
      longAssignedApproxOrdinaryWeight F hF K (r+4) θ u*n|≤ξSeed*n)) ∧
        ((∀(i:Option (Fin K)) (root:LongRawHubResource n U),state root=true→
      |resourcePatternLoad (Rsrc i) (W i) (fun _ _=>true) root state-
        longAssignedMixedTarget F hF K (r+4) θ Dv p k i root|≤terr+τerr*longAssignedMixedTarget F hF K (r+4) θ Dv p k i root)) ∧
        ((∀(Del:SimpleGraph (Fin n)) (δDel:ℝ), (∀x,(Del.degree x:ℝ)≤δDel)→δDel≤ΔSeed*n→
      0≤terr+C*(δDel/(n:ℝ))+4*τerr ∧ terr+C*(δDel/(n:ℝ))+4*τerr≤eps/2))) ∧
      ((RetainedRestrictionGood π d σ false (startRetentionMinimum (rawStartHubSet π d (fun e=>rawExpandedMarkedCollapse (Sum.inr e) (z.1 (Sum.inr e))) false))
      (fun _:Unit=>Finset.univ) (fun _:Unit=>Finset.univ) ζret z.2) ∧
        ((∀v,((rawIntervalBoundaryHubSet π d σ Finset.univ v).card:ℝ)≤4*(Fintype.card U:ℝ)/d+4*(n:ℝ)^(3/4:ℝ)))) ∧
      (((∀Del:SimpleGraph (Fin n),(∀v,(Del.degree v:ℝ)≤Δ*n)→
      LongEarlyMatchingListsForDeletion r K d θ Dv a γ eps Δ βList P π F hF weight w z Inner Del))))→
    ∀(γLoss σLoss:ℝ) (D₀:MarkedReferenceDeletion P π d (fun e=>rawExpandedMarkedCollapse e (z.1 e)))
      (CReserve:Finset (Finset (Fin n)⊕(Fin n×U))) (Bpart:ℕ),
    LongEveryClassValidDeletionEvent Δ P π d r γLoss σLoss ξPart z
      (Vort.extendedVertices 1) (Vort.extendedIndices 1) K Bpart θ Dv a γ eps βList F hF weight w→
    D₀.Valid (retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) false
      (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false)) z.2 false false)
      (r+4) (Vort.extendedVertices 1) (Vort.extendedIndices 1) (γLoss*n) (σLoss*n)→
    (let σ:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedMarkedCollapse e (z.1 e)
      let σ':=rawMarkedDeleteRims σ (markedSampleArcSetGraph P π d σ D₀.arcs).edgeFinset
      let E':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) false
      let K':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) true;
      ∃C':MarkedSupportedEdgeSet (fun e:E'=>e.val.1) (fun e=>e.val.2)
        (fun e:K'=>e.val.1) (fun e=>e.val.2) π U,C'.edges=CReserve)→
    CReserve.card≤Bpart→Disjoint D₀.removed CReserve→
    ∀(X₀:Finset (Fin n)) (Z₀:Finset U),
    MarkedFixedTerminalAbsorber P π d (r+4) (fun e=>rawExpandedMarkedCollapse e (z.1 e))
      (retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) false
        (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false)) z.2 false false) CReserve X₀ Z₀→
    0<Fintype.card U→∀(hπ:∀i v,π v∈Vort.extendedVertices i↔v∈Vort.extendedVertices i),
    ∀(H:Finset U),H=Vort.extendedIndices 1→
    5*Real.sqrt δglobal≤δLoss→
    ∀(αAssign βfinal ρreserve:ℝ),αAssign/2=α→ε≤δglobal→0<βfinal→βfinal≤1→
    δglobal≤(βfinal/100)^2→100/βfinal≤(n:ℝ)→2/Real.sqrt δglobal≤(n:ℝ)→Fintype.card U≤n→
    0≤ρreserve→(CReserve.card:ℝ)≤ρreserve*n→βfinal+2*ρreserve≤βList/2→Δ≤ξ→
    let G:=P
    let D:=Dv
    let I:=Vort.extendedVertices 1
    let Dmatch:ℝ:=Dv
    let alpha:=a
    let ζ:=Δ
    let εQ:=ε
    let b:=bmatch
    let ρstep:=ρ₀
    let ξClass:=ξPart
    let C:=CReserve
    let βpre:=βList/2;
    ∀S:SimpleGraph (Fin n),S≤G → S.IsRegularOfDegree (2*Fintype.card U) →
    (∀v,((changed ((longPhysicalStateGraph G z.1 {0,1,2,3,4}).neighborFinset v) (S.neighborFinset v)).card:ℝ)≤ξClass*n) →
    (∀x∈I,∀y∈I,S.Adj x y↔(longPhysicalStateGraph G z.1 {0,1,2,3,4}).Adj x y) → markedResourceRimGraph C≤S →
    ∃Del:SimpleGraph (Fin n), ∃Mhost:Fin n→Fin n→ℕ,
    LongClassMatchingDeletionWitness ζ G π d r z I K θ Dmatch alpha γ eps βList F hF weight w D₀ C S Mhost Del ∧
    FirstVortexClassPreparedRetainedFullPackingOutcomeWithAllHubLoad G S π D mm d (r+4) β εQ Vort F hF θ lamAssign eps δlocal δglobal (αAssign/2) b ρstep ξ ζ alpha γ weight w z.1
      (startRetentionMinimum (rawStartHubSet π d (fun x=>z.1 (Sum.inr x)) false)) z.2 ∧
    let Jret:=z.2
    let t:=startRetentionMinimum (rawStartHubSet π d (fun x=>z.1 (Sum.inr x)) false)
    let raw:RawMarkedOutcome (Fin n) U Bool Bool:=fun x=>rawExpandedApproximateCollapse x (z.1 x)
    let ℓ:=fun i:Fin K=>longPaddedSeedExponent i+2
    let R:=mixedCandidateResources (longRawSeedResources (U:=U) π d (r+4) ℓ)
    let Tmix:=bernoulliVertexSet (longRawHubState G π d raw true true)
    let Q:=longRawSurvivingResources G π d raw true true Del.edgeFinset
    let q:=survivingCandidateEmbedding R Q Tmix (long_raw_surviving_resources_subset G π d raw true true Del.edgeFinset)
    let φ:=markedRawSampledPhysicalEmbedding G π d raw true true;
    ∀(X:Finset (Fin n)) (Z:Finset U),
    0<K→θ≤1→∀ζRet cap:ℝ,
    0<cap→0<εQ→εQ≤1/4→0<mm→0≤ζRet→ζRet≤cap/128→
    (2*((n:ℝ)+2*(n:ℝ)^(3/4:ℝ))/(d:ℝ)+2*max alpha γ*n)≤cap*(εQ*n)/128→
    (∀E:ℕ,(E:ℝ)≤(θ*εQ^2+lamAssign*εQ)*(n:ℝ)^2+24*d*n→
      2*(⌈4*(E:ℝ)/(((ρstep/4)/40000)*n)⌉₊:ℕ)≤cap*(εQ*n)/128)→
    RetainedRestrictionLocalGood π d (fun e=>raw (Sum.inr e)) false t I Finset.univ ζRet z.2→
    (∀w g,|rawIntervalHubStartCount π d g (fun e=>raw (Sum.inr e)) w-
      (n:ℝ)*longAssignedIntervalProbability F hF K (r+4) θ w g/(d:ℝ)|<(n:ℝ)^(3/4:ℝ)/(d:ℝ))→
    MarkedFixedTerminalAbsorber G π d (r+4) (fun e=>rawExpandedMarkedCollapse e (z.1 e))
      (retainedRawMarkedSpokes π d (fun e=>raw (Sum.inr e)) false t Jret false false) C X Z→
    (I.card:ℝ)≤εInner*n→C.card≤e→∀p₂ k₂ u:ℝ,
    (∀v,|((rawStartHubSet π d (fun x=>z.1 (Sum.inr x)) false v).card:ℝ)-
      (∑w,longAssignedIntervalProbability F hF K (r+4) θ w false/(d:ℝ))|<(n:ℝ)^(3/5:ℝ))→
    (∀j v,|((∑x,sampledColourOrientation G (fun x=>z.1 (Sum.inl x)) j x v:ℕ):ℝ)-
      markedExpandedPhysicalProbability (initialIndexDensity U D*(1/100:ℝ)/2) (initialIndexDensity U D*((1/100:ℝ)/((r+4:ℕ):ℝ))/2) p₂ k₂ u j/2*G.degree v|<(n:ℝ)^(3/5:ℝ))→
    0≤γ→0≤θ→u≤2*θ→
    (∀v,|((sampledColourDegree G (fun e=>(z.1 (Sum.inl e)).1) 4 v):ℝ)-u*(G.degree v:ℝ)|≤(n:ℝ)^(3/5:ℝ))→
    ∃Mix:Finset (RestrictedResource R (Function.Embedding.subtype (·∈Q))),
      (∀c∈Mix,∀c'∈Mix,c≠c'→Disjoint (restrictedResourceSet R (Function.Embedding.subtype (·∈Q)) c)
        (restrictedResourceSet R (Function.Embedding.subtype (·∈Q)) c')) ∧
      (∀i,((longRawIncidenceSet Q i\Mix.biUnion (restrictedResourceSet R (Function.Embedding.subtype (·∈Q)))).card:ℝ)≤
        max (alpha*n) (γ*(longRawIncidenceSet Q i).card)) ∧
    ∃(Pack:Finset (Sym2 (Fin n))) (E:U→Finset (Sym2 (Fin n))) (Spokes:U→Finset (Fin n)),
      let Used:=physicalRimCandidateUnion φ (restrictedResourceSet R (Function.Embedding.subtype (·∈Tmix))) (Mix.map q)
      let Sel:=longSelectedPhysicalGraph G π d z.1
      let Req:=fun x y=>Mhost x y=1 ∧ markedPhysicalRim G π (3*d)
        (fun x=>markedExpandedPhysicalCollapse (z.1 (Sum.inl x))) true x (π.symm y)≠1
      let Kbase:=longRequiredPhysicalGraph S (S\Used) Sel π d I Req (fun x y=>Used.Adj x y)
      let Kplus:=fun Pack:Finset (Sym2 (Fin n))=>longClassInnerRequiredRepair S Used Kbase I Pack
      let DelPlus:=Del⊔markedResourceRimGraph C
      let Small:=SimpleGraph.fromEdgeSet (↑Pack:Set (Sym2 (Fin n)))⊔prescribedPhysicalUnion E
      let P:=longEligibleResidualArc Mhost Small ⊥
      let T₁:=longDualInitialMarked G (fun x=>z.1 (Sum.inl x)) Mhost Small (longOrdinaryArcEligible π d) (longMarkedArcEligible π d);
      ∃T:Finset {x:(Fin n)×(Fin n) // P x},
      (∀v,((changed ((longSelectedPhysicalGraph G π d z.1).neighborFinset v) ((S\Small).neighborFinset v)).card:ℝ)≤
        (2*θ+2*max alpha (4*γ)+2*ξClass+5*Real.sqrt δglobal)*n+(n:ℝ)^(3/5:ℝ)+ζ*n+2*(6*d+2:ℕ)) ∧
      Pack=Used.edgeFinset ∧ Pack⊆(longApproximatePhysicalGraph G π d z.1).edgeFinset ∧
      (∀v,((prescribedPhysicalUnion E).degree v:ℝ)≤5*Real.sqrt δglobal*Fintype.card (Fin n)) ∧
      (∀x y,Small.Adj x y→¬(markedResourceRimGraph C).Adj x y) ∧
      (∀v,directedInCount P T v=d*startRetentionMinimum (rawStartHubSet π d (fun x=>z.1 (Sum.inr x)) false)) ∧
      (∀x∈T,longMarkedArcEligible π d x.val) ∧ (∀x,x∉T→longOrdinaryArcEligible π d x.val) ∧
      (∀x,x.val.1∈I→(x∈T↔x∈T₁)) ∧
      (∀x,Sum.inl ({x.val.1,x.val.2}:Finset (Fin n))∈C→(x∈T↔x∈T₁)) ∧
      (∀v,((physicalEdgeGraph (changedDirectedPhysicalEdges P T T₁)).degree v:ℝ)≤(1+2/rho)*eta*n+(n:ℝ)^(3/5:ℝ)) ∧
      (∀mark a b,a∈I→b∈I→
        (markedPhysicalRim G π (3*d) (fun x=>markedExpandedPhysicalCollapse (z.1 (Sum.inl x))) mark a b=1 ↔
          if mark then ∃e:residualMarkedArc P T,e.val.val.1=a∧π.symm e.val.val.2=b
          else ∃e:residualOrdinaryArc P T,e.val.val.1=a∧e.val.val.2=b)) ∧
      let Y:=fun w=>markedIntervalRootSet π (fun _:retainedMarkedIndex π d (fun x=>raw (Sum.inr x)) false t Jret w=>d) Subtype.val
      let H₀:=fun v w=>v∈Spokes w\Y w
      MarkedRemainderDivisible
        (fun x:residualOrdinaryArc P T=>x.val.val.1) (fun x=>x.val.val.2)
        (fun x:residualMarkedArc P T=>x.val.val.1) (fun x=>π.symm x.val.val.2)
        (retainedRawMarkedSpokes π d (fun x=>raw (Sum.inr x)) false t Jret false true true) Finset.univ
        (Finset.univ.filter (fun z:(Fin n)×U=>H₀ z.1 z.2∨retainedRawMarkedSpokes π d (fun x=>raw (Sum.inr x)) false t Jret false true true z.1 z.2)) (r+4) ∧
      ∃A:Finset (Fin n×Fin n),Small.edgeFinset=A.image (fun a=>s(a.1,a.2)) ∧
        (∀a∈A,Mhost a.1 a.2=1) ∧
        LongFactorComplementProvenance F S G π d (r+4) raw t Jret Pack E A Spokes ∧
        LongResidualSpokeCompletionControl π d raw t Jret Spokes θ δglobal ∧
        (∀w,((I.filter (fun v=>retainedRawMarkedSpokes π d (fun x=>raw (Sum.inr x)) false t Jret false false false v w ∧ v∉Spokes w\Y w)).card:ℝ)≤
          ζRet*I.card+(2*((n:ℝ)+2*(n:ℝ)^(3/4:ℝ))/(d:ℝ)+2*max alpha γ*n)+2*(⌈4*((Kplus Pack).edgeFinset.card:ℝ)/(((ρstep/4)/40000)*n)⌉₊:ℕ)) ∧
        (∀w v,v∈I→v∈Spokes w\Y w → retainedRawMarkedSpokes π d (fun x=>raw (Sum.inr x)) false t Jret false false false v w) ∧
        (∃Old,(FirstVortexClassPrescribedAssignmentNoMarkedBudget G S DelPlus Used (Kplus Pack) I π d z.1 t Jret H αAssign b ρstep θ εQ lamAssign Old Pack ∧ Pack=Used.edgeFinset) ∧
          ∀w,((innerRequiredTargets H I (rawReservedSpokeList π d (fun e=>raw (Sum.inr e)))
            (retainedFinalMarkedAt π d (fun e=>raw (Sum.inr e)) t Jret) (fun _=>∅) Old w).card:ℝ)≤(θ/1024)*n) ∧
        (∀w∈H,∀v∈I,v∈Spokes w\Y w↔retainedRawMarkedSpokes π d (fun e=>raw (Sum.inr e)) false t Jret false false false v w) ∧
      ∃τ:RawMarkedOutcome (Fin n) U Bool Bool,
        (∀e,τ (Sum.inr e)=rawExpandedMarkedCollapse (Sum.inr e) (z.1 (Sum.inr e))) ∧
        (∀e:Sym2 (Fin n),e.toFinset⊆Vort.extendedVertices 1→τ (Sum.inl e)=markedExpandedPhysicalCollapse (z.1 (Sum.inl e))) ∧
        (let f:=markedVortexActiveVertexEmbedding Vort 1
         let g:=markedVortexNonDeeperHubToPhysical Vort 0
         let ρ:=markedVortexActivePermutation Vort π hπ 1;
         rawMarkedPairRims (G.comap f) ρ d (rawMarkedRestrictPair f g τ)=
         rawMarkedPairRims (G.comap f) ρ d (rawMarkedRestrictPair f g (fun e=>rawExpandedMarkedCollapse e (z.1 e)))) ∧
        (∀ (i:ℕ), 1 ≤ i →
          rawMarkedRestrictPair (markedVortexVertexEmbedding Vort i) (markedVortexHubEmbedding Vort i) (fun e=>rawExpandedMarkedCollapse e (z.1 e))=
          rawMarkedRestrictPair (markedVortexVertexEmbedding Vort i) (markedVortexHubEmbedding Vort i) τ ∧
          (fun b v u=>retainedRawMarkedSpokes π d (fun e=>raw (Sum.inr e)) false t Jret false false b (markedVortexVertexEmbedding Vort i v) (markedVortexHubEmbedding Vort i u))=
          (fun b v u=>if b then retainedRawMarkedSpokes π d (fun e=>raw (Sum.inr e)) false t Jret false false true (markedVortexVertexEmbedding Vort i v) (markedVortexHubEmbedding Vort i u)
            else markedVortexVertexEmbedding Vort i v∈Spokes (markedVortexHubEmbedding Vort i u)\Y (markedVortexHubEmbedding Vort i u))) ∧
        (∀mark x y,markedPhysicalRim G π (3*d) (fun e=>τ (Sum.inl e)) mark x y=1 ↔
          if mark then ∃e:residualMarkedArc P T,e.val.val.1=x∧π.symm e.val.val.2=y
          else ∃e:residualOrdinaryArc P T,e.val.val.1=x∧e.val.val.2=y) ∧
        MarkedRemainderDivisible
          (fun e:MarkedSampleArc G π (3*d) (fun e=>τ (Sum.inl e)) false=>e.val.1) (fun e=>e.val.2)
          (fun e:MarkedSampleArc G π (3*d) (fun e=>τ (Sum.inl e)) true=>e.val.1) (fun e=>e.val.2)
          (retainedRawMarkedSpokes π d (fun e=>raw (Sum.inr e)) false t Jret false true true) Finset.univ
          (Finset.univ.filter (fun z:(Fin n)×U=>H₀ z.1 z.2∨retainedRawMarkedSpokes π d (fun e=>raw (Sum.inr e)) false t Jret false true true z.1 z.2)) (r+4) ∧
        (let W:=↥((Finset.univ\markedVortexInnerVertices Vort 1):Finset (markedVortexVertexType Vort 1))
         let Z:=markedVortexNonDeeperHubType Vort 0
         let f:=markedVortexActiveVertexEmbedding Vort 1
         let g:=markedVortexNonDeeperHubToPhysical Vort 0
         let H:=retainedRawMarkedSpokes π d (fun e=>raw (Sum.inr e)) false t Jret false false
         let H':=fun b v w=>if b then H true v w else v∈Spokes w\Y w
         let HL:=fun b v u=>H b (f v) (g u)
         let HL':=fun b v u=>H' b (f v) (g u)
         let FS:=markedSpokeChangeGraph HL HL';
         (∀b v u,¬(HL b v u↔HL' b v u)→FS.Adj (Sum.inl v) (Sum.inr u)) ∧
         (∀u:Z,(FS.degree (Sum.inr u):ℝ)≤cap*Fintype.card W)) :=by
  obtain ⟨Nprep,hPrep⟩:=first_vortex_all_fixed_classes_from_combined_boundary_event α lam lamAssign ε δold δlocal δglobal θ eps ξ ρ₀ bmatch ξPart ζret d K r
    hα hlam hε hδ hδ1 hθ hepsPos hρ₀ hbmatch hαb hbd hεsmall hθδ hθlocal hθhi hlamlocal hspacing hd hK hm heps hξ hξ0
    hρ₀hi hδglobal hθglobal hprecise ξCap hξPartCap hCap hlamθ hdlarge Nret hNret
  obtain ⟨Ncorr,hCorr⟩:=long_encoded_active_from_matching_on_fixed_class d e r ρ₀ rho Δ δLoss εInner eta hρ₀ hrho heta hetaR hbudget hsupply
  refine ⟨max Nprep Ncorr,?_⟩
  intro n hn _ U _ _ P π Dv mm β Vort hreg hDv hρhi hρlo hDlo hDhi hmm F hF Allowed hAllowed hclass hcut hcutHost hnoshort
    hεα hlamhi a γ ρ ξSeed ΔSeed haEq hγEq hρEq hΔeps hξSeed hΔSeed heps1 hζ hζ0 τ Asrc BM hBM weight hw BO hBO w hw0 hwupper z ζselect hζselect Inner βList terr τerr hτerr
    raw σ ni hni ℓ p k udens pstar BMseed BOseed C Wm Wo W Rsrc R state hub hEvents γLoss σLoss D₀ CReserve Bpart hEvery hValid hSupported hCard hDis X₀ Z₀ hTerminal hU hπ H hHeq hLossScale αAssign βfinal ρreserve hαEq hεδ hβ hβ1 hδbound hnβ hnδ hu hρreserve hCreserve hListMargin hΔξ G D I Dmatch alpha ζ εQ b ρstep ξClass C' βpre S hSP hSreg hSedit hSinner hSreserve
  obtain ⟨Csup,hCsup⟩:=hSupported
  subst CReserve
  have hInputs:=long_valid_deletion_reserve_class_inputs P π d r Dv mm β ε Vort γLoss σLoss ξPart z θ eps Δ a γ βList F hF weight w Bpart hEvery D₀ hValid Csup hCard hDis
  have hdecInputs6:referenceWitnessFinDecidable 6=firstVortexFixedEventCorrectionSix:=Subsingleton.elim _ _
  try rw [hdecInputs6] at hInputs
  obtain ⟨hA,hSample,hClass⟩:=hInputs
  have hp:=hPrep n (by omega)
  have hdec:firstVortexUniversalSelectedClassFin n=firstVortexFixedEventCorrectionFin n:=Subsingleton.elim _ _
  have hdecK:firstVortexUniversalSelectedClassFin K=firstVortexFixedEventCorrectionFin K:=Subsingleton.elim _ _
  try rw [hdec] at hp
  try rw [hdecK] at hp
  have hdec6:firstVortexUniversalSelectedClassFin 6=firstVortexFixedEventCorrectionSix:=Subsingleton.elim _ _
  try rw [hdec6] at hp
  have hSelected:=hp U P π Dv mm β Vort hreg hDv hρhi hρlo hDlo hDhi hmm F hF Allowed hAllowed hclass hcut hcutHost hnoshort
    hεα hlamhi a γ ρ Δ ξSeed ΔSeed haEq hγEq hρEq hΔeps hξSeed hΔSeed heps1 hζ hζ0 τ Asrc BM hBM weight hw BO hBO w hw0 hwupper z ζselect hζselect Inner βList terr τerr hτerr (by simpa only [raw,σ,udens,p,k,pstar,BMseed,BOseed,C,Wm,Wo,W,Rsrc,state,ni,ℓ,Nat.cast_add,Nat.cast_ofNat] using hEvents) γLoss σLoss D₀ Csup.edges Bpart hClass S hSP hSreg hSedit hSinner hSreserve
  have hc:=hCorr n (by omega)
  have hdecCorr:fixedClassEncodedActiveFin n=firstVortexFixedEventCorrectionFin n:=Subsingleton.elim _ _
  have hdecCorrK:fixedClassEncodedActiveFin K=firstVortexFixedEventCorrectionFin K:=Subsingleton.elim _ _
  try rw [hdecCorr] at hc
  try rw [hdecCorrK] at hc
  have hdecCorr6:fixedClassEncodedActiveSix=firstVortexFixedEventCorrectionSix:=Subsingleton.elim _ _
  try rw [hdecCorr6] at hc
  have hαassign:αAssign/16≤bmatch:=by linarith [hαb]
  have hn0:0<n:=by have hh:=Fintype.card_pos (α:=Fin n);simpa only [Fintype.card_fin] using hh
  apply hc U K Dv P hreg hDv (by omega) hρlo hDlo π z (Vort.extendedVertices 1) θ Dv a γ eps βList rfl F hF weight w D₀ Csup.edges (hπ 1) X₀ Z₀ hTerminal hU hnoshort (by omega) H δlocal ρ₀ δglobal hLossScale ε lamAssign αAssign bmatch (βList/2) βfinal ρreserve rfl hρ₀ hbmatch.le hbd hαassign hθglobal hεδ hβ hβ1 hδglobal hδbound hn0 hnβ hnδ hu hρreserve hCreserve hListMargin mm β ξ Vort rfl hHeq hπ hΔξ ξPart S
  simpa only [hαEq] using (show S≤P ∧ S.IsRegularOfDegree (2*Fintype.card U) ∧ _ from ⟨hSP,hSreg,hSedit,hSinner,hSreserve,hSelected⟩)
end Oberwolfach
