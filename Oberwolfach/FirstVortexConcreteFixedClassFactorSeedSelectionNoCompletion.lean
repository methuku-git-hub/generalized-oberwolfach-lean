module

public import Oberwolfach.FirstVortexConcreteFixedClassFactorSeedNoCompletion
public import Oberwolfach.FirstVortexFixedClassFactorSeedProjection
public import Oberwolfach.FirstVortexFullMatchingContinuationAdapter

@[expose] public section
/-! Apply the later chain to the selector's actual concentration event and
sampling probabilities, preserving any remaining continuation. -/
/-! The same sample consequence without the unnecessary universal
regular-completion event; all actual target hypotheses are retained. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance concreteFixedClassFactorSeedSelectionFinNoCompletion (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n
local instance (priority := 2000) concreteFixedClassFactorSeedSelectionSixNoCompletion:DecidableEq (Fin 6):=instDecidableEqFin 6

theorem first_vortex_concrete_fixed_class_factor_seed_selection_no_completion
    {n K D Dclass:ℕ} [Nonempty (Fin n)]
    (hn:0<n) (hK:0<K) (hD:0<D)
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d r:ℕ)
    (F:(Fin (Dclass/2))→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (θ ρ₀ γ:ℝ) (hθ:0≤θ) (hθ1:θ≤1) (hρ₀:0<ρ₀) (hγ:0≤γ)
    (hρlo:ρ₀≤ initialIndexDensity (Fin (Dclass/2)) D) (hρhi:initialIndexDensity (Fin (Dclass/2)) D≤1)
    (ε active t c ζret ζlocal ηBalance κaux cap capStable cLocal:ℝ) (mm:ℕ)
    (hε:0<ε) (hε1:ε≤1/4) (hmm:0<mm)
    (hret:FirstVortexRetentionBalanceRates r d ε active θ t c ζret ζlocal ηBalance κaux)
    (hactive:0<active) (hcap:0<cap) (hcapStable:cap≤capStable)
    (hactiveGlobal:active≤(min cap (1:ℝ))/2) (hactiveLocal:active≤cLocal)
    (αRef κ ζCfg thetaDeep BA:ℝ) (hαRef:0<αRef)
    (hChosen:FirstVortexExactParentCapBound r αRef ρ₀ κ ζCfg thetaDeep BA cap hαRef hρ₀)
    (z:MarkedExpandedActualOutcome (U:=Fin (Dclass/2)) π d)
    (Parent Common:RawMarkedRetainedOutcome (U:=Fin (Dclass/2)) (Color:=Bool) π d false→Prop)
    (hParent:Parent (markedExpandedActualSelected π d z)) (hCommon:Common (markedExpandedActualSelected π d z))
    (β:ℝ) (Vort:Vortex (Fin (Dclass/2)) P D β ε mm)
    (hπ:∀i v,π v∈Vort.extendedVertices i↔v∈Vort.extendedVertices i)
    (αHost ξClass γLoss σLoss:ℝ) (hsmall:ε≤αHost/100000) (L e₀:ℕ) (εStable:ℝ) (sizeStable eStable:ℕ)
    (D₀:MarkedReferenceDeletion P π d (fun e=>rawExpandedMarkedCollapse e (z.1 e)))
    (C:Finset (Finset (Fin n)⊕(Fin n×(Fin (Dclass/2)))))
    (hTerminal:longTerminalProtectedReserve P π d r z z.2 (Vort.extendedVertices 1) (Vort.extendedIndices 1)
      γLoss σLoss e₀ (Vort.extendedVertices (L+1)) (Vort.extendedIndices (L+1)) D₀ C)
    (X:Prop)
    (lamAssign epsOrd δlocal δglobal α bmatch ξ Δ a βList:ℝ)
    (weight:(Fin ((r+4)+1)→Fin n)→ℝ)
    (w:∀i:Fin K,OrdinaryCycle P (longPaddedSeedExponent i+2)→ℝ)
    :
    let Result:=fun (S:SimpleGraph (Fin n)) (M:Fin n→Fin n→ℕ) (Del:SimpleGraph (Fin n)) (ζRet ζChange:ℝ)=>
    ∃(Pack:Finset (Sym2 (Fin n))) (E:(Fin (Dclass/2))→Finset (Sym2 (Fin n))) (Spokes:(Fin (Dclass/2))→Finset (Fin n))
      (A:Finset (Fin n×Fin n)),
      let Small:=SimpleGraph.fromEdgeSet (↑Pack:Set (Sym2 (Fin n)))⊔prescribedPhysicalUnion E;
      Small.edgeFinset=A.image (fun a=>s(a.1,a.2)) ∧
      LongFactorComplementProvenance F S P π d (r+4) (fun e=>rawExpandedApproximateCollapse e (z.1 e)) (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false)) z.2 Pack E A Spokes ∧
      ∃T:Finset {a:Fin n×Fin n // longEligibleResidualArc M Small ⊥ a},
      ∃τ:RawMarkedOutcome (Fin n) (Fin (Dclass/2)) Bool Bool,
      (∀mark x y,markedPhysicalRim P π (3*d) (fun e=>τ (Sum.inl e)) mark x y=1 ↔
        if mark then ∃e:residualMarkedArc (longEligibleResidualArc M Small ⊥) T,e.val.val.1=x∧π.symm e.val.val.2=y
        else ∃e:residualOrdinaryArc (longEligibleResidualArc M Small ⊥) T,e.val.val.1=x∧e.val.val.2=y) ∧
      let Y:=fun w=>markedIntervalRootSet π (fun _:retainedMarkedIndex π d (fun x=>rawExpandedApproximateCollapse (Sum.inr x) (z.1 (Sum.inr x))) false (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false)) z.2 w=>d) Subtype.val
      let Hnew:Bool→Fin n→(Fin (Dclass/2))→Prop:=fun b v w=>if b then retainedRawMarkedSpokes π d (fun e=>rawExpandedApproximateCollapse (Sum.inr e) (z.1 (Sum.inr e))) false (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false)) z.2 false true true v w else v∈Spokes w\Y w;
      FirstVortexNamedLevelChainContinuation P π d r D mm β ε Vort hπ L z τ Hnew active cLocal ζChange εStable sizeStable eStable
    let Match:=fun (S:SimpleGraph (Fin n)) (M:Fin n→Fin n→ℕ) (Del:SimpleGraph (Fin n))=>
      LongClassMatchingDeletionWitness Δ P π d r z (Vort.extendedVertices 1) K θ D a γ epsOrd βList F hF weight w D₀ C S M Del ∧
      FirstVortexClassPreparedRetainedFullPackingOutcomeWithAllHubLoad P S π D mm d (r+4) β ε Vort F hF θ lamAssign epsOrd δlocal δglobal α bmatch ρ₀ ξ Δ a γ weight w z.1
        (startRetentionMinimum (rawStartHubSet π d (fun x=>z.1 (Sum.inr x)) false)) z.2
    let m:ℝ:=(r+4:ℕ)
    let ρ:=initialIndexDensity (Fin (Dclass/2)) D
    let p:ℝ:=ρ*(1/100)/2
    let k:ℝ:=ρ*((1/100)/m)/2
    let q:=longAssignedIntervalProbability F hF K (r+4) θ
    let p₂:ℝ:=(∑w,longAssignedApproxOrdinaryWeight F hF K (r+4) θ w)/(D:ℝ)
    let k₂:ℝ:=(∑w,longAssignedApproxMarkedWeight F hF K (r+4) θ w)/(D:ℝ)
    let u:ℝ:=2*(∑w,(1-1/100-(1/100)/m-longAssignedApproxMarkedWeight F hF K (r+4) θ w-
      longAssignedApproxOrdinaryWeight F hF K (r+4) θ w))/(D:ℝ)
    let σ:=fun e:Sym2 (Fin n)=>z.1 (Sum.inl e);
    ((True) ∧ ((X ∧ (∀(j:Fin 6) (v:Fin n),
      |((∑x,sampledColourOrientation P σ j v x:ℕ):ℝ)-markedExpandedPhysicalProbability p k p₂ k₂ u j/2*P.degree v|<(n:ℝ)^(3/5:ℝ) ∧
      |((∑x,sampledColourOrientation P σ j x v:ℕ):ℝ)-markedExpandedPhysicalProbability p k p₂ k₂ u j/2*P.degree v|<(n:ℝ)^(3/5:ℝ) ∧
      |(sampledColourDegree P (fun e=>(σ e).1) j v:ℝ)-markedExpandedPhysicalProbability p k p₂ k₂ u j*P.degree v|<(n:ℝ)^(3/5:ℝ))) ∧ (∀g v,|((rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) g v).card:ℝ)-(∑w,q w g/(d:ℝ))|<(n:ℝ)^(3/5:ℝ))))→
    (∀S:SimpleGraph (Fin n),S≤P→S.IsRegularOfDegree (2*Fintype.card (Fin (Dclass/2)))→
      (∀v,((changed ((longPhysicalStateGraph P z.1 {0,1,2,3,4}).neighborFinset v) (S.neighborFinset v)).card:ℝ)≤ξClass*n)→
      (∀x∈Vort.extendedVertices 1,∀y∈Vort.extendedVertices 1,S.Adj x y↔(longPhysicalStateGraph P z.1 {0,1,2,3,4}).Adj x y)→
      markedResourceRimGraph C≤S→∃M:Fin n→Fin n→ℕ,∃Del:SimpleGraph (Fin n),
      S≤P ∧ S.IsRegularOfDegree (2*Fintype.card (Fin (Dclass/2))) ∧
      (∀v,((changed ((longPhysicalStateGraph P z.1 {0,1,2,3,4}).neighborFinset v) (S.neighborFinset v)).card:ℝ)≤ξClass*n) ∧
      (∀x∈Vort.extendedVertices 1,∀y∈Vort.extendedVertices 1,S.Adj x y↔(longPhysicalStateGraph P z.1 {0,1,2,3,4}).Adj x y) ∧
      markedResourceRimGraph C≤S ∧
      (∀x∈Vort.extendedVertices 1,∀y∈Vort.extendedVertices 1,(longSelectedPhysicalGraph P π d z.1).Adj x y→S.Adj x y) ∧
      LongClassMatchingDeletionWitness Δ P π d r z (Vort.extendedVertices 1) K θ D a γ epsOrd βList F hF weight w D₀ C S M Del ∧
      FirstVortexClassPreparedRetainedFullPackingOutcomeWithAllHubLoad P S π D mm d (r+4) β ε Vort F hF θ lamAssign epsOrd δlocal δglobal α bmatch ρ₀ ξ Δ a γ weight w z.1
        (startRetentionMinimum (rawStartHubSet π d (fun x=>z.1 (Sum.inr x)) false)) z.2 ∧
    (0<K→θ≤1→∀ζRet:ℝ,0<active→0<ε→ε≤1/4→0<mm→0≤ζRet→ζRet≤active/128→ζret≤ζRet*ε/2→
      ∀p₂' k₂' u':ℝ,
      (∀v,|((rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false v).card:ℝ)-(∑w,q w false/(d:ℝ))|<(n:ℝ)^(3/5:ℝ))→
      (∀j v,|((∑x,sampledColourOrientation P σ j x v:ℕ):ℝ)-markedExpandedPhysicalProbability p k p₂' k₂' u' j/2*P.degree v|<(n:ℝ)^(3/5:ℝ))→
      0≤γ→0≤θ→u'≤2*θ→
      (∀v,|(sampledColourDegree P (fun e=>(σ e).1) 4 v:ℝ)-u'*(P.degree v:ℝ)|≤(n:ℝ)^(3/5:ℝ))→
      ∀ζChange:ℝ,0≤ζChange→ζChange≤capStable→active≤ζChange→(min cap (1:ℝ))/2≤ζChange→
        0≤cLocal→active≤cLocal→Result S M Del ζRet ζChange) )→
    Parent (markedExpandedActualSelected π d z) ∧ Common (markedExpandedActualSelected π d z) ∧
    ∀S:SimpleGraph (Fin n),S≤P→S.IsRegularOfDegree (2*Fintype.card (Fin (Dclass/2)))→
      (∀v,((changed ((longPhysicalStateGraph P z.1 {0,1,2,3,4}).neighborFinset v) (S.neighborFinset v)).card:ℝ)≤ξClass*n)→
      (∀x∈Vort.extendedVertices 1,∀y∈Vort.extendedVertices 1,S.Adj x y↔(longPhysicalStateGraph P z.1 {0,1,2,3,4}).Adj x y)→
      markedResourceRimGraph C≤S→
    ∃(M:Fin n→Fin n→ℕ) (Del:SimpleGraph (Fin n)) (ζChange:ℝ),
      0≤ζChange ∧ FirstVortexExactParentCapBound r αRef ρ₀ κ ζCfg thetaDeep BA ζChange hαRef hρ₀ ∧
      Match S M Del ∧ Result S M Del 0 ζChange :=by
  intro Result Match m ρ p k q p₂ k₂ u σ hExpanded hFor
  have hout:=first_vortex_concrete_fixed_class_factor_seed_no_completion hn hK hD P π d r F hF θ ρ₀ γ hθ hθ1 hρ₀ hγ hρlo hρhi
    ε active t c ζret ζlocal ηBalance κaux cap capStable cLocal mm hε hε1 hmm hret hactive hcap hcapStable hactiveGlobal hactiveLocal
    αRef κ ζCfg thetaDeep BA hαRef hChosen z Parent Common hParent hCommon β Vort hπ αHost ξClass γLoss σLoss hsmall L e₀ εStable sizeStable eStable D₀ C hTerminal X
    lamAssign epsOrd δlocal δglobal α bmatch ξ Δ a βList weight w hExpanded hFor
  obtain ⟨hPar,hCom,hFixed⟩:=hout
  refine ⟨hPar,hCom,?_⟩
  intro S hSP hReg hEdit hInner hC
  obtain ⟨M,Del,hMatch,ζRet,ζChange,hRet0,hRetCap,hRetRate,hChange0,hChangeCap,hActiveChange,hChangeLow,hChangeEq,hParentCap,hSeed⟩:=
    hFixed S hSP hReg hEdit hInner hC
  exact ⟨M,Del,ζChange,hChange0,hParentCap,hMatch,hSeed⟩
end Oberwolfach
