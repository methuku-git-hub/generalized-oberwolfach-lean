module

public import Oberwolfach.LongSameSampleChangeGraphsMinimalBalance
public import Oberwolfach.MarkedVortexActualResidualDeeperEquality

@[expose] public section
/-! The physical correction and its two change graphs retain the original
sample exactly on every positive vortex level. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 15000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance minimalBalancedVortexChangeGraphsFin (n:ℕ):DecidableEq (Fin n):=factorRootsFin n
local instance minimalBalancedVortexChangeGraphsArc {n:ℕ} (P:Fin n×Fin n→Prop):DecidableEq {e:Fin n×Fin n // P e}:=Classical.decEq _
attribute [local instance] partitionedDivisibleArcFinite partitionedDivisibleOrdFinite partitionedDivisibleMarkFinite
theorem long_same_sample_vortex_change_graphs_minimal_balance
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U] [Nonempty (Fin n)]
    (F:U→SimpleGraph (Fin n)) (G S Del:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ)
    (hd:2≤d) (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (ω:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (M:Fin n→Fin n→ℕ) (I:Finset (Fin n)) (t:ℕ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool)
    (J:StartRetentionOutcome (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false) t)
    (Pack:Finset (Sym2 (Fin n))) (Enew:U→Finset (Sym2 (Fin n))) (A:Finset (Fin n×Fin n))
    (R:U→Finset (Fin n)) (θ δ ηphys ηdel ηtype lossRow lossCol ε ζ:ℝ)
    (hphysical:∀x y,M x y+M y x=if S.Adj x y then 1 else 0)
    (hhost:∀x y,M x y=1→G.Adj x y)
    (hcorrect:orientationDisagreementGraph (longPhysicalStateGraph G ω {0,1,2,3,4}) (fun e=>(ω (Sum.inl e)).2) M≤Del)
    (hI:∀v,π v∈I↔v∈I)
    (hprov:LongFactorComplementProvenance F S G π d m raw t J Pack Enew A R)
    (hcontrol:LongResidualSpokeCompletionControl π d raw t J R θ δ)
    {DQ mm:ℕ} {β εQ:ℝ} (Q:Vortex U G DQ β εQ mm) (Hinner:Finset U)
    (hIeq:I=Q.extendedVertices 1) (hHeq:Hinner=Q.extendedIndices 1):
    let Small:=SimpleGraph.fromEdgeSet (↑Pack:Set (Sym2 (Fin n)))⊔prescribedPhysicalUnion Enew
    let P:=longEligibleResidualArc M Small ⊥
    let T₁:=longDualInitialMarked G (fun e=>ω (Sum.inl e)) M Small (longOrdinaryArcEligible π d) (longMarkedArcEligible π d)
    let σ:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedMarkedCollapse e (ω e)
    let ρ:=fun e=>raw (Sum.inr e)
    let Y:=fun w=>markedIntervalRootSet π (fun _:retainedMarkedIndex π d ρ false t J w=>d) Subtype.val
    let H:=retainedRawMarkedSpokes π d ρ false t J false false
    let H₀:=fun v w=>v∈R w\Y w
    let HK:=retainedRawMarkedSpokes π d ρ false t J false true true
    let H':Bool→Fin n→U→Prop:=fun b v w=>if b then HK v w else H₀ v w;
    ∀T:Finset {e:Fin n×Fin n // P e},
    (∀e∈T,longMarkedArcEligible π d e.val)→(∀e,e∉T→longOrdinaryArcEligible π d e.val)→
    (∀mark x y,x∈I→y∈I→
      (markedPhysicalRim G π (3*d) (fun e=>σ (Sum.inl e)) mark x y=1 ↔
        if mark then ∃e:residualMarkedArc P T,e.val.val.1=x∧π.symm e.val.val.2=y
        else ∃e:residualOrdinaryArc P T,e.val.val.1=x∧e.val.val.2=y))→
    MarkedRemainderDivisible (fun e:residualOrdinaryArc P T=>e.val.val.1) (fun e=>e.val.val.2)
      (fun e:residualMarkedArc P T=>e.val.val.1) (fun e=>π.symm e.val.val.2) HK Finset.univ
      (Finset.univ.filter (fun z:Fin n×U=>H₀ z.1 z.2∨HK z.1 z.2)) m→
    MarkedRestrictedBalanceWithSpokes G π d m Finset.univ Finset.univ ε σ H→
    (∀v,((changed ((longSelectedPhysicalGraph G π d ω).neighborFinset v) ((S\Small).neighborFinset v)).card:ℝ)≤ηphys)→
    (∀v,(Del.degree v:ℝ)≤ηdel)→
    (∀v,((physicalEdgeGraph (changedDirectedPhysicalEdges P T T₁)).degree v:ℝ)≤ηtype)→
    (∀v,((Finset.univ.filter (fun w=>¬(H false v w↔rawMarkedPairSpokes π d raw false false false v w))).card:ℝ)≤lossRow)→
    (∀w,((Finset.univ.filter (fun v=>¬(H false v w↔rawMarkedPairSpokes π d raw false false false v w))).card:ℝ)≤lossCol)→
    2*(lossRow+(δ*n+(Real.sqrt δ*n+1)))+(ε+2*(ηphys+ηdel+ηtype))≤ζ*n→
    2*(lossCol+10*θ*n)+ε≤ζ*n→
    (∀w∈Hinner,∀v∈I,v∈R w\Y w↔H false v w)→
    ∃(τ:RawMarkedOutcome (Fin n) U Bool Bool) (FR:SimpleGraph (Fin n)) (FS:SimpleGraph (Fin n⊕U)),
      (∀e,τ (Sum.inr e)=σ (Sum.inr e)) ∧
      (∀e:Sym2 (Fin n),e.toFinset⊆I→τ (Sum.inl e)=σ (Sum.inl e)) ∧
      (∀mark x y,markedPhysicalRim G π (3*d) (fun e=>τ (Sum.inl e)) mark x y=1 ↔
        if mark then ∃e:residualMarkedArc P T,e.val.val.1=x∧π.symm e.val.val.2=y
        else ∃e:residualOrdinaryArc P T,e.val.val.1=x∧e.val.val.2=y) ∧
      (∀a,¬(rawMarkedPairRims G π d σ a↔rawMarkedPairRims G π d τ a)→markedPairPhysical π a∈FR.edgeFinset) ∧
      (∀v,(FR.degree v:ℝ)≤ηphys+ηdel+ηtype) ∧
      (∀b v w,¬(H b v w↔H' b v w)→FS.Adj (Sum.inl v) (Sum.inr w)) ∧
      (∀z,(FS.degree z:ℝ)≤ζ*n) ∧
      (∀ (i:ℕ), 1 ≤ i →
        rawMarkedRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i) σ=
        rawMarkedRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i) τ ∧
        (fun b v u=>H b (markedVortexVertexEmbedding Q i v) (markedVortexHubEmbedding Q i u))=
        (fun b v u=>H' b (markedVortexVertexEmbedding Q i v) (markedVortexHubEmbedding Q i u))):=by
  intro Small P T₁ σ ρ Y H H₀ HK H' T hMarked hOrd hInner hdiv hbal hChange hDel hType hRetRow hRetCol hBudgetRow hBudgetCol hFirst
  have hbase:=long_same_sample_corrected_change_graphs_from_balance_minimal F G S Del π d m hd hnoshort ω M I t raw J Pack Enew A R θ δ ηphys ηdel ηtype lossRow lossCol ε ζ
    hphysical hhost hcorrect hI hprov hcontrol
  have hdec:sameSampleChangeGraphsMinimalBalanceFin n=minimalBalancedVortexChangeGraphsFin n:=Subsingleton.elim _ _
  have hdec6:sameSampleChangeGraphsMinimalBalanceFin 6=minimalBalancedVortexChangeGraphsFin 6:=Subsingleton.elim _ _
  try rw [hdec] at hbase
  try rw [hdec6] at hbase
  obtain ⟨τ,FR,FS,hinterval,hinner,hRims,hRimChange,hFR,hSpokeChange,hFS⟩:=hbase T hMarked hOrd hInner hdiv hbal hChange hDel hType hRetRow hRetCol hBudgetRow hBudgetCol
  have hfirst:∀w∈Q.extendedIndices 1,∀v∈Q.extendedVertices 1,v∈R w\Y w↔retainedRawMarkedSpokes π d ρ false t J false false false v w:=by
    simpa only [←hIeq,←hHeq,H] using hFirst
  have hdeep:=marked_vortex_actual_residual_deeper_equality Q π d ρ t J σ τ R
    (fun e he=>(hinner e (by simpa only [hIeq] using he)).symm) (fun e=>(hinterval e).symm) hfirst
  exact ⟨τ,FR,FS,hinterval,hinner,hRims,hRimChange,hFR,hSpokeChange,hFS,hdeep⟩
end Oberwolfach
