module

public import Oberwolfach.LongFactorComplementCorrectedSpokeGeometry
public import Oberwolfach.LongSameSampleVortexChangeGraphsGlobalBalance
public import Oberwolfach.LongMatchingPhysicalCorrectionFields
public import Oberwolfach.LongSameSampleChangeGraphsFromReference
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
local instance matchingGlobalBalanceGraphsFin (n:ℕ):DecidableEq (Fin n):=factorRootsFin n
local instance matchingGlobalBalanceGraphsArc {n:ℕ} (P:Fin n×Fin n→Prop):DecidableEq {e:Fin n×Fin n // P e}:=Classical.decEq _
attribute [local instance] partitionedDivisibleArcFinite partitionedDivisibleOrdFinite partitionedDivisibleMarkFinite
theorem long_matching_witness_vortex_graphs_global_balance
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U] [Nonempty (Fin n)]
    (F:U→SimpleGraph (Fin n)) (G S Del:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d r:ℕ)
    (hd:2≤d) (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (z:MarkedExpandedActualOutcome (U:=U) π d) (M:Fin n→Fin n→ℕ) (I:Finset (Fin n)):
    let m:=r+4
    let ω:=z.1
    let raw:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedApproximateCollapse e (ω e)
    let t:=startRetentionMinimum (rawStartHubSet π d (fun e=>ω (Sum.inr e)) false)
    let J:=z.2;
    ∀ (Pack:Finset (Sym2 (Fin n))) (Enew:U→Finset (Sym2 (Fin n))) (A:Finset (Fin n×Fin n))
    (R:U→Finset (Fin n)) (θ δ ηphys ηdel ηtype lossRow lossCol ε ζ:ℝ)
    (hI:∀v,π v∈I↔v∈I)
    (hprov:LongFactorComplementProvenance F S G π d m raw t J Pack Enew A R)
    (hcontrol:LongResidualSpokeCompletionControl π d raw t J R θ δ)
    (Δ:ℝ) (K:ℕ) (Dmatch alpha γ eps βList:ℝ)
    (hF:∀u,(F u).IsRegularOfDegree 2) (weight:(Fin (r+4+1)→Fin n)→ℝ)
    (w:∀i:Fin K,OrdinaryCycle G (longPaddedSeedExponent i+2)→ℝ)
    (D₀:MarkedReferenceDeletion G π d (fun e=>rawExpandedMarkedCollapse e (z.1 e)))
    (C:Finset (Finset (Fin n)⊕(Fin n×U)))
    (hw:LongClassMatchingDeletionWitness Δ G π d r z I K θ Dmatch alpha γ eps βList F hF weight w D₀ C S M Del)
    (hDelBound:Δ*n≤ηdel)
    (h:ℕ) (hh:1≤h) (q s:U→Bool→ℝ) (D p k μ εR δref γref εrow εcol:ℝ)
    (hεR:0≤εR) (hεrow:0≤εrow) (hεcol:0≤εcol)
    (hq:∀u,q u false=μ) (hs:∀u,s u false=(m:ℝ)*μ)
    (hp:p*D=(m:ℝ)*(μ*Fintype.card U)) (hk:k*D=μ*Fintype.card U)
    {DQ mm:ℕ} {β εQ:ℝ} (Q:Vortex U G DQ β εQ mm) (Hinner:Finset U)
    (hIeq:I=Q.extendedVertices 1) (hHeq:Hinner=Q.extendedIndices 1),
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
        (fun b v u=>H' b (markedVortexVertexEmbedding Q i v) (markedVortexHubEmbedding Q i u))) ∧
      (∀v u,¬(H' false v u∧H' true v u)) ∧
      (∀u v w,H' false v u→H' true w u→v≠π w):=by
  intro m ω raw t J Pack Enew A R θ δ ηphys ηdel ηtype lossRow lossCol ε ζ hI hprov hcontrol
    Δ K Dmatch alpha γ eps βList hF weight w D₀ C hw hDelBound h hh q s D p k μ εR δref γref εrow εcol
    hεR hεrow hεcol hq hs hp hk DQ mm β εQ Q Hinner hIeq hHeq Small P T₁ σ ρ Y H H₀ HK H' T
    hMarked hOrd hInner hdiv hbal hChange hType hRetRow hRetCol hBudgetRow hBudgetCol hFirst
  have hmatch:=long_matching_physical_correction_fields Δ G π d r z I K θ Dmatch alpha γ eps βList F hF weight w D₀ C S Del M hw
  have hdec:matchingPhysicalCorrectionFin n=globalBalancedVortexChangeGraphsFin n:=Subsingleton.elim _ _
  have hdec6:matchingPhysicalCorrectionSix=globalBalancedVortexChangeGraphsFin 6:=Subsingleton.elim _ _
  try rw [hdec] at hmatch
  try rw [hdec6] at hmatch
  have hbase:=long_same_sample_vortex_change_graphs_from_global_balance F G S Del π d m hd hnoshort ω M I t raw J Pack Enew A R θ δ ηphys ηdel ηtype lossRow lossCol ε ζ
    hmatch.1 hmatch.2.1 hmatch.2.2.1 hI hprov hcontrol h hh q s D p k μ εR δref γref εrow εcol hεR hεrow hεcol hq hs hp hk Q Hinner hIeq hHeq
  have hdec':globalBalancedVortexChangeGraphsFin n=matchingGlobalBalanceGraphsFin n:=Subsingleton.elim _ _
  try rw [hdec'] at hbase
  obtain ⟨τ,FR,FS,h1,h2,h3,h4,h5,h6,h7,h8⟩:=hbase T hMarked hOrd hInner hdiv hbal hChange
    (fun v=>(hmatch.2.2.2 v).trans hDelBound) hType hRetRow hRetCol hBudgetRow hBudgetCol hFirst
  have hspokes:=long_factor_complement_corrected_spoke_geometry F S G π d m (by omega) raw t J Pack Enew A R hprov
  exact ⟨τ,FR,FS,h1,h2,h3,h4,h5,h6,h7,h8,hspokes.1,hspokes.2⟩
end Oberwolfach
