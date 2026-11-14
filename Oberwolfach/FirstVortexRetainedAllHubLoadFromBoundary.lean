module

public import Oberwolfach.FirstVortexGlobalLoadFromBoundaryTarget
public import Oberwolfach.LongSelectedRetainedSourceDynamicAllHubLoad
public import Oberwolfach.LongSelectedRetainedSourceDynamicGlobalLoad
public import Oberwolfach.LongInnerTargetsFromAlignedWheels
public import Oberwolfach.LongAlignedResidualCapacityPreparedTargetSum
public import Oberwolfach.ActualPrescribedLoadFromInnerTargets
public import Oberwolfach.FirstVortexResidualTargetBudget
public import Oberwolfach.FirstVortexResidualTargetSize
public import Oberwolfach.FirstVortexMatchingScalePositive
public import Oberwolfach.FirstVortexHubCardinality
public import Oberwolfach.PartitionMargins

@[expose] public section
/-! Add all-hub target capacity and vertex-load bounds to the selected
retained source using the same matching and global sampling tests. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance firstVortexAllHubBoundaryRepairFin (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n

theorem first_vortex_retained_all_hub_load_from_boundary_tests
    (ε θ δglobal ρ₀ lam:ℝ) (m d:ℕ) (hm:0<m) (hd:0<d)
    (hε:0<ε) (hθ:0<θ) (hθmax:θ≤1/100) (hδ:0<δglobal) (hθδ:10*θ≤δglobal)
    (hρ₀:0<ρ₀) (hρhi:ρ₀≤1) (hεsmall:ε≤(ρ₀/4)/80000)
    (hlam:0≤lam) (hlam1:lam≤1) (hlamθ:lam≤θ) (hinv:1/(d:ℝ)≤θ/1024):
    ∃N:ℕ,∀n K:ℕ,N≤n→0<n→3≤K→∀(U:Type) [Fintype U] [DecidableEq U]
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (Dv mm:ℕ) (β:ℝ) (Vort:Vortex U P Dv β ε mm)
    (hreg:P.IsRegularOfDegree Dv) (hDv:0<Dv) (hρ:initialIndexDensity U Dv≤1)
    (σE:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (Del:Finset (Sym2 (Fin n))) (t:ℕ)
    (Jret:StartRetentionOutcome (rawStartHubSet π d
      (fun e=>rawExpandedApproximateCollapse (Sum.inr e) (σE (Sum.inr e))) false) t),
    let ℓ:=fun i:Fin K=>longPaddedSeedExponent i+2
    let raw:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedApproximateCollapse e (σE e)
    let H:=Vort.extendedIndices 1
    let A:=Vort.extendedVertices 1
    let σ:=fun e=>raw (Sum.inr e)
    let R:=mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)
    let T:=bernoulliVertexSet (longRawHubState P π d raw true true)
    let S:=longRawSurvivingResources P π d raw true true Del
    let hST:=long_raw_surviving_resources_subset P π d raw true true Del
    let q:=survivingCandidateEmbedding R S T hST
    let Q:=restrictedResourceSet R (Function.Embedding.subtype (·∈S));
    ∀(M:Finset (RestrictedResource R (Function.Embedding.subtype (·∈S))))
    (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (eps a γ ζ ρ α:ℝ) (heps0:0≤eps) (hγ:0≤γ)
    (ha:a≤lam/(10*(d:ℝ))) (hγcap:γ≤lam/(10*(d:ℝ)))
    (hζ0:0≤ζ) (hζ:ζ≤θ/4096) (hρ0:0≤ρ) (hρscale:ρ≤θ/4096)
    (hscale:max a γ*n≤ρ*A.card) (hα:0<α)
    (hepsAssign:3*eps≤lam*(θ/(100*(K:ℝ)^2)))
    (hαsmall:α/16≤((ρ₀/4)/40000)*θ/1024)
    (hdisj:∀c∈M,∀c'∈M,c≠c'→Disjoint (Q c) (Q c'))
    (hmatch:∀i,((longRawIncidenceSet S i\M.biUnion Q).card:ℝ)≤max (a*n) (γ*(longRawIncidenceSet S i).card))
    (hcounts:∀w g,|rawIntervalHubStartCount π d g σ w-
      (n:ℝ)*longAssignedIntervalProbability F hF K m θ w g/(d:ℝ)|<(n:ℝ)^(3/4:ℝ)/(d:ℝ))
    (hsourceCount:LongMatchingSourceCountWitness F hF π d m ℓ θ eps T (M.map q))
    (hboundary:∀v,((rawIntervalBoundaryHubSet π d σ Finset.univ v).card:ℝ)≤
      4*(Fintype.card U:ℝ)/d+4*(n:ℝ)^(3/4:ℝ))
    (hrows:RetainedRestrictionGood π d σ false t (fun _:Unit=>Finset.univ) (fun _:Unit=>Finset.univ) ζ Jret)
    (hfixed:∀w,|rawIntervalUnassignedHubCountOn π d σ w A-
      (A.card:ℝ)*(1-(∑g,longAssignedIntervalProbability F hF K m θ w g)-
        (∑j,longAssignedSpokeProbability F hF K m θ w j))|<(n:ℝ)^(3/4:ℝ))
    (hcolumn:∀v,|rawIntervalUnassignedColumnCount π d σ v Finset.univ-
      ∑w:U,(1-(∑g,longAssignedIntervalProbability F hF K m θ w g)-
        (∑j,longAssignedSpokeProbability F hF K m θ w j))|<(n:ℝ)^(3/4:ℝ))
    (Kbad:Finset (Sym2 (Fin n))→SimpleGraph (Fin n)) (Used:SimpleGraph (Fin n))
    (absorber:U→Finset (Fin n)) (δ:ℝ) (hU:0<Fintype.card U)
    (Extra:(U→Finset (Fin n))→Finset (Sym2 (Fin n))→Prop)
    (hExtraDegree:∀occupied Pack,Extra occupied Pack→∀v,((Kbad Pack).degree v:ℝ)≤(α/16)*n)
    (hExtraGlobal:∀occupied Pack,Extra occupied Pack→∀v,((Kbad Pack).degree v:ℝ)≤δglobal*n/4),
    LongSelectedRetainedSourceDynamicGlobalLoad hU F P π d m ℓ raw t Jret σE H A Kbad Used absorber δ Extra ρ₀ θ δglobal (M.map q) →
    LongSelectedRetainedSourceDynamicAllHubLoad hU F P π d m ℓ raw t Jret σE H A Kbad Used absorber δ Extra ρ₀ θ δglobal (M.map q) :=by
  obtain ⟨Ncap,hNcap⟩:=long_aligned_residual_capacity_from_prepared_target_sum m d hm hd θ hθ
  obtain ⟨Npow,hNpow⟩:=eventually_three_quarters_and_constant_le_linear (min (θ/4096) (δglobal/16)) 0 (by positivity)
  obtain ⟨Nbound,hNbound⟩:=first_vortex_global_load_from_boundary_and_target_budget δglobal θ d hδ hθ hθδ hinv
  refine ⟨max Ncap (max Npow (max Nbound 1)),?_⟩
  intro n K hn hn0 hK U _ _ P π Dv mm β Vort hreg hDv hρ σE hnoshort Del t Jret ℓ raw H A σ R T S hST q Q M F hF eps a γ ζ ρ α heps0 hγ ha hγcap hζ0 hζ hρ0 hρscale hscale hα hepsAssign hαsmall hdisj hmatch hcounts hsourceCount hboundary hrows hfixed hcolumn Kbad Used absorber δ hU Extra hExtraDegree hExtraGlobal hsource
  letI:Nonempty U:=Fintype.card_pos_iff.mp hU
  rcases hsource with ⟨Dsrc,orig,hPair,hValid,hUnion,hArcs,E,hAlign,hLate,ext,inner,ψ,assign,data,hprops,pieces,hpieceEdge,hpieceArc,Pack,hExact,hload,hOldDisj,hOldPack,hApprox,hSelected,hassign,hsize,hUsed,hExtra,hcapacity,hupper,hglobal⟩
  let occupied:=fun w=>((data w).oldDomain\bufferedPathStrictInterior (fun _=>(m+1)*d) (inner w)).image (ψ w)
  let AbsAll:=fun w=>if w∈H then absorber w else ∅
  let Zall:=innerRequiredTargets Finset.univ A (rawReservedSpokeList π d σ) (retainedFinalMarkedAt π d σ t Jret) AbsAll occupied
  have hu:=first_vortex_hub_cardinality_le_host hreg hn0 hDv hρ
  have hprops':∀w,(data w).s₂=secondSumIndices ∧
      (∀i∈(data w).s₂,∀j:Fin (d+1),∃x∈(data w).oldDomain\bufferedPathStrictInterior (fun _=>(m+1)*d) (inner w),
        ψ w x=(π^j.val) (retainedAndRawIntervalRoot π d σ false true t Jret w i)) ∧
      (∀j:{a:LongRawSelectedOrdinary π d m ℓ (Function.Embedding.subtype (·∈T)) (M.map q) // (assign a).1=w},
        ∀v∈Finset.univ.image ((longRawSelectedOrdinaryWheel π d m ℓ (Function.Embedding.subtype (·∈T)) (M.map q) j.val).val.1.val),v∈occupied w) ∧
      (∀W∈longRawMarkedWheelsAtHub P π d m ℓ raw true true (M.map q) w,∀i:Fin (m+1),W.1.val i∈occupied w):=by
    intro w
    rcases hprops w with ⟨_,_,_,_,_,_,_,hmarker,_,_,_,_,hs₂,_,_,_,_,hOrd,hMarked,_,_,_,_⟩
    exact ⟨hs₂,hmarker,hOrd,hMarked⟩
  have hrow0:=long_inner_targets_from_aligned_wheel_images (n:=n) (K:=K) (U:=U) hn0 (by omega) m d hm F hF θ hθ.le (by linarith) π
  have heq:instDecidableEqFin n=firstVortexAllHubBoundaryRepairFin n:=Subsingleton.elim _ _
  have heqK:instDecidableEqFin K=firstVortexAllHubBoundaryRepairFin K:=Subsingleton.elim _ _
  try rw [heq] at hrow0
  try rw [heqK] at hrow0
  have hrow:=hrow0 raw t Jret Finset.univ A AbsAll ζ hrows hfixed hcolumn P ℓ Del a γ hγ hu M hmatch assign hassign data inner ψ hprops'
  have hpow0:=hNpow n (by omega)
  have hnR:(0:ℝ)≤n:=Nat.cast_nonneg n
  have hpow:((n:ℝ)^(3/4:ℝ))≤(θ/4096)*n:=by
    have hh:=mul_le_mul_of_nonneg_right (min_le_left (θ/4096) (δglobal/16)) hnR
    nlinarith only [hpow0,hh]
  have hglobalPow:4*(n:ℝ)^(3/4:ℝ)≤δglobal*n/4:=by
    have hh:=mul_le_mul_of_nonneg_right (min_le_right (θ/4096) (δglobal/16)) hnR
    nlinarith only [hpow0,hh]
  have hA:(A.card:ℝ)≤ε*n:=by
    simpa only [A,Fintype.card_fin] using Vort.first_inner_vertex_size_upper hε.le
  have htarget:∀w,((Zall w).card:ℝ)≤(θ/1024)*n:=by
    intro w
    have hc:=first_vortex_residual_target_coefficient d hd θ ρ₀ ε (θ/4096) ζ lam a γ
      hθ hρhi hεsmall (le_refl _) hζ hlam hlam1 hinv ha hγcap
    have hmul:=mul_le_mul_of_nonneg_right hc hnR
    have hA':=mul_le_mul_of_nonneg_left hA (by positivity:0≤2*θ)
    have hh:=hrow.1 w
    dsimp only [Zall] at hh ⊢
    nlinarith only [hh,hA',hpow,hmul]
  have htargetGlobal:∀v,((Finset.univ.filter (fun w=>v∈Zall w)).card:ℝ)≤(2*θ+θ/4096+ζ+ρ)*n:=by
    intro v
    have hh:=hrow.2 v
    have hU':(Fintype.card U:ℝ)≤n:=by exact_mod_cast hu
    have hA':(A.card:ℝ)≤n:=by exact_mod_cast (le_trans (Finset.card_le_univ A) (by simp))
    have h1:=mul_le_mul_of_nonneg_left hU' (by positivity:0≤2*θ)
    have h2:=mul_le_mul_of_nonneg_left hU' hζ0
    have h3:=mul_le_mul_of_nonneg_left hA' hρ0
    dsimp only [Zall] at hh ⊢
    nlinarith only [hh,h1,h2,h3,hpow,hscale]
  have hN':=hNcap n K (by omega) hn0 hK
  have hdec:alignedCapacityPreparedTargetSumFin n=firstVortexAllHubBoundaryRepairFin n:=Subsingleton.elim _ _
  have hdecK:alignedCapacityPreparedTargetSumFin K=firstVortexAllHubBoundaryRepairFin K:=Subsingleton.elim _ _
  try rw [hdec] at hN'
  try rw [hdecK] at hN'
  have hcapacityAll:∀w,8*(residualSubtypeSet (data w).remaining (data w).prescribed).card+
      8*⌈4*((Kbad Pack).edgeFinset.card:ℝ)/(((ρ₀/4)/40000)*Fintype.card (Fin n))⌉₊+4*(Zall w).card+10≤
        Fintype.card {x // x∈(data w).remaining}:=by
    intro w
    rcases hprops w with ⟨hc,hd',hs1,hEmbed,_,_,_,_,_,_,_,_,hs2,ht,hT,hlen,_,_,_⟩
    have hpositions:∀x:{x:Fin n // rawIntervalColouredStart π d (fun e=>raw (Sum.inr (w,e))) x true},
      (data w).T (.inr x)=packedPhysicalSpokePositions _ _ _ _ m (3*d) d π
        (rawMarkedPairSpokes π d raw true true false) (rawMarkedPairSpokes π d raw true true true)
        (longRawMarkedWheelsAtHub P π d m ℓ raw true true (M.map q) w) w x.val:=by
      intro x
      simpa only [retainedAndRawIntervalRoot] using hT (.inr x)
    have hC:=hN' U F hF P π raw hnoshort t Jret Del M hdisj w assign hassign hsize
    exact hC (data w) hc hd' hs1 hs2 eps hθmax heps0 (hcounts w) ht hEmbed hlen hsourceCount a γ ρ₀ α lam hγ hρ₀ hα hlam hlamθ hepsAssign hinv ha hγcap hαsmall hmatch (Kbad Pack) (Zall w) (hExtraDegree occupied Pack hExtra) (htarget w) hpositions
  have htargetBound:∀v,((Finset.univ.filter (fun w=>v∈Zall w)).card:ℝ)≤δglobal*n/4:=by
    intro v
    have hc:=inner_target_occurrence_budget θ δglobal (θ/4096) ζ ρ hθ.le hθδ (le_refl _) hζ hρscale
    have hh:=mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg n)
    linarith [htargetGlobal v]
  have hscale':max a γ*n≤(θ/4096)*n:=by
    have hA':(A.card:ℝ)≤n:=by exact_mod_cast (le_trans (Finset.card_le_univ A) (by simp))
    have hh:=mul_le_mul_of_nonneg_left hA' hρ0
    have hh':=mul_le_mul_of_nonneg_right hρscale (Nat.cast_nonneg n)
    linarith
  have hBound:=hNbound n K (by omega) U
  have hdecBound:firstGlobalBoundaryTargetFin n=firstVortexAllHubBoundaryRepairFin n:=Subsingleton.elim _ _
  have hdecBoundK:firstGlobalBoundaryTargetFin K=firstVortexAllHubBoundaryRepairFin K:=Subsingleton.elim _ _
  try rw [hdecBound] at hBound
  try rw [hdecBoundK] at hBound
  have hglobalAll:=hBound P π m (m+1) (by omega) ℓ raw Del t Jret M F data ext ψ
    (fun w=>(hprops w).1) (fun w=>(hprops w).2.1)
    (fun w=>(hprops w).2.2.2.2.2.2.2.2.2.2.2.2.1)
    (fun w=>(hprops w).2.2.2.2.1) (fun w=>(hprops w).2.2.2.2.2.2.1)
    (fun w=>(hprops w).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    a γ hγ hu hmatch hboundary (Kbad Pack) Zall hscale' (hExtraGlobal occupied Pack hExtra) htargetBound
  exact ⟨Dsrc,orig,hPair,hValid,hUnion,hArcs,E,hAlign,hLate,ext,inner,ψ,assign,data,hprops,pieces,hpieceEdge,hpieceArc,Pack,hExact,hload,hOldDisj,hOldPack,hApprox,hSelected,hassign,hsize,hUsed,hExtra,hcapacity,hupper,hglobal,hcapacityAll,hglobalAll⟩
end Oberwolfach
