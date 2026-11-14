module

public import Oberwolfach.FirstVortexResidualTargetSize
public import Oberwolfach.LongInnerTargetsAlignedWheelsLocal
public import Oberwolfach.FirstVortexLocalLoadPowerMargins
public import Oberwolfach.FirstVortexHubCardinality
public import Oberwolfach.LongSelectedAlignedSourceWithLoadAndMatching

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance firstVortexSourceMatchingTargetSizeFin (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n

theorem first_vortex_source_matching_target_size
    (ε θ ρ₀ lam:ℝ) (d:ℕ) (hε:0<ε) (hθ:0<θ) (hθ1:θ≤1)
    (hρhi:ρ₀≤1) (hεsmall:ε≤(ρ₀/4)/80000)
    (hlam:0≤lam) (hlam1:lam≤1) (hd:0<d) (hspacing:1/(d:ℝ)≤θ/1024):
    ∃N:ℕ,∀n K:ℕ,N≤n→0<K→∀(U:Type) [Fintype U] [DecidableEq U]
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (m:ℕ) (hm:0<m) (ℓ:Fin K→ℕ)
    (Dv mm:ℕ) (β:ℝ) (Vort:Vortex U P Dv β ε mm)
    (hreg:P.IsRegularOfDegree Dv) (hDv:0<Dv) (hρ:initialIndexDensity U Dv≤1) (hmm:0<mm)
    (σE:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (Del:Finset (Sym2 (Fin n))) (t:ℕ)
    (Jret:StartRetentionOutcome (rawStartHubSet π d
      (fun e=>rawExpandedApproximateCollapse (Sum.inr e) (σE (Sum.inr e))) false) t),
    let raw:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedApproximateCollapse e (σE e)
    let H:=Vort.extendedIndices 1
    let A:=Vort.extendedVertices 1
    let σ:=fun e=>raw (Sum.inr e)
    let R:=mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)
    let T:=bernoulliVertexSet (longRawHubState P π d raw true true)
    let S:=longRawSurvivingResources P π d raw true true Del
    let hST:=long_raw_surviving_resources_subset P π d raw true true Del
    let q:=survivingCandidateEmbedding R S T hST
    let Q:=restrictedResourceSet R (Function.Embedding.subtype (·∈S))
    ∀(M:Finset (RestrictedResource R (Function.Embedding.subtype (·∈S))))
    (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (a γ ζ:ℝ) (hγ:0≤γ) (ha:a≤lam/(10*d)) (hγcap:γ≤lam/(10*d))
    (hζ:ζ≤θ/4096) (hζ0:0≤ζ)
    (hmatch:∀i,((longRawIncidenceSet S i\M.biUnion Q).card:ℝ)≤max (a*n) (γ*(longRawIncidenceSet S i).card))
    (hrows:RetainedRestrictionLocalGood π d σ false t A H ζ Jret)
    (hfixed:∀w∈H,|rawIntervalUnassignedHubCountOn π d σ w A-
      (A.card:ℝ)*(1-(∑g,longAssignedIntervalProbability F hF K m θ w g)-
        (∑j,longAssignedSpokeProbability F hF K m θ w j))|<(A.card:ℝ)^(3/4:ℝ))
    (hcolumn:∀v∈A,|rawIntervalUnassignedColumnCount π d σ v H-
      ∑w∈H,(1-(∑g,longAssignedIntervalProbability F hF K m θ w g)-
        (∑j,longAssignedSpokeProbability F hF K m θ w j))|<(A.card:ℝ)^(3/4:ℝ))
    (Kbad Used:SimpleGraph (Fin n)) (absorber:U→Finset (Fin n)) (δ:ℝ) (hU:0<Fintype.card U)
    (Extra:(U→Finset (Fin n))→Finset (Sym2 (Fin n))→Prop),
    LongSelectedAlignedSourceWithLoadAndMatching hU F P π d m ℓ raw t Jret σE H A Kbad Used absorber δ Extra (M.map q) →
    LongSelectedAlignedSourceWithLoadAndMatching hU F P π d m ℓ raw t Jret σE H A Kbad Used absorber δ
      (fun occupied Pack=>Extra occupied Pack ∧ ∀w,
        ((innerRequiredTargets H A (rawReservedSpokeList π d σ)
          (retainedFinalMarkedAt π d σ t Jret) absorber occupied w).card:ℝ)≤(θ/1024)*n) (M.map q) :=by
  obtain ⟨N,hN⟩:=first_vortex_local_load_power_margins ε 1 θ hε (by norm_num) hθ
  refine ⟨max N 1,?_⟩
  intro n K hn hK U _ _ P π m hm ℓ Dv mm β Vort hreg hDv hρ hmm σE Del t Jret raw H A σ R T S hST q Q M F hF a γ ζ hγ ha hγcap hζ hζ0 hmatch hrows hfixed hcolumn Kbad Used absorber δ hU Extra hsource
  letI:Nonempty U:=Fintype.card_pos_iff.mp hU
  rcases hsource with ⟨Dsrc,orig,hPair,hValid,hUnion,hArcs,E,hAlign,hLate,ext,inner,ψ,assign,data,hprops,hload,pieces,hpieceEdge,hpieceArc,Pack,hOldDisj,hOldPack,hApprox,hSelected,hassign,hsize,hUsed,hExtra⟩
  let occupied:=fun w=>((data w).oldDomain\bufferedPathStrictInterior (fun _=>(m+1)*d) (inner w)).image (ψ w)
  have hn0:0<n:=by omega
  have hu:=first_vortex_hub_cardinality_le_host hreg hn0 hDv hρ
  have hprops':∀w,(data w).s₂=secondSumIndices ∧
      (∀i∈(data w).s₂,∀j:Fin (d+1),∃x∈(data w).oldDomain\bufferedPathStrictInterior (fun _=>(m+1)*d) (inner w),
        ψ w x=(π^j.val) (retainedAndRawIntervalRoot π d σ false true t Jret w i)) ∧
      (∀j:{a:LongRawSelectedOrdinary π d m ℓ (Function.Embedding.subtype (·∈T)) (M.map q) // (assign a).1=w},
        ∀v∈Finset.univ.image ((longRawSelectedOrdinaryWheel π d m ℓ (Function.Embedding.subtype (·∈T)) (M.map q) j.val).val.1.val),v∈occupied w) ∧
      (∀W∈longRawMarkedWheelsAtHub P π d m ℓ raw true true (M.map q) w,∀i:Fin (m+1),W.1.val i∈occupied w):=by
    intro w
    rcases hprops w with ⟨_,_,_,_,_,_,_,hmarker,_,_,_,_,hs₂,_,_,_,_,hOrd,hMarked⟩
    exact ⟨hs₂,hmarker,hOrd,hMarked⟩
  have hrow0:=long_inner_targets_from_aligned_wheel_images_local hn0 hK m d hm F hF θ hθ.le hθ1 π
  have heq : instDecidableEqFin n = firstVortexSourceMatchingTargetSizeFin n := Subsingleton.elim _ _
  have heqK : instDecidableEqFin K = firstVortexSourceMatchingTargetSizeFin K := Subsingleton.elim _ _
  try rw [heq] at hrow0
  try rw [heqK] at hrow0
  have hrow:=hrow0 raw t Jret H A absorber ζ hrows hfixed hcolumn P ℓ Del a γ hγ hu M hmatch assign hassign data inner ψ hprops'
  have hI:(A.card:ℝ)≤ε*n:=by
    simpa only [A,Fintype.card_fin] using Vort.first_inner_vertex_size_upper hε.le
  have hA:(A.card:ℝ)≤n:=by exact_mod_cast (le_trans (Finset.card_le_univ A) (by simp))
  have hpow:= (hN n (le_trans (le_max_left _ _) hn) U P Dv mm β Vort hmm).2
  have hsub:(A.card:ℝ)^(3/4:ℝ)≤(θ/4096)*n:=by
    have hh:=mul_le_mul_of_nonneg_left hA (by positivity : 0≤θ/4096)
    exact hpow.trans hh
  have htarget0:=first_vortex_residual_target_size_from_local_rows (n:=n) (U:=U)
  try rw [heq] at htarget0
  have htarget:=htarget0 H A (rawReservedSpokeList π d σ)
    (retainedFinalMarkedAt π d σ t Jret) absorber occupied d hd θ ρ₀ ε (θ/4096) ζ lam a γ
    hθ hρhi hεsmall hI hsub (le_refl _) hζ hζ0 hlam hlam1 hspacing ha hγcap hrow.1
  refine ⟨Dsrc,orig,hPair,hValid,hUnion,hArcs,E,hAlign,hLate,ext,inner,ψ,assign,data,hprops,hload,pieces,hpieceEdge,hpieceArc,Pack,hOldDisj,hOldPack,hApprox,hSelected,hassign,hsize,hUsed,?_⟩
  exact ⟨hExtra,htarget⟩
end Oberwolfach
