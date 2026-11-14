module

public import Oberwolfach.LongSelectedOrientedSourceWithLoadAndMatching
public import Oberwolfach.LongSelectedOrientedSourceWithMatchingCapacity
public import Oberwolfach.LongSelectedOrientedSourceCapacityUpper
public import Oberwolfach.LongSelectedOrientedSourceGlobalLoad
public import Oberwolfach.LongSelectedOrientedSourceResidualCompletion
public import Oberwolfach.LongSelectedOrientedSourceCapacityUpper
public import Oberwolfach.LongSelectedOrientedSourceGlobalLoad
public import Oberwolfach.LongSelectedOrientedSourceWithMatchingCapacity
public import Oberwolfach.LongSelectedAlignedSourceGlobalLoad
public import Oberwolfach.FirstVortexTargetGlobalOccurrence
public import Oberwolfach.ActualPrescribedLoadFromInnerTargets
public import Oberwolfach.FirstVortexSourceMatchingTargetSize

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance firstVortexOrientedGlobalLoadFin (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n

theorem first_vortex_oriented_global_prescribed_load
    (ε θ δglobal:ℝ) (d:ℕ) (hε:0<ε) (hθ:0<θ) (hθ1:θ≤1) (hδ:0<δglobal) (hθδ:10*θ≤δglobal)
    (hd:0<d):
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
    (a γ ζ ρ:ℝ) (hγ:0≤γ) (hζ:ζ≤θ/4096) (hζ0:0≤ζ)
    (hρscale:ρ≤θ/4096) (hρscale0:0≤ρ) (hscale:max a γ*n≤ρ*A.card)
    (hmarg:4/(m:ℝ)≤δglobal/4)
    (hOcc:∀v,((rawIntervalExtendedAnyHubSet π d σ v).card:ℝ)≤4*(Fintype.card U:ℝ)/(m:ℝ)+4*(n:ℝ)^(3/4:ℝ))
    (hmatch:∀i,((longRawIncidenceSet S i\M.biUnion Q).card:ℝ)≤max (a*n) (γ*(longRawIncidenceSet S i).card))
    (hrows:RetainedRestrictionLocalGood π d σ false t A H ζ Jret)
    (hfixed:∀w∈H,|rawIntervalUnassignedHubCountOn π d σ w A-
      (A.card:ℝ)*(1-(∑g,longAssignedIntervalProbability F hF K m θ w g)-
        (∑j,longAssignedSpokeProbability F hF K m θ w j))|<(A.card:ℝ)^(3/4:ℝ))
    (hcolumn:∀v∈A,|rawIntervalUnassignedColumnCount π d σ v H-
      ∑w∈H,(1-(∑g,longAssignedIntervalProbability F hF K m θ w g)-
        (∑j,longAssignedSpokeProbability F hF K m θ w j))|<(A.card:ℝ)^(3/4:ℝ))
    (Kbad Used:SimpleGraph (Fin n)) (absorber:U→Finset (Fin n)) (δ ρ₀:ℝ) (hU:0<Fintype.card U)
    (Extra:(U→Finset (Fin n))→Finset (Sym2 (Fin n))→Prop)
    (hExtraDegree:∀occupied Pack,Extra occupied Pack→∀v,(Kbad.degree v:ℝ)≤δglobal*n/4),
    LongSelectedOrientedSourceWithMatchingCapacityUpper hU F P π d m ℓ raw t Jret σE H A Kbad Used absorber δ Extra ρ₀ θ (M.map q) →
    LongSelectedOrientedSourceWithGlobalLoadCapacityUpper hU F P π d m ℓ raw t Jret σE H A Kbad Used absorber δ Extra ρ₀ θ δglobal (M.map q) :=by
  obtain ⟨N,hN⟩:=first_vortex_local_load_power_margins ε δglobal θ hε hδ hθ
  obtain ⟨Nglobal,hNglobal⟩:=eventually_three_quarters_and_constant_le_linear (δglobal/16) 0 (by positivity)
  refine ⟨max N (max Nglobal 1),?_⟩
  intro n K hn hK U _ _ P π m hm ℓ Dv mm β Vort hreg hDv hρ hmm σE Del t Jret raw H A σ R T S hST q Q M F hF a γ ζ ρ hγ hζ hζ0 hρscale hρscale0 hscale hmarg hOcc hmatch hrows hfixed hcolumn Kbad Used absorber δ ρ₀ hU Extra hExtraDegree hsource
  letI:Nonempty U:=Fintype.card_pos_iff.mp hU
  rcases hsource with ⟨Dsrc,orig,hPair,hValid,hUnion,hArcs,E,hAlign,hLate,ext,inner,ψ,assign,data,hprops,hload,pieces,hpieceEdge,hpieceArc,Pack,hOldDisj,hOldPack,hApprox,hSelected,hassign,hsize,hUsed,hExtra,hcapacity,hupper⟩
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
    rcases hprops w with ⟨_,_,_,_,_,_,_,hmarker,_,_,_,_,hs₂,_,_,_,_,hOrd,hMarked,_,_,_,_⟩
    exact ⟨hs₂,hmarker,hOrd,hMarked⟩
  have hrow0:=long_inner_targets_from_aligned_wheel_images_local hn0 hK m d hm F hF θ hθ.le hθ1 π
  have heq : instDecidableEqFin n = firstVortexOrientedGlobalLoadFin n := Subsingleton.elim _ _
  have heqK : instDecidableEqFin K = firstVortexOrientedGlobalLoadFin K := Subsingleton.elim _ _
  try rw [heq] at hrow0
  try rw [heqK] at hrow0
  have hrow:=hrow0 raw t Jret H A absorber ζ hrows hfixed hcolumn P ℓ Del a γ hγ hu M hmatch assign hassign data inner ψ hprops'
  have hA:(A.card:ℝ)≤n:=by exact_mod_cast (le_trans (Finset.card_le_univ A) (by simp))
  have hH:(H.card:ℝ)≤n:=by exact_mod_cast (le_trans (Finset.card_le_univ H) hu)
  have hpow:=(hN n (by omega) U P Dv mm β Vort hmm).2
  have hsub:(A.card:ℝ)^(3/4:ℝ)≤(θ/4096)*n:=by
    have hh:=mul_le_mul_of_nonneg_left hA (by positivity : 0≤θ/4096)
    exact hpow.trans hh
  let Z:=innerRequiredTargets H A (rawReservedSpokeList π d σ) (retainedFinalMarkedAt π d σ t Jret) absorber occupied
  have htarget0:=first_vortex_target_global_occurrence (n:=n) (U:=U)
  try rw [heq] at htarget0
  have htarget:=htarget0 H A (rawReservedSpokeList π d σ) (retainedFinalMarkedAt π d σ t Jret) absorber occupied
    θ (θ/4096) ζ ρ a γ hθ.le hζ0 hρscale0 hH hA hsub hscale hrow.2
  have hglobal:4*(n:ℝ)^(3/4:ℝ)≤δglobal*n/4:=by
    have hh:=hNglobal n (by omega)
    nlinarith
  have hbad:=hExtraDegree occupied Pack hExtra
  have hload0:=actual_prescribed_load_with_inner_target_bounds (n:=n) (U:=U)
    (J:=fun w=>{a:LongRawSelectedOrdinary π d m ℓ (Function.Embedding.subtype (·∈T)) (M.map q) // (assign a).1=w})
  try rw [heq] at hload0
  have hglobalLoad:=hload0 π d (m+1) σ t Jret F data ext ψ (fun w=>(hprops w).1)
    (fun w=>(hprops w).2.1) (fun w=>(hprops w).2.2.2.2.1) (fun w=>(hprops w).2.2.2.2.2.2.1)
    Kbad Z δglobal m (by exact_mod_cast hm) hδ.le hu hmarg hglobal hOcc hbad θ (θ/4096) ζ ρ hθ.le hθδ (le_refl _) hζ hρscale htarget
  refine ⟨Dsrc,orig,hPair,hValid,hUnion,hArcs,E,hAlign,hLate,ext,inner,ψ,assign,data,hprops,hload,pieces,hpieceEdge,hpieceArc,Pack,hOldDisj,hOldPack,hApprox,hSelected,hassign,hsize,hUsed,hExtra,hcapacity,hupper,?_⟩
  exact hglobalLoad
end Oberwolfach
