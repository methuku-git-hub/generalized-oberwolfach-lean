module

public import Oberwolfach.LongInnerTargetsActualMatchingLocal
public import Oberwolfach.LongRawAlignedAllWheelOccupancySelectedHost
public import Oberwolfach.LongApproximateOccupiedFromMarkers
public import Oberwolfach.LongInnerTargetsFromActualMatching
public import Oberwolfach.LongInnerTargetsFromMatchingDefects
public import Oberwolfach.LongUnusedOrdinarySpokeFromMatching
public import Oberwolfach.LongInnerRequiredTargetBound
public import Oberwolfach.LongInnerOccurrenceFromFullColumn
public import Oberwolfach.LongUnusedOrdinarySpokeCover
public import Oberwolfach.LongUnusedSpokeLinearBounds

@[expose] public section
/-! The common row and column tests and matching defects bound required targets. -/
set_option autoImplicit false
set_option maxHeartbeats 16000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_inner_targets_from_aligned_wheel_images_local
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U] (hn:0<n) (hK:0<K)
    (m d:ℕ) (hm:0<m) (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (θ:ℝ) (hθ:0≤θ) (hθ1:θ≤1) (π:Equiv.Perm (Fin n))
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (t:ℕ)
    (J:StartRetentionOutcome (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false) t)
    (inner:Finset U) (vertices:Finset (Fin n)) (absorber:U→Finset (Fin n))
    (ζ:ℝ) (hrows:RetainedRestrictionLocalGood π d (fun e=>raw (Sum.inr e)) false t vertices inner ζ J)
    (hfixed:∀w∈inner,|rawIntervalUnassignedHubCountOn π d (fun e=>raw (Sum.inr e)) w vertices-
      (vertices.card:ℝ)*(1-(∑g,longAssignedIntervalProbability F hF K m θ w g)-
        (∑j,longAssignedSpokeProbability F hF K m θ w j))|<(vertices.card:ℝ)^(3/4:ℝ))
    (hcolumn:∀v∈vertices,|rawIntervalUnassignedColumnCount π d (fun e=>raw (Sum.inr e)) v inner-
      ∑w∈inner,(1-(∑g,longAssignedIntervalProbability F hF K m θ w g)-
        (∑j,longAssignedSpokeProbability F hF K m θ w j))|<(vertices.card:ℝ)^(3/4:ℝ))
    (P₀:SimpleGraph (Fin n)) (ℓ:Fin K→ℕ) (Del:Finset (Sym2 (Fin n)))
    (a γ:ℝ) (hγ:0≤γ) (hu:Fintype.card U≤n):
    let R:=mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)
    let T:=bernoulliVertexSet (longRawHubState P₀ π d raw true true)
    let S:=longRawSurvivingResources P₀ π d raw true true Del
    let hST:=long_raw_surviving_resources_subset P₀ π d raw true true Del
    let q:=survivingCandidateEmbedding R S T hST
    let Q:=restrictedResourceSet R (Function.Embedding.subtype (·∈S))
    ∀(M:Finset (RestrictedResource R (Function.Embedding.subtype (·∈S)))),
    (∀i,((longRawIncidenceSet S i\M.biUnion Q).card:ℝ)≤max (a*n) (γ*(longRawIncidenceSet S i).card))→
    ∀(assign:LongRawSelectedOrdinary π d m ℓ (Function.Embedding.subtype (·∈T)) (M.map q)↪(Σw,(F w).ConnectedComponent)),
    (∀a,(assign a).1=(longRawSelectedOrdinaryWheel π d m ℓ (Function.Embedding.subtype (·∈T)) (M.map q) a).val.2)→
    ∀(data:∀w,ActualResidualData
      (K:=(retainedMarkedIndex π d (fun e=>raw (Sum.inr e)) false t J w) ⊕
        {a:Fin n // rawIntervalColouredStart π d (fun e=>raw (Sum.inr (w,e))) a true})
      (J:={a:LongRawSelectedOrdinary π d m ℓ (Function.Embedding.subtype (·∈T)) (M.map q) // (assign a).1=w}) (F w))
      (paths:∀w,retainedMarkedIndex π d (fun e=>raw (Sum.inr e)) false t J w→Fin ((m+1)*d+1)↪Fin n)
      (ψ:∀w,Fin n→Fin n),
    let occupied:=fun w=>((data w).oldDomain\bufferedPathStrictInterior (fun _=>(m+1)*d) (paths w)).image (ψ w)
    (∀w,(data w).s₂=secondSumIndices ∧
      (∀i∈(data w).s₂,∀j:Fin (d+1),∃x∈(data w).oldDomain\bufferedPathStrictInterior (fun _=>(m+1)*d) (paths w),
        ψ w x=(π^j.val) (retainedAndRawIntervalRoot π d (fun e=>raw (Sum.inr e)) false true t J w i)) ∧
      (∀j:{a:LongRawSelectedOrdinary π d m ℓ (Function.Embedding.subtype (·∈T)) (M.map q) // (assign a).1=w},
        ∀v∈Finset.univ.image ((longRawSelectedOrdinaryWheel π d m ℓ (Function.Embedding.subtype (·∈T)) (M.map q) j.val).val.1.val),v∈occupied w) ∧
      (∀W∈longRawMarkedWheelsAtHub P₀ π d m ℓ raw true true (M.map q) w,∀i:Fin (m+1),W.1.val i∈occupied w))→
    let Z:=innerRequiredTargets inner vertices (rawReservedSpokeList π d (fun e=>raw (Sum.inr e)))
      (retainedFinalMarkedAt π d (fun e=>raw (Sum.inr e)) t J) absorber occupied
    (∀w∈inner,((Z w).card:ℝ)≤2*θ*vertices.card+(vertices.card:ℝ)^(3/4:ℝ)+ζ*vertices.card+max a γ*n) ∧
    (∀v∈vertices,((Finset.univ.filter (fun w=>v∈Z w)).card:ℝ)≤
      2*θ*inner.card+(vertices.card:ℝ)^(3/4:ℝ)+ζ*inner.card+max a γ*n):=by
  intro R T S hST q Q M hmatch assign hhub data paths ψ occupied hprops Z
  have happrox:∀w x,rawIntervalFamilyState π d (fun e=>raw (Sum.inr e)) (x,w)=some (Sum.inl true)→x∈occupied w:=by
    intro w
    apply long_approximate_labels_occupied_from_markers π d (fun e=>raw (Sum.inr e)) w (data w) (hprops w).1
      (bufferedPathStrictInterior (fun _=>(m+1)*d) (paths w)) (ψ w)
      (retainedAndRawIntervalRoot π d (fun e=>raw (Sum.inr e)) false true t J w)
    · intro b
      rfl
    · exact (hprops w).2.1
  have hOrd:∀(w:U) (a:LongRawSelectedOrdinary π d m ℓ (Function.Embedding.subtype (·∈T)) (M.map q)),
      (longRawSelectedOrdinaryWheel π d m ℓ (Function.Embedding.subtype (·∈T)) (M.map q) a).val.2=w→
      ∀v∈Finset.univ.image ((longRawSelectedOrdinaryWheel π d m ℓ (Function.Embedding.subtype (·∈T)) (M.map q) a).val.1.val),v∈occupied w:=by
    intro w a ha
    exact (hprops w).2.2.1 ⟨a,(hhub a).trans ha⟩
  have hMarked:=fun w=>(hprops w).2.2.2
  exact long_inner_targets_from_actual_matching_local hn hK m d hm F hF θ hθ hθ1 π raw t J inner vertices absorber occupied happrox ζ hrows hfixed hcolumn P₀ ℓ Del a γ hγ hu M hmatch hOrd hMarked
end Oberwolfach
