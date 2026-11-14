module

public import Oberwolfach.LongResidualGainFromLocalTestsSplit
public import Oberwolfach.LongInnerTargetsAlignedWheelsLocal
public import Oberwolfach.LongUnusedSpokeLinearBounds

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 25000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_residual_gain_from_aligned_wheel_images_split
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U] (hn:0<n) (hK:0<K)
    (m d:ℕ) (hm:0<m) (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (θ:ℝ) (hθ:0≤θ) (hθ1:θ≤1) (π:Equiv.Perm (Fin n))
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (t:ℕ)
    (J:StartRetentionOutcome (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false) t)
    (vertices:Finset (Fin n))
    (ζ:ℝ) (hrows:RetainedRestrictionLocalGood π d (fun e=>raw (Sum.inr e)) false t vertices Finset.univ ζ J)
    (hfixed:∀w,|rawIntervalUnassignedHubCountOn π d (fun e=>raw (Sum.inr e)) w vertices-
      (vertices.card:ℝ)*(1-(∑g,longAssignedIntervalProbability F hF K m θ w g)-
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
    ∀(Rnew:U→Finset (Fin n)),
    let Y:=retainedFinalMarkedAt π d (fun e=>raw (Sum.inr e)) t J
    let Hold:=fun w=>Finset.univ.filter (fun v=>retainedRawMarkedSpokes π d (fun e=>raw (Sum.inr e)) false t J false false false v w);
    (∀w,Disjoint (Rnew w\Y w) (occupied w))→
    ∀w,((vertices∩((Rnew w\Y w)\Hold w)).card:ℝ)≤
      2*θ*vertices.card+(vertices.card:ℝ)^(3/4:ℝ)+2*ζ*vertices.card+max a γ*n :=by
  intro R T S hST q Q M hmatch assign hhub data paths ψ occupied hprops Rnew Y Hold hOld w
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
  let unused:=longUnusedOrdinarySpokes π d raw occupied
  have hord:=long_unused_ordinary_spokes_cover π d raw occupied
  obtain ⟨hr,hc⟩:=long_unused_ordinary_spokes_matching_bounds P₀ π d m ℓ raw Del M occupied hOrd hMarked
  have hlinear:=long_unused_spoke_linear_bounds S (M.biUnion Q) unused a γ hγ hu hmatch hr hc
  have hh:=long_residual_gain_from_local_tests_split hn hK m d hm F hF θ hθ hθ1 π (fun e=>raw (Sum.inr e)) t J
    vertices Rnew occupied unused happrox hord ζ hrows hfixed hOld w
  have hsub:((unused w∩vertices).card:ℝ)≤(unused w).card:=by exact_mod_cast Finset.card_le_card Finset.inter_subset_left
  exact hh.trans (by linarith [hlinear.1 w])
end Oberwolfach
