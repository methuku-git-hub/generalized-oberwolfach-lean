module

public import Oberwolfach.LongSelectedRetainedClassDynamicSameBalancedAllHub
public import Oberwolfach.LongSelectedRetainedClassDynamicSameBalancedAllHubBudget
public import Oberwolfach.LongSelectedRetainedClassDynamicSameBalancedTrackedLocal
public import Oberwolfach.LongSelectedRetainedClassDynamicSameBalancedTrackedBudget
public import Oberwolfach.LongResidualPrescribedFromCounts

@[expose] public section
/-! The prescribed vertices in the balanced completion are bounded by the
start-count tests and the incidence guarantee of the same matching. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance balancedAllHubPrescribedFromMatchingFin (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n

theorem long_balanced_all_hub_prescribed_from_matching
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (hn:0<n) (hK:0<K) (hU:0<Fintype.card U)
    (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ) (hd:1≤d) (hm:0<m)
    (ℓ:Fin K→ℕ) (raw:RawMarkedOutcome (Fin n) U Bool Bool) (t:ℕ)
    (Jret:StartRetentionOutcome (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false) t)
    (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (H:Finset U) (A:Finset (Fin n)) (Sclass:SimpleGraph (Fin n))
    (Kbad:Finset (Sym2 (Fin n))→SimpleGraph (Fin n)) (Used DelG Reserve:SimpleGraph (Fin n))
    (absorber:U→Finset (Fin n)) (δ:ℝ) (Mhost:Fin n→Fin n→ℕ) (Dhost:Fin n→Fin n→Prop)
    (Extra:(U→Finset (Fin n))→Finset (Sym2 (Fin n))→Prop) (ρ₀ θ δglobal α γ:ℝ)
    (hθ:0≤θ) (hθ1:θ≤1) (hγ:0≤γ)
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (Del:Finset (Sym2 (Fin n)))
    (hcounts:∀w g,|rawIntervalHubStartCount π d g (fun e=>raw (Sum.inr e)) w-
      (n:ℝ)*longAssignedIntervalProbability F hF K m θ w g/(d:ℝ)|<(n:ℝ)^(3/4:ℝ)/(d:ℝ)):
    let R:=mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)
    let T:=bernoulliVertexSet (longRawHubState P π d raw true true)
    let S:=longRawSurvivingResources P π d raw true true Del
    let hST:=long_raw_surviving_resources_subset P π d raw true true Del
    let q:=survivingCandidateEmbedding R S T hST
    let Q:=restrictedResourceSet R (Function.Embedding.subtype (·∈S));
    ∀Mix:Finset (RestrictedResource R (Function.Embedding.subtype (·∈S))),
    (∀i,((longRawIncidenceSet S i\Mix.biUnion Q).card:ℝ)≤max (α*n) (γ*(longRawIncidenceSet S i).card))→
    LongSelectedRetainedClassDynamicSourceSameBalancedAllHub hU F P π d m ℓ raw t Jret σ H A Sclass Kbad Used DelG Reserve absorber δ Mhost Dhost Extra ρ₀ θ δglobal (Mix.map q)→
    LongSelectedRetainedClassDynamicSourceSameBalancedAllHubBudget hU F P π d m ℓ raw t Jret σ H A Sclass Kbad Used DelG Reserve absorber δ Mhost Dhost Extra ρ₀ θ δglobal
      (2*((n:ℝ)+2*(n:ℝ)^(3/4:ℝ))/(d:ℝ)+2*max α γ*n) (Mix.map q) :=by
  intro R T S hST q Q Mix hmatch hsource
  letI:Nonempty U:=Fintype.card_pos_iff.mp hU
  rcases hsource with ⟨Dsrc,orig,hPair,hValid,hUnion,hArcs,E,hAlign,hLate,ext,inner,ψ,assign,data,hprops,pieces,hpieceEdge,hpieceArc,Pack,hExact,hload,hOldDisj,hOldPack,hApprox,hSelected,hassign,hsize,hUsed,hExtra,hcapacity,hupper,hglobal,hallload,hcompletion,piecesNew,Φ,fC,hgraphNew,hC,hR,hZ,hImage,hYavoid,hstart,hfinish,hSpokes,hsourceTail,hCover,hDirected,hHost,hPacked,hFirst,hNoNew,hTracked,hLocal,hBalance,hKcover,hJavoid,hPackAvoid,hEunion,hLoss,hReserve⟩
  have hpres:∀w,((residualSubtypeSet (data w).remaining (data w).prescribed).card:ℝ)≤
      2*((n:ℝ)+2*(n:ℝ)^(3/4:ℝ))/(d:ℝ)+2*max α γ*n:=by
    intro w
    rcases hprops w with ⟨hc,hd',hs1,hcycle,hsupp,hinner,hmarker,hocc,hdr,hinj,hold,hreserved,hs2,ht,hT,hlen,hverts,hOrd,hMarked,hdis,hOldAvoid,hDirection,hOldDirected⟩
    apply long_actual_residual_prescribed_from_common_counts hn P π d m hd hm F hF θ hθ hθ1 hnoshort ℓ raw t Jret Del Mix w α γ hγ hmatch (data w) (hcounts w) hs1 hd' hs2
    intro b
    simpa only [retainedAndRawIntervalRoot] using hT (.inr b)
  exact ⟨Dsrc,orig,hPair,hValid,hUnion,hArcs,E,hAlign,hLate,ext,inner,ψ,assign,data,hprops,hpres,pieces,hpieceEdge,hpieceArc,Pack,hExact,hload,hOldDisj,hOldPack,hApprox,hSelected,hassign,hsize,hUsed,hExtra,hcapacity,hupper,hglobal,hallload,hcompletion,piecesNew,Φ,fC,hgraphNew,hC,hR,hZ,hImage,hYavoid,hstart,hfinish,hSpokes,hsourceTail,hCover,hDirected,hHost,hPacked,hFirst,hNoNew,hTracked,hLocal,hBalance,hKcover,hJavoid,hPackAvoid,hEunion,hLoss,hReserve⟩
end Oberwolfach
