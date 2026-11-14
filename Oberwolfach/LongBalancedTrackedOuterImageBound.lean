module

public import Oberwolfach.LongSelectedRetainedClassDynamicSameBalancedTrackedBudget
public import Oberwolfach.LongSelectedRetainedClassDynamicSameBalancedTrackedOuter

@[expose] public section
/-! At outer hubs the required target set is empty, so the tracked
completion's local image is bounded by prescribed vertices and the
assigned-edge cap. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance balancedTrackedOuterImageBoundFin (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n

theorem long_balanced_tracked_outer_image_bound
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (hU:0<Fintype.card U) (F:U→SimpleGraph (Fin n)) (P:SimpleGraph (Fin n))
    (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (t:ℕ)
    (Jret:StartRetentionOutcome (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false) t)
    (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (H:Finset U) (A:Finset (Fin n)) (Sclass:SimpleGraph (Fin n))
    (Kbad:Finset (Sym2 (Fin n))→SimpleGraph (Fin n)) (Used DelG Reserve:SimpleGraph (Fin n))
    (absorber:U→Finset (Fin n)) (δ:ℝ) (Mhost:Fin n→Fin n→ℕ) (Dhost:Fin n→Fin n→Prop)
    (Extra:(U→Finset (Fin n))→Finset (Sym2 (Fin n))→Prop) (ρ₀ θ δglobal Pbound:ℝ):
    let T:=bernoulliVertexSet (longRawHubState P π d raw true true)
    let e:{z // z∈T}↪_:=Function.Embedding.subtype _;
    ∀M:Finset (RestrictedResource (mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)) e),
    LongSelectedRetainedClassDynamicSourceSameBalancedTrackedBudget hU F P π d m ℓ raw t Jret σ H A Sclass Kbad Used DelG Reserve absorber δ Mhost Dhost Extra ρ₀ θ δglobal Pbound M→
    LongSelectedRetainedClassDynamicSourceSameBalancedTrackedOuter hU F P π d m ℓ raw t Jret σ H A Sclass Kbad Used DelG Reserve absorber δ Mhost Dhost Extra ρ₀ θ δglobal Pbound M :=by
  intro T e M hsource
  letI:Nonempty U:=Fintype.card_pos_iff.mp hU
  rcases hsource with ⟨Dsrc,orig,hPair,hValid,hUnion,hArcs,E,hAlign,hLate,ext,inner,ψ,assign,data,hprops,hpres,pieces,hpieceEdge,hpieceArc,Pack,hExact,hload,hOldDisj,hOldPack,hApprox,hSelected,hassign,hsize,hUsed,hExtra,hcapacity,hupper,hglobal,hcompletion,piecesNew,Φ,fC,hgraphNew,hC,hR,hZ,hImage,hYavoid,hstart,hfinish,hSpokes,hsourceTail,hCover,hDirected,hHost,hPacked,hFirst,hTracked,hLocal,hBalance,hKcover,hJavoid,hPackAvoid,hEunion,hLoss,hReserve⟩
  let occupied:=fun w=>((data w).oldDomain\bufferedPathStrictInterior (fun _=>(m+1)*d) (inner w)).image (ψ w)
  let Z:=innerRequiredTargets H A (fun w=>Finset.univ.filter (fun v=>retainedRawMarkedSpokes π d (fun e=>raw (Sum.inr e)) false t Jret false false false v w))
    (retainedFinalMarkedAt π d (fun e=>raw (Sum.inr e)) t Jret) absorber occupied
  have hOuter:∀w∉H,(((Finset.univ.image (Φ w))∩A).card:ℝ)≤Pbound+
      2*(⌈4*((Kbad Pack).edgeFinset.card:ℝ)/(((ρ₀/4)/40000)*Fintype.card (Fin n))⌉₊:ℕ):=by
    intro w hw
    have hz:Z w=∅:=by simp [Z,innerRequiredTargets,hw]
    have hh:=hLocal w
    change (((Finset.univ.image (Φ w))∩A).card)≤
      (residualSubtypeSet (data w).remaining (data w).prescribed).card+
        2*⌈4*((Kbad Pack).edgeFinset.card:ℝ)/(((ρ₀/4)/40000)*Fintype.card (Fin n))⌉₊+(Z w).card at hh
    rw [hz] at hh
    simp only [Finset.card_empty,Nat.add_zero] at hh
    have hcast:(((Finset.univ.image (Φ w))∩A).card:ℝ)≤
        ((residualSubtypeSet (data w).remaining (data w).prescribed).card:ℝ)+
          2*(⌈4*((Kbad Pack).edgeFinset.card:ℝ)/(((ρ₀/4)/40000)*Fintype.card (Fin n))⌉₊:ℕ):=by exact_mod_cast hh
    linarith [hpres w]
  exact ⟨Dsrc,orig,hPair,hValid,hUnion,hArcs,E,hAlign,hLate,ext,inner,ψ,assign,data,hprops,hpres,pieces,hpieceEdge,hpieceArc,Pack,hExact,hload,hOldDisj,hOldPack,hApprox,hSelected,hassign,hsize,hUsed,hExtra,hcapacity,hupper,hglobal,hcompletion,piecesNew,Φ,fC,hgraphNew,hC,hR,hZ,hImage,hYavoid,hstart,hfinish,hSpokes,hsourceTail,hCover,hDirected,hHost,hPacked,hFirst,hTracked,hLocal,hOuter,hBalance,hKcover,hJavoid,hPackAvoid,hEunion,hLoss,hReserve⟩
end Oberwolfach
