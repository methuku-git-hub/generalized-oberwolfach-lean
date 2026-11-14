module

public import Oberwolfach.LongSelectedOrientedSourceComplement
public import Oberwolfach.LongSelectedOrientedSourceResidualCompletion
public import Oberwolfach.LongSelectedProtectedSourceComplement
public import Oberwolfach.RetainedMarkedRootUniformity
public import Oberwolfach.LongSelectedAlignedSourceComplement
public import Oberwolfach.LongActualPhysicalGraphsInHost
public import Oberwolfach.FactorCycleOrientationEdges

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance longSelectedOrientedSourceComplementFin (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n

theorem long_selected_oriented_source_complement
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (hU:0<Fintype.card U) (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (t:ℕ)
    (Jret:StartRetentionOutcome (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false) t)
    (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (H:Finset U) (A:Finset (Fin n)) (Kbad Used DelG:SimpleGraph (Fin n)) (absorber:U→Finset (Fin n))
    (δ:ℝ) (Extra:(U→Finset (Fin n))→Finset (Sym2 (Fin n))→Prop) (ρ₀ θ δglobal:ℝ)
    (hKbad:Kbad≤P) (hd:2≤d):
    let T:=bernoulliVertexSet (longRawHubState P π d raw true true)
    let e:{z // z∈T}↪_:=Function.Embedding.subtype _
    ∀M:Finset (RestrictedResource (mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)) e),
    LongSelectedOrientedSourceWithResidualCompletion hU F P π d m ℓ raw t Jret σ H A Kbad Used DelG absorber δ Extra ρ₀ θ δglobal M →
    LongSelectedOrientedSourceWithComplement hU F P π d m ℓ raw t Jret σ H A Kbad Used DelG absorber δ Extra ρ₀ θ δglobal M :=by
  intro T e M hsource
  letI:Nonempty U:=Fintype.card_pos_iff.mp hU
  have hdec0 : selectedOrientedResidualCompletionFin n = longSelectedOrientedSourceComplementFin n := Subsingleton.elim _ _
  have hdec0K : selectedOrientedResidualCompletionFin K = longSelectedOrientedSourceComplementFin K := Subsingleton.elim _ _
  have hdec1 : selectedOrientedSourceComplementFin n = longSelectedOrientedSourceComplementFin n := Subsingleton.elim _ _
  have hdec1K : selectedOrientedSourceComplementFin K = longSelectedOrientedSourceComplementFin K := Subsingleton.elim _ _
  try rw [hdec0] at hsource
  try rw [hdec0K] at hsource
  try rw [hdec1]
  try rw [hdec1K]
  rcases hsource with ⟨Dsrc,orig,hPair,hValid,hUnion,hArcs,E,hAlign,hLate,ext,inner,ψ,assign,data,hprops,hload,pieces,hpieceEdge,hpieceArc,Pack,hOldDisj,hOldPack,hApprox,hSelected,hassign,hsize,hUsed,hExtra,hcapacity,hupper,hglobal,hcompletion⟩
  let Interiors:=fun w=>bufferedPathStrictInterior (fun _=>(m+1)*d) (inner w)
  let occupied:=fun w=>((data w).oldDomain\Interiors w).image (ψ w)
  let Z:=innerRequiredTargets H A (rawReservedSpokeList π d (fun e=>raw (Sum.inr e)))
    (retainedFinalMarkedAt π d (fun e=>raw (Sum.inr e)) t Jret) absorber occupied
  let Jbad:=spanningRestriction (P\Used) A\Kbad
  let Lbad:=protectedPairEdgeHubs (rawReservedSpokeList π d (fun e=>raw (Sum.inr e))) H
  let Bad:=fun v:Fin n=>Finset.univ.filter (fun w=>v∈retainedFinalMarkedAt π d (fun e=>raw (Sum.inr e)) t Jret w)
  let Dfree:=fun x y=>rawSelectedPhysicalRelation P π d (fun e=>σ (Sum.inl e)) x y ∧ ¬DelG.Adj x y
  let Dstar:=fun x y=>Dfree x y ∨ Kbad.Adj x y
  let Lists:=fun w=>rawReservedSpokeList π d (fun e=>raw (Sum.inr e)) w\
    (A∪retainedFinalMarkedAt π d (fun e=>raw (Sum.inr e)) t Jret w)
  have hPackP:Pack⊆P.edgeFinset:=by
    intro edge he
    have hh:=hApprox he
    exact SimpleGraph.edgeFinset_mono (long_approximate_physical_graph_le_host P π d σ) hh
  have hDstar:∀x y,Dstar x y→P.Adj x y:=by
    intro x y h
    rcases h with h|h
    · exact raw_selected_physical_relation_in_host P π d (fun e=>σ (Sum.inl e)) x y h.1
    · exact hKbad h
  have hOrient:∀w x y,(F w).Adj x y→Dsrc w x y ∨ Dsrc w y x:=by
    intro w x y h
    rcases (factor_cycle_orientation_edge_iff (F w) (hF w) (E w) x y).mp h with hh|hh
    · left; simpa [hh] using hAlign w x
    · right; simpa [hh] using hAlign w y
  have hCycle:∀w,(data w).t.biUnion (fun j=>((data w).C j).support.toFinset)⊆(data w).Cembed:=by
    intro w;rw [(hprops w).2.2.2.1]
  let Y:=fun w=>markedIntervalRootSet π (fun _:retainedMarkedIndex π d (fun e=>raw (Sum.inr e)) false t Jret w=>d) Subtype.val
  have hY:∀w,Y w=retainedFinalMarkedAt π d (fun e=>raw (Sum.inr e)) t Jret w:=by
    intro w
    ext v
    simpa only [Y,retainedFinalMarkedAt,Finset.mem_filter,Finset.mem_univ,true_and] using
      retained_marked_root_membership π d (by omega) (fun e=>raw (Sum.inr e)) false t Jret w v
  have hYBad:∀w v,v∈Y w→w∈Bad v:=by
    intro w v hv
    simp only [Bad,Finset.mem_filter,Finset.mem_univ,true_and]
    rw [←hY w]
    exact hv
  have hZY:∀w,Disjoint (Z w) (Y w):=by
    intro w
    apply Finset.disjoint_left.mpr
    intro v hv hy
    by_cases hw:w∈H
    · have hv':=hv
      simp only [Z,innerRequiredTargets,hw,if_true,Finset.mem_sdiff,Finset.mem_union] at hv'
      exact hv'.2 (Or.inl (Or.inl (Or.inr ((hY w) ▸ hy))))
    · simp [Z,innerRequiredTargets,hw] at hv
  have hLY:∀w,Disjoint (Lists w) (Y w):=by
    intro w
    apply Finset.disjoint_left.mpr
    intro v hv hy
    exact (Finset.mem_sdiff.mp hv).2 (Finset.mem_union_right A ((hY w) ▸ hy))
  have hOldAvoid:∀w x,x∈(data w).oldDomain→x∉bufferedPathFullDomain (fun _=>(m+1)*d) (inner w)→ψ w x∉Y w:=by
    intro w
    rcases hprops w with ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,havoid,_,_⟩
    exact havoid
  have hComplement:=actual_residual_completion_complement_avoids_roots
    (fun w=>retainedMarkedIndex π d (fun e=>raw (Sum.inr e)) false t Jret w)
    (fun w=>{a:Fin n // rawIntervalColouredStart π d (fun e=>raw (Sum.inr (w,e))) a true})
    (fun w=>{a:LongRawSelectedOrdinary π d m ℓ e M // (assign a).1=w})
    F hF P Dsrc data (m+1) d (fun w=>(hprops w).1) (fun w=>(hprops w).2.1)
    (fun w=>(hprops w).2.2.1) ext inner (fun w=>(hprops w).2.2.2.2.1)
    (fun w=>(hprops w).2.2.2.2.2.1) hCycle ψ Kbad Jbad Lbad Bad Z Dfree Dstar Pack Lists δglobal hOldPack hPackP hOrient hDstar Y hYBad hZY hLY hOldAvoid hcompletion
  have hdec2 : actualResidualCompletionRootAvoidanceFin n = longSelectedOrientedSourceComplementFin n := Subsingleton.elim _ _
  try rw [hdec2] at hComplement
  exact ⟨Dsrc,orig,hPair,hValid,hUnion,hArcs,E,hAlign,hLate,ext,inner,ψ,assign,data,hprops,hload,pieces,hpieceEdge,hpieceArc,Pack,hOldDisj,hOldPack,hApprox,hSelected,hassign,hsize,hUsed,hExtra,hcapacity,hupper,hglobal,hcompletion,hComplement⟩
end Oberwolfach
