module

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
local instance longSelectedSourceComplementFin (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n

theorem long_selected_source_complement
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (hU:0<Fintype.card U) (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (t:ℕ)
    (Jret:StartRetentionOutcome (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false) t)
    (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (H:Finset U) (A:Finset (Fin n)) (Kbad Used DelG:SimpleGraph (Fin n)) (absorber:U→Finset (Fin n))
    (δ:ℝ) (Extra:(U→Finset (Fin n))→Finset (Sym2 (Fin n))→Prop) (ρ₀ θ δglobal:ℝ)
    (hKbad:Kbad≤P):
    let T:=bernoulliVertexSet (longRawHubState P π d raw true true)
    let e:{z // z∈T}↪_:=Function.Embedding.subtype _
    ∀M:Finset (RestrictedResource (mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)) e),
    LongSelectedAlignedSourceWithResidualCompletion hU F P π d m ℓ raw t Jret σ H A Kbad Used DelG absorber δ Extra ρ₀ θ δglobal M →
    LongSelectedAlignedSourceWithComplement hU F P π d m ℓ raw t Jret σ H A Kbad Used DelG absorber δ Extra ρ₀ θ δglobal M :=by
  intro T e M hsource
  letI:Nonempty U:=Fintype.card_pos_iff.mp hU
  have hdec0 : selectedAlignedSourceResidualCompletionFin n = longSelectedSourceComplementFin n := Subsingleton.elim _ _
  have hdec0K : selectedAlignedSourceResidualCompletionFin K = longSelectedSourceComplementFin K := Subsingleton.elim _ _
  have hdec1 : selectedAlignedSourceComplementFin n = longSelectedSourceComplementFin n := Subsingleton.elim _ _
  have hdec1K : selectedAlignedSourceComplementFin K = longSelectedSourceComplementFin K := Subsingleton.elim _ _
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
  have hComplement:=actual_residual_completion_complement
    (fun w=>retainedMarkedIndex π d (fun e=>raw (Sum.inr e)) false t Jret w)
    (fun w=>{a:Fin n // rawIntervalColouredStart π d (fun e=>raw (Sum.inr (w,e))) a true})
    (fun w=>{a:LongRawSelectedOrdinary π d m ℓ e M // (assign a).1=w})
    F hF P Dsrc data (m+1) d (fun w=>(hprops w).1) (fun w=>(hprops w).2.1)
    (fun w=>(hprops w).2.2.1) ext inner (fun w=>(hprops w).2.2.2.2.1)
    (fun w=>(hprops w).2.2.2.2.2.1) hCycle ψ Kbad Jbad Lbad Bad Z Dfree Dstar Pack Lists δglobal hOldPack hPackP hOrient hDstar hcompletion
  have hdec2 : actualResidualCompletionComplementFin n = longSelectedSourceComplementFin n := Subsingleton.elim _ _
  try rw [hdec2] at hComplement
  exact ⟨Dsrc,orig,hPair,hValid,hUnion,hArcs,E,hAlign,hLate,ext,inner,ψ,assign,data,hprops,hload,pieces,hpieceEdge,hpieceArc,Pack,hOldDisj,hOldPack,hApprox,hSelected,hassign,hsize,hUsed,hExtra,hcapacity,hupper,hglobal,hcompletion,hComplement⟩
end Oberwolfach
