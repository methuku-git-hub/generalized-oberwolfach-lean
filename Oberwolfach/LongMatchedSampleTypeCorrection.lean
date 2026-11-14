module

public import Oberwolfach.LongResidualSampleTypeCorrection
public import Oberwolfach.LongMatchingWitnessCorrection
public import Oberwolfach.LongIneligibleUnionDegree
public import Oberwolfach.LongSelectedMarkedSampleBalance
public import Oberwolfach.LongAssignedReferenceLawAlignment

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance matchedSampleTypeFin (n:ℕ):DecidableEq (Fin n):=selectedMarkedSampleBalanceFin n
local instance matchedSampleTypeArc (n:ℕ) (P:(Fin n)×(Fin n)→Prop):DecidableEq {e:(Fin n)×(Fin n) // P e}:=reservedCandidateArcDecEq P

theorem long_matched_sample_types_protected_correction
    {n d r K D m:ℕ} {U:Type} [Fintype U] [DecidableEq U] [Nonempty (Fin n)]
    (G:SimpleGraph (Fin n)) (hreg:G.IsRegularOfDegree D) (hD:0<D) (hd:0<d) (hm:0<m)
    (π:Equiv.Perm (Fin n)) (z:MarkedExpandedActualOutcome (U:=U) π d) (T:Finset (Fin n))
    (ζ θ Dmatch alpha γ eps βList:ℝ) (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (weight:(Fin (r+4+1)→Fin n)→ℝ)
    (w:∀i:Fin K,OrdinaryCycle G (longPaddedSeedExponent i+2)→ℝ)
    (D₀:MarkedReferenceDeletion G π d (fun e=>rawExpandedMarkedCollapse e (z.1 e)))
    (C:Finset (Finset (Fin n)⊕(Fin n×U))) (S Del Small Loss:SimpleGraph (Fin n)) (Mhost:Fin n→Fin n→ℕ)
    (hw:LongClassMatchingDeletionWitness ζ G π d r z T K θ Dmatch alpha γ eps βList F hF weight w D₀ C S Mhost Del)
    (hcover:Small≤longPhysicalStateGraph G z.1 {2,3}⊔Loss)
    (δLoss:ℝ) (hLoss:∀v,(Loss.degree v:ℝ)≤δLoss*n)
    (p p₂ k₂ u err:ℝ) (herr:0≤err)
    (hstarts:∀v,|((rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false v).card:ℝ)-
      (∑w,longAssignedIntervalProbability F hF K m θ w false/(d:ℝ))|≤err)
    (hdegrees:∀j v,|((∑x,sampledColourOrientation G (fun e=>z.1 (Sum.inl e)) j x v:ℕ):ℝ)-
      markedExpandedPhysicalProbability p (initialIndexDensity U D*((1/100:ℝ)/(m:ℝ))/2) p₂ k₂ u j/2*G.degree v|≤err)
    (rho eta:ℝ) (hrho:0<rho) (heta:0<eta) (hetaR:eta≤rho):
    let L:ℝ:=(ζ+δLoss)*n+(6*d+2:ℕ)
    (err+(d:ℝ)*err+L≤eta*n)→
    (∀v,rho*n≤markedExpandedPhysicalProbability p (initialIndexDensity U D*((1/100:ℝ)/(m:ℝ))/2) p₂ k₂ u 0/2*G.degree v-err-L-T.card-C.card)→
    (∀v,rho*n≤markedExpandedPhysicalProbability p (initialIndexDensity U D*((1/100:ℝ)/(m:ℝ))/2) p₂ k₂ u 1/2*G.degree v-err-L-T.card-C.card)→
    let Bad:=longPreparationIneligibleGraph G π d
    let P:=longResidualHostArc Mhost Small Bad
    let T₁:=longResidualInitialMarked G (fun e=>z.1 (Sum.inl e)) Mhost Small Bad
    ∃M:Finset {e:(Fin n)×(Fin n) // P e},
      (∀v,directedInCount P M v=d*startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false)) ∧
      (∀e,e.val.1∈T→(e∈M↔e∈T₁)) ∧
      (∀e,Sum.inl ({e.val.1,e.val.2}:Finset (Fin n))∈C→(e∈M↔e∈T₁)) ∧
      (∀v,((physicalEdgeGraph (changedDirectedPhysicalEdges P M T₁)).degree v:ℝ)≤
        (1+2/rho)*eta*n+(n:ℝ)^(3/5:ℝ)) :=by
  intro L hbudget hm₀ hm₁ Bad P T₁
  have hc:=long_matching_witness_correction_bound ζ G π z T θ Dmatch alpha γ eps βList F hF weight w D₀ C S Del Mhost hw
  have hgraph:=long_ineligible_union_degree_budget (d:=d) G Del Loss π ζ δLoss hc.2 hLoss
  have hraw:=long_sample_marked_retained_indegree_balance G hreg hD hd hm π (fun e=>z.1 (Sum.inr e))
    (fun e=>z.1 (Sum.inl e)) (longAssignedIntervalProbability F hF K m θ) (1/100:ℝ) p p₂ k₂ u err herr
    (long_assigned_reference_colour_marginals F hF K m θ).1 hstarts (hdegrees 1)
  have hraw':∀v,|((∑x,sampledColourOrientation G (fun e=>z.1 (Sum.inl e)) 1 x v:ℕ):ℝ)-
    (d*startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false):ℕ)|≤err+(d:ℝ)*err:=by
    simpa only [Nat.cast_mul] using hraw
  have hh:=long_residual_sample_types_protected_correction G Del Small Bad Loss z.1 Mhost hc.1 (by
      intro x y h
      have hh:=hcover h
      simpa only [longPhysicalStateGraph,Finset.mem_insert,Finset.mem_singleton] using hh) L hgraph
    p (initialIndexDensity U D*((1/100:ℝ)/(m:ℝ))/2) p₂ k₂ u err hdegrees T C
    (d*startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false)) rho eta (err+(d:ℝ)*err)
    hrho heta hetaR hraw' (by simpa only [Fintype.card_fin] using hbudget)
    (by simpa only [Fintype.card_fin] using hm₀) (by simpa only [Fintype.card_fin] using hm₁)
  simpa only [Fintype.card_fin] using hh
end Oberwolfach
