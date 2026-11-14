module

public import Oberwolfach.LongDualSampleCorrectionSelectedInnerSum
public import Oberwolfach.LongDualResidualEligibility
public import Oberwolfach.LongResidualEligibility
public import Oberwolfach.LongMatchingWitnessCorrection
public import Oberwolfach.LongIneligibleUnionDegree
public import Oberwolfach.LongSelectedMarkedSampleBalance
public import Oberwolfach.LongAssignedReferenceLawAlignment
public import Oberwolfach.MarkedExpandedPhysicalLaw

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance matchedDualInnerSumFin (n:ℕ):DecidableEq (Fin n):=selectedMarkedSampleBalanceFin n
local instance matchedDualInnerSumArc (n:ℕ) (P:(Fin n)×(Fin n)→Prop):DecidableEq {e:(Fin n)×(Fin n) // P e}:=reservedCandidateArcDecEq P

theorem long_matched_dual_sample_correction_selected_inner_sum
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
    (hFull:∀x y,Mhost x y=1→¬Small.Adj x y→longOrdinaryArcEligible π d (x,y)∨longMarkedArcEligible π d (x,y))
    (δLoss:ℝ) (hLoss:∀v,(Loss.degree v:ℝ)≤δLoss*n)
    (lossLocal loc lossInside inside:ℝ) (hloc:0≤loc) (hinside:0≤ inside)
    (hLossInside:(∑v∈T,((Del⊔(Loss⊓longPhysicalStateGraph G z.1 {1})⊔longPreparationIneligibleGraph G π d).degree v:ℝ))≤lossInside)
    (hLossLocal:∀v,v∉T→(Loss.degree v:ℝ)≤lossLocal)
    (p p₂ k₂ u err:ℝ) (herr:0≤err)
    (hstarts:∀v,|((rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false v).card:ℝ)-
      (∑w,longAssignedIntervalProbability F hF K m θ w false/(d:ℝ))|≤err)
    (hdegrees:∀j v,|((∑x,sampledColourOrientation G (fun e=>z.1 (Sum.inl e)) j x v:ℕ):ℝ)-
      markedExpandedPhysicalProbability p (initialIndexDensity U D*((1/100:ℝ)/(m:ℝ))/2) p₂ k₂ u j/2*G.degree v|≤err)
    (rho eta:ℝ) (hrho:0<rho) (heta:0<eta) (hetaR:eta≤rho):
    let L:ℝ:=(ζ+δLoss)*n+(6*d+2:ℕ)
    (err+(d:ℝ)*err+L≤eta*n)→
    loc≤eta*n→inside≤(T.card:ℝ)*eta*n→(T.card:ℝ)*(err+(d:ℝ)*err)+lossInside≤ inside→
    err+(d:ℝ)*err+(ζ*n+lossLocal+(6*d+2:ℕ))≤loc→
    (∀v,rho*n≤markedExpandedPhysicalProbability p (initialIndexDensity U D*((1/100:ℝ)/(m:ℝ))/2) p₂ k₂ u 0/2*G.degree v-err-L-T.card-C.card-(6*d+2:ℕ))→
    (∀v,rho*n≤markedExpandedPhysicalProbability p (initialIndexDensity U D*((1/100:ℝ)/(m:ℝ))/2) p₂ k₂ u 1/2*G.degree v-err-L-T.card-C.card-(6*d+2:ℕ))→
    let P:=longEligibleResidualArc Mhost Small ⊥
    let T₁:=longDualInitialMarked G (fun e=>z.1 (Sum.inl e)) Mhost Small (longOrdinaryArcEligible π d) (longMarkedArcEligible π d)
    ∃M:Finset {e:(Fin n)×(Fin n) // P e},
      (∀v,directedInCount P M v=d*startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false)) ∧
      (∀e∈M,longMarkedArcEligible π d e.val) ∧ (∀e,e∉M→longOrdinaryArcEligible π d e.val) ∧
      (∀e,e.val.1∈T→(e∈M↔e∈T₁)) ∧
      (∀e,Sum.inl ({e.val.1,e.val.2}:Finset (Fin n))∈C→(e∈M↔e∈T₁)) ∧
      (∀v,((physicalEdgeGraph (changedDirectedPhysicalEdges P M T₁)).degree v:ℝ)≤
        (1+2/rho)*eta*n+1) ∧
      (∀v,v∉T→((physicalEdgeGraph (changedDirectedPhysicalEdges P M T₁)).degree v:ℝ)≤
        loc+(inside/n+loc)/rho+1) :=by
  intro L hbudget hlocGlobal hinsideGlobal hinsideBudget hlocalBudget hm₀ hm₁ P T₁
  have hc:=long_matching_witness_correction_bound ζ G π z T θ Dmatch alpha γ eps βList F hF weight w D₀ C S Del Mhost hw
  have hgraph:=long_ineligible_union_degree_budget (d:=d) G Del Loss π ζ δLoss hc.2 hLoss
  have hraw:=long_sample_marked_retained_indegree_balance G hreg hD hd hm π (fun e=>z.1 (Sum.inr e))
    (fun e=>z.1 (Sum.inl e)) (longAssignedIntervalProbability F hF K m θ) (1/100:ℝ) p p₂ k₂ u err herr
    (long_assigned_reference_colour_marginals F hF K m θ).1 hstarts (hdegrees 1)
  have hraw':∀v,|((∑x,sampledColourOrientation G (fun e=>z.1 (Sum.inl e)) 1 x v:ℕ):ℝ)-
    (d*startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false):ℕ)|≤err+(d:ℝ)*err:=by
    simpa only [Nat.cast_mul] using hraw
  let k:=initialIndexDensity U D*((1/100:ℝ)/(m:ℝ))/2
  let b₀:=fun v=>markedExpandedPhysicalProbability p k p₂ k₂ u 0/2*G.degree v-err
  let b₁:=fun v=>markedExpandedPhysicalProbability p k p₂ k₂ u 1/2*G.degree v-err
  have h₀:∀v,b₀ v≤((∑x,sampledColourOrientation G (fun e=>z.1 (Sum.inl e)) 0 x v:ℕ):ℝ):=by
    intro v;have h:=(abs_le.mp (hdegrees 0 v)).1;dsimp [b₀,k];linarith only [h]
  have h₁:∀v,b₁ v≤((∑x,sampledColourOrientation G (fun e=>z.1 (Sum.inl e)) 1 x v:ℕ):ℝ):=by
    intro v;have h:=(abs_le.mp (hdegrees 1 v)).1;dsimp [b₁,k];linarith only [h]
  have hbad:∀v,((longPreparationIneligibleGraph G π d).degree v:ℝ)≤(6*d+2:ℕ):=by
    intro v;exact_mod_cast long_preparation_ineligible_degree G π d v
  have hhost:∀x y,Mhost x y=1→G.Adj x y:=hw.2.2.2.2.2.2.2.2.2.1
  let Eligible:((Fin n)×(Fin n))→Prop:=fun e=>longOrdinaryArcEligible π d e ∧ longMarkedArcEligible π d e
  have hgraphLocal:∀v,v∉T→((Del⊔Loss⊔longPreparationIneligibleGraph G π d).degree v:ℝ)≤ζ*n+lossLocal+(6*d+2:ℕ):=by
    intro v hv
    have hd:=long_three_graph_degree_bound Del Loss (longPreparationIneligibleGraph G π d) v
    have hi:=long_preparation_ineligible_degree G π d v
    have hDel:=hc.2 v
    have hLv:=hLossLocal v hv
    simp only [← SimpleGraph.ncard_neighborSet] at hd hi hDel hLv ⊢
    have hdr:(((Del⊔Loss⊔longPreparationIneligibleGraph G π d).neighborSet v).ncard:ℝ)≤
      (Del.neighborSet v).ncard+(Loss.neighborSet v).ncard+((longPreparationIneligibleGraph G π d).neighborSet v).ncard:=by exact_mod_cast hd
    have hir:(((longPreparationIneligibleGraph G π d).neighborSet v).ncard:ℝ)≤(6*d+2:ℕ):=by exact_mod_cast hi
    linarith only [hdr,hir,hDel,hLv]
  have hh:=long_dual_sample_types_correction_selected_inner_sum G Del Small (longPreparationIneligibleGraph G π d) Loss z.1 Mhost
    (longOrdinaryArcEligible π d) (longMarkedArcEligible π d) Eligible (by intro e;rfl) hc.1
    (by intro x y h;have hh:=hcover h;simpa only [longPhysicalStateGraph,Finset.mem_insert,Finset.mem_singleton] using hh)
    (long_dual_ineligible_incident G π d) hhost hFull L (6*d+2:ℕ) hgraph hbad b₀ b₁ h₀ h₁ T C
    (d*startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false)) rho eta (err+(d:ℝ)*err) hrho heta hetaR hraw'
    (by simpa only [Fintype.card_fin] using hbudget)
    (ζ*n+lossLocal+(6*d+2:ℕ)) loc lossInside inside hloc hinside
    (by simpa only [Fintype.card_fin] using hlocGlobal) (by simpa only [Fintype.card_fin] using hinsideGlobal)
    hinsideBudget (by convert hLossInside using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _) hlocalBudget hgraphLocal (by simpa only [Fintype.card_fin,b₀,k] using hm₀)
    (by simpa only [Fintype.card_fin,b₁,k] using hm₁)

  simpa only [Fintype.card_fin] using hh
end Oberwolfach
