module

public import Oberwolfach.LongMatchedSelectedInnerTotalLoss
public import Oberwolfach.LongMatchedDualCorrectionSelectedInnerSum
public import Oberwolfach.LongDualResidualCoverage
public import Oberwolfach.LongSelectedTypeMargins
public import Oberwolfach.LongEligibleAsymptoticMargins
public import Oberwolfach.LongEmbeddedPackingStateCover

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance matchedDualUsedTotalLossFin (n:ℕ):DecidableEq (Fin n):=selectedMarkedSampleBalanceFin n
local instance matchedDualUsedTotalLossArc (n:ℕ) (P:(Fin n)×(Fin n)→Prop):DecidableEq {e:(Fin n)×(Fin n) // P e}:=reservedCandidateArcDecEq P

theorem long_matched_dual_used_eventual_correction_total_loss
    (d e m:ℕ) (ρ₀ rho ζ δLoss εInner eta:ℝ)
    (hρ₀:0<ρ₀) (hm:0<m) (hrho:0<rho) (heta:0<eta) (hetaR:eta≤rho)
    (hbudget:ζ+δLoss<eta) (hsupply:rho+ζ+δLoss+εInner<ρ₀/(400*(m:ℝ))):
    ∃N:ℕ,∀n:ℕ,N≤n→∀ [Nonempty (Fin n)] (U:Type) [Fintype U] [DecidableEq U]
    (r K D:ℕ) (G:SimpleGraph (Fin n)) (hreg:G.IsRegularOfDegree D) (hD:0<D) (hd:0<d)
    (hρlo:ρ₀ ≤ initialIndexDensity U D) (hDlo:(n:ℝ)/2≤D)
    (π:Equiv.Perm (Fin n)) (z:MarkedExpandedActualOutcome (U:=U) π d) (T:Finset (Fin n))
    (θ Dmatch alpha γ eps βList:ℝ) (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (weight:(Fin (r+4+1)→Fin n)→ℝ)
    (w:∀i:Fin K,OrdinaryCycle G (longPaddedSeedExponent i+2)→ℝ)
    (D₀:MarkedReferenceDeletion G π d (fun x=>rawExpandedMarkedCollapse x (z.1 x)))
    (C:Finset (Finset (Fin n)⊕(Fin n×U))) (S Del Small Loss:SimpleGraph (Fin n)) (Mhost:Fin n→Fin n→ℕ)
    (hw:LongClassMatchingDeletionWitness ζ G π d r z T K θ Dmatch alpha γ eps βList F hF weight w D₀ C S Mhost Del)
    (Pack:Finset (Sym2 (Fin n))) (hPack:Pack⊆(longApproximatePhysicalGraph G π d z.1).edgeFinset)
    (hSmall:Small≤SimpleGraph.fromEdgeSet (↑Pack:Set (Sym2 (Fin n)))⊔Loss)
    (Used:SimpleGraph (Fin n)) (hUsed:∀x y,Mhost x y=1→Used.Adj x y→
      longOrdinaryArcEligible π d (x,y) ∨ longMarkedArcEligible π d (x,y))
    (hRequired:longCloseRequiredGraph S π d
      (fun x y=>Mhost x y=1 ∧ markedPhysicalRim G π (3*d)
        (fun e=>markedExpandedPhysicalCollapse (z.1 (Sum.inl e))) true x (π.symm y)≠1)
      (fun x y=>Used.Adj x y)≤Small)
    (hLoss:∀v,(Loss.degree v:ℝ)≤δLoss*n)
    (lossLocal loc lossInside inside:ℝ) (hloc:0≤loc) (hinside:0≤ inside)
    (hLossLocal:∀v,v∉T→(Loss.degree v:ℝ)≤lossLocal) (hLocal:0≤lossLocal)
    (Req:Fin n→Fin n→Prop) (E:U→Finset (Sym2 (Fin n))) (hPackFull:Pack=Used.edgeFinset)
    (hLossEq:Loss=prescribedPhysicalUnion E) (hEHost:prescribedPhysicalUnion E≤S)
    (hAvoid:∀w,Disjoint (E w) ((spanningRestriction (S\Used) T)\
      (longClassInnerRequiredRepair S Used (longRequiredPhysicalGraph S (S\Used)
        (longSelectedPhysicalGraph G π d z.1) π d T Req (fun x y=>Used.Adj x y)) T Pack)).edgeFinset)
    (hInsideBound:(T.card:ℝ)*(ζ*n+2*((6*d+2:ℕ):ℝ))+(n:ℝ)*lossLocal≤lossInside)
    (hlocGlobal:loc≤eta*n) (hinsideGlobal:inside≤(T.card:ℝ)*eta*n)
    (hinsideBudget:(T.card:ℝ)*((n:ℝ)^(3/5:ℝ)+(d:ℝ)*(n:ℝ)^(3/5:ℝ))+lossInside≤ inside)
    (hlocalBudget:(n:ℝ)^(3/5:ℝ)+(d:ℝ)*(n:ℝ)^(3/5:ℝ)+(ζ*n+lossLocal+(6*d+2:ℕ))≤loc)
    (hT:(T.card:ℝ)≤εInner*n) (hC:C.card≤e)
    (p₂ k₂ u:ℝ)
    (hstarts:∀v,|((rawStartHubSet π d (fun x=>z.1 (Sum.inr x)) false v).card:ℝ)-
      (∑w,longAssignedIntervalProbability F hF K m θ w false/(d:ℝ))|<(n:ℝ)^(3/5:ℝ))
    (hdegrees:∀j v,|((∑x,sampledColourOrientation G (fun x=>z.1 (Sum.inl x)) j x v:ℕ):ℝ)-
      markedExpandedPhysicalProbability (initialIndexDensity U D*(1/100:ℝ)/2) (initialIndexDensity U D*((1/100:ℝ)/(m:ℝ))/2) p₂ k₂ u j/2*G.degree v|<(n:ℝ)^(3/5:ℝ)),
    let P:=longEligibleResidualArc Mhost Small ⊥
    let T₁:=longDualInitialMarked G (fun x=>z.1 (Sum.inl x)) Mhost Small (longOrdinaryArcEligible π d) (longMarkedArcEligible π d)
    ∃M:Finset {x:(Fin n)×(Fin n) // P x},
      (∀v,directedInCount P M v=d*startRetentionMinimum (rawStartHubSet π d (fun x=>z.1 (Sum.inr x)) false)) ∧
      (∀x∈M,longMarkedArcEligible π d x.val) ∧ (∀x,x∉M→longOrdinaryArcEligible π d x.val) ∧
      (∀x,x.val.1∈T→(x∈M↔x∈T₁)) ∧
      (∀x,Sum.inl ({x.val.1,x.val.2}:Finset (Fin n))∈C→(x∈M↔x∈T₁)) ∧
      (∀v,((physicalEdgeGraph (changedDirectedPhysicalEdges P M T₁)).degree v:ℝ)≤
        (1+2/rho)*eta*n+1) ∧
      (∀v,v∉T→((physicalEdgeGraph (changedDirectedPhysicalEdges P M T₁)).degree v:ℝ)≤
        loc+(inside/n+loc)/rho+1) :=by
  obtain ⟨N,hN⟩:=long_eligible_type_eventual_margins d e rho ζ δLoss εInner eta (ρ₀/(400*(m:ℝ))) hbudget hsupply
  refine ⟨N,?_⟩
  intro n hn _ U _ _ r K D G hreg hD hd hρlo hDlo π z T θ Dmatch alpha γ eps βList F hF weight w D₀ C S Del Small Loss Mhost hw Pack hPack hSmall Used hUsed hRequired hLoss lossLocal loc lossInside inside hloc hinside hLossLocal hLocal Req E hPackFull hLossEq hEHost hAvoid hInsideBound hlocGlobal hinsideGlobal hinsideBudget hlocalBudget hT hC p₂ k₂ u hstarts hdegrees P T₁
  have hcover:=long_embedded_physical_packing_state_cover G Loss Small π d z.1 Pack hPack hSmall
  have hbound:=hN n hn T.card C.card hT hC
  have herr:(0:ℝ)≤(n:ℝ)^(3/5:ℝ):=by positivity
  let L:ℝ:=(ζ+δLoss)*n+(6*d+2:ℕ)
  have hcost:rho*n+(n:ℝ)^(3/5:ℝ)+(L+(6*d+2:ℕ))+T.card+C.card≤ρ₀/(400*(m:ℝ))*n:=by
    dsimp [L] at *
    push_cast at *
    linarith only [hbound.2]
  have hmargins:=long_selected_type_supply_margins ρ₀ (initialIndexDensity U D) n D rho ((n:ℝ)^(3/5:ℝ)) (L+(6*d+2:ℕ)) T.card C.card m
    hρ₀ hρlo hm (by positivity) hDlo hcost p₂ k₂ u
  have hSP:S≤G:=by
    intro x y hxy
    have hh:=hw.2.2.2.2.2.2.2.2.1 S (le_refl S) x y hxy
    rcases hh with hh|hh
    · exact hw.2.2.2.2.2.2.2.2.2.1 x y hh
    · exact (hw.2.2.2.2.2.2.2.2.2.1 y x hh).symm
  have hdel:=long_matching_witness_correction_bound ζ G π z T θ Dmatch alpha γ eps βList F hF weight w D₀ C S Del Mhost hw
  have hsum:=long_matched_selected_inner_total_loss G S Used Del π d T z.1 Req Pack E hSP hPackFull hPack hEHost (ζ*n) lossLocal hLocal
    (by intro v hv; exact hdel.2 v) (by
      intro v hv
      have hh:=hLossLocal v hv
      rw [hLossEq] at hh
      convert hh using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _) hAvoid
  have hLossInside:(∑v∈T,((Del⊔(Loss⊓longPhysicalStateGraph G z.1 {1})⊔longPreparationIneligibleGraph G π d).degree v:ℝ))≤lossInside:=by
    have hh:=hsum.trans (by simpa only [Fintype.card_fin] using hInsideBound)
    rw [←hLossEq] at hh
    convert hh using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _
  have hFull:=long_dual_residual_eligibility_from_used_or_required G S Small Used π d (fun e=>z.1 (Sum.inl e)) Mhost hw.1 hUsed hRequired
  apply long_matched_dual_sample_correction_selected_inner_sum G hreg hD hd hm π z T ζ θ Dmatch alpha γ eps βList F hF weight w D₀ C S Del Small Loss Mhost hw
  · intro x y h
    have hh:=hcover h
    simpa only [longPhysicalStateGraph,Finset.mem_insert,Finset.mem_singleton] using hh
  · exact hFull
  · exact hLoss
  · exact hloc
  · exact hinside
  · exact hLossInside
  · exact hLossLocal
  · exact herr
  · intro v;exact (hstarts v).le
  · intro j v;exact (hdegrees j v).le
  · exact hrho
  · exact heta
  · exact hetaR
  · exact hbound.1
  · exact hlocGlobal
  · exact hinsideGlobal
  · exact hinsideBudget
  · exact hlocalBudget
  · intro v;have hh:=hmargins.1;rw [hreg v];dsimp [L] at *;push_cast at *;linarith only [hh]
  · intro v;have hh:=hmargins.2;rw [hreg v];dsimp [L] at *;push_cast at *;linarith only [hh]
end Oberwolfach
