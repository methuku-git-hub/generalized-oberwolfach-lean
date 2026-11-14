module

public import Oberwolfach.LongMatchedSampleCappedMargin
public import Oberwolfach.LongSelectedTypeAsymptoticMargins
public import Oberwolfach.LongEmbeddedPackingStateCover

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance matchedEventualFin (n:ℕ):DecidableEq (Fin n):=selectedMarkedSampleBalanceFin n
local instance matchedEventualArc (n:ℕ) (P:(Fin n)×(Fin n)→Prop):DecidableEq {e:(Fin n)×(Fin n) // P e}:=reservedCandidateArcDecEq P

theorem long_matched_sample_eventual_type_correction
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
    (hLoss:∀v,(Loss.degree v:ℝ)≤δLoss*n) (hT:(T.card:ℝ)≤εInner*n) (hC:C.card≤e)
    (p₂ k₂ u:ℝ)
    (hstarts:∀v,|((rawStartHubSet π d (fun x=>z.1 (Sum.inr x)) false v).card:ℝ)-
      (∑w,longAssignedIntervalProbability F hF K m θ w false/(d:ℝ))|<(n:ℝ)^(3/5:ℝ))
    (hdegrees:∀j v,|((∑x,sampledColourOrientation G (fun x=>z.1 (Sum.inl x)) j x v:ℕ):ℝ)-
      markedExpandedPhysicalProbability (initialIndexDensity U D*(1/100:ℝ)/2) (initialIndexDensity U D*((1/100:ℝ)/(m:ℝ))/2) p₂ k₂ u j/2*G.degree v|<(n:ℝ)^(3/5:ℝ)),
    let Bad:=longPreparationIneligibleGraph G π d
    let P:=longResidualHostArc Mhost Small Bad
    let T₁:=longResidualInitialMarked G (fun x=>z.1 (Sum.inl x)) Mhost Small Bad
    ∃M:Finset {x:(Fin n)×(Fin n) // P x},
      (∀v,directedInCount P M v=d*startRetentionMinimum (rawStartHubSet π d (fun x=>z.1 (Sum.inr x)) false)) ∧
      (∀x,x.val.1∈T→(x∈M↔x∈T₁)) ∧
      (∀x,Sum.inl ({x.val.1,x.val.2}:Finset (Fin n))∈C→(x∈M↔x∈T₁)) ∧
      (∀v,((physicalEdgeGraph (changedDirectedPhysicalEdges P M T₁)).degree v:ℝ)≤
        (1+2/rho)*eta*n+(n:ℝ)^(3/5:ℝ)) :=by
  obtain ⟨N,hN⟩:=long_selected_type_eventual_margins d e rho ζ δLoss εInner eta (ρ₀/(400*(m:ℝ))) hbudget hsupply
  refine ⟨N,?_⟩
  intro n hn _ U _ _ r K D G hreg hD hd hρlo hDlo π z T θ Dmatch alpha γ eps βList F hF weight w D₀ C S Del Small Loss Mhost hw Pack hPack hSmall hLoss hT hC p₂ k₂ u hstarts hdegrees Bad P T₁
  have hcover:=long_embedded_physical_packing_state_cover G Loss Small π d z.1 Pack hPack hSmall
  have hbound:=hN n hn T.card C.card hT hC
  have herr:(0:ℝ)≤(n:ℝ)^(3/5:ℝ):=by positivity
  apply long_matched_sample_types_capped_margin_correction G hreg hD hd hm π z T ζ θ Dmatch alpha γ eps βList F hF weight w D₀ C S Del Small Loss Mhost hw
  · intro x y h
    have hh:=hcover h
    simpa only [longPhysicalStateGraph,Finset.mem_insert,Finset.mem_singleton] using hh
  · exact hLoss
  · exact herr
  · exact hρ₀
  · exact hρlo
  · exact hDlo
  · intro v;exact (hstarts v).le
  · intro j v;exact (hdegrees j v).le
  · exact hrho
  · exact heta
  · exact hetaR
  · exact hbound.1
  · exact hbound.2
end Oberwolfach
