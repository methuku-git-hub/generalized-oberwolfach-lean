module

public import Oberwolfach.LongMatchedSampleTypeCorrection
public import Oberwolfach.LongSelectedTypeMargins
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
local instance matchedCappedFin (n:ℕ):DecidableEq (Fin n):=selectedMarkedSampleBalanceFin n
local instance matchedCappedArc (n:ℕ) (P:(Fin n)×(Fin n)→Prop):DecidableEq {e:(Fin n)×(Fin n) // P e}:=reservedCandidateArcDecEq P

theorem long_matched_sample_types_capped_margin_correction
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
    (ρ₀ p₂ k₂ u err:ℝ) (herr:0≤err) (hρ₀:0<ρ₀) (hρlo:ρ₀ ≤ initialIndexDensity U D) (hDlo:(n:ℝ)/2≤D)
    (hstarts:∀v,|((rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false v).card:ℝ)-
      (∑w,longAssignedIntervalProbability F hF K m θ w false/(d:ℝ))|≤err)
    (hdegrees:∀j v,|((∑x,sampledColourOrientation G (fun e=>z.1 (Sum.inl e)) j x v:ℕ):ℝ)-
      markedExpandedPhysicalProbability (initialIndexDensity U D*(1/100:ℝ)/2) (initialIndexDensity U D*((1/100:ℝ)/(m:ℝ))/2) p₂ k₂ u j/2*G.degree v|≤err)
    (rho eta:ℝ) (hrho:0<rho) (heta:0<eta) (hetaR:eta≤rho):
    let L:ℝ:=(ζ+δLoss)*n+(6*d+2:ℕ)
    (err+(d:ℝ)*err+L≤eta*n)→
    (rho*n+err+L+T.card+C.card≤ρ₀/(400*(m:ℝ))*n)→
    let Bad:=longPreparationIneligibleGraph G π d
    let P:=longResidualHostArc Mhost Small Bad
    let T₁:=longResidualInitialMarked G (fun e=>z.1 (Sum.inl e)) Mhost Small Bad
    ∃M:Finset {e:(Fin n)×(Fin n) // P e},
      (∀v,directedInCount P M v=d*startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false)) ∧
      (∀e,e.val.1∈T→(e∈M↔e∈T₁)) ∧
      (∀e,Sum.inl ({e.val.1,e.val.2}:Finset (Fin n))∈C→(e∈M↔e∈T₁)) ∧
      (∀v,((physicalEdgeGraph (changedDirectedPhysicalEdges P M T₁)).degree v:ℝ)≤
        (1+2/rho)*eta*n+(n:ℝ)^(3/5:ℝ)) :=by
  intro L hbudget hcost Bad P T₁
  have hmargins:=long_selected_type_supply_margins ρ₀ (initialIndexDensity U D) n D rho err L T.card C.card m
    hρ₀ hρlo hm (by positivity) hDlo hcost p₂ k₂ u
  exact long_matched_sample_types_protected_correction G hreg hD hd hm π z T ζ θ Dmatch alpha γ eps βList F hF weight w D₀ C S Del Small Loss Mhost hw hcover δLoss hLoss
    (initialIndexDensity U D*(1/100:ℝ)/2) p₂ k₂ u err herr hstarts hdegrees rho eta hrho heta hetaR hbudget
    (fun v=>by simpa only [hreg v] using hmargins.1)
    (fun v=>by simpa only [hreg v] using hmargins.2)
end Oberwolfach
