module

public import Oberwolfach.LongMatchedDualUsedEventual
public import Oberwolfach.LongMatchedRequiredPackingReady

@[expose] public section
/-! The selected matching and its prescribed packing supply the hypotheses
of the dual-type correction on the same expanded sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance matchedPackedDualEventualFin (n:ℕ):DecidableEq (Fin n):=selectedMarkedSampleBalanceFin n
local instance matchedPackedDualEventualArc (n:ℕ) (P:(Fin n)×(Fin n)→Prop):DecidableEq {e:(Fin n)×(Fin n) // P e}:=reservedCandidateArcDecEq P

theorem long_matched_packed_dual_eventual_correction
    (d e r:ℕ) (ρ₀ rho ζ δLoss εInner eta:ℝ)
    (hρ₀:0<ρ₀) (hrho:0<rho) (heta:0<eta) (hetaR:eta≤rho)
    (hbudget:ζ+δLoss<eta) (hsupply:rho+ζ+δLoss+εInner<ρ₀/(400*((r+4:ℕ):ℝ))):
    ∃N:ℕ,∀n:ℕ,N≤n→∀ [Nonempty (Fin n)] (U:Type) [Fintype U] [DecidableEq U]
    (K D:ℕ) (G:SimpleGraph (Fin n)) (hreg:G.IsRegularOfDegree D) (hD:0<D) (hd:0<d)
    (hρlo:ρ₀ ≤ initialIndexDensity U D) (hDlo:(n:ℝ)/2≤D)
    (π:Equiv.Perm (Fin n)) (z:MarkedExpandedActualOutcome (U:=U) π d) (T:Finset (Fin n))
    (θ Dmatch alpha γ eps βList:ℝ) (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (weight:(Fin (r+4+1)→Fin n)→ℝ)
    (w:∀i:Fin K,OrdinaryCycle G (longPaddedSeedExponent i+2)→ℝ)
    (D₀:MarkedReferenceDeletion G π d (fun x=>rawExpandedMarkedCollapse x (z.1 x)))
    (C:Finset (Finset (Fin n)⊕(Fin n×U))) (S Del:SimpleGraph (Fin n)) (Mhost:Fin n→Fin n→ℕ)
    (hw:LongClassMatchingDeletionWitness ζ G π d r z T K θ Dmatch alpha γ eps βList F hF weight w D₀ C S Mhost Del)
    (Pack:Finset (Sym2 (Fin n))) (hPack:Pack⊆(longApproximatePhysicalGraph G π d z.1).edgeFinset)
    (E:U→Finset (Sym2 (Fin n))),
    let raw:RawMarkedOutcome (Fin n) U Bool Bool:=fun x=>rawExpandedApproximateCollapse x (z.1 x)
    let ℓ:=fun i:Fin K=>longPaddedSeedExponent i+2
    let R:=mixedCandidateResources (longRawSeedResources (U:=U) π d (r+4) ℓ)
    let Tmix:=bernoulliVertexSet (longRawHubState G π d raw true true)
    let Q:=longRawSurvivingResources G π d raw true true Del.edgeFinset
    let q:=survivingCandidateEmbedding R Q Tmix (long_raw_surviving_resources_subset G π d raw true true Del.edgeFinset)
    let φ:=markedRawSampledPhysicalEmbedding G π d raw true true;
    ∀Mix:Finset (RestrictedResource R (Function.Embedding.subtype (·∈Q))),
    let Used:=physicalRimCandidateUnion φ (restrictedResourceSet R (Function.Embedding.subtype (·∈Tmix))) (Mix.map q)
    let Req:=fun x y=>Mhost x y=1 ∧ markedPhysicalRim G π (3*d)
      (fun x=>markedExpandedPhysicalCollapse (z.1 (Sum.inl x))) true x (π.symm y)≠1
    let Sel:=longSelectedPhysicalGraph G π d z.1
    let Kbad:=longRequiredPhysicalGraph S (S\Used) Sel π d T Req (fun x y=>Used.Adj x y)
    let Loss:=prescribedPhysicalUnion E
    let Small:=SimpleGraph.fromEdgeSet (↑Pack:Set (Sym2 (Fin n)))⊔Loss;
    Kbad.edgeFinset⊆Finset.univ.biUnion E→
    (∀v,(Loss.degree v:ℝ)≤δLoss*n)→(T.card:ℝ)≤εInner*n→C.card≤e→
    ∀p₂ k₂ u:ℝ,
    (∀v,|((rawStartHubSet π d (fun x=>z.1 (Sum.inr x)) false v).card:ℝ)-
      (∑w,longAssignedIntervalProbability F hF K (r+4) θ w false/(d:ℝ))|<(n:ℝ)^(3/5:ℝ))→
    (∀j v,|((∑x,sampledColourOrientation G (fun x=>z.1 (Sum.inl x)) j x v:ℕ):ℝ)-
      markedExpandedPhysicalProbability (initialIndexDensity U D*(1/100:ℝ)/2) (initialIndexDensity U D*((1/100:ℝ)/((r+4:ℕ):ℝ))/2) p₂ k₂ u j/2*G.degree v|<(n:ℝ)^(3/5:ℝ))→
    let P:=longEligibleResidualArc Mhost Small ⊥
    let T₁:=longDualInitialMarked G (fun x=>z.1 (Sum.inl x)) Mhost Small (longOrdinaryArcEligible π d) (longMarkedArcEligible π d);
    ∃M:Finset {x:(Fin n)×(Fin n) // P x},
      (∀v,directedInCount P M v=d*startRetentionMinimum (rawStartHubSet π d (fun x=>z.1 (Sum.inr x)) false)) ∧
      (∀x∈M,longMarkedArcEligible π d x.val) ∧ (∀x,x∉M→longOrdinaryArcEligible π d x.val) ∧
      (∀x,x.val.1∈T→(x∈M↔x∈T₁)) ∧
      (∀x,Sum.inl ({x.val.1,x.val.2}:Finset (Fin n))∈C→(x∈M↔x∈T₁)) ∧
      (∀v,((physicalEdgeGraph (changedDirectedPhysicalEdges P M T₁)).degree v:ℝ)≤
        (1+2/rho)*eta*n+(n:ℝ)^(3/5:ℝ)):=by
  obtain ⟨N,hN⟩:=long_matched_dual_used_eventual_correction d e (r+4) ρ₀ rho ζ δLoss εInner eta hρ₀ (by omega) hrho heta hetaR hbudget hsupply
  refine ⟨N,?_⟩
  intro n hn _ U _ _ K D G hreg hD hd hρlo hDlo π z T θ Dmatch alpha γ eps βList F hF weight w D₀ C S Del Mhost hw Pack hPack E raw ℓ R Tmix Q q φ Mix Used Req Sel Kbad Loss Small hcover hLoss hT hC p₂ k₂ u hstarts hdegrees P T₁
  have hready0:=long_matched_required_packing_ready ζ G π z T θ Dmatch alpha γ eps βList F hF weight w D₀ C S Del Sel Mhost hw
  have hdec:instDecidableEqFin n=matchedPackedDualEventualFin n:=Subsingleton.elim _ _
  have hdecK:instDecidableEqFin K=matchedPackedDualEventualFin K:=Subsingleton.elim _ _
  try rw [hdec] at hready0
  try rw [hdecK] at hready0
  have hready:=hready0 Mix Pack E hcover
  have hh:=hN n hn
  have hdual:matchedDualUsedFin n=matchedPackedDualEventualFin n:=Subsingleton.elim _ _
  have hdualK:matchedDualUsedFin K=matchedPackedDualEventualFin K:=Subsingleton.elim _ _
  try rw [hdual] at hh
  try rw [hdualK] at hh
  exact hh U r K D G hreg hD hd hρlo hDlo π z T θ Dmatch alpha γ eps βList F hF weight w D₀ C S Del Small Loss Mhost hw Pack hPack (le_refl _) Used hready.1 hready.2 hLoss hT hC p₂ k₂ u hstarts hdegrees
end Oberwolfach
