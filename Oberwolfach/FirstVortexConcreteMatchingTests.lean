module

public import Oberwolfach.FirstVortexConcreteBoundaryEvent
public import Oberwolfach.FirstVortexCombinedSelectorBoundaryEvent

@[expose] public section
/-! The concrete tests required by the first-vortex preparation, grouped
on the same expanded sample used by the synchronized selector. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance concreteBoundaryMatchingTestsFin (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n

theorem first_vortex_concrete_matching_tests
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U] [Nonempty (Fin n)]
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d r Dv mm:ℕ) (β ε:ℝ)
    (Vort:Vortex U P Dv β ε mm) (θ ρ₀ BM:ℝ) (BO:Fin K→ℝ)
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (weight:(Fin ((r+4)+1)→Fin n)→ℝ)
    (w:∀i:Fin K,OrdinaryCycle P (longPaddedSeedExponent i+2)→ℝ)
    (a γ eps Δ ξSeed ΔSeed ζret ζselect βList terr τerr:ℝ)
    (z:MarkedExpandedActualOutcome (U:=U) π d) (Inner:Finset (Fin n)) :
    FirstVortexConcreteBoundaryEvent P π d r Dv mm β ε Vort θ ρ₀ BM BO F hF weight w
      a γ eps Δ ξSeed ΔSeed ζret ζselect βList terr τerr z Inner →
    (∀u,|rawIntervalUnassignedHubCountOn π d (fun e=>z.1 (Sum.inr e)) u (Vort.extendedVertices 1)-
      ((Vort.extendedVertices 1).card:ℝ)*(1-(∑g,longAssignedIntervalProbability F hF K (r+4) θ u g)-
        (∑j,longAssignedSpokeProbability F hF K (r+4) θ u j))|<(n:ℝ)^(3/4:ℝ)) ∧
    (∀v,|rawIntervalUnassignedColumnCount π d (fun e=>z.1 (Sum.inr e)) v Finset.univ-
      ∑u:U,(1-(∑g,longAssignedIntervalProbability F hF K (r+4) θ u g)-
        (∑j,longAssignedSpokeProbability F hF K (r+4) θ u j))|<(n:ℝ)^(3/4:ℝ)) ∧
    RetainedRestrictionGood π d (fun e=>z.1 (Sum.inr e)) false
      (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false))
      (fun _:Unit=>Finset.univ) (fun _:Unit=>Finset.univ) ζret z.2 ∧
    (∀v,((rawIntervalBoundaryHubSet π d (fun e=>z.1 (Sum.inr e)) Finset.univ v).card:ℝ)≤
      4*(Fintype.card U:ℝ)/d+4*(n:ℝ)^(3/4:ℝ)) ∧
    (∀u g,|rawIntervalHubStartCount π d g (fun e=>z.1 (Sum.inr e)) u-
      (n:ℝ)*longAssignedIntervalProbability F hF K (r+4) θ u g/d|<(n:ℝ)^(3/4:ℝ)/d) :=by
  intro h
  dsimp only [FirstVortexConcreteBoundaryEvent] at h
  have hdec:concreteBoundaryEventFin n=concreteBoundaryMatchingTestsFin n:=Subsingleton.elim _ _
  have hdecK:concreteBoundaryEventFin K=concreteBoundaryMatchingTestsFin K:=Subsingleton.elim _ _
  try rw [hdec] at h
  try rw [hdecK] at h
  rcases h with ⟨hAll,hLocal,hCounts,hLoads,hGlobal,hLists⟩
  simpa only [rawExpandedApproximateCollapse,rawExpandedMarkedCollapse,id,Nat.cast_add,Nat.cast_ofNat] using
    (show _ ∧ _ ∧ _ ∧ _ ∧ _ from ⟨hAll.1,hAll.2,hGlobal.1,hGlobal.2,hCounts.2⟩)
end Oberwolfach
