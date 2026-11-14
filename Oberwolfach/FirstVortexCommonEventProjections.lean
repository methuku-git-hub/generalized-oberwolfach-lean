module

public import Oberwolfach.FirstVortexRetainedSourceAndMatching

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance firstVortexCommonEventProjectionFin (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n

theorem first_vortex_common_event_local_tests
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (P:SimpleGraph (Fin n)) (Dv m:ℕ) (β ε:ℝ) (Q:Vortex U P Dv β ε m)
    (π:Equiv.Perm (Fin n)) (d t:ℕ) (σ:RawIntervalFamilyOutcome (Fin n) U Bool Bool)
    (J:StartRetentionOutcome (rawStartHubSet π d σ false) t)
    (q:U→Bool→ℝ) (s:U→Bool→ℝ) (ζ:ℝ)
    (hfixed:∀j∈Finset.Icc 1 Q.length,∀w∈Q.extendedIndices j,
      |rawIntervalUnassignedHubCountOn π d σ w (Q.extendedVertices j)-
      ((Q.extendedVertices j).card:ℝ)*(1-(∑g,q w g)-(∑k,s w k))|<((Q.extendedVertices j).card:ℝ)^(3/4:ℝ))
    (hcolumn:∀j∈Finset.Icc 1 Q.length,∀v∈Q.extendedVertices j,
      |rawIntervalUnassignedColumnCount π d σ v (Q.extendedIndices j)-
      ∑w∈Q.extendedIndices j,(1-(∑g,q w g)-(∑k,s w k))|<((Q.extendedVertices j).card:ℝ)^(3/4:ℝ))
    (hboundary:∀j∈Finset.Icc 1 Q.length,∀v∈Q.extendedVertices j,
      ((rawIntervalBoundaryHubSet π d σ (Q.extendedIndices j) v).card:ℝ)≤
        4*((Q.extendedIndices j).card:ℝ)/d+4*((Q.extendedVertices j).card:ℝ)^(3/4:ℝ))
    (hrows:∀j∈Finset.Icc 1 Q.length,RetainedRestrictionLocalGood π d σ false t
      (Q.extendedVertices j) (Q.extendedIndices j) ζ J):
    (∀w∈Q.extendedIndices 1,
      |rawIntervalUnassignedHubCountOn π d σ w (Q.extendedVertices 1)-
      ((Q.extendedVertices 1).card:ℝ)*(1-(∑g,q w g)-(∑k,s w k))|<((Q.extendedVertices 1).card:ℝ)^(3/4:ℝ)) ∧
    (∀v∈Q.extendedVertices 1,
      |rawIntervalUnassignedColumnCount π d σ v (Q.extendedIndices 1)-
      ∑w∈Q.extendedIndices 1,(1-(∑g,q w g)-(∑k,s w k))|<((Q.extendedVertices 1).card:ℝ)^(3/4:ℝ)) ∧
    (∀v∈Q.extendedVertices 1,
      ((rawIntervalBoundaryHubSet π d σ (Q.extendedIndices 1) v).card:ℝ)≤
        4*((Q.extendedIndices 1).card:ℝ)/d+4*((Q.extendedVertices 1).card:ℝ)^(3/4:ℝ)) ∧
    RetainedRestrictionLocalGood π d σ false t (Q.extendedVertices 1) (Q.extendedIndices 1) ζ J :=by
  have hfirst:1∈Finset.Icc 1 Q.length:=Finset.mem_Icc.mpr ⟨le_rfl,Q.length_pos⟩
  exact ⟨hfixed 1 hfirst,hcolumn 1 hfirst,hboundary 1 hfirst,hrows 1 hfirst⟩

theorem first_vortex_common_event_count_budget (n:ℕ) (ξ eps:ℝ) (hξ:4*ξ≤eps/2):
    4*(ξ*n)≤(eps/2)*n :=by
  have hn:0≤(n:ℝ):=by positivity
  nlinarith
end Oberwolfach
