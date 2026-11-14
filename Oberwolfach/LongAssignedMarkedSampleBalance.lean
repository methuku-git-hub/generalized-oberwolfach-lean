module

public import Oberwolfach.MarkedExpandedActualSample
public import Oberwolfach.LongSelectedMarkedSampleBalance
public import Oberwolfach.LongAssignedReferenceLawAlignment

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance assignedMarkedSampleBalanceFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

/-- The incoming marked-degree and start-count tests from the same actual
expanded sample have exactly the common retained-start target. -/
theorem long_assigned_sample_marked_retained_indegree_balance
    {n d D m K:ℕ} {U:Type} [Fintype U] [DecidableEq U] [Nonempty (Fin n)]
    (G:SimpleGraph (Fin n)) (hreg:G.IsRegularOfDegree D) (hD:0<D) (hd:0<d) (hm:0<m)
    (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2) (θ:ℝ)
    (π:Equiv.Perm (Fin n))
    (z:MarkedExpandedActualOutcome (U:=U) π d)
    (p p₂ k₂ u err:ℝ) (herr:0≤err)
    (hstarts:∀v,|((rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false v).card:ℝ)-
      (∑w,longAssignedIntervalProbability F hF K m θ w false/(d:ℝ))|<err)
    (hheads:∀v,|((∑x,sampledColourOrientation G (fun e=>z.1 (Sum.inl e)) 1 x v:ℕ):ℝ)-
      markedExpandedPhysicalProbability p (initialIndexDensity U D*((1/100:ℝ)/(m:ℝ))/2) p₂ k₂ u 1/2*G.degree v|<err):
    ∀v,|((∑x,sampledColourOrientation G (fun e=>z.1 (Sum.inl e)) 1 x v:ℕ):ℝ)-
      (d:ℝ)*(startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false):ℝ)|≤err+(d:ℝ)*err:=by
  apply long_sample_marked_retained_indegree_balance G hreg hD hd hm π (fun e=>z.1 (Sum.inr e))
    (fun e=>z.1 (Sum.inl e)) (longAssignedIntervalProbability F hF K m θ) (1/100:ℝ) p p₂ k₂ u err herr
  · exact (long_assigned_reference_colour_marginals F hF K m θ).1
  · intro v;exact (hstarts v).le
  · intro v;exact (hheads v).le
end Oberwolfach
