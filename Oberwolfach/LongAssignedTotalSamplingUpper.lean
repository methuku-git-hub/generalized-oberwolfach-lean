module

public import Oberwolfach.LongAssignedTotalSamplingMass

@[expose] public section
/-! The original selection recipe leaves at least the θ fraction before
sampling errors. -/
set_option autoImplicit false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_assigned_sampling_mass_upper
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U] (hn:0<n)
    (m:ℕ) (hm:0<m) (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (θ:ℝ) (hθ:θ≤1) (u:U):
    ((m:ℝ)+1)*(∑g:Bool,longAssignedIntervalProbability F hF K m θ u g)+
      (1-θ)*(∑i:Fin K,longAssignedKeptFraction F hF K θ i u)≤1-θ:=by
  have hbound:∀i:Fin K,longAssignedKeptFraction F hF K θ i u≤ordinaryAssignedFraction F hF K u (some i):=by
    intro i
    unfold longAssignedKeptFraction
    split_ifs
    · exact le_rfl
    · unfold ordinaryAssignedFraction; positivity
  have hsum:=Finset.sum_le_sum (fun i (_:i∈(Finset.univ:Finset (Fin K)))=>hbound i)
  have hmass:=long_assigned_fraction_partition (K:=K) hn F hF u
  have hh:=mul_le_mul_of_nonneg_left hsum (show 0≤1-θ by linarith)
  rw [long_assigned_interval_probability_sum hn m hm F hF θ u]
  nlinarith
end Oberwolfach
