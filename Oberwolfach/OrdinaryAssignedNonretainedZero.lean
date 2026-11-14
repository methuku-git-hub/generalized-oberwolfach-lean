module

public import Oberwolfach.OrdinaryAssignedFrequencyCoefficient
public import Oberwolfach.LongRetainedPaddedIndexSet

@[expose] public section
/-! No fractional cycle weights are needed for an index that is not
retained by any factor; its actual assigned coefficient is identically zero. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_assigned_nonretained_fraction_zero
    {n K:ℕ} {U:Type} [Fintype U]
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (i₀:Fin K) (rsv θ:ℝ) (hs0:0≤rsv) (i:Fin K)
    (hi:i∉longRetainedSeedIndices F hF K θ) (u:U):
    ordinaryAssignedKeptFraction F hF K i₀ rsv θ u i=0 :=by
  have hnot:¬θ/(100*(K:ℝ))≤ordinaryAssignedFraction F hF K u (some i):=by
    intro hh
    apply hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,⟨u,hh⟩⟩
  have hlt:ordinaryAssignedFraction F hF K u (some i)<θ/(100*(K:ℝ)):=lt_of_not_ge hnot
  have hsub:ordinaryAssignedFraction F hF K u (some i)-(if i=i₀ then rsv else 0)<θ/(100*(K:ℝ)):=by
    split_ifs <;> linarith
  simp only [ordinaryAssignedKeptFraction,hsub,ite_true]

theorem ordinary_assigned_nonretained_coefficient_zero
    {n K:ℕ} {U:Type} [Fintype U]
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (i₀:Fin K) (rsv θ c:ℝ) (hs0:0≤rsv) (i:Fin K)
    (hi:i∉longRetainedSeedIndices F hF K θ) (u:U):
    ordinaryAssignedFrequencyCoefficient F hF K i₀ rsv θ c u i=0 :=by
  simp only [ordinaryAssignedFrequencyCoefficient,
    ordinary_assigned_nonretained_fraction_zero F hF i₀ rsv θ hs0 i hi u,mul_zero,zero_div]
end Oberwolfach
