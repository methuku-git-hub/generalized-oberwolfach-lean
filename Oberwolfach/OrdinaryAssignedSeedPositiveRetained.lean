module

public import Oberwolfach.OrdinaryAssignedNamedSeeds

@[expose] public section
/-! Positive unmarked seed weight is possible only at a retained length
for the wheel's own hub. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]

theorem ordinary_assigned_seed_positive_retained
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (i₀:Fin K) (rsv θ c D:ℝ) (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d:ℕ)
    (weight:∀i:Fin K,OrdinaryCycle P (longPaddedSeedExponent i+2)→ℝ)
    (i:Fin K) (W:OrderedOrdinaryWheel (U:=U) π (3*d) (longPaddedSeedExponent i+2))
    (hpositive:0<ordinaryAssignedUnshiftedSeed F hF i₀ rsv θ c D P π d weight i W):
    θ/(100*(K:ℝ))≤ordinaryAssignedKeptFraction F hF K i₀ rsv θ W.2 i :=by
  by_contra h
  have hlt:ordinaryAssignedKeptFraction F hF K i₀ rsv θ W.2 i < θ/(100*(K:ℝ)):=lt_of_not_ge h
  have hzero:ordinaryAssignedKeptFraction F hF K i₀ rsv θ W.2 i=0:=by
    by_cases hf:ordinaryAssignedFraction F hF K W.2 (some i)-(if i=i₀ then rsv else 0)<θ/(100*(K:ℝ))
    · simp only [ordinaryAssignedKeptFraction,hf,if_true]
    · simp only [ordinaryAssignedKeptFraction,hf,if_false] at hlt
  have hz:ordinaryAssignedFrequencyCoefficient F hF K i₀ rsv θ c W.2 i=0:=by
    simp only [ordinaryAssignedFrequencyCoefficient,hzero,mul_zero,zero_div]
  simp only [ordinaryAssignedUnshiftedSeed,hz,zero_mul,zero_div,lt_self_iff_false] at hpositive
end Oberwolfach
