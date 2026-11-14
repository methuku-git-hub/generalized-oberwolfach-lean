module

public import Oberwolfach.OrdinaryAssignedNamedSeeds

@[expose] public section
/-! The named assigned seeds are the generic marked and unmarked weights
with the actual categorical probabilities and frequency coefficients. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]

theorem ordinary_assigned_shifted_seed_factorization
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (i₀:Fin K) (rsv θ c D:ℝ) (π:Equiv.Perm (Fin n)) (d m:ℕ)
    (weight:(Fin (m+1)→Fin n)→ℝ):
    let s:=ordinaryAssignedSpokeProbability F hF K i₀ rsv θ c
    let p:=ordinaryAssignedApproxRimProbability F hF i₀ rsv θ c D;
    ordinaryAssignedShiftedSeed F hF i₀ rsv θ c D π d m weight=
      (fun W=>weight W.1.val/(D*p^(m+1)*(s W.2.val true)^m)) :=by
  intro s p
  funext W
  simp only [ordinaryAssignedShiftedSeed,s,ordinaryAssignedSpokeProbability,ite_true,p]

theorem ordinary_assigned_unshifted_seed_factorization
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (i₀:Fin K) (rsv θ c D:ℝ) (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d:ℕ)
    (weight:∀i:Fin K,OrdinaryCycle P (longPaddedSeedExponent i+2)→ℝ):
    let s:=ordinaryAssignedSpokeProbability F hF K i₀ rsv θ c
    let p:=ordinaryAssignedApproxRimProbability F hF i₀ rsv θ c D
    let η:=fun i u=>ordinaryAssignedFrequencyCoefficient F hF K i₀ rsv θ c u i;
    ordinaryAssignedUnshiftedSeed F hF i₀ rsv θ c D P π d weight=
      (fun i W=>η i W.2*physicalOrdinaryTupleWeight (π:=π) (b:=3*d) (long_padded_seed_exponent_positive i) (weight i) W.1.val/
        (((longPaddedSeedExponent i+2:ℕ):ℝ)*D*p^(longPaddedSeedExponent i+2)*(s W.2 true)^(longPaddedSeedExponent i+1))) :=by
  intro s p η
  funext i W
  simp only [ordinaryAssignedUnshiftedSeed,s,ordinaryAssignedSpokeProbability,ite_true,p,η]
end Oberwolfach
