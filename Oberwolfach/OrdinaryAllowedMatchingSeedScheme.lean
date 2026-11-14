module

public import Oberwolfach.OrdinaryAllowedThresholdMatchingSeedWeights

@[expose] public section
/-! A named original-host scheme carries the matching and ordinary weights
for one selected successor length. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option synthInstance.maxSize 16384
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance (priority := 100000) allowedSeedSchemeFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

def OrdinaryAllowedMatchingSeedScheme (Allowed:Set ℕ) (K k:ℕ) (α θ τ:ℝ):Prop :=
    ∃BO:Fin K→ℝ,∃BM A:ℝ,(∀i,0<BO i) ∧ 0<BM ∧ 0<A ∧ ∀d:ℕ,∃N:ℕ,∀n:ℕ,N≤n→0<n→
    ∀(U:Type) [Fintype U] (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
      (hK:0<K) (hLengths:∀u,AllowedCycleLengths (F u) Allowed)
      (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (D:ℕ),
    P.IsRegularOfDegree D→(allowedThreshold Allowed+α)*n≤D→
    ∃w:∀i:Fin K,OrdinaryCycle (ordinaryEligibleHost P π d) (longPaddedSeedExponent i+2)→ℝ,
    ∃seed:(Fin (((k+2)*2-1)+1)→Fin n)→ℝ,
      (∀i C,0≤w i C ∧ w i C≤BO i/(n:ℝ)^(longPaddedSeedExponent i)) ∧
      SuccessorSequenceWeightConditions (ordinaryEligibleHost P π d) π (3*d) D τ A BM seed

theorem ordinary_allowed_matching_seed_scheme_choice
    (Allowed:Set ℕ) (hAllowed:Allowed.Nonempty) (hValid:∀s∈Allowed,3≤s)
    (K:ℕ) (α θ τ:ℝ) (hα:0<α) (hθ:0<θ) (hτ:0<τ):
    ∃k₀:ℕ,∀k:ℕ,k₀≤k→OrdinaryAllowedMatchingSeedScheme Allowed K k α θ τ :=by
  exact ordinary_allowed_threshold_matching_seed_weights Allowed hAllowed hValid K α θ τ hα hθ hτ
end Oberwolfach
