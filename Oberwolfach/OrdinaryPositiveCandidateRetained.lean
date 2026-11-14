module

public import Oberwolfach.OrdinaryAssignedSeedPositiveRetained
public import Oberwolfach.OrdinaryAssignedRetainedHubTests

@[expose] public section
/-! In the mixed family, a positively weighted unmarked candidate belongs
to a retained cycle length at its own hub. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]

theorem ordinary_positive_candidate_retained
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (i₀:Fin K) (rsv θ c D:ℝ) (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ)
    (weights:∀i:Fin K,OrdinaryCycle P (longPaddedSeedExponent i+2)→ℝ)
    (wM:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ (_:U)=>True) (fun _ (_:U)=>True)→ℝ)
    (x:Σj,OrdinaryMixedGenericFamily
      (MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d)
        (fun _ (_:U)=>True) (fun _ (_:U)=>True))
      (fun i=>OrderedOrdinaryWheel (U:=U) π (3*d) (longPaddedSeedExponent i+2)) j)
    (i:Fin K) (htag:x.1=some i)
    (hpositive:0<mixedCandidateWeight (ordinaryMixedGenericWeight wM
      (ordinaryAssignedUnshiftedSeed F hF i₀ rsv θ c D P π d weights)) x):
    θ/(100*(K:ℝ))≤ordinaryAssignedKeptFraction F hF K i₀ rsv θ
      (ordinaryMixedGenericWheelHub (U:=U) π (3*d) m longPaddedSeedExponent x.1 x.2) i :=by
  rcases x with ⟨j,W⟩
  cases j with
  | none => simp at htag
  | some j =>
    have hij:j=i:=Option.some.inj htag
    subst i
    exact ordinary_assigned_seed_positive_retained F hF i₀ rsv θ c D P π d weights j W hpositive
end Oberwolfach
