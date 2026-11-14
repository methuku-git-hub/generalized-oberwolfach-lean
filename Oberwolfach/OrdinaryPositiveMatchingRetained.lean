module

public import Oberwolfach.OrdinaryPositiveCandidateRetained
public import Oberwolfach.OrdinaryAssignedMatchedRelativeFrequency

@[expose] public section
/-! A positive-support physical matching contains no unretained short class. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]

theorem ordinary_positive_matching_retained
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (i₀:Fin K) (rsv θ c D:ℝ) (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ)
    (weights:∀i:Fin K,OrdinaryCycle P (longPaddedSeedExponent i+2)→ℝ)
    (wM:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ (_:U)=>True) (fun _ (_:U)=>True)→ℝ)
    (R:∀i,OrdinaryMixedGenericFamily
      (MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d)
        (fun _ (_:U)=>True) (fun _ (_:U)=>True))
      (fun i=>OrderedOrdinaryWheel (U:=U) π (3*d) (longPaddedSeedExponent i+2)) i→
        Finset (((Fin n×Fin n)⊕(Fin n×Fin n))⊕(Bool×Fin n×U)))
    (state:(((Fin n×Fin n)⊕(Fin n×Fin n))⊕(Bool×Fin n×U))→Bool)
    (L:Finset (PhysicalSampledCandidate (mixedCandidateResources R) state))
    (hsupp:∀x∈L,0<mixedCandidateWeight (ordinaryMixedGenericWeight wM
      (ordinaryAssignedUnshiftedSeed F hF i₀ rsv θ c D P π d weights)) x.val):
    ∀x∈L,∀i:Fin K,x.val.1=some i→
      θ/(100*(K:ℝ))≤ordinaryAssignedKeptFraction F hF K i₀ rsv θ
        (ordinaryMixedGenericWheelHub (U:=U) π (3*d) m longPaddedSeedExponent x.val.1 x.val.2) i:=by
  intro x hx i htag
  exact ordinary_positive_candidate_retained F hF i₀ rsv θ c D P π d m weights wM x.val i htag (hsupp x hx)
end Oberwolfach
