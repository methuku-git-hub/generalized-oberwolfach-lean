module

public import Oberwolfach.OrdinaryShiftedMatchingCoreEvent

@[expose] public section
/-! Name the matching-core event with an arbitrary dependent-stage prior.
The prior can contain the protected reservoir and later shared tests. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def OrdinaryShiftedMatchingWithPrior
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (Pmatch:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m K:ℕ)
    (p₂ k₂:ℝ) (q s:U→Bool→ℝ)
    (wM:MarkedWheel (Prod.fst:(Fin n)×(Fin n)→(Fin n)) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ (_:U)=>True) (fun _ (_:U)=>True)→ℝ)
    (wO:∀i:Fin K,OrderedOrdinaryWheel (U:=U) π (3*d) (longPaddedSeedExponent i+2)→ℝ)
    (t ξ:ℝ)
    {R:(∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)→Type}
    (E:(Σσ,R σ)→Prop) (z:Σσ,R σ):Prop :=
  E z ∧ OrdinaryShiftedMatchingCoreEvent Pmatch π d m p₂ k₂ q s wM wO t ξ z.1

theorem ordinary_shifted_matching_with_prior_left
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (Pmatch:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m K:ℕ)
    (p₂ k₂:ℝ) (q s:U→Bool→ℝ)
    (wM:MarkedWheel (Prod.fst:(Fin n)×(Fin n)→(Fin n)) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ (_:U)=>True) (fun _ (_:U)=>True)→ℝ)
    (wO:∀i:Fin K,OrderedOrdinaryWheel (U:=U) π (3*d) (longPaddedSeedExponent i+2)→ℝ)
    (t ξ:ℝ) {R:(∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)→Type}
    (E:(Σσ,R σ)→Prop) (z:Σσ,R σ)
    (h:OrdinaryShiftedMatchingWithPrior Pmatch π d m K p₂ k₂ q s wM wO t ξ E z):E z:=h.1
end Oberwolfach
