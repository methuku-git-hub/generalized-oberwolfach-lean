module

public import Oberwolfach.OrdinaryAssignedNamedSeeds
public import Oberwolfach.OrdinaryCandidateClassReservation
public import Oberwolfach.CandidateOrdinaryAssignedUniformApproximateSeedBounds
public import Oberwolfach.OrdinaryAssignedUniformApproximateSeedBounds
public import Oberwolfach.LongRetainedPaddedIndexSet

@[expose] public section
/-! The actual ordinary approximate rim probability and the two named
families of fixed preparation seed weights. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]

theorem ordinary_assigned_named_seed_bounds_candidate
    (hn:0<n) (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (hK:0<K) (i₀:Fin K) (rsv θ c ρ₀ ρ D:ℝ) (d m:ℕ) (hd:2≤d) (hm:1≤m)
    (hs0:0≤rsv) (hs1:rsv≤1/100) (hθ:0<θ) (hθ1:θ≤1/100) (hc:8≤c)
    (hda:1/θ≤d) (hρ₀:0<ρ₀) (hρlo:ρ₀≤ρ) (hρ:0<ρ) (hρ1:ρ≤1) (hD:0<D)
    (hsize:ρ*D=2*(Fintype.card U:ℝ))
    (Allowed:Set ℕ) (hAllowed:∀w,AllowedCycleLengths (F w) Allowed)
    (hsclass:rsv≤1/(2*(K:ℝ))) (hclass:∀w,i₀∈factorShortCandidates (F w) K)
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (τ A BM:ℝ) (weight:(Fin (m+1)→Fin n)→ℝ)
    (hw:SuccessorSequenceWeightConditions P π (3*d) D τ A BM weight)
    (hDlo:(n:ℝ)/2≤D) (hDhi:D≤2*n) (hBM:0≤BM)
    (BO:Fin K→ℝ) (hBO:∀i,0≤BO i)
    (w:∀i,OrdinaryCycle P (longPaddedSeedExponent i+2)→ℝ) (hw0:∀i C,0≤w i C)
    (hwupper:∀i C,w i C≤BO i/(n:ℝ)^(longPaddedSeedExponent i)):
    let pstar:=min (1/2:ℝ) (ρ₀/4);
    0<pstar ∧
    (∀W,0≤ordinaryAssignedShiftedSeed F hF i₀ rsv θ c D π d m weight W ∧
      ordinaryAssignedShiftedSeed F hF i₀ rsv θ c D π d m weight W≤(2*BM/pstar^(2*m+1))/(n:ℝ)^m) ∧
    (∀i W,0≤ordinaryAssignedUnshiftedSeed F hF i₀ rsv θ c D P π d w i W ∧
      ordinaryAssignedUnshiftedSeed F hF i₀ rsv θ c D P π d w i W≤
        (2*BO i/pstar^(2*(longPaddedSeedExponent i+2)))/(n:ℝ)^(longPaddedSeedExponent i+1)):=by
  intro pstar
  have hh:=ordinary_assigned_uniform_approximate_seed_bounds_candidate hn F hF K hK i₀ rsv θ c ρ₀ ρ D d hd
    hs0 hs1 hθ hθ1 hc hda hρ₀ hρlo hρ hρ1 hD hsize Allowed hAllowed hsclass hclass
    P π (3*d) m hm longPaddedSeedExponent long_padded_seed_exponent_positive id τ A BM weight hw
    hDlo hDhi hBM BO hBO w hw0 hwupper
  simpa only [ordinaryAssignedShiftedSeed,ordinaryAssignedUnshiftedSeed,ordinaryAssignedApproxRimProbability,
    id_eq,pstar] using hh
end Oberwolfach
