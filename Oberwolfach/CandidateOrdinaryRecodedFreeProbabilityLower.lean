module

public import Oberwolfach.CandidateOrdinaryUnusedPhysicalLower
public import Oberwolfach.CandidateOrdinaryAssignedSamplingParameters
public import Oberwolfach.CandidateOrdinaryAssignedNamedSamplingWitness

@[expose] public section
/-! The original assigned recipe leaves a positive density of physical edges
outside the reference and approximate-matching colours. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_assigned_recoded_free_probability_lower_candidate
    {n D:ℕ} (hn:0<n) (hD:0<D)
    {U:Type} [Fintype U] [DecidableEq U] (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (Allowed:Set ℕ) (hAllowed:∀w,AllowedCycleLengths (F w) Allowed)
    (K:ℕ) (hK:0<K) (i₀:Fin K) (rsv θ c ρ₀ smin:ℝ) (d:ℕ) (hd:2≤d)
    (hρ₀:0<ρ₀) (hρlo:ρ₀ ≤ initialIndexDensity U D) (hρhi:initialIndexDensity U D≤1)
    (hsmin:0<smin) (hslo:smin≤rsv) (hs1:rsv≤1/100)
    (hθ:0<θ) (hθ1:θ≤1/100) (hc:8≤c) (hda:1/θ≤d)
    (hsclass:rsv≤1/(2*(K:ℝ))) (hclass:∀w,i₀∈factorShortCandidates (F w) K)
    (sampling:OrdinaryAssignedVortexExactSamplingData (D:=D) F hF K i₀ rsv θ c ρ₀ smin d):
    ρ₀*θ/4≤ initialIndexDensity U D*rsv/2+sampling.u/2 :=by
  have hu:=ordinary_assigned_unused_physical_probability_lower_candidate hn hD F hF Allowed hAllowed K hK i₀ rsv θ c ρ₀ smin d hd
    hρ₀ hρlo hρhi hsmin hslo hs1 hθ hθ1 hc hda hsclass hclass sampling
  have hp:=sampling.hp
  linarith
end Oberwolfach
