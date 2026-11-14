module

public import Oberwolfach.OrdinaryAssignedRetainedCoefficient
public import Oberwolfach.OrdinaryCandidateClassReservation
public import Oberwolfach.CandidateOrdinaryAssignedFrequencyCoefficient
public import Oberwolfach.OrdinaryAssignedFrequencyCoefficient

@[expose] public section
/-! Every retained ordinary frequency has a uniform positive coefficient;
the actual factor-assigned short-spoke density is used in the denominator. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_assigned_retained_coefficient_lower_candidate
    {n:ℕ} (hn:0<n) {U:Type} [Fintype U]
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (Allowed:Set ℕ) (hAllowed:∀u,AllowedCycleLengths (F u) Allowed)
    (K:ℕ) (hK:0<K) (i₀:Fin K) (rsv θ c:ℝ)
    (hs0:0≤rsv) (hs1:rsv≤1/100) (hθ:0<θ) (hθ1:θ≤1/100) (hc:8≤c)
    (hsclass:rsv≤1/(2*(K:ℝ))) (hclass:∀u,i₀∈factorShortCandidates (F u) K)
    (hb:∀u,ordinaryAssignedShortWeight F hF K i₀ rsv θ c u≤1)
    (u:U) (i:Fin K)
    (hret:θ/(100*(K:ℝ))≤ordinaryAssignedKeptFraction F hF K i₀ rsv θ u i):
    θ/(200*(K:ℝ))≤ordinaryAssignedFrequencyCoefficient F hF K i₀ rsv θ c u i :=by
  have hcoef:=ordinary_assigned_frequency_coefficient_candidate hn F hF Allowed hAllowed K hK i₀ rsv θ c
    hs0 hs1 hθ hθ1 hc hsclass hclass u
  let b:=ordinaryAssignedShortWeight F hF K i₀ rsv θ c u
  let f:=ordinaryAssignedKeptFraction F hF K i₀ rsv θ u i
  let η:=ordinaryAssignedFrequencyCoefficient F hF K i₀ rsv θ c u i
  have hbpos:0<b:=hcoef.1
  have hb1:b≤1:=hb u
  have hη:0≤η:=(hcoef.2.1 i).1
  have hbalance:η*b=(1-θ)*f:=hcoef.2.2 i
  have hKreal:0<(K:ℝ):=by exact_mod_cast hK
  have hmin:0≤θ/(100*(K:ℝ)):=by positivity
  have hf:θ/(100*(K:ℝ))≤f:=hret
  have hhalf:(1/2:ℝ)≤1-θ:=by linarith
  have hprod:=mul_le_mul hhalf hf hmin (by positivity : 0≤1-θ)
  have hupper:η*b≤η:=by nlinarith [mul_nonneg hη (sub_nonneg.mpr hb1)]
  have heq:(1/2:ℝ)*(θ/(100*(K:ℝ)))=θ/(200*(K:ℝ)):=by ring
  linarith
end Oberwolfach
