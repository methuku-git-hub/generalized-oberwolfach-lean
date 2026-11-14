module

public import Oberwolfach.CandidateOrdinaryAssignedNamedSamplingWitnessDirectReserve
public import Oberwolfach.CandidateOrdinaryAssignedVortexExactSamplingDataDirectReserve
public import Oberwolfach.OrdinaryAssignedReserveBasic

@[expose] public section
/-! The unused physical-edge colour in the original assigned recipe has
small density; the estimate follows from the actual factor marginals. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_assigned_unused_density_upper
    {n D:ℕ} (hn:0<n) (hD:0<D) {U:Type} [Fintype U] [DecidableEq U]
    (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (Allowed:Set ℕ) (hAllowed:∀w,AllowedCycleLengths (F w) Allowed)
    (K:ℕ) (hK:0<K) (i₀:Fin K) (rsv θ c ρ₀ smin:ℝ) (d:ℕ) (hd:2≤d)
    (hrs0:0≤ rsv) (hrs1:rsv≤1/100) (hθ:0<θ) (hθ1:θ≤1/100) (hc:8≤c)
    (hda:1/θ≤d) (hρ₀:0<ρ₀) (hρlo:ρ₀≤ initialIndexDensity U D) (hρhi:initialIndexDensity U D≤1)
    (hClass:OrdinaryClassReserveBound F hF i₀ rsv)
    (sampling:OrdinaryAssignedVortexExactSamplingData (D:=D) F hF K i₀ rsv θ c ρ₀ smin d):
    sampling.u≤2*θ*initialIndexDensity U D ∧ sampling.u≤2*θ :=by
  have hDreal:0<(D:ℝ):=by exact_mod_cast hD
  have hρ:0< initialIndexDensity U D:=hρ₀.trans_le hρlo
  have hsize:initialIndexDensity U D*(D:ℝ)=2*(Fintype.card U:ℝ):=by
    simp [initialIndexDensity,ne_of_gt hDreal]
  obtain ⟨u',_,_,_,hprob,hud,_,_,_,_,_⟩:=
    ordinary_assigned_named_sampling_witness_candidate_direct_reserve hn F hF Allowed hAllowed K hK i₀ rsv θ c
      (initialIndexDensity U D) D d hd hrs0 hrs1 hθ hθ1 hc hda hρ hρhi hDreal hsize hClass
  have huEq:sampling.u=u':=by
    have hsamp:=sampling.hphysical
    linarith
  have hpoint:∀w,1-rsv-ordinaryAssignedLongWeight F hF K θ c w-
      ordinaryAssignedShortWeight F hF K i₀ rsv θ c w≤2*θ:=by
    intro w
    have hh:=ordinary_factor_actual_marginals hn (F w) (hF w) K hK i₀ rsv θ c hrs0 hrs1 hθ.le hθ1 hc (hClass w)
    simpa only [ordinaryAssignedShortWeight,ordinaryAssignedLongWeight,ordinaryAssignedFraction] using hh.2.2.2.2.1
  have hsum:(∑w:U,(1-rsv-ordinaryAssignedLongWeight F hF K θ c w-
      ordinaryAssignedShortWeight F hF K i₀ rsv θ c w))≤(Fintype.card U:ℝ)*(2*θ):=by
    calc
      _ ≤ ∑_w:U,(2*θ):=Finset.sum_le_sum (by intro w _;exact hpoint w)
      _ = _ :=by simp [mul_comm]
  have hfirst:sampling.u≤2*θ*initialIndexDensity U D:=by
    rw [huEq]
    have hh:u'*(D:ℝ)≤(2*θ*initialIndexDensity U D)*(D:ℝ):=by
      nlinarith [hud,hsum,hsize]
    exact le_of_mul_le_mul_right hh hDreal
  refine ⟨hfirst,?_⟩
  have hh:=mul_le_mul_of_nonneg_left hρhi (show 0≤2*θ by positivity)
  nlinarith [hfirst,hh]
end Oberwolfach
