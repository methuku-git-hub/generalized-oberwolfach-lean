module

public import Oberwolfach.OrdinaryClassReserveBound
public import Oberwolfach.CandidateOrdinaryAssignedRootCountUpper
public import Oberwolfach.OrdinaryAssignedRootCountUpper
public import Oberwolfach.OrdinaryCandidateClassReservation
public import Oberwolfach.OrdinaryFactorActualMarginals
public import Oberwolfach.OrdinaryClassReservation
public import Oberwolfach.OrdinaryAssignedClassRecipe
public import Oberwolfach.RetainedRawIntervalRootUpperGeneral

@[expose] public section
/-! The sampled retained and raw interval roots at a hub have the needed
uniform upper bound for the actual assigned ordinary factor. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_assigned_root_count_upper_candidate_direct_reserve
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (hn:0<n) (hK:0<K) (m d:ℕ) (hm:7≤m) (hd:0<d)
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (Allowed:Set ℕ) (hAllowed:∀u,AllowedCycleLengths (F u) Allowed)
    (i₀:Fin K) (rsv θ:ℝ) (hrs0:0≤rsv) (hrs1:rsv≤1/100) (hθ:0<θ) (hθ1:θ≤1/100)
    (hClassReserve:OrdinaryClassReserveBound F hF i₀ rsv)
    (π:Equiv.Perm (Fin n)) (σ:RawIntervalFamilyOutcome (Fin n) U Bool Bool)
    (r:ℕ) (Jret:StartRetentionOutcome (rawStartHubSet π d σ false) r) (u:U)
    (hcounts:∀g,|rawIntervalHubStartCount π d g σ u-
      (n:ℝ)*ordinaryAssignedMarkedProbability F hF K θ ((m:ℝ)+1) u g/d|<(n:ℝ)^(3/4:ℝ)/d):
    (Fintype.card (retainedAndRawIntervalIndex π d σ false true r Jret u):ℝ)≤
      ((n:ℝ)+2*(n:ℝ)^(3/4:ℝ))/d:=by
  have hm8:8≤(m:ℝ)+1:=by
    have hh:8≤m+1:=by omega
    exact_mod_cast hh
  have hc0:0<(m:ℝ)+1:=by linarith
  have hreserve:=hClassReserve
  have hh:=ordinary_factor_actual_marginals hn (F u) (hF u) K hK i₀ rsv θ ((m:ℝ)+1)
    hrs0 hrs1 hθ.le hθ1 hm8 (hreserve u)
  have ha:ordinaryAssignedLongWeight F hF K θ ((m:ℝ)+1) u≤1/((m:ℝ)+1):=by
    simpa only [ordinaryAssignedLongWeight,ordinaryAssignedFraction] using hh.2.2.2.2.2.2.1
  have hone:1/((m:ℝ)+1)≤1:=(div_le_one₀ hc0).2 (by linarith)
  have hq:ordinaryAssignedMarkedProbability F hF K θ ((m:ℝ)+1) u false+
      ordinaryAssignedMarkedProbability F hF K θ ((m:ℝ)+1) u true≤1:=by
    simp only [ordinaryAssignedMarkedProbability,Bool.false_eq_true,ite_false,ite_true,zero_add]
    exact ha.trans hone
  have hroot:=retained_raw_interval_root_upper_general π d 1 hd (by omega) σ r Jret u
    (ordinaryAssignedMarkedProbability F hF K θ ((m:ℝ)+1) u) ((n:ℝ)^(3/4:ℝ)) hcounts
  simp only [Nat.cast_one,one_mul] at hroot
  have hqN:=mul_le_mul_of_nonneg_left hq (show (0:ℝ)≤n by positivity)
  have hd0:0<(d:ℝ):=by exact_mod_cast hd
  apply (le_div_iff₀ hd0).2
  nlinarith
end Oberwolfach
