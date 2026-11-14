module

public import Oberwolfach.OrdinaryClassReserveBound
public import Oberwolfach.CandidateOrdinaryAssignedUnassignedSlack
public import Oberwolfach.OrdinaryAssignedUnassignedSlack
public import Oberwolfach.OrdinaryCandidateClassReservation
public import Oberwolfach.CandidateOrdinaryAssignedSamplingParametersDirectReserve
public import Oberwolfach.OrdinaryAssignedClassRecipe

@[expose] public section
/-! The actual assigned-factor marginals leave the manuscript's required
positive unassigned fraction at every hub. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_assigned_unassigned_slack_candidate_direct_reserve
    {n:ℕ} (hn:0<n) {U:Type} [Fintype U]
    (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (K:ℕ) (hK:0<K) (i₀:Fin K) (rsv θ c ρ D:ℝ) (d:ℕ) (hd:2≤d)
    (hs0:0≤rsv) (hs1:rsv≤1/100) (hθ:0<θ) (hθ1:θ≤1/100) (hc:8≤c)
    (hda:1/θ≤d) (hρ:0<ρ) (hρ1:ρ≤1) (hD:0<D) (hsize:ρ*D=2*(Fintype.card U:ℝ))
    (S:Set ℕ) (hS:∀w,AllowedCycleLengths (F w) S)
    (hClassReserve:OrdinaryClassReserveBound F hF i₀ rsv):
    let q:=ordinaryAssignedMarkedProbability F hF K θ c
    let s:=ordinaryAssignedSpokeProbability F hF K i₀ rsv θ c;
    (∀w,θ/2≤1-(∑g,q w g)-(∑j,s w j) ∧ 1-(∑g,q w g)-(∑j,s w j)≤2*θ) ∧
    1/(8*(d:ℝ))≤(θ/2)/2 :=by
  have h:=ordinary_class_assigned_sampling_parameters_candidate_direct_reserve hn F hF K hK i₀ rsv θ c ρ D d hd
    hs0 hs1 hθ hθ1 hc hda hρ hρ1 hD hsize S hS hClassReserve
  intro q s
  constructor
  · intro w
    have hw:=h.1 w
    have hlo:θ/2≤1-rsv-ordinaryAssignedLongWeight F hF K θ c w-ordinaryAssignedShortWeight F hF K i₀ rsv θ c w:=by
      convert hw.2.2.2.1 using 1 <;>
        simp only [ordinaryAssignedShortWeight,ordinaryAssignedLongWeight,ordinaryAssignedFraction]
    have hhi:1-rsv-ordinaryAssignedLongWeight F hF K θ c w-ordinaryAssignedShortWeight F hF K i₀ rsv θ c w≤2*θ:=by
      convert hw.2.2.2.2.1 using 1 <;>
        simp only [ordinaryAssignedShortWeight,ordinaryAssignedLongWeight,ordinaryAssignedFraction]
    dsimp only [q,s,ordinaryAssignedMarkedProbability,ordinaryAssignedSpokeProbability]
    simp only [Fintype.sum_bool,Bool.false_eq_true,ite_false,ite_true]
    constructor <;> linarith
  · have hdR:0<(d:ℝ):=by exact_mod_cast (show 0<d by omega)
    have hθd:1≤(d:ℝ)*θ:=(div_le_iff₀ hθ).1 hda
    apply (div_le_iff₀ (show 0<8*(d:ℝ) by positivity)).2
    nlinarith
end Oberwolfach
