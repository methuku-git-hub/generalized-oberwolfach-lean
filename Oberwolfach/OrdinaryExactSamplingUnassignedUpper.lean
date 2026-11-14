module

public import Oberwolfach.OrdinaryAssignedVortexExactSamplingData
public import Oberwolfach.CandidateOrdinaryAssignedSamplingParametersDirectReserve

@[expose] public section
/-! The exact original sampling law has at most twice the matching slack
in its unassigned physical state. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
open scoped BigOperators

theorem ordinary_exact_sampling_unassigned_upper
    {n D:ℕ} (hn:0<n) (hD:0<D) {U:Type} [Fintype U] [DecidableEq U]
    (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (K:ℕ) (hK:0<K) (i₀:Fin K) (rsv θ c ρ₀ smin:ℝ) (d:ℕ) (hd:2 ≤ d)
    (hs0:0 ≤ rsv) (hs1:rsv ≤ 1/100) (hθ:0<θ) (hθ1:θ ≤ 1/100) (hc:8 ≤ c)
    (hda:1/θ ≤ d) (hρ:0 < initialIndexDensity U D) (hρ1:initialIndexDensity U D ≤ 1)
    (S:Set ℕ) (hS:∀w,AllowedCycleLengths (F w) S)
    (hClass:OrdinaryClassReserveBound F hF i₀ rsv)
    (sampling:OrdinaryAssignedVortexExactSamplingData (D:=D) F hF K i₀ rsv θ c ρ₀ smin d):
    sampling.u ≤ 2*θ :=by
  let ρ:=initialIndexDensity U D
  let a:=ordinaryAssignedLongWeight F hF K θ c
  let b:=ordinaryAssignedShortWeight F hF K i₀ rsv θ c
  let rem:=fun w=>1-rsv-a w-b w
  let unassigned:ℝ:=2*(∑w,rem w)/(D:ℝ)
  have hDr:0<(D:ℝ):=by exact_mod_cast hD
  have hsize:ρ*(D:ℝ)=2*(Fintype.card U:ℝ):=by
    simp [ρ,initialIndexDensity,ne_of_gt hDr]
  have hh:=ordinary_class_assigned_sampling_parameters_candidate_direct_reserve hn F hF K hK i₀ rsv θ c ρ D d hd
    hs0 hs1 hθ hθ1 hc hda hρ hρ1 hDr hsize S hS hClass
  rcases hh with ⟨hubs,hq,hqsum,hs,hssum,hp0,hp20,hu0,htotal,hcap,hpD,hplow,huid⟩
  have hrem:∀w,rem w ≤ 2*θ:=by
    intro w
    have hh:=(hubs w).2.2.2.2.1
    simpa only [rem,a,b,ordinaryAssignedShortWeight,ordinaryAssignedLongWeight,ordinaryAssignedFraction] using hh
  have hsum:(∑w,rem w) ≤ (Fintype.card U:ℝ)*(2*θ):=by
    calc
      _  ≤  ∑_w:U,2*θ:=Finset.sum_le_sum (by intro w hw;exact hrem w)
      _ = _ :=by simp
  have htotal':ρ*rsv+2*ordinaryAssignedApproxRimProbability F hF i₀ rsv θ c D+unassigned=ρ:=by
    convert htotal using 1 <;>
      simp only [ρ,unassigned,rem,a,b,ordinaryAssignedApproxRimProbability,ordinaryAssignedShortWeight,ordinaryAssignedLongWeight,ordinaryAssignedFraction] <;> ring
  have hsame:sampling.u=unassigned:=by
    have hp:=sampling.hphysical
    change 2*(ρ*rsv/2)+2*0+2*ordinaryAssignedApproxRimProbability F hF i₀ rsv θ c D+2*0+sampling.u=ρ at hp
    linarith
  have hρmul:ρ*(2*θ) ≤ 2*θ:=by nlinarith [hρ1,hθ]
  have hρD:=mul_le_mul_of_nonneg_right hρmul hDr.le
  have hsizeθ:=congrArg (fun x:ℝ=>(2*θ)*x) hsize
  have hbound:unassigned ≤ 2*θ:=by
    dsimp [unassigned]
    apply (div_le_iff₀ hDr).2
    nlinarith [hsum,hsizeθ,hρD]
  exact hsame.trans_le hbound
end Oberwolfach
