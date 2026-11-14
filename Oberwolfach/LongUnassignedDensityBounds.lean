module

public import Oberwolfach.LongAssignedUnassignedUpper
public import Oberwolfach.LongAssignedUnassignedSlack
public import Oberwolfach.Vortex

@[expose] public section

set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_unassigned_density_bounds
    {n K m D:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (hn:0<n) (hK:0<K) (hm:0<m) (hD:0<D)
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (θ:ℝ) (hθ:0≤θ) (hθ1:θ≤1) (hρ:initialIndexDensity U D≤1):
    let u:=2*(∑w:U,(1-(1/100:ℝ)-(1/100:ℝ)/(m:ℝ)-
      longAssignedApproxMarkedWeight F hF K m θ w-longAssignedApproxOrdinaryWeight F hF K m θ w))/(D:ℝ)
    0≤u ∧ u≤2*θ:=by
  intro u
  let p:=fun w:U=>1-(∑g:Bool,longAssignedIntervalProbability F hF K m θ w g)-
      (∑j:Bool,longAssignedSpokeProbability F hF K m θ w j)
  have hp0:∀w,0≤p w:=by
    intro w
    exact hθ.trans (long_assigned_unassigned_probability_at_least_theta hn F hF K m hm θ hθ1 w)
  have hp2:∀w,p w≤2*θ:=fun w=>long_assigned_unassigned_probability_at_most_two_theta hn hK m hm F hF θ hθ hθ1 w
  have hsum0:0≤∑w:U,p w:=Finset.sum_nonneg (by intro w hw;exact hp0 w)
  have hsum:(∑w:U,p w)≤(Fintype.card U:ℝ)*(2*θ):=by
    calc
      _ ≤ ∑_w:U,2*θ:=Finset.sum_le_sum (by intro w hw;exact hp2 w)
      _ = _:=by simp [mul_comm]
  have hDpos:(0:ℝ)<D:=by exact_mod_cast hD
  have hmass:2*(Fintype.card U:ℝ)≤D:=by
    have hh:=(div_le_iff₀ hDpos).1 hρ
    simpa [initialIndexDensity] using hh
  have heq:u=2*(∑w:U,p w)/(D:ℝ):=by
    dsimp [u,p]
    congr 2
    apply Finset.sum_congr rfl
    intro w hw
    simp [Fintype.sum_bool,longAssignedIntervalProbability,longAssignedSpokeProbability]
    ring
  rw [heq]
  constructor
  · positivity
  · apply (div_le_iff₀ hDpos).2
    have hh:=mul_le_mul_of_nonneg_left hmass (show 0≤θ by exact hθ)
    nlinarith only [hsum,hh]
end Oberwolfach
