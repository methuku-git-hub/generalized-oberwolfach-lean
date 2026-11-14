module

public import Oberwolfach.MarkedPartitionedResidualDegrees
public import Oberwolfach.RetainedMarkedSpokeChanges
public import Oberwolfach.RetainedIntervalIdentities

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U] [Fintype Γ] [Fintype Color]
local instance residualSpokeBalanceDecEq : DecidableEq V := Classical.decEq V
local instance residualSpokeBalanceArc (P:V×V→Prop):DecidableEq {e:V×V // P e}:=Classical.decEq _
local instance residualSpokeBalanceArcFinite (P:V×V→Prop):Fintype {e:V×V // P e}:=Fintype.ofFinite _
local instance residualSpokeBalanceMarkedFinite (P:V×V→Prop) (M:Finset {e:V×V // P e}):Fintype (residualMarkedArc P M):=by
  change Fintype {e:{a:V×V // P a} // e∈M}
  exact Fintype.ofFinite _

theorem long_residual_marked_head_spoke_balance
    (P:V×V→Prop) (M:Finset {e:V×V // P e}) (π:Equiv.Perm V) (d:ℕ) (hd:1≤d)
    (hnoshort:∀x l,0<l→l<d→(π^l) x≠x)
    (σ:RawIntervalFamilyOutcome V U Γ Color) (g:Γ) (j:Color) (t:ℕ)
    (J:StartRetentionOutcome (rawStartHubSet π d σ g) t)
    (hbalance:∀v,directedInCount P M v=d*t):
    ∀v,occurrenceDegree (fun e:residualMarkedArc P M=>π.symm e.val.val.2) v=
      ∑u,if retainedRawMarkedSpokes π d σ g t J g j true v u then (1:ℝ) else 0:=by
  intro v
  rw [partitioned_marked_head_degree,hbalance]
  have hc:=retainedRawFamily_covered_card π d hd hnoshort σ g t J v
  have hsum:(∑u,if retainedRawMarkedSpokes π d σ g t J g j true v u then (1:ℝ) else 0)=
      ((Finset.univ.filter (fun u=>retainedRawFamilyState π d σ g t J (v,u)=some (Sum.inl g))).card:ℝ):=by
    rw [Finset.card_filter,Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro u hu
    by_cases h:retainedRawFamilyState π d σ g t J (v,u)=some (Sum.inl g) <;> simp [retainedRawMarkedSpokes,h]
  rw [hsum,hc]
end Oberwolfach
