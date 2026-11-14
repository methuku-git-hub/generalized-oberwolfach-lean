module

public import Oberwolfach.FirstVortexExpandedSixLocalTests
public import Oberwolfach.FirstVortexExpandedUnassignedAllHubsProbability

@[expose] public section
/-! Named unassigned-count tests on all hubs. The six-test event already
provides the first of these two bounds at the stronger local scale. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [LinearOrder V] [Nonempty V] [Fintype U] [DecidableEq U]

def FirstVortexExpandedAllHubTests (G:SimpleGraph V) (π:Equiv.Perm V) (d D m:ℕ) (β ε:ℝ)
    (Q:Vortex U G D β ε m) (q s:U→Bool→ℝ) (z:MarkedExpandedActualOutcome (U:=U) π d):Prop:=
    (∀u,|rawIntervalUnassignedHubCountOn π d (fun e=>z.1 (Sum.inr e)) u (Q.extendedVertices 1)-
      ((Q.extendedVertices 1).card:ℝ)*(1-(∑g,q u g)-(∑j,s u j))|<(Fintype.card V:ℝ)^(3/4:ℝ)) ∧
    (∀v,|rawIntervalUnassignedColumnCount π d (fun e=>z.1 (Sum.inr e)) v Finset.univ-
      ∑u:U,(1-(∑g,q u g)-(∑j,s u j))|<(Fintype.card V:ℝ)^(3/4:ℝ))

theorem first_vortex_expanded_six_tests_all_hub_rows
    (G:SimpleGraph V) (π:Equiv.Perm V) (d D m:ℕ) (β ε:ℝ)
    (Q:Vortex U G D β ε m) (q s:U→Bool→ℝ) (u ζ:ℝ)
    (z:MarkedExpandedActualOutcome (U:=U) π d)
    (h:FirstVortexExpandedSixLocalTests G π d D m β ε Q q s u ζ z):
    ∀w,|rawIntervalUnassignedHubCountOn π d (fun e=>z.1 (Sum.inr e)) w (Q.extendedVertices 1)-
      ((Q.extendedVertices 1).card:ℝ)*(1-(∑g,q w g)-(∑j,s w j))|<(Fintype.card V:ℝ)^(3/4:ℝ):=by
  have hcard:((Q.extendedVertices 1).card:ℝ)≤Fintype.card V:=by exact_mod_cast Finset.card_le_univ _
  have hpow:=Real.rpow_le_rpow (Nat.cast_nonneg (Q.extendedVertices 1).card) hcard (by norm_num:(0:ℝ)≤3/4)
  intro w
  exact lt_of_lt_of_le (h.2.1 w) hpow
end Oberwolfach
