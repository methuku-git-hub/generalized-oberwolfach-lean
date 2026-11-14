module

public import Oberwolfach.RawIntervalExtendedHubLossOn
public import Oberwolfach.RawIntervalExtendedHubsUpper
public import Oberwolfach.RawIntervalExtendedHubLoss

@[expose] public section
/-! Two interval colours occupy few hub columns at any fixed vertex when
their original marginal probabilities are small. -/
set_option autoImplicit false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem raw_interval_extended_any_hubs_upper_on
    {V U Color:Type} [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U] [Fintype Color]
    (π:Equiv.Perm V) (d:ℕ) (hd:0<d) (σ:RawIntervalFamilyOutcome V U Bool Color)
    (q:U→Bool→ℝ) (A:Finset V) (J:Finset U) (m t:ℝ) (hm:0<m) (hq0:∀u g,0≤q u g) (hq:∀u g,q u g≤1/m)
    (hLabel:∀v ∈ A, ∀g,|rawIntervalAssignedLabelColumnCount π d σ v g J-∑u ∈ J,q u g|<t)
    (hStart:∀v ∈ A, ∀g,|rawIntervalStartColumnCount π d σ ((π^d).symm v) g J-∑u ∈ J,q u g/(d:ℝ)|<t):
    ∀v ∈ A,((rawIntervalExtendedAnyHubSet π d σ v ∩ J).card:ℝ)≤4*(J.card:ℝ)/m+4*t:=by
  have hdR:1≤(d:ℝ):=by exact_mod_cast hd
  have hmean:∀g,(∑u ∈ J,q u g)≤(J.card:ℝ)/m:=by
    intro g
    calc
      _ ≤ ∑_u ∈ J,(1/m):=Finset.sum_le_sum (fun u _=>hq u g)
      _ = _:=by simp [div_eq_mul_inv,mul_comm]
  have hmean0:∀g,0≤∑u ∈ J,q u g:=fun g=>Finset.sum_nonneg (fun u _=>hq0 u g)
  have hstartMean:∀g,(∑u ∈ J,q u g/(d:ℝ))≤(J.card:ℝ)/m:=by
    intro g
    rw [←Finset.sum_div]
    exact (div_le_self (hmean0 g) hdR).trans (hmean g)
  have hone:∀v ∈ A, ∀g,((rawIntervalExtendedHubSet π d σ v g ∩ J).card:ℝ)≤2*(J.card:ℝ)/m+2*t:=by
    intro v hv g
    have hh:=raw_interval_extended_hub_count_bound_on π d hd σ v g J
    have ha:rawIntervalAssignedLabelColumnCount π d σ v g J< (∑u ∈ J,q u g)+t:=by
      have h:=(abs_lt.mp (hLabel v hv g)).2
      linarith
    have hs:rawIntervalStartColumnCount π d σ ((π^d).symm v) g J< (∑u ∈ J,q u g/(d:ℝ))+t:=by
      have h:=(abs_lt.mp (hStart v hv g)).2
      linarith
    have heq:2*(J.card:ℝ)/m=2*((J.card:ℝ)/m):=by ring
    rw [heq]
    linarith [hmean g,hstartMean g]
  intro v hv
  have hcard:=Finset.card_union_le (rawIntervalExtendedHubSet π d σ v false ∩ J) (rawIntervalExtendedHubSet π d σ v true ∩ J)
  have hcardR:((rawIntervalExtendedAnyHubSet π d σ v ∩ J).card:ℝ)≤
      (rawIntervalExtendedHubSet π d σ v false ∩ J).card+(rawIntervalExtendedHubSet π d σ v true ∩ J).card:=by
    unfold rawIntervalExtendedAnyHubSet
    rw [Finset.union_inter_distrib_right]
    exact_mod_cast hcard
  have heq:4*(J.card:ℝ)/m=4*((J.card:ℝ)/m):=by ring
  rw [heq]
  have hh₀:=hone v hv false
  have hh₁:=hone v hv true
  rw [show 2*(J.card:ℝ)/m=2*((J.card:ℝ)/m) by ring] at hh₀ hh₁
  linarith
end Oberwolfach
