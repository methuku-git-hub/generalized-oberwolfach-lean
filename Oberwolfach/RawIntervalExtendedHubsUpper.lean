module

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

def rawIntervalExtendedAnyHubSet {V U Color:Type} [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]
    [Fintype Color] (π:Equiv.Perm V) (d:ℕ) (σ:RawIntervalFamilyOutcome V U Bool Color) (x:V):Finset U:=
  rawIntervalExtendedHubSet π d σ x false∪rawIntervalExtendedHubSet π d σ x true

theorem raw_interval_extended_any_hubs_upper
    {V U Color:Type} [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U] [Fintype Color]
    (π:Equiv.Perm V) (d:ℕ) (hd:0<d) (σ:RawIntervalFamilyOutcome V U Bool Color)
    (q:U→Bool→ℝ) (m t:ℝ) (hm:0<m) (hq0:∀u g,0≤q u g) (hq:∀u g,q u g≤1/m)
    (hLabel:∀v g,|rawIntervalAssignedLabelColumnCount π d σ v g Finset.univ-∑u,q u g|<t)
    (hStart:∀v g,|rawIntervalStartColumnCount π d σ v g Finset.univ-∑u,q u g/(d:ℝ)|<t):
    ∀v,((rawIntervalExtendedAnyHubSet π d σ v).card:ℝ)≤4*(Fintype.card U:ℝ)/m+4*t:=by
  have hdR:1≤(d:ℝ):=by exact_mod_cast hd
  have hmean:∀g,(∑u,q u g)≤(Fintype.card U:ℝ)/m:=by
    intro g
    calc
      _ ≤ ∑_u:U,(1/m):=Finset.sum_le_sum (fun u _=>hq u g)
      _ = _:=by simp [div_eq_mul_inv,mul_comm]
  have hmean0:∀g,0≤∑u,q u g:=fun g=>Finset.sum_nonneg (fun u _=>hq0 u g)
  have hstartMean:∀g,(∑u,q u g/(d:ℝ))≤(Fintype.card U:ℝ)/m:=by
    intro g
    rw [←Finset.sum_div]
    exact (div_le_self (hmean0 g) hdR).trans (hmean g)
  have hone:∀v g,((rawIntervalExtendedHubSet π d σ v g).card:ℝ)≤2*(Fintype.card U:ℝ)/m+2*t:=by
    intro v g
    have hh:=raw_interval_extended_hub_count_bound π d hd σ v g
    have ha:rawIntervalAssignedLabelColumnCount π d σ v g Finset.univ< (∑u,q u g)+t:=by
      have h:=(abs_lt.mp (hLabel v g)).2
      linarith
    have hs:rawIntervalStartColumnCount π d σ ((π^d).symm v) g Finset.univ< (∑u,q u g/(d:ℝ))+t:=by
      have h:=(abs_lt.mp (hStart ((π^d).symm v) g)).2
      linarith
    have heq:2*(Fintype.card U:ℝ)/m=2*((Fintype.card U:ℝ)/m):=by ring
    rw [heq]
    linarith [hmean g,hstartMean g]
  intro v
  have hcard:=Finset.card_union_le (rawIntervalExtendedHubSet π d σ v false) (rawIntervalExtendedHubSet π d σ v true)
  have hcardR:((rawIntervalExtendedAnyHubSet π d σ v).card:ℝ)≤
      (rawIntervalExtendedHubSet π d σ v false).card+(rawIntervalExtendedHubSet π d σ v true).card:=by
    unfold rawIntervalExtendedAnyHubSet
    exact_mod_cast hcard
  have heq:4*(Fintype.card U:ℝ)/m=4*((Fintype.card U:ℝ)/m):=by ring
  rw [heq]
  have hh₀:=hone v false
  have hh₁:=hone v true
  rw [show 2*(Fintype.card U:ℝ)/m=2*((Fintype.card U:ℝ)/m) by ring] at hh₀ hh₁
  linarith
end Oberwolfach
