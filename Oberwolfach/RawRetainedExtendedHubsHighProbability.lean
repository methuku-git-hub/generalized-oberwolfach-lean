module

public import Oberwolfach.RawMarkedRetainedAssignedStarts
public import Oberwolfach.RawIntervalExtendedHubsUpper
public import Oberwolfach.FiniteLawIntersectionLower

@[expose] public section
/-! The global interval-load bound holds with arbitrarily high probability
on the retained sample, without imposing a pair-availability spacing bound. -/
set_option autoImplicit false
set_option maxHeartbeats 16000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem raw_retained_extended_hubs_high_probability
    (d:ℕ) (hd:2≤d) (δ:ℝ) (hδ:0<δ):
    ∃N:ℕ,∀(V:Type) [Fintype V] [LinearOrder V] [Nonempty V],N≤Fintype.card V→
    ∀(U Color:Type) [Fintype U] [DecidableEq U] [Fintype Color],
    0<Fintype.card U→Fintype.card U≤Fintype.card V→
    ∀(π:Equiv.Perm V) (p k:ℝ) (hp:0≤p) (hk:0≤k) (hphys:2*p+2*k≤1)
    (q:U→Bool→ℝ) (hq:∀u g,0≤q u g) (hQ:∀u,∑g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀u j,0≤s u j) (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑g,q u g))
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (m:ℝ) (hm:0<m) (hqBound:∀u g,q u g≤1/m),
    1-δ≤(rawMarkedRetentionLaw π d hd false p k hp hk hphys q hq hQ s hs hS).probability
      (fun z=>∀v,((rawIntervalExtendedAnyHubSet π d (fun e=>z.1 (Sum.inr e)) v).card:ℝ)≤
        4*(Fintype.card U:ℝ)/m+4*(Fintype.card V:ℝ)^(3/4:ℝ)) := by
  obtain ⟨N,hN⟩:=raw_marked_retained_assigned_starts_high_probability d hd δ hδ
  refine ⟨N,?_⟩
  intro V _ _ _ hn U Color _ _ _ hU0 hU π p k hp hk hphys q hq hQ s hs hS hnoshort m hm hqBound
  have hh:=hN V hn U Color hU0 hU π p k hp hk hphys q hq hQ s hs hS hnoshort
  apply hh.trans
  apply finiteLaw_probability_mono
  intro z hz
  exact raw_interval_extended_any_hubs_upper π d (by omega) (fun e=>z.1 (Sum.inr e)) q m
    ((Fintype.card V:ℝ)^(3/4:ℝ)) hm hq hqBound hz.1 hz.2
end Oberwolfach
