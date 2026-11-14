module

public import Oberwolfach.ExpandedIntervalArbitraryStage
public import Oberwolfach.RawAssignedStartsHighProbability
public import Oberwolfach.RawIntervalExtendedHubsUpper

@[expose] public section
/-! The extended interval occupancy bound holds on the expanded sample and
survives any dependent second sampling stage. -/
set_option autoImplicit false
set_option maxHeartbeats 16000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem expanded_interval_occupancy_high
    (d:ℕ) (hd:2≤d) (δ:ℝ) (hδ:0<δ):
    ∃N:ℕ,∀(V U Color:Type) [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U] [Fintype Color],
    N≤Fintype.card V→0<Fintype.card U→Fintype.card U≤Fintype.card V→
    ∀(π:Equiv.Perm V) (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (q:U→Bool→ℝ) (hq:∀w g,0≤q w g) (hQ:∀w,∑g,q w g≤1/8)
    (s:U→Color→ℝ) (hs:∀w j,0≤s w j) (hS:∀w,∑j,s w j ≤ intervalUncoveredProbability d (∑g,q w g))
    (m:ℝ) (hm:0<m) (hqBound:∀w g,q w g≤1/m)
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    {R:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Bool Color e)→Type}
    [∀σ,Fintype (R σ)] (ν:∀σ,FiniteLaw (R σ)),
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS);
    1-δ≤(μ.sigma ν).probability (fun z=>∀v,
      ((rawIntervalExtendedAnyHubSet π d (fun e=>z.1 (Sum.inr e)) v).card:ℝ)≤
        4*(Fintype.card U:ℝ)/m+4*(Fintype.card V:ℝ)^(3/4:ℝ)):=by
  obtain ⟨N,hN⟩:=raw_assigned_and_start_columns_high_probability d hd δ hδ
  refine ⟨N,?_⟩
  intro V U Color _ _ _ _ _ hn hU0 hU π p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum q hq hQ s hs hS m hm hqBound hnoshort R _ ν μ
  let E:RawIntervalFamilyOutcome V U Bool Color→Prop:=fun σ=>∀v,
    ((rawIntervalExtendedAnyHubSet π d σ v).card:ℝ)≤
      4*(Fintype.card U:ℝ)/m+4*(Fintype.card V:ℝ)^(3/4:ℝ)
  have hRaw:=hN V hn U Color hU0 hU π q hq hQ s hs hS hnoshort
  have hOcc:1-δ≤(FiniteLaw.pi (rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS)).probability E:=by
    apply hRaw.trans
    apply finiteLaw_probability_mono
    intro σ h
    exact raw_interval_extended_any_hubs_upper π d (by omega) σ q m ((Fintype.card V:ℝ)^(3/4:ℝ)) hm hq hqBound h.1 h.2
  have hProj:=expanded_interval_event_probability_arbitrary_stage d hd p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum q hq hQ s hs hS ν E
  change 1-δ≤(μ.sigma ν).probability (fun z=>E (fun e=>z.1 (Sum.inr e)))
  exact hProj.symm ▸ hOcc
end Oberwolfach
