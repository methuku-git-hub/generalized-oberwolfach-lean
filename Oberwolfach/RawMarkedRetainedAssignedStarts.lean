module

public import Oberwolfach.RawAssignedStartsHighProbability
public import Oberwolfach.RawMarkedRetention
public import Oberwolfach.FiniteProductProjection

@[expose] public section
/-! Pair and start-column events survive projection to the retained marked law. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem raw_marked_retained_assigned_starts_high_probability
    (d:ℕ) (hd:2≤d) (δ:ℝ) (hδ:0<δ):
    ∃N:ℕ,∀(V:Type) [Fintype V] [LinearOrder V] [Nonempty V],N≤Fintype.card V→
    ∀(U Color:Type) [Fintype U] [DecidableEq U] [Fintype Color],
    0<Fintype.card U→Fintype.card U≤Fintype.card V→
    ∀(π:Equiv.Perm V) (p k:ℝ) (hp:0≤p) (hk:0≤k) (hphys:2*p+2*k≤1)
    (q:U→Bool→ℝ) (hq:∀u g,0≤q u g) (hQ:∀u,∑g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀u j,0≤s u j) (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑g,q u g))
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x),
    1-δ≤(rawMarkedRetentionLaw π d hd false p k hp hk hphys q hq hQ s hs hS).probability
      (fun z=>
        (∀v g,|rawIntervalAssignedLabelColumnCount π d (fun e=>z.1 (Sum.inr e)) v g Finset.univ-∑u,q u g|<(Fintype.card V:ℝ)^(3/4:ℝ)) ∧
        ∀v g,|rawIntervalStartColumnCount π d (fun e=>z.1 (Sum.inr e)) v g Finset.univ-∑u,q u g/(d:ℝ)|<(Fintype.card V:ℝ)^(3/4:ℝ)):=by
  obtain ⟨N,hN⟩:=raw_assigned_and_start_columns_high_probability d hd δ hδ
  refine ⟨N,?_⟩
  intro V _ _ _ hn U Color _ _ _ hU0 hU π p k hp hk hphys q hq hQ s hs hS hnoshort
  let E:=fun (σ:RawIntervalFamilyOutcome V U Bool Color)=>
    (∀v g,|rawIntervalAssignedLabelColumnCount π d σ v g Finset.univ-∑u,q u g|<(Fintype.card V:ℝ)^(3/4:ℝ)) ∧
    ∀v g,|rawIntervalStartColumnCount π d σ v g Finset.univ-∑u,q u g/(d:ℝ)|<(Fintype.card V:ℝ)^(3/4:ℝ)
  have hh:=hN V hn U Color hU0 hU π q hq hQ s hs hS hnoshort
  have heq:(rawMarkedRetentionLaw π d hd false p k hp hk hphys q hq hQ s hs hS).probability
      (fun z=>E (fun e=>z.1 (Sum.inr e)))=
      (FiniteLaw.pi (rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS)).probability E:=by
    calc
      _ = (FiniteLaw.pi (rawMarkedWheelLaw p k hp hk hphys d hd q hq hQ s hs hS)).probability
          (fun σ=>E (fun e=>σ (Sum.inr e))):=by
        exact rawMarkedRetentionLaw_raw_projection π d hd false p k hp hk hphys q hq hQ s hs hS (fun σ=>E (fun e=>σ (Sum.inr e)))
      _ = _:=by
        exact finiteLaw_pi_injective_projection_event (rawMarkedWheelLaw p k hp hk hphys d hd q hq hQ s hs hS)
          (Sum.inr:(U×RawIntervalCoordinate V)→RawWheelCoordinate V U) Sum.inr_injective E
  change 1-δ≤(rawMarkedRetentionLaw π d hd false p k hp hk hphys q hq hQ s hs hS).probability (fun z=>E (fun e=>z.1 (Sum.inr e)))
  rw [heq]
  exact hh
end Oberwolfach
