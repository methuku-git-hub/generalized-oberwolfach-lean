module

public import Oberwolfach.RawMarkedRetainedPairsStarts
public import Oberwolfach.RawMarkedRetainedAssignedStarts
public import Oberwolfach.FiniteLawIntersectionLower

@[expose] public section
/-! Pair availability, interval occupancy and start-column estimates all hold
on one retained outcome with arbitrarily high probability. -/
set_option autoImplicit false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem raw_marked_retained_pairs_assigned_starts_high_probability
    (d:ℕ) (hd:2≤d) (θ δ:ℝ) (hθ:0<θ) (hδ:0<δ) (hspace:1/(8*(d:ℝ))≤θ/2):
    ∃N:ℕ,∀(V:Type) [Fintype V] [LinearOrder V] [Nonempty V],N≤Fintype.card V→
    ∀(U Color:Type) [Fintype U] [DecidableEq U] [Fintype Color],
    0<Fintype.card U→Fintype.card U≤Fintype.card V→
    ∀(π:Equiv.Perm V) (p k:ℝ) (hp:0≤p) (hk:0≤k) (hphys:2*p+2*k≤1)
    (q:U→Bool→ℝ) (hq:∀u g,0≤q u g) (hQ:∀u,∑g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀u j,0≤s u j) (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑g,q u g))
    (hrem:∀u,θ≤1-(∑g,q u g)-(∑j,s u j))
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x),
    1-δ≤(rawMarkedRetentionLaw π d hd false p k hp hk hphys q hq hQ s hs hS).probability
      (fun z=>
        (∀x y,x≠y→(5/32:ℝ)*θ^2*Fintype.card U-(Fintype.card V:ℝ)^(3/4:ℝ)≤
          rawIntervalUnassignedPairColumnCount π d (fun e=>z.1 (Sum.inr e)) x y Finset.univ) ∧
        (∀v g,|rawIntervalAssignedLabelColumnCount π d (fun e=>z.1 (Sum.inr e)) v g Finset.univ-∑u,q u g|<(Fintype.card V:ℝ)^(3/4:ℝ)) ∧
        ∀v g,|rawIntervalStartColumnCount π d (fun e=>z.1 (Sum.inr e)) v g Finset.univ-∑u,q u g/(d:ℝ)|<(Fintype.card V:ℝ)^(3/4:ℝ)):=by
  have hhalf:0<δ/2:=by linarith
  obtain ⟨N₁,h₁⟩:=raw_marked_retained_pairs_starts_high_probability d hd θ (δ/2) hθ hhalf hspace
  obtain ⟨N₂,h₂⟩:=raw_marked_retained_assigned_starts_high_probability d hd (δ/2) hhalf
  refine ⟨max N₁ N₂,?_⟩
  intro V _ _ _ hn U Color _ _ _ hU0 hU π p k hp hk hphys q hq hQ s hs hS hrem hnoshort
  let μ:=rawMarkedRetentionLaw π d hd false p k hp hk hphys q hq hQ s hs hS
  let A:=fun z:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d false=>
    (∀x y,x≠y→(5/32:ℝ)*θ^2*Fintype.card U-(Fintype.card V:ℝ)^(3/4:ℝ)≤
      rawIntervalUnassignedPairColumnCount π d (fun e=>z.1 (Sum.inr e)) x y Finset.univ) ∧
    ∀v g,|rawIntervalStartColumnCount π d (fun e=>z.1 (Sum.inr e)) v g Finset.univ-∑u,q u g/(d:ℝ)|<(Fintype.card V:ℝ)^(3/4:ℝ)
  let B:=fun z:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d false=>
    (∀v g,|rawIntervalAssignedLabelColumnCount π d (fun e=>z.1 (Sum.inr e)) v g Finset.univ-∑u,q u g|<(Fintype.card V:ℝ)^(3/4:ℝ)) ∧
    ∀v g,|rawIntervalStartColumnCount π d (fun e=>z.1 (Sum.inr e)) v g Finset.univ-∑u,q u g/(d:ℝ)|<(Fintype.card V:ℝ)^(3/4:ℝ)
  have hA:1-δ/2≤μ.probability A:=h₁ V (by omega) U Color hU0 hU π p k hp hk hphys q hq hQ s hs hS hrem hnoshort
  have hB:1-δ/2≤μ.probability B:=h₂ V (by omega) U Color hU0 hU π p k hp hk hphys q hq hQ s hs hS hnoshort
  have hh:=finiteLaw_intersection_lower μ A B (δ/2) (δ/2) hA hB
  have hh':1-δ≤μ.probability (fun z=>A z ∧ B z):=by linarith
  apply hh'.trans
  apply finiteLaw_probability_mono
  intro z hz
  exact ⟨hz.1.1,hz.2.1,hz.1.2⟩
end Oberwolfach
