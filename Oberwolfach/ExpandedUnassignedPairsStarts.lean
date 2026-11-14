module

public import Oberwolfach.ExpandedIntervalArbitraryStage
public import Oberwolfach.RawUnassignedPairsStartsHighProbability

@[expose] public section
/-! Pair availability and interval-start columns retain their high-probability
bound on an expanded sample with any dependent second stage. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem expanded_unassigned_pairs_starts_high
    (d:ℕ) (hd:2≤d) (θ ζ:ℝ) (hθ:0<θ) (hζ:0<ζ) (hspace:1/(8*(d:ℝ))≤θ/2):
    ∃N:ℕ,∀(V U Color:Type) [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U] [Fintype Color],
    N≤Fintype.card V→0<Fintype.card U→Fintype.card U≤Fintype.card V→
    ∀(π:Equiv.Perm V) (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (q:U→Bool→ℝ) (hq:∀w g,0≤q w g) (hQ:∀w,∑g,q w g≤1/8)
    (s:U→Color→ℝ) (hs:∀w j,0≤s w j) (hS:∀w,∑j,s w j ≤ intervalUncoveredProbability d (∑g,q w g))
    (hrem:∀w,θ≤1-(∑g,q w g)-(∑j,s w j))
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    {R:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Bool Color e)→Type}
    [∀σ,Fintype (R σ)] (ν:∀σ,FiniteLaw (R σ)),
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS);
    1-ζ≤(μ.sigma ν).probability (fun z=>
      (∀x y,x≠y→(5/32:ℝ)*θ^2*Fintype.card U-(Fintype.card V:ℝ)^(3/4:ℝ)≤
        rawIntervalUnassignedPairColumnCount π d (fun e=>z.1 (Sum.inr e)) x y Finset.univ) ∧
      ∀v g,|rawIntervalStartColumnCount π d (fun e=>z.1 (Sum.inr e)) v g Finset.univ-∑w,q w g/(d:ℝ)|<(Fintype.card V:ℝ)^(3/4:ℝ)) :=by
  obtain ⟨N,hN⟩:=raw_unassigned_pairs_and_starts_high_probability d hd θ ζ hθ hζ hspace
  refine ⟨N,?_⟩
  intro V U Color _ _ _ _ _ hn hU0 hU π p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum q hq hQ s hs hS hrem hnoshort R _ ν μ
  let E:RawIntervalFamilyOutcome V U Bool Color→Prop:=fun σ=>
      (∀x y,x≠y→(5/32:ℝ)*θ^2*Fintype.card U-(Fintype.card V:ℝ)^(3/4:ℝ)≤
        rawIntervalUnassignedPairColumnCount π d σ x y Finset.univ) ∧
      ∀v g,|rawIntervalStartColumnCount π d σ v g Finset.univ-∑w,q w g/(d:ℝ)|<(Fintype.card V:ℝ)^(3/4:ℝ)
  have hRaw:=hN V hn U Color hU0 hU π q hq hQ s hs hS hrem hnoshort
  have hProj:=expanded_interval_event_probability_arbitrary_stage d hd p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum q hq hQ s hs hS ν E
  change 1-ζ≤(μ.sigma ν).probability (fun z=>E (fun e=>z.1 (Sum.inr e)))
  exact hProj.symm ▸ hRaw
end Oberwolfach
