module

public import Oberwolfach.OrdinaryPlacementRecodeProbability
public import Oberwolfach.ExpandedSelectedNeighbourAnyStage
public import Oberwolfach.ExpandedSelectedTwoPathsAnyStage
public import Oberwolfach.FiniteLawIntersectionLower

@[expose] public section
/-! The two-path and unassigned-neighbour tests for the enlarged placement
colour can be added to any prior on the original sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_placement_recoded_tests_and_prior
    (d:ℕ) (hd:2≤d) (χ:ℝ) (hχ:0<χ):
    ∃N:ℕ,∀(V U Γ Color:Type) [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U] [Fintype Γ] [Fintype Color],
    N≤Fintype.card V→Fintype.card U≤Fintype.card V→
    ∀(P:SimpleGraph V) (π:Equiv.Perm V) (p k p₂ k₂ u:ℝ)
    (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u) (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (q:U→Γ→ℝ) (hq:∀w g,0≤q w g) (hQ:∀w,∑g,q w g≤1/8)
    (s:U→Color→ℝ) (hs:∀w j,0≤s w j) (hS:∀w,∑j,s w j ≤ intervalUncoveredProbability d (∑g,q w g))
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    {R:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)→Type}
    [∀σ,Fintype (R σ)] (ν:∀σ,FiniteLaw (R σ))
    (E:(Σσ,R σ)→Prop) (εE:ℝ),
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)
    let pfree:=p+u/2
    let Paths:=fun σ:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)=>∀x y,x≠y→
      ((P.neighborFinset x∩P.neighborFinset y).card:ℝ)*pfree^2-(Fintype.card V:ℝ)^(3/4:ℝ)-2*(2*((3*d:ℕ):ℝ)+1)≤
      ((Finset.univ.filter (fun v=>0<markedPhysicalRim P π (3*d)
        (fun e=>markedExpandedPhysicalCollapse (σ (Sum.inl e))) false x v ∧
        0<markedPhysicalRim P π (3*d)
        (fun e=>markedExpandedPhysicalCollapse (σ (Sum.inl e))) false v y)).card:ℝ)
    let Counts:=fun σ:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)=>∀w i,
      |rawIntervalUnassignedHubCountOn π d (fun e=>σ (Sum.inr e)) w
          (rawSelectedNeighbourTestSet P π d (fun e=>σ (Sum.inl e)) i)-
        (rawSelectedNeighbourTestSet P π d (fun e=>σ (Sum.inl e)) i).card*(1-(∑g,q w g)-(∑j,s w j))|<
          (Fintype.card V:ℝ)^(3/4:ℝ);
    1-εE≤(μ.sigma ν).probability E→
    1-(εE+2*χ)≤(μ.sigma ν).probability (fun z=>E z ∧
      Paths (fun e=>ordinaryPlacementWheelRecode e (z.1 e)) ∧ Counts (fun e=>ordinaryPlacementWheelRecode e (z.1 e))) :=by
  obtain ⟨Npaths,hpaths⟩:=expanded_selected_two_paths_any_stage d hd χ hχ
  obtain ⟨Ncounts,hcounts⟩:=expanded_selected_neighbour_tests_any_stage d hd χ hχ
  refine ⟨max Npaths Ncounts,?_⟩
  intro V U Γ Color _ _ _ _ _ _ hn hU P π p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum q hq hQ s hs hS hnoshort R _ ν E εE μ pfree Paths Counts hE
  let μ':=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) (p+u/2) k p₂ k₂ 0
    (by positivity) hk hp₂ hk₂ (by norm_num) (by linarith) d hd q hq hQ s hs hS)
  let νunit:=fun (_:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)=>FiniteLaw.uniform Unit
  have hp0:0≤p+u/2:=by positivity
  have hsum':2*(p+u/2)+2*k+2*p₂+2*k₂+0≤1:=by linarith
  have hp':1-χ≤μ'.probability Paths:=by
    have hh:1-χ≤(μ'.sigma νunit).probability (fun z=>Paths z.1):=by
      exact hpaths V U Γ Color (by omega) P π (p+u/2) k p₂ k₂ 0 hp0 hk hp₂ hk₂ (by norm_num) hsum' q hq hQ s hs hS νunit
    rw [finiteLaw_sigma_first_probability μ' νunit Paths] at hh
    exact hh
  have hc':1-χ≤μ'.probability Counts:=by
    have hh:1-χ≤(μ'.sigma νunit).probability (fun z=>Counts z.1):=by
      exact hcounts V U Γ Color (by omega) hU P π (p+u/2) k p₂ k₂ 0 hp0 hk hp₂ hk₂ (by norm_num) hsum' q hq hQ s hs hS hnoshort νunit
    rw [finiteLaw_sigma_first_probability μ' νunit Counts] at hh
    exact hh
  have hpSame:1-χ≤(μ.sigma ν).probability (fun z=>Paths (fun e=>ordinaryPlacementWheelRecode e (z.1 e))):=by
    rw [ordinary_placement_recode_probability_on_same_sample p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS ν Paths]
    exact hp'
  have hcSame:1-χ≤(μ.sigma ν).probability (fun z=>Counts (fun e=>ordinaryPlacementWheelRecode e (z.1 e))):=by
    rw [ordinary_placement_recode_probability_on_same_sample p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS ν Counts]
    exact hc'
  have hfirst:=finiteLaw_intersection_lower (μ.sigma ν) E
    (fun z=>Paths (fun e=>ordinaryPlacementWheelRecode e (z.1 e))) εE χ hE hpSame
  have hsecond:=finiteLaw_intersection_lower (μ.sigma ν)
    (fun z=>E z ∧ Paths (fun e=>ordinaryPlacementWheelRecode e (z.1 e)))
    (fun z=>Counts (fun e=>ordinaryPlacementWheelRecode e (z.1 e))) (εE+χ) χ
    (by linarith [hfirst]) hcSame
  have hfinal:1-(εE+2*χ)≤(μ.sigma ν).probability (fun z=>
      (E z ∧ Paths (fun e=>ordinaryPlacementWheelRecode e (z.1 e))) ∧ Counts (fun e=>ordinaryPlacementWheelRecode e (z.1 e))):=by
    linarith [hsecond]
  apply hfinal.trans
  apply finiteLaw_probability_mono
  intro z hz
  exact ⟨hz.1.1,hz.1.2,hz.2⟩
end Oberwolfach
