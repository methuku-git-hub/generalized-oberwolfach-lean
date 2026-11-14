module

public import Oberwolfach.ExpandedSelectedNeighbourAnyStage
public import Oberwolfach.FiniteLawIntersectionLower
public import Oberwolfach.FiniteSigmaSameFirstEvent

@[expose] public section
/-! The selected-physical-neighbour concentration event survives an
arbitrary dependent second stage of the same expanded sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem expanded_selected_neighbour_tests_and_event
    (d:ℕ) (hd:2≤d) (δ:ℝ) (hδ:0<δ):
    ∃N:ℕ,∀(V U Γ Color:Type) [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U] [Fintype Γ] [Fintype Color],
    N≤Fintype.card V→Fintype.card U≤Fintype.card V→
    ∀(P:SimpleGraph V) (π:Equiv.Perm V) (p k p₂ k₂ u:ℝ)
    (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u) (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (q:U→Γ→ℝ) (hq:∀w g,0≤q w g) (hQ:∀w,∑g,q w g≤1/8)
    (s:U→Color→ℝ) (hs:∀w j,0≤s w j) (hS:∀w,∑j,s w j ≤ intervalUncoveredProbability d (∑g,q w g))
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    {R:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)→Type}
    [∀σ,Fintype (R σ)] (ν:∀σ,FiniteLaw (R σ)),
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS);
    ∀(b:ℝ) (E:(Σσ,R σ)→Prop),1-b≤(μ.sigma ν).probability E→
    1-b-δ≤(μ.sigma ν).probability (fun z=>E z ∧ ∀w i,
      |rawIntervalUnassignedHubCountOn π d (fun e=>z.1 (Sum.inr e)) w
          (rawSelectedNeighbourTestSet P π d (fun e=>z.1 (Sum.inl e)) i)-
        (rawSelectedNeighbourTestSet P π d (fun e=>z.1 (Sum.inl e)) i).card*(1-(∑g,q w g)-(∑j,s w j))|<
          (Fintype.card V:ℝ)^(3/4:ℝ)):=by
  obtain ⟨N,hN⟩:=expanded_selected_neighbour_tests_any_stage d hd δ hδ
  refine ⟨N,?_⟩
  intro V U Γ Color _ _ _ _ _ _ hn hU P π p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum q hq hQ s hs hS hnoshort R _ ν μ b E hE
  have hh:=hN V U Γ Color hn hU P π p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum q hq hQ s hs hS hnoshort ν
  exact finiteLaw_intersection_lower (μ.sigma ν) E _ b δ hE hh
end Oberwolfach
