module

public import Oberwolfach.RawSelectedPhysicalNeighbourTests
public import Oberwolfach.RawReservedLabelAdaptiveHighProbability

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
theorem raw_reserved_selected_neighbour_tests_high_probability
    (d:ℕ) (hd:2≤d) (δ:ℝ) (hδ:0<δ):
    ∃N:ℕ,∀(V:Type) [Fintype V] [LinearOrder V],N≤Fintype.card V→
    ∀(U Γ Color:Type) [Fintype U] [DecidableEq U] [Fintype Γ] [Fintype Color],
    Fintype.card U≤Fintype.card V→
    ∀(color:Color) (P:SimpleGraph V) (π:Equiv.Perm V) (p k p₂ k₂ u:ℝ)
    (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u) (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (q:U→Γ→ℝ) (hq:∀w g,0≤q w g) (hQ:∀w,∑g,q w g≤1/8)
    (s:U→Color→ℝ) (hs:∀w j,0≤s w j) (hS:∀w,∑j,s w j≤ intervalUncoveredProbability d (∑g,q w g))
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (F:RawMarkedOutcome V U Γ Color→Type) [∀a,Fintype (F a)] (ν:∀a,FiniteLaw (F a)),
    let law:=rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS
    let μ:=FiniteLaw.pi law
    let f:=fun (ω:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e) e=>rawExpandedMarkedCollapse e (ω e)
    1-δ≤(μ.sigma (fun ω=>ν (f ω))).probability (fun z=>
      ∀w i,|rawIntervalReservedLabelHubCountOn π d (fun e=>z.1 (Sum.inr e)) w color
          (rawSelectedNeighbourTestSet P π d (fun e=>z.1 (Sum.inl e)) i)-
        (rawSelectedNeighbourTestSet P π d (fun e=>z.1 (Sum.inl e)) i).card*s w color|<
          (Fintype.card V:ℝ)^(3/4:ℝ)):=by
  obtain ⟨N,hN⟩:=raw_reserved_label_physical_adaptive_high_probability d hd δ hδ
  refine ⟨max N 1,?_⟩
  intro V _ _ hn U Γ Color _ _ _ _ hU color P π p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum q hq hQ s hs hS hnoshort F _ ν law μ f
  have hn0:0<Fintype.card V:=by omega
  exact hN V (by omega) U Γ Color (RawNeighbourTestIndex V) hU (raw_neighbour_test_index_card_bound hn0)
    π p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum q hq hQ s hs hS hnoshort color (rawSelectedNeighbourTestSet P π d) F ν
end Oberwolfach
