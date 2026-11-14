module

public import Oberwolfach.RawSelectedRimTwoPaths
public import Oberwolfach.FiniteSigmaSameFirstEvent

@[expose] public section
/-! Selected physical two-path estimates survive any dependent second stage
of the expanded sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem expanded_selected_two_paths_any_stage
    (d:ℕ) (hd:2≤d) (δ:ℝ) (hδ:0<δ):
    ∃N:ℕ,∀(V U Γ Color:Type) [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U] [Fintype Γ] [Fintype Color],
    N≤Fintype.card V→∀(P:SimpleGraph V) (π:Equiv.Perm V) (p k p₂ k₂ u:ℝ)
    (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u) (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (q:U→Γ→ℝ) (hq:∀w g,0≤q w g) (hQ:∀w,∑g,q w g≤1/8)
    (s:U→Color→ℝ) (hs:∀w j,0≤s w j) (hS:∀w,∑j,s w j ≤ intervalUncoveredProbability d (∑g,q w g))
    {R:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)→Type}
    [∀σ,Fintype (R σ)] (ν:∀σ,FiniteLaw (R σ)),
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS);
    1-δ≤(μ.sigma ν).probability (fun z=>∀x y,x≠y→
      ((P.neighborFinset x∩P.neighborFinset y).card:ℝ)*p^2-(Fintype.card V:ℝ)^(3/4:ℝ)-2*(2*((3*d:ℕ):ℝ)+1)≤
      ((Finset.univ.filter (fun v=>0<markedPhysicalRim P π (3*d)
        (fun e=>markedExpandedPhysicalCollapse (z.1 (Sum.inl e))) false x v ∧
        0<markedPhysicalRim P π (3*d)
        (fun e=>markedExpandedPhysicalCollapse (z.1 (Sum.inl e))) false v y)).card:ℝ)):=by
  obtain ⟨N,hN⟩:=raw_expanded_selected_rim_two_paths_high_probability d hd δ hδ
  refine ⟨N,?_⟩
  intro V U Γ Color _ _ _ _ _ _ hn P π p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum q hq hQ s hs hS R _ ν μ
  let E:=fun (σ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)=>∀x y,x≠y→
      ((P.neighborFinset x∩P.neighborFinset y).card:ℝ)*p^2-(Fintype.card V:ℝ)^(3/4:ℝ)-2*(2*((3*d:ℕ):ℝ)+1)≤
      ((Finset.univ.filter (fun v=>0<markedPhysicalRim P π (3*d)
        (fun e=>markedExpandedPhysicalCollapse (σ (Sum.inl e))) false x v ∧
        0<markedPhysicalRim P π (3*d)
        (fun e=>markedExpandedPhysicalCollapse (σ (Sum.inl e))) false v y)).card:ℝ)
  let νunit:=fun (_:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)=>FiniteLaw.uniform Unit
  have hh:1-δ≤(μ.sigma νunit).probability (fun z=>E z.1):=by
    exact hN V hn U Γ Color P π p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum q hq hQ s hs hS (fun _=>Unit) (fun _=>FiniteLaw.uniform Unit)
  rw [finiteLaw_sigma_same_first_event μ νunit ν E] at hh
  exact hh
end Oberwolfach
