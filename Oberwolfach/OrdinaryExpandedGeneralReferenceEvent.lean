module

public import Oberwolfach.ExpandedOrdinarySelectedLaw
public import Oberwolfach.FiniteSigmaFirstMap
public import Oberwolfach.FiniteLawIntersectionLower

@[expose] public section
/-! Add any ordinary reference event to an event of the same expanded
sample, including an arbitrary dependent second stage. All five physical
state probabilities are kept. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_expanded_add_general_reference_event
    {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [DecidableEq V] [DecidableEq U]
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (d:ℕ) (hd:2≤d) (q:U→Γ→ℝ) (hq:∀w g,0≤q w g) (hQ:∀w,∑g,q w g≤1/8)
    (s:U→Color→ℝ) (hs:∀w j,0≤s w j) (hS:∀w,∑j,s w j≤ intervalUncoveredProbability d (∑g,q w g))
    {R:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)→Type}
    [∀σ,Fintype (R σ)] (ν:∀σ,FiniteLaw (R σ))
    (A:RawWheelOutcome V U Γ Color→Prop)
    (E:(Σσ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e,R σ)→Prop)
    (εA εE:ℝ)
    (hA:1-εA≤(FiniteLaw.pi (rawWheelLaw (V:=V) (fun _=>2*p)
      (fun _=>by linarith) (fun _=>by linarith) d hd q hq hQ s hs hS)).probability A)
    (hE:let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS);
      1-εE≤(μ.sigma ν).probability E):
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS);
    1-(εE+εA)≤(μ.sigma ν).probability (fun z=>E z ∧ A (fun e=>expandedOrdinarySelectedCollapse e (z.1 e))) :=by
  intro μ
  let ref:=fun (σ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e) e=>expandedOrdinarySelectedCollapse e (σ e)
  have hRefLaw:μ.map ref=
      FiniteLaw.pi (rawWheelLaw (V:=V) (fun _=>2*p) (fun _=>by linarith) (fun _=>by linarith)
        d hd q hq hQ s hs hS):=
    expanded_ordinary_selected_wheel_law p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS
  have hAraw:1-εA≤μ.probability (fun σ=>A (ref σ)):=by
    have hh:=finiteLaw_map_probability μ ref A
    rw [hRefLaw] at hh
    exact hh.symm ▸ hA
  have hAready:1-εA≤(μ.sigma ν).probability (fun z=>A (ref z.1)):=by
    have hh:=finiteLaw_sigma_first_probability μ ν (fun σ=>A (ref σ))
    exact hh.symm ▸ hAraw
  simpa only [sub_add_eq_sub_sub,ref] using finiteLaw_intersection_lower (μ.sigma ν) E _ εE εA hE hAready
end Oberwolfach
