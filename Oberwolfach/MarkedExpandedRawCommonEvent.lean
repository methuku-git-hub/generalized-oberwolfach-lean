module

public import Oberwolfach.MarkedExpandedRawLaw
public import Oberwolfach.MarkedRefinedExposureCommonEvent

@[expose] public section
/-! Combining a selected-layer event with an event measurable on the richer
physical exposure. The latter event's probability bound remains an input. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem raw_expanded_marked_retained_common_event
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (d:ℕ) (hd:2≤d) (q:U→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀ u j,0≤s u j) (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
    (F:RawMarkedOutcome V U Γ Color→Type) [∀ a,Fintype (F a)]
    (ν:∀ a,FiniteLaw (F a))
    (E:(Σ a,F a)→Prop)
    (Extra:(Σ ω:(∀ e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e),
        F (fun e=>rawExpandedMarkedCollapse e (ω e)))→Prop)
    (hE:(7:ℝ)/10≤((FiniteLaw.pi (rawMarkedWheelLaw (V:=V) p k hp hk (by linarith) d hd q hq hQ s hs hS)).sigma ν).probability E)
    (hExtra:(99:ℝ)/100≤((FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)).sigma
      (fun ω=>ν (fun e=>rawExpandedMarkedCollapse e (ω e)))).probability Extra):
    ∃ z,0<((FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)).sigma
      (fun ω=>ν (fun e=>rawExpandedMarkedCollapse e (ω e)))).mass z ∧
      E ⟨(fun e=>rawExpandedMarkedCollapse e (z.1 e)),z.2⟩ ∧ Extra z := by
  let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)
  let f:=fun (ω:∀ e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e) e=>rawExpandedMarkedCollapse e (ω e)
  have hproj:μ.map f=FiniteLaw.pi (rawMarkedWheelLaw (V:=V) p k hp hk (by linarith) d hd q hq hQ s hs hS):=
    raw_expanded_marked_wheel_law_projection p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS
  have hE':1-(3:ℝ)/10≤((μ.map f).sigma ν).probability E:=by rw [hproj]; norm_num at *; exact hE
  have hExtra':1-(1:ℝ)/100≤(μ.sigma (fun ω=>ν (f ω))).probability Extra:=by norm_num at *; exact hExtra
  have hh:=finite_refined_exposure_common_event μ f ν E Extra (3/10) (1/100) hE' hExtra'
  exact hh.2 (by norm_num)
end Oberwolfach
