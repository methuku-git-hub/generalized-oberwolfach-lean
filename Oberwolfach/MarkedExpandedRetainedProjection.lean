module

public import Oberwolfach.MarkedExpandedRawCommonEvent

@[expose] public section
/-! The richer physical experiment projects to the exact selected retained
law, even when retention depends on the collapsed raw outcome. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem raw_expanded_marked_retained_projection_probability
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (d:ℕ) (hd:2≤d) (q:U→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀ u j,0≤s u j) (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
    (F:RawMarkedOutcome V U Γ Color→Type) [∀ a,Fintype (F a)] (ν:∀ a,FiniteLaw (F a))
    (E:(Σ a,F a)→Prop):
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)
    let f:=fun (ω:∀ e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e) e=>rawExpandedMarkedCollapse e (ω e);
    (μ.sigma (fun ω=>ν (f ω))).probability (fun z=>E ⟨f z.1,z.2⟩)=
      ((FiniteLaw.pi (rawMarkedWheelLaw (V:=V) p k hp hk (by linarith) d hd q hq hQ s hs hS)).sigma ν).probability E:=by
  intro μ f
  rw [finiteLaw_sigma_projection_probability]
  have hproj:μ.map f=FiniteLaw.pi (rawMarkedWheelLaw (V:=V) p k hp hk (by linarith) d hd q hq hQ s hs hS):=
    raw_expanded_marked_wheel_law_projection p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS
  rw [hproj]
end Oberwolfach
