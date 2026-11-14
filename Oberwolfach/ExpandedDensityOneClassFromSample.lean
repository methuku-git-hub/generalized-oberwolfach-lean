module

public import Oberwolfach.ExpandedDensityOneClass

@[expose] public section
/-! Density one requires no class regularisation on the same positive-mass
expanded outcome, even with dependent retention. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem expanded_density_one_class_eq_host
    {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [LinearOrder V] [DecidableEq U]
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (hone:2*p+2*k+2*p₂+2*k₂+u=1)
    (d:ℕ) (hd:2≤d) (q:U→Γ→ℝ) (hq:∀w g,0≤q w g) (hQ:∀w,∑g,q w g≤1/8)
    (s:U→Color→ℝ) (hs:∀w j,0≤s w j) (hS:∀w,∑j,s w j≤ intervalUncoveredProbability d (∑g,q w g))
    {R:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)→Type}
    [∀σ,Fintype (R σ)] (ν:∀σ,FiniteLaw (R σ))
    (P:SimpleGraph V) (z:Σσ,R σ)
    (hpos:0<((FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)).sigma ν).mass z):
    longPhysicalStateGraph P z.1 {0,1,2,3,4}=P:=by
  apply expanded_class_eq_host_of_no_state_five P z.1
  exact expanded_density_one_support p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum hone
    d hd q hq hQ s hs hS ν z hpos
end Oberwolfach
