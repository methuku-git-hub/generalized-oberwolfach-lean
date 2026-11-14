module

public import Oberwolfach.OrdinaryTriangleFiniteCoverEvent
public import Oberwolfach.OrdinaryExpandedGeneralReferenceEvent

@[expose] public section
/-! Join the actual robust deep-cover event to any dependent event of the
    same expanded sample, with an additive failure bound. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [LinearOrder U]

theorem ordinary_expanded_add_triangle_cover_event
    (P F:SimpleGraph V) (π:Equiv.Perm V) (J:Finset U) (d:ℕ) (hd:2≤d) (κ:ℝ) (j:Color)
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (q:U→Γ→ℝ) (hq:∀w g,0≤q w g) (hQ:∀w,∑g,q w g≤1/8)
    (s:U→Color→ℝ) (hs:∀w j,0≤s w j) (hS:∀w,∑j,s w j≤ intervalUncoveredProbability d (∑g,q w g))
    {R:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)→Type}
    [∀σ,Fintype (R σ)] (ν:∀σ,FiniteLaw (R σ))
    (E:(Σσ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e,R σ)→Prop)
    (εE εDeep:ℝ)
    (hDeep:1-εDeep≤(FiniteLaw.pi (rawWheelLaw (V:=V) (fun _=>2*p)
      (fun _=>by linarith) (fun _=>by linarith) d hd q hq hQ s hs hS)).probability
      (OrdinaryTriangleFiniteCoverEvent κ P F J π d j))
    (hE:let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS);
      1-εE≤(μ.sigma ν).probability E):
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS);
    1-(εE+εDeep)≤(μ.sigma ν).probability (fun z=>E z ∧
      OrdinaryTriangleFiniteCoverEvent κ P F J π d j (fun e=>expandedOrdinarySelectedCollapse e (z.1 e))):=by
  exact ordinary_expanded_add_general_reference_event p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS ν
    (OrdinaryTriangleFiniteCoverEvent κ P F J π d j) E εDeep εE hDeep hE
end Oberwolfach
