module

public import Oberwolfach.OrdinaryPlacementColourRecode
public import Oberwolfach.MarkedExpandedRawLaw

@[expose] public section
/-! Recode only the physical coordinates; the entire interval sample and its
law are unchanged. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

def ordinaryPlacementWheelRecode (e:RawWheelCoordinate V U):
    RawExpandedMarkedCoordinateState Γ Color e→RawExpandedMarkedCoordinateState Γ Color e:=
  match e with
  | Sum.inl _=>ordinaryPlacementColourRecode
  | Sum.inr _=>id

theorem ordinary_placement_wheel_recode_law
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (d:ℕ) (hd:2≤d) (q:U→Γ→ℝ) (hq:∀w g,0≤q w g) (hQ:∀w,∑g,q w g≤1/8)
    (s:U→Color→ℝ) (hs:∀w j,0≤s w j) (hS:∀w,∑j,s w j≤ intervalUncoveredProbability d (∑g,q w g)):
    (FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)).map
      (fun σ e=>ordinaryPlacementWheelRecode e (σ e)) =
    FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) (p+u/2) k p₂ k₂ 0
      (by positivity) hk hp₂ hk₂ (by norm_num) (by linarith) d hd q hq hQ s hs hS) :=by
  rw [finiteLaw_pi_map]
  congr 1
  funext e
  cases e with
  | inl e=>exact ordinary_placement_colour_recode_law p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum
  | inr e=>
    apply finiteLaw_ext
    intro z
    simp [FiniteLaw.map,ordinaryPlacementWheelRecode,rawExpandedMarkedWheelLaw]
end Oberwolfach
