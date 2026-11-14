module

public import Oberwolfach.OrdinaryPlacementWheelRecodeLaw
public import Oberwolfach.FiniteLawSigmaProjection

@[expose] public section
/-! Events of the recoded outcome have the recoded law on the same original
sample, even after an arbitrary outcome-dependent second stage. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem ordinary_placement_recode_probability_on_same_sample
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (d:ℕ) (hd:2≤d) (q:U→Γ→ℝ) (hq:∀w g,0≤q w g) (hQ:∀w,∑g,q w g≤1/8)
    (s:U→Color→ℝ) (hs:∀w j,0≤s w j) (hS:∀w,∑j,s w j ≤ intervalUncoveredProbability d (∑g,q w g))
    {R:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)→Type}
    [∀σ,Fintype (R σ)] (ν:∀σ,FiniteLaw (R σ))
    (E:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)→Prop):
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)
    let μ':=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) (p+u/2) k p₂ k₂ 0
      (by positivity) hk hp₂ hk₂ (by norm_num) (by linarith) d hd q hq hQ s hs hS);
    (μ.sigma ν).probability (fun z=>E (fun e=>ordinaryPlacementWheelRecode e (z.1 e)))=μ'.probability E:=by
  intro μ μ'
  calc
    _ = μ.probability (fun σ=>E (fun e=>ordinaryPlacementWheelRecode e (σ e))):=finiteLaw_sigma_first_probability μ ν _
    _ = _ := by
      rw [←finiteLaw_map_probability,ordinary_placement_wheel_recode_law p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS]
end Oberwolfach
