module

public import Oberwolfach.MarkedExpandedDegreeEvent
public import Oberwolfach.GoodPlacementEvents

@[expose] public section
/-! Add simultaneous physical colour-degree concentration to an arbitrary
prior event on the same expanded sample and conditional continuation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem ordinary_expanded_all_colour_degrees_and_prior
    (P:SimpleGraph V)
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1) (d:ℕ) (hd:2≤d)
    (q:U→Γ→ℝ) (hq:∀w g,0≤q w g) (hQ:∀w,∑g,q w g≤1/8)
    (s:U→Color→ℝ) (hs:∀w j,0≤s w j) (hS:∀w,∑j,s w j≤ intervalUncoveredProbability d (∑g,q w g))
    (t:ℝ) (ht:0≤t)
    {R:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)→Type}
    [∀σ,Fintype (R σ)] (ν:∀σ,FiniteLaw (R σ))
    (E:(Σσ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e,R σ)→Prop) (εE:ℝ)
    (hE:let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS);
      1-εE≤(μ.sigma ν).probability E):
    let ρ:=markedExpandedPhysicalProbability p k p₂ k₂ u
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)
    let loss:=36*(Fintype.card V:ℝ)*Real.exp (-2*t^2/Fintype.card V);
    1-(εE+loss)≤(μ.sigma ν).probability (fun z=>E z ∧ ∀a x,
      |((∑y,sampledColourOrientation P (fun e=>z.1 (Sum.inl e)) a x y:ℕ):ℝ)-ρ a/2*P.degree x|<t ∧
      |((∑y,sampledColourOrientation P (fun e=>z.1 (Sum.inl e)) a y x:ℕ):ℝ)-ρ a/2*P.degree x|<t ∧
      |(sampledColourDegree P (fun e=>(z.1 (Sum.inl e)).1) a x:ℝ)-ρ a*P.degree x|<t):=by
  intro ρ μ loss
  let D:=fun σ:(Sym2 V→Fin 6×Bool)=>∀a x,
      |((∑y,sampledColourOrientation P σ a x y:ℕ):ℝ)-ρ a/2*P.degree x|<t ∧
      |((∑y,sampledColourOrientation P σ a y x:ℕ):ℝ)-ρ a/2*P.degree x|<t ∧
      |(sampledColourDegree P (fun e=>(σ e).1) a x:ℝ)-ρ a*P.degree x|<t
  have hc:=sampledColourDegrees_common_event P P ρ
    (markedExpandedPhysicalProbability_nonneg p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum)
    (markedExpandedPhysicalProbability_sum p k p₂ k₂ u) ht
  have hproj:(μ.sigma ν).probability (fun z=>D (fun e=>z.1 (Sum.inl e)))=
      (FiniteLaw.pi (fun _:Sym2 V=>FiniteLaw.categoricalDirection ρ
        (markedExpandedPhysicalProbability_nonneg p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum)
        (markedExpandedPhysicalProbability_sum p k p₂ k₂ u))).probability D:=by
    calc
      _ = μ.probability (fun ω=>D (fun e=>ω (Sum.inl e))):=finiteLaw_sigma_first_probability μ ν _
      _ = _ := by
        simpa only [μ,rawExpandedMarkedWheelLaw] using
          (finiteLaw_pi_injective_projection_event
            (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)
            Sum.inl Sum.inl_injective D)
  have hD:1-loss≤(μ.sigma ν).probability (fun z=>D (fun e=>z.1 (Sum.inl e))):=by
    rw [hproj]
    norm_num [D,loss] at hc ⊢
    exact hc
  have hh:=finiteLaw_good_intersection (μ.sigma ν) E (fun z=>D (fun e=>z.1 (Sum.inl e))) loss hD
  linarith [hE]
end Oberwolfach
