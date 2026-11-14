module

public import Oberwolfach.OrdinaryColourDegreesOnPrior
public import Oberwolfach.OrdinaryZeroRetentionPrior

@[expose] public section
/-! Add the colour-degree tests and the zero-retention event to any prior
on one expanded sample; the zero-retention step has no additional loss. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_colour_zero_on_prior (δ:ℝ) (hδ:0<δ):
    ∃N:ℕ,1≤N ∧ ∀(V:Type) [Fintype V] [LinearOrder V],N≤Fintype.card V→
    ∀(U Γ Color:Type) [Fintype U] [Fintype Γ] [Fintype Color] [DecidableEq U]
    (P:SimpleGraph V) (π:Equiv.Perm V)
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1) (d:ℕ) (hd:2≤d)
    (q:U→Γ→ℝ) (hq:∀w g,0≤q w g) (hQ:∀w,∑g,q w g≤1/8)
    (s:U→Color→ℝ) (hs:∀w j,0≤s w j) (hS:∀w,∑j,s w j≤ intervalUncoveredProbability d (∑g,q w g))
    (g₀:Γ) (hzero:∀w,q w g₀=0)
    {R:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)→Type}
    [∀σ,Fintype (R σ)] (ν:∀σ,FiniteLaw (R σ)) (E:(Σσ,R σ)→Prop) (εE:ℝ),
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS);
    1-εE≤(μ.sigma ν).probability E→
    1-(εE+δ)≤(μ.sigma ν).probability (fun z=>
      (E z ∧ (∀a x,|(sampledColourDegree P (fun e=>(z.1 (Sum.inl e)).1) a x:ℝ)-
        markedExpandedPhysicalProbability p k p₂ k₂ u a*P.degree x|<(Fintype.card V:ℝ)^(3/5:ℝ))) ∧
      OrdinaryZeroRetentionEvent π d g₀ z.1) :=by
  obtain ⟨N,hN,hcolour⟩:=ordinary_colour_degrees_on_prior_arbitrary_failure δ hδ
  refine ⟨N,hN,?_⟩
  intro V _ _ hn U Γ Color _ _ _ _ P π p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS g₀ hzero R _ ν E εE μ hE
  let Prior:=fun z:(Σσ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e,R σ)=>
    E z ∧ ∀a x,|(sampledColourDegree P (fun e=>(z.1 (Sum.inl e)).1) a x:ℝ)-
      markedExpandedPhysicalProbability p k p₂ k₂ u a*P.degree x|<(Fintype.card V:ℝ)^(3/5:ℝ)
  have hc:1-(εE+δ)≤(μ.sigma ν).probability Prior:=hcolour V hn U Γ Color P p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS ν E εE hE
  have hz:=ordinary_zero_retention_on_prior p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS g₀ hzero π ν Prior
  exact hc.trans hz
end Oberwolfach
