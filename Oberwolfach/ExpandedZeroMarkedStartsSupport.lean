module

public import Oberwolfach.ExpandedDensityOneSupport
public import Oberwolfach.RetentionRestrictionCommonEvent
public import Oberwolfach.RetainedMarkedRootUniformity

@[expose] public section
/-! A colour with zero assigned start mass is absent on every positive-mass
expanded outcome, even with an arbitrary dependent second sampling stage. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem expanded_zero_marked_starts_on_support
    {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [LinearOrder V] [DecidableEq U]
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (d:ℕ) (hd:2≤d) (q:U→Γ→ℝ) (hq:∀w g,0≤q w g) (hQ:∀w,∑g,q w g≤1/8)
    (s:U→Color→ℝ) (hs:∀w j,0≤s w j) (hS:∀w,∑j,s w j≤ intervalUncoveredProbability d (∑g,q w g))
    (g₀:Γ) (hzero:∀w,q w g₀=0)
    {R:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)→Type}
    [∀σ,Fintype (R σ)] (ν:∀σ,FiniteLaw (R σ))
    (z:Σσ,R σ)
    (hpos:0<((FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)).sigma ν).mass z)
    (π:Equiv.Perm V):
    ∀w x,¬rawIntervalColouredStart π d (fun e=>z.1 (Sum.inr (w,e))) x g₀:=by
  intro w x hstart
  let e:RawWheelCoordinate V U:=Sum.inr (w,Sum.inr (Sum.inl x))
  have hmark:z.1 e=some g₀:=hstart.2
  have hzeroMass:(rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS e).mass (z.1 e)=0:=by
    rw [hmark]
    simp [e,rawExpandedMarkedWheelLaw,rawIntervalFamilyLaw,rawIntervalCoordinateLaw,rawIntervalStartLaw,FiniteLaw.withRemainder,hzero]
  have hpizero:(FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)).mass z.1=0:=by
    change (∏i,(rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS i).mass (z.1 i))=0
    exact Finset.prod_eq_zero (Finset.mem_univ e) hzeroMass
  change 0<(FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)).mass z.1 * (ν z.1).mass z.2 at hpos
  rw [hpizero,zero_mul] at hpos
  exact (lt_irrefl 0) hpos
end Oberwolfach
