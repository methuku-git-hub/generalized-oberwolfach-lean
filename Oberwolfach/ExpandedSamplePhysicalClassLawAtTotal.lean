module

public import Oberwolfach.ExpandedSamplePhysicalClassLaw
public import Oberwolfach.ExpandedBinaryColourProjection
public import Oberwolfach.ExpandedBinaryClassGraph
public import Oberwolfach.ClassColourRetainedGraphAlignment

@[expose] public section
/-! The physical selected class of the retained expanded construction has
exactly the independent edge-retention law, even after dependent retention. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem expanded_sample_physical_class_probability_at_total
    {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [LinearOrder V] [DecidableEq U]
    (P:SimpleGraph V) (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (ρ:ℝ) (hρ:0≤ρ) (hρ1:ρ≤1) (heq:2*p+2*k+2*p₂+2*k₂+u=ρ)
    (d:ℕ) (hd:2≤d) (q:U→Γ→ℝ) (hq:∀u g,0≤q u g) (hQ:∀u,∑g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀u j,0≤s u j) (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑g,q u g))
    {R:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)→Type}
    [∀σ,Fintype (R σ)] (ν:∀σ,FiniteLaw (R σ)) (Good:SimpleGraph V→Prop):
    ((FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)).sigma ν).probability
      (fun z=>Good (longPhysicalStateGraph P z.1 {0,1,2,3,4}))=
    (FiniteLaw.pi (fun _:Sym2 V=>FiniteLaw.retentionCoin ρ hρ hρ1)).probability (fun σ=>Good (retainedGraph P σ)) :=by
  subst ρ
  exact expanded_sample_physical_class_probability P p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS ν Good
end Oberwolfach
