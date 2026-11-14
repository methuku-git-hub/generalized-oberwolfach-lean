module

public import Oberwolfach.MarkedExpandedRawLaw
public import Oberwolfach.FiniteSumProduct
public import Oberwolfach.ProductFailureBounds
public import Oberwolfach.FiniteSigmaFirstMap

@[expose] public section
/-! The orientation bits in the original expanded experiment have exactly
the fair product law, also after dependent retention is sampled. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

 theorem expanded_orientation_probability
    {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [LinearOrder V] [DecidableEq U]
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (d:ℕ) (hd:2≤d) (q:U→Γ→ℝ) (hq:∀u g,0≤q u g) (hQ:∀u,∑g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀u j,0≤s u j) (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑g,q u g))
    (E:(Sym2 V→Bool)→Prop):
    (FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)).probability
      (fun σ=>E (fun e=>(σ (Sum.inl e)).2))=
      (FiniteLaw.pi (fun _:Sym2 V=>FiniteLaw.fairCoin)).probability E:=by
  let law:=rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS
  let μ:=FiniteLaw.pi (fun b=>law (Sum.inr b))
  let ν:=FiniteLaw.pi (fun a=>law (Sum.inl a))
  rw [finiteLaw_pi_sum_probability law (fun _ σ=>E (fun e=>(σ e).2))]
  rw [finiteLaw_prod_probability_slices μ ν (fun _ σ=>E (fun e=>(σ e).2))]
  simp only [← Finset.sum_mul,μ.total,mul_one,one_mul]
  exact categoricalDirection_direction_probability (markedExpandedPhysicalProbability p k p₂ k₂ u)
    (markedExpandedPhysicalProbability_nonneg p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum)
    (markedExpandedPhysicalProbability_sum p k p₂ k₂ u) E

theorem expanded_orientation_probability_after_retention
    {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [LinearOrder V] [DecidableEq U]
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (d:ℕ) (hd:2≤d) (q:U→Γ→ℝ) (hq:∀u g,0≤q u g) (hQ:∀u,∑g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀u j,0≤s u j) (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑g,q u g))
    {R:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)→Type}
    [∀σ,Fintype (R σ)] (ν:∀σ,FiniteLaw (R σ)) (E:(Sym2 V→Bool)→Prop):
    ((FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)).sigma ν).probability
      (fun z=>E (fun e=>(z.1 (Sum.inl e)).2))=
      (FiniteLaw.pi (fun _:Sym2 V=>FiniteLaw.fairCoin)).probability E:=by
  exact (finiteLaw_sigma_first_probability _ ν (fun σ=>E (fun e=>(σ (Sum.inl e)).2))).trans
    (expanded_orientation_probability p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS E)
end Oberwolfach
