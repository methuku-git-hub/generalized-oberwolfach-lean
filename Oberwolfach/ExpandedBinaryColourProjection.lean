module

public import Oberwolfach.ExpandedBinaryClassProjection

@[expose] public section
/-! The grouped class colours alone retain their exact product law after
arbitrary dependent retention. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem expanded_binary_colour_probability_after_retention
    {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [LinearOrder V] [DecidableEq U]
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (d:ℕ) (hd:2≤d) (q:U→Γ→ℝ) (hq:∀u g,0≤q u g) (hQ:∀u,∑g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀u j,0≤s u j) (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑g,q u g))
    {R:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)→Type}
    [∀σ,Fintype (R σ)] (ν:∀σ,FiniteLaw (R σ)) (B:(Sym2 V→Fin 2)→Prop):
    ((FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)).sigma ν).probability
      (fun z=>B (fun e=>(expandedBinaryClass (z.1 (Sum.inl e))).1))=
    (FiniteLaw.pi (fun _:Sym2 V=>FiniteLaw.categorical (expandedBinaryProbability p k p₂ k₂ u)
      (expanded_binary_probability_nonneg p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum)
      (expanded_binary_probability_sum p k p₂ k₂ u))).probability B:=by
  exact (expanded_binary_class_probability_after_retention p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS ν
    (fun σ=>B (fun e=>(σ e).1))).trans
    (categoricalDirection_colour_probability (expandedBinaryProbability p k p₂ k₂ u)
      (expanded_binary_probability_nonneg p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum)
      (expanded_binary_probability_sum p k p₂ k₂ u) B)
end Oberwolfach
