module

public import Oberwolfach.ExpandedBinaryClassLaw
public import Oberwolfach.MarkedExpandedRawLaw
public import Oberwolfach.FiniteSumProduct
public import Oberwolfach.ProductFailureBounds
public import Oberwolfach.FiniteSigmaFirstMap
public import Oberwolfach.FiniteLawMap

@[expose] public section
/-! The grouped physical states and their direction bits have the exact
independent two-colour law on the original retained expanded sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem expanded_binary_class_product_probability
    {E:Type} [Fintype E] [DecidableEq E] (p k p₂ k₂ u:ℝ)
    (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1) (B:(E→Fin 2×Bool)→Prop):
    (FiniteLaw.pi (fun _:E=>FiniteLaw.categoricalDirection (markedExpandedPhysicalProbability p k p₂ k₂ u)
      (markedExpandedPhysicalProbability_nonneg p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum)
      (markedExpandedPhysicalProbability_sum p k p₂ k₂ u))).probability
      (fun σ=>B (fun e=>expandedBinaryClass (σ e)))=
    (FiniteLaw.pi (fun _:E=>FiniteLaw.categoricalDirection (expandedBinaryProbability p k p₂ k₂ u)
      (expanded_binary_probability_nonneg p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum)
      (expanded_binary_probability_sum p k p₂ k₂ u))).probability B:=by
  rw [←finiteLaw_map_probability]
  rw [finiteLaw_pi_map]
  simp_rw [expanded_binary_class_law p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum]

theorem expanded_binary_class_probability_after_retention
    {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [LinearOrder V] [DecidableEq U]
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (d:ℕ) (hd:2≤d) (q:U→Γ→ℝ) (hq:∀u g,0≤q u g) (hQ:∀u,∑g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀u j,0≤s u j) (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑g,q u g))
    {R:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)→Type}
    [∀σ,Fintype (R σ)] (ν:∀σ,FiniteLaw (R σ)) (B:(Sym2 V→Fin 2×Bool)→Prop):
    ((FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)).sigma ν).probability
      (fun z=>B (fun e=>expandedBinaryClass (z.1 (Sum.inl e))))=
    (FiniteLaw.pi (fun _:Sym2 V=>FiniteLaw.categoricalDirection (expandedBinaryProbability p k p₂ k₂ u)
      (expanded_binary_probability_nonneg p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum)
      (expanded_binary_probability_sum p k p₂ k₂ u))).probability B:=by
  apply (finiteLaw_sigma_first_probability _ ν (fun σ=>B (fun e=>expandedBinaryClass (σ (Sum.inl e))))).trans
  let law:=rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS
  let μ:=FiniteLaw.pi (fun b=>law (Sum.inr b))
  let η:=FiniteLaw.pi (fun a=>law (Sum.inl a))
  rw [finiteLaw_pi_sum_probability law (fun _ σ=>B (fun e=>expandedBinaryClass (σ e)))]
  rw [finiteLaw_prod_probability_slices μ η (fun _ σ=>B (fun e=>expandedBinaryClass (σ e)))]
  simp only [←Finset.sum_mul,μ.total,one_mul]
  exact expanded_binary_class_product_probability p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum B
end Oberwolfach
