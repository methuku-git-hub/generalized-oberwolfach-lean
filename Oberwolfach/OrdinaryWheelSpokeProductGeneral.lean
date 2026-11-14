module

public import Oberwolfach.FinitePatternUniformRootSum
public import Oberwolfach.OrdinaryRawMeanFactors

@[expose] public section
/-! The omitted-spoke product-sum identity for any finite wheel family with
constant rim and spoke marginals on every candidate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U : Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_wheel_spoke_marginal_product_sum
    (P F : SimpleGraph V) (H : V → U → Prop) (r : ℕ) (hr : 1 ≤ r)
    (p : Sym2 V ⊕ (V × U) → ℝ) (pR pH : ℝ) (hpH : 0 < pH)
    (hp : ∀ (W : OrdinaryWheel P F H r) a, a ∈ ordinaryWheelResources W →
      p a = Sum.elim (fun _ => pR) (fun _ => pH) a)
    (w : OrdinaryWheel P F H r → ℝ) (v : V) (u : U) :
    (∑ W, (if Sum.inr (v,u) ∈ ordinaryWheelResources W then w W else 0) *
      ∏ a ∈ ordinaryWheelResources W \ {Sum.inr (v,u)}, p a) =
      pR^r * pH^(r-1) * ordinarySpokeLoad w v u := by
  have hprod (W : OrdinaryWheel P F H r) (he : Sum.inr (v,u) ∈ ordinaryWheelResources W) :
      (∏ a ∈ ordinaryWheelResources W \ {Sum.inr (v,u)}, p a) = pR^r*pH^(r-1) := by
    have hh := Finset.prod_congr rfl (fun a (ha : a ∈ ordinaryWheelResources W \ {Sum.inr (v,u)}) =>
      hp W a (Finset.mem_sdiff.mp ha).1)
    rw [hh]
    exact ordinaryWheelResources_spoke_omitted_product W hr pR pH hpH.ne' _ he
  have hh := finite_pattern_uniform_root_sum ordinaryWheelResources w (Sum.inr (v,u)) p
    (pR^r*pH^(r-1)) hprod
  rw [ordinaryWheelResources_load_spoke] at hh
  exact hh
end Oberwolfach
