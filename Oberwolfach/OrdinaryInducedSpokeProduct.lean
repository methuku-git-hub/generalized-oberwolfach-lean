module

public import Oberwolfach.OrdinaryInducedRawMarginal
public import Oberwolfach.OrdinaryWheelSpokeProductGeneral

@[expose] public section
/-! Product-of-marginals sum for a fixed induced-wheel spoke root. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 450000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Color : Type} [Fintype V] [Fintype U] [Fintype Color] [DecidableEq V] [DecidableEq U]

theorem ordinary_induced_spoke_marginal_product_sum
    (P F : SimpleGraph V) (A : Set V) (u : U) (r : ℕ) (hr : 1≤r)
    (s : U → Color → ℝ) (j : Color) (pR pH : ℝ) (hpH : 0<pH) (hj : s u j=pH)
    (w : OrdinaryWheel (P.induce A) (F.induce A) (fun _ : A => fun _ : Unit => True) r → ℝ)
    (v : A) :
    (∑ W : OrdinaryWheel (P.induce A) (F.induce A) (fun _ : A => fun _ : Unit => True) r, (if Sum.inr (v,()) ∈ ordinaryWheelResources W then w W else 0) *
      ∏ a ∈ ordinaryWheelResources W \ {Sum.inr (v,())},
        rawWheelMarginal P (fun _ => pR) s j (ordinaryInducedRawResource A u a)) =
      pR^r*pH^(r-1)*ordinarySpokeLoad w v () := by
  have hh := ordinary_wheel_spoke_marginal_product_sum (V:=A) (U:=Unit) (P.induce A) (F.induce A)
    (fun _ : A => fun _ : Unit => True) r hr
    (fun a => rawWheelMarginal P (fun _ => pR) s j (ordinaryInducedRawResource A u a))
    pR pH hpH
    (fun W a ha => ordinary_induced_raw_marginal_on_candidate P F A u r s j pR pH hj W a ha)
    w v ()
  convert hh using 1 <;> congr!
end Oberwolfach
