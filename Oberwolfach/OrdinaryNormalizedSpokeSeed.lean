module

public import Oberwolfach.OrdinaryNormalizedCycleVertexLoad
public import Oberwolfach.OrdinarySeedLift

@[expose] public section

/-! Lift the normalized original cycle weights to wheel coefficients with a
single formal hub, preserving the conflict-free vertex-load estimate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_normalized_spoke_seed {V:Type} [Fintype V] [DecidableEq V]
    (P F:SimpleGraph V) (r:ℕ) (hr:2≤r) (hn:0<Fintype.card V)
    (weight:OrdinaryCycle P r→ℝ) (hweight:∀ C,0≤weight C)
    (B:ℝ) (hB:0≤B) (hb:∀ C,weight C≤B/(Fintype.card V:ℝ)^(r-2))
    (L:ℝ) (hdeg:∀ v,(F.degree v:ℝ)≤L)
    (he:∀ x y,(∑ C,if C.val.val.Adj x y then weight C else 0)=if P.Adj x y then 1 else 0)
    (D ε:ℝ) (hD:0<D) (hnear:∀ v,|(P.degree v:ℝ)-D|≤ε*Fintype.card V) (v:V):
    |(2/D)*ordinarySpokeLoad (ordinaryCycleWheelWeight (U:=Unit) P F r weight 1) v ()-1|≤
      (6*(r:ℝ)^4*B*L+ε*Fintype.card V)/D := by
  have hload:=ordinaryCycleWheelWeight_spoke_load (U:=Unit) P F r weight 1 v ()
  simp only [one_div,inv_one,one_mul] at hload
  rw [hload]
  have hh:=ordinary_normalized_admissible_vertex_load P F r hr hn weight hweight B hB hb L hdeg he D ε hD hnear v
  convert hh using 1 <;> congr!
end Oberwolfach
