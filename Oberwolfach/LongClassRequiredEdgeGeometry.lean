module

public import Oberwolfach.LongClassRequiredOutsideDegree
public import Oberwolfach.LongClassRequiredGlobalGeometry

@[expose] public section
/-! A global edge-count estimate for the actual repaired required graph,
using its sparse degree outside the first inner set. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [LinearOrder V]

theorem long_class_required_edge_geometry
    (P S Sel Used:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (I:Finset V)
    (Req:V→V→Prop) (Pack:Finset (Sym2 V)) (hSP:S≤P):
    let K:=longRequiredPhysicalGraph S (S\Used) Sel π d I Req (fun x y=>Used.Adj x y)
    let Kplus:=longClassInnerRequiredRepair S Used K I Pack;
    2*Kplus.edgeFinset.card≤I.card^2+(6*d+2)*Fintype.card V :=by
  intro K Kplus
  have hin:=long_class_required_global_geometry S Sel Used π d I Req Pack
  have hout:=long_class_required_outside_degree P S Sel Used π d I Req Pack hSP
  have hdeg:∀v:V,Kplus.degree v≤(if v∈I then I.card else 0)+(6*d+2):=by
    intro v
    by_cases hv:v∈I
    · simpa [hv] using hin v
    · simpa [hv] using hout v hv
  have hsum:(∑v:V,Kplus.degree v)≤∑v:V,((if v∈I then I.card else 0)+(6*d+2)):=by
    apply Finset.sum_le_sum
    intro v _
    exact hdeg v
  have hcalc:(∑v:V,((if v∈I then I.card else 0)+(6*d+2)))=I.card^2+(6*d+2)*Fintype.card V:=by
    simp [Finset.sum_add_distrib,Finset.sum_ite, pow_two, Nat.mul_comm]
  rw [hcalc,Kplus.sum_degrees_eq_twice_card_edges] at hsum
  omega
end Oberwolfach
