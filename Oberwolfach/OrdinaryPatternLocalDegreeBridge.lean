module

public import Oberwolfach.OrdinaryPatternSpokeLocalBridge
public import Oberwolfach.OrdinaryLocalPotentialDivision

@[expose] public section

/-! At an existing root of the actual sampled spoke domain, the normalized
root-omitted pattern load equals the weighted degree of its local cycles. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance 100000] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V] {r:ℕ}

theorem ordinary_pattern_spoke_local_degree
    (P Q F:SimpleGraph V) (H:V→Unit→Prop) (hQP:Q≤P)
    (weight:OrdinaryCycle P r→ℝ) (D c:ℝ) (v:V) (hv:H v ()):
    let T:=Finset.univ.filter (fun z=>H z ())
    let φ:=fun C:OrdinaryCycle P r=>weight C/D/c;
    hypergraphWeightedDegree localOrdinaryVertices
      (fun C:LocalOrdinaryCycle Q F T r=>φ (localOrdinaryParent hQP C)) v=
      resourcePatternLoad ordinaryWheelResources (ordinaryCycleWheelWeight (U:=Unit) P F r weight D)
        (fun _ _=>true) (Sum.inr (v,())) (ordinaryResourceState Q H)/c := by
  intro T φ
  have hvT:v∈T:=Finset.mem_filter.mpr ⟨Finset.mem_univ _,hv⟩
  have hpres:=ordinaryLocalPotential_present P Q F T hQP φ v hvT
  have hdiv:=ordinary_local_potential_div P Q F T (fun C=>weight C/D) c v
  have hpat:=ordinary_pattern_spoke_eq_local_bridge P Q F H weight D v ()
  rw [←hpres,hdiv,←hpat]
end Oberwolfach
