module

public import Oberwolfach.OrdinaryPackingCleanupData

@[expose] public section
/-! The incidence error in a selected unreserved packing is exactly the
physical maximum-degree error of its leftover. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_unreserved_packing_leftover_bound
    (Q F:SimpleGraph V) (H:V→U→Prop) (X:Finset V) (Z:Finset U)
    (R:SimpleGraph (V⊕U)) (r:ℕ) (t:ℝ) (K:OrdinaryUnreservedPackingData Q F H X Z R r t):
    let G:=ordinaryUnreservedRim Q X R;let J:=ordinaryUnreservedSpokes H X Z R;
    let D:=ordinaryWheelRimGraph K.wheels;let E:=ordinaryPackingSpokes K.wheels;
    ∀a:V⊕U,(((ordinaryPhysicalGraph G J)\ordinaryPhysicalGraph D E).degree a:ℝ)≤t:=by
  intro G J D E a
  have hh:=ordinary_packing_leftover_physical_degree K.wheels a
  have he:=ordinary_physical_graph_after_deletion G J (ordinaryPhysicalGraph D E)
  change ordinaryPhysicalGraph (G\D) (fun v u=>J v u∧¬E v u)=_ at he
  rw [he] at hh
  have hh':=(Nat.cast_le (α:=ℝ)).mpr (le_of_eq hh)
  have hb:=hh'.trans (K.leftover a)
  convert hb using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach
