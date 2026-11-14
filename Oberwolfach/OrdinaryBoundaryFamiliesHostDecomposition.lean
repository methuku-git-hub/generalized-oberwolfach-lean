module

public import Oberwolfach.OrdinaryHostDecompositions

@[expose] public section
/-! Preserve the host and all-pairs forbidden condition while joining two
physically disjoint families of ordinary wheels. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U I J:Type} [Fintype V] [Fintype U] [Fintype I] [Fintype J]
  [DecidableEq V] [DecidableEq U]

theorem ordinary_boundary_families_host_decomposition
    (r:ℕ) (Q F:SimpleGraph V) (H:V→U→Prop)
    (W:J→OrdinaryWheel Q F H r) (C:I→OrdinaryWheel Q F H r)
    (hW:∀a b,a≠b→Disjoint (ordinaryWheelResources (W a)) (ordinaryWheelResources (W b)))
    (hC:∀a b,a≠b→Disjoint (ordinaryWheelResources (C a)) (ordinaryWheelResources (C b)))
    (hcross:∀i,Disjoint (ordinaryWheelResources (C i)) (ordinaryHostResources (wheelFamilyRim W) (wheelFamilySpokes W))):
    HasResourceDecomposition (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=r))
      (ordinaryHostResources (wheelFamilyRim W⊔wheelFamilyRim C)
        (fun v u=>wheelFamilySpokes W v u∨wheelFamilySpokes C v u)):=by
  have hdis:Disjoint (ordinaryHostResources (wheelFamilyRim W) (wheelFamilySpokes W))
      (ordinaryHostResources (wheelFamilyRim C) (wheelFamilySpokes C)):=by
    apply Finset.disjoint_left.mpr
    intro e he hf
    rw [wheelFamily_resources] at hf
    obtain ⟨i,_,hi⟩:=Finset.mem_biUnion.mp hf
    exact (Finset.disjoint_left.mp (hcross i)) hi he
  have hh:=resource_decomposition_union _ _ _ (wheelFamily_host_decomposition W hW)
    (wheelFamily_host_decomposition C hC) hdis
  rw [ordinaryHostResources_union]
  exact hh
end Oberwolfach
