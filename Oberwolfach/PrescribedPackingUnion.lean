module

public import Oberwolfach.PrescribedEdgePacking

@[expose] public section

/-! Exact edge-set conclusion for the union of the prescribed-edge wheels. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U T:Type*} [Fintype V] [Fintype U] [Fintype T] [DecidableEq V] [DecidableEq U]
  {Q F:SimpleGraph V} {H:V→U→Prop} {r:ℕ}

theorem prescribed_wheel_family_exact_union (C:T→OrdinaryWheel Q F H r)
    (E:Finset (Sym2 V⊕(V×U))) (e:T→Sym2 V⊕(V×U))
    (hdis:∀ i j,i≠j → Disjoint (ordinaryWheelResources (C i)) (ordinaryWheelResources (C j)))
    (hinner:∀ i,ordinaryWheelResources (C i)∩E={e i}) :
    HasOrdinaryWheelDecomposition (wheelFamilyRim C) (wheelFamilySpokes C) r ∧
      ordinaryHostResources (wheelFamilyRim C) (wheelFamilySpokes C)∩E=Finset.univ.image e ∧
      ∀ i,(ordinaryWheelResources (C i)∩Finset.univ.image e)={e i} :=by
  have he:ordinaryHostResources (wheelFamilyRim C) (wheelFamilySpokes C)∩E=Finset.univ.image e:=by
    rw [wheelFamily_resources,Finset.biUnion_inter]
    simp only [hinner,Finset.biUnion_singleton]
  refine ⟨wheelFamily_decomposition C hdis,he,?_⟩
  intro i
  have hsub:Finset.univ.image e⊆E:=by rw [←he];exact Finset.inter_subset_right
  apply Finset.Subset.antisymm
  · exact (Finset.inter_subset_inter_left hsub).trans_eq (hinner i)
  · intro a ha
    have ha':a=e i:=Finset.mem_singleton.mp ha
    subst a
    have hi:e i∈ordinaryWheelResources (C i)∩E:=by rw [hinner i];simp
    exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hi).1,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩

end Oberwolfach
