module

public import Oberwolfach.OrdinaryPackingGlue
public import Oberwolfach.PrescribedPackingUnion
public import Oberwolfach.RowCoverUnion

@[expose] public section

/-! Exact recombination of the prescribed-inner-edge packing with a deep
packing in its actual remainder. Protected intersections and covered stars
are computed in the original physical graph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Z:Type} [Fintype V] [Fintype U] [Fintype Z] [DecidableEq V] [DecidableEq U]
  {Q F:SimpleGraph V} {H:V→U→Prop} {r nr nh:ℕ}

theorem prescribed_deep_packing_union (C:Z→OrdinaryWheel Q F H r)
    (hC:∀ i j,i≠j→Disjoint (ordinaryWheelResources (C i)) (ordinaryWheelResources (C j)))
    (E:Finset (Sym2 V⊕(V×U))) (e:Z→Sym2 V⊕(V×U))
    (hinner:∀ i,ordinaryWheelResources (C i)∩E={e i})
    (M:Finset (OrdinaryWheel (Q\wheelFamilyRim C) F (fun v u=>H v u∧¬wheelFamilySpokes C v u) r))
    (hM:∀ A∈M,∀ B∈M,A≠B→Disjoint (ordinaryWheelResources A) (ordinaryWheelResources B))
    (hME:Disjoint (M.biUnion ordinaryWheelResources) E)
    (x:Fin nr→V) (u:Fin nh→U)
    (hrim:∀ i v,(ordinaryWheelRimGraph M).Adj (x i) v↔(Q\wheelFamilyRim C).Adj (x i) v)
    (hrow:∀ i v,ordinaryPackingSpokes M (x i) v↔H (x i) v∧¬wheelFamilySpokes C (x i) v)
    (hcol:∀ i v,ordinaryPackingSpokes M v (u i)↔H v (u i)∧¬wheelFamilySpokes C v (u i)):
    ∃ P:Finset (OrdinaryWheel Q F H r),
      (∀ A∈P,∀ B∈P,A≠B→Disjoint (ordinaryWheelResources A) (ordinaryWheelResources B)) ∧
      P.biUnion ordinaryWheelResources=ordinaryHostResources (wheelFamilyRim C) (wheelFamilySpokes C)∪M.biUnion ordinaryWheelResources ∧
      P.biUnion ordinaryWheelResources∩E=Finset.univ.image e ∧
      ordinaryWheelRimGraph P=wheelFamilyRim C⊔ordinaryWheelRimGraph M ∧
      (∀ v a,ordinaryPackingSpokes P v a↔wheelFamilySpokes C v a∨ordinaryPackingSpokes M v a) ∧
      (∀ i v,(ordinaryWheelRimGraph P).Adj (x i) v↔Q.Adj (x i) v) ∧
      (∀ i v,ordinaryPackingSpokes P (x i) v↔H (x i) v) ∧
      (∀ i v,ordinaryPackingSpokes P v (u i)↔H v (u i)):=by
  have hi:∀ A∈Finset.univ.image C,∀ B∈Finset.univ.image C,A≠B→Disjoint (ordinaryWheelResources A) (ordinaryWheelResources B):=by
    intro A hA B hB hne
    obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hA
    obtain ⟨j,_,rfl⟩:=Finset.mem_image.mp hB
    exact hC i j (fun he=>hne (congrArg C he))
  have hg:=ordinary_wheel_packing_glue (Finset.univ.image C)
  rw [ordinary_family_image_rim C,ordinary_family_image_spokes C] at hg
  obtain ⟨P,hP,hres,hPr,hPs⟩:=hg M hi hM
  have hfamily:(Finset.univ.image C).biUnion ordinaryWheelResources=
      ordinaryHostResources (wheelFamilyRim C) (wheelFamilySpokes C):=by
    rw [wheelFamily_resources,Finset.image_biUnion]
  rw [hfamily] at hres
  have hsub:=wheelFamily_subhost C
  refine ⟨P,hP,hres,?_,hPr,hPs,?_,?_,?_⟩
  · rw [hres,Finset.union_inter_distrib_right,Finset.disjoint_iff_inter_eq_empty.mp hME,Finset.union_empty]
    exact (prescribed_wheel_family_exact_union C E e hC hinner).2.1
  · intro i v
    rw [hPr,SimpleGraph.sup_adj,hrim]
    have hh: (wheelFamilyRim C).Adj (x i) v→Q.Adj (x i) v:=fun h=>hsub.1 h
    change _∨(Q.Adj (x i) v∧¬_)↔Q.Adj (x i) v
    tauto
  · intro i v
    rw [hPs,hrow]
    have hh:=hsub.2 (x i) v
    tauto
  · intro i v
    rw [hPs,hcol]
    have hh:=hsub.2 v (u i)
    tauto

end Oberwolfach
