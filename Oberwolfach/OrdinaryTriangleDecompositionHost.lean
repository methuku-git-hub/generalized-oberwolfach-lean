module

public import Oberwolfach.OrdinaryExactDecomposition
public import Oberwolfach.TriangleSupportEdges

@[expose] public section
/-! An exact triangle-wheel decomposition in a graph disjoint from the
conflict graph can be realized in that host with its conflict condition.
For triangles, every two distinct supported rim vertices are adjacent. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
set_option synthInstance.maxSize 2048
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_triangle_decomposition_in_conflict_free_host
    (Q F:SimpleGraph V) (H:V→U→Prop) (hQF:Disjoint Q F)
    (hdec:HasOrdinaryWheelDecomposition Q H 3):
    HasResourceDecomposition (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=3))
      (ordinaryHostResources Q H):=by
  obtain ⟨M,hM,hcover⟩:=hdec
  have hsurv (W:UniversalOrdinaryWheel V U 3) (hW:W∈M):OrdinaryWheelSurvives W Q H:=by
    apply (ordinaryWheelResources_subset_host W Q H).mp
    intro e he
    rw [←hcover]
    exact Finset.mem_biUnion.mpr ⟨W,hW,he⟩
  let f:{W:UniversalOrdinaryWheel V U 3 // W∈M}→OrdinaryWheel Q F H 3:=fun W=>
    ⟨(⟨W.val.val.1.val,(hsurv W.val W.property).1⟩,W.val.val.2),
      (hsurv W.val W.property).2,by
        intro v hv w hw hfw
        by_cases hvw:v=w
        · subst w;exact hfw.ne rfl
        · have hrim: (ordinaryWheelRim W.val).Adj v w:=
            (W.val.val.1.val.property.triangle_adj v w).mpr ⟨hv,hw,hvw⟩
          exact (disjoint_iff_inf_le.mp hQF) ⟨(hsurv W.val W.property).1 hrim,hfw⟩⟩
  have hf (W:{W:UniversalOrdinaryWheel V U 3 // W∈M}):ordinaryWheelResources (f W)=ordinaryWheelResources W.val:=rfl
  let N:=Finset.univ.image f
  refine ⟨N,?_,?_⟩
  · intro A hA B hB hne
    obtain ⟨a,_,rfl⟩:=Finset.mem_image.mp hA
    obtain ⟨b,_,rfl⟩:=Finset.mem_image.mp hB
    rw [hf,hf]
    apply hM a.val a.property b.val b.property
    intro he
    apply hne
    exact congrArg f (Subtype.ext he)
  · ext e
    constructor
    · intro he
      obtain ⟨W,hW,heW⟩:=Finset.mem_biUnion.mp he
      obtain ⟨a,_,rfl⟩:=Finset.mem_image.mp hW
      rw [hf] at heW
      rw [←hcover]
      exact Finset.mem_biUnion.mpr ⟨a.val,a.property,heW⟩
    · intro he
      rw [←hcover] at he
      obtain ⟨W,hW,heW⟩:=Finset.mem_biUnion.mp he
      apply Finset.mem_biUnion.mpr
      refine ⟨f ⟨W,hW⟩,Finset.mem_image.mpr ⟨⟨W,hW⟩,Finset.mem_univ _,rfl⟩,?_⟩
      rw [hf]
      exact heW
theorem ordinary_triangle_decomposition_in_ambient_host
    (P Q F:SimpleGraph V) (Hbase H:V→U→Prop) (hQP:Q≤P) (hQF:Disjoint Q F)
    (hH:∀v u,H v u→Hbase v u) (hdec:HasOrdinaryWheelDecomposition Q H 3):
    HasResourceDecomposition (ordinaryWheelResources (P:=P) (F:=F) (Hbase:=Hbase) (r:=3))
      (ordinaryHostResources Q H):=by
  have hh:=ordinary_triangle_decomposition_in_conflict_free_host Q F H hQF hdec
  exact resource_decomposition_map ordinaryWheelResources ordinaryWheelResources
    (ordinaryWheelToLarger (F:=F) (r:=3) hQP hH)
    (ordinaryWheelToLarger_resources hQP hH) (ordinaryHostResources Q H) hh
end Oberwolfach
