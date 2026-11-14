module

public import Oberwolfach.OrdinaryWheelDisjointness
public import Oberwolfach.OrdinaryWheelFamilies

@[expose] public section

/-! Triangle families with three disjoint vertex classes. The middle
label need not be injective. Its pair with the root, and its pair with the
hub, are the quantities required to be injective. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U I:Type} [Fintype V] [Fintype U] [Fintype I]
  [DecidableEq V] [DecidableEq U] [DecidableEq I]

theorem triangle_wheel_family_packing (Q F:SimpleGraph V) (H:V→U→Prop)
    (C:I→OrdinaryWheel Q F H 3) (x a z:I→V) (u:I→U)
    (hC:∀ i,∀ v∈(ordinaryWheelRim (C i)).support,v=x i∨v=a i∨v=z i)
    (hhub:∀ i,ordinaryWheelHub (C i)=u i)
    (hxa:∀ i j,x i≠a j) (hxz:∀ i j,x i≠z j) (haz:∀ i j,a i≠z j)
    (hzi:Function.Injective z) (hxai:Function.Injective (fun i=>(x i,a i)))
    (hxui:Function.Injective (fun i=>(x i,u i))) (haui:Function.Injective (fun i=>(a i,u i))):
    (∀ i j,i≠j→Disjoint (ordinaryWheelResources (C i)) (ordinaryWheelResources (C j))) ∧
    HasOrdinaryWheelDecomposition (wheelFamilyRim C) (wheelFamilySpokes C) 3:=by
  have hclass (i j:I) (v:V) (hv:v∈(ordinaryWheelRim (C i)).support)
      (hw:v∈(ordinaryWheelRim (C j)).support):
      (v=x i∧v=x j)∨(v=a i∧v=a j)∨(v=z i∧v=z j):=by
    rcases hC i v hv with hi|hi|hi <;> rcases hC j v hw with hj|hj|hj
    · exact Or.inl ⟨hi,hj⟩
    · exact (hxa i j (hi.symm.trans hj)).elim
    · exact (hxz i j (hi.symm.trans hj)).elim
    · exact (hxa j i (hj.symm.trans hi)).elim
    · exact Or.inr (Or.inl ⟨hi,hj⟩)
    · exact (haz i j (hi.symm.trans hj)).elim
    · exact (hxz j i (hj.symm.trans hi)).elim
    · exact (haz j i (hj.symm.trans hi)).elim
    · exact Or.inr (Or.inr ⟨hi,hj⟩)
  have hd (i j:I) (hij:i≠j):Disjoint (ordinaryWheelResources (C i)) (ordinaryWheelResources (C j)):=by
    apply (ordinaryWheelResources_disjoint_iff _ _).mpr
    constructor
    · apply disjoint_iff_inf_le.mpr
      intro v w hvw
      have hv:=hclass i j v hvw.1.mem_support_left hvw.2.mem_support_left
      have hw:=hclass i j w hvw.1.mem_support_right hvw.2.mem_support_right
      have hnoz (v:V) (h:v=z i∧v=z j):False:=hij (hzi (h.1.symm.trans h.2))
      have hv':(v=x i∧v=x j)∨(v=a i∧v=a j):=by
        rcases hv with h|h|h
        · exact Or.inl h
        · exact Or.inr h
        · exact (hnoz v h).elim
      have hw':(w=x i∧w=x j)∨(w=a i∧w=a j):=by
        rcases hw with h|h|h
        · exact Or.inl h
        · exact Or.inr h
        · exact (hnoz w h).elim
      rcases hv' with hv|hv <;> rcases hw' with hw|hw
      · exact (hvw.1.ne (hv.1.trans hw.1.symm)).elim
      · exact (hij (hxai (Prod.ext (hv.1.symm.trans hv.2) (hw.1.symm.trans hw.2)))).elim
      · exact (hij (hxai (Prod.ext (hw.1.symm.trans hw.2) (hv.1.symm.trans hv.2)))).elim
      · exact (hvw.1.ne (hv.1.trans hw.1.symm)).elim
    · intro he
      rw [hhub,hhub] at he
      apply Finset.disjoint_left.mpr
      intro v hv hw
      rcases hclass i j v (Set.mem_toFinset.mp hv) (Set.mem_toFinset.mp hw) with h|h|h
      · exact hij (hxui (Prod.ext (h.1.symm.trans h.2) he))
      · exact hij (haui (Prod.ext (h.1.symm.trans h.2) he))
      · exact hij (hzi (h.1.symm.trans h.2))
  exact ⟨hd,wheelFamily_decomposition C hd⟩

end Oberwolfach
