module

public import Oberwolfach.MarkedCycleRestrictionByEndpoints
public import Oberwolfach.TypedMarkedPotentialDeletion
public import Oberwolfach.MarkedCommonCycleTransfers

@[expose] public section

/-! Fixed cycle weights at a hub, including their exact restriction under
rim deletion. The spoke at the tested root is omitted in the parent sum. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [DecidableEq V]
    {tail head:E→V} {ktail khead:K→V} {m b:ℕ} {π:Equiv.Perm V} {H₀ Hₖ:V→U→Prop}

def hubMarkedCycleClassEquiv (u:U) (A B:Finset V)
    (hA:∀ v,v∈A↔Hₖ v u) (hB:∀ v,v∈B↔H₀ v u):
    HubMarkedCycle tail head ktail khead m π b H₀ Hₖ u≃
      ClassMarkedCycle tail head ktail khead m π b A B where
  toFun C:=⟨C.val,C.property.1,(hA _).mpr C.property.2.1,fun i=>(hB _).mpr (C.property.2.2 i)⟩
  invFun C:=⟨C.val,C.property.1,(hA _).mp C.property.2.1,fun i=>(hB _).mp (C.property.2.2 i)⟩
  left_inv _:=rfl
  right_inv _:=rfl

def hubMarkedCycleCommonEquiv (u:U):
    HubMarkedCycle tail head ktail khead m π b H₀ Hₖ u≃
      CommonMarkedCycle tail head ktail khead m π b H₀ Hₖ u u where
  toFun C:=⟨⟨C.val,C.property.1⟩,C.property.2,C.property.2⟩
  invFun C:=⟨C.val.val,C.val.property,C.property.1⟩
  left_inv _:=rfl
  right_inv _:=rfl

theorem hub_marked_degree_eq_omitted (u:U) (hdis:∀ v,¬(H₀ v u∧Hₖ v u))
    (w:MarkedCycleTuple tail head ktail khead m π b→ℝ) (j:Bool) (v:V)
    (hv:if j then Hₖ v u else H₀ v u):
    hypergraphWeightedDegree (hubMarkedCycleVertices (H₀:=H₀) (Hₖ:=Hₖ) u) (fun C=>w (hubCycleAsMarked u C)) v=
      resourceRootOmittedLoad typedMarkedCycleVertices w (fun x:Bool×V=>if x.1 then Hₖ x.2 u else H₀ x.2 u) (j,v):=by
  let A:=Finset.univ.filter (fun v=>Hₖ v u)
  let B:=Finset.univ.filter (fun v=>H₀ v u)
  have hA:∀ v,v∈A↔Hₖ v u:=by intro v;simp [A]
  have hB:∀ v,v∈B↔H₀ v u:=by intro v;simp [B]
  have hAB:Disjoint A B:=by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact hdis x ⟨(hB _).mp hy,(hA _).mp hx⟩
  have hdeg:hypergraphWeightedDegree (hubMarkedCycleVertices (H₀:=H₀) (Hₖ:=Hₖ) u) (fun C=>w (hubCycleAsMarked u C)) v=
      hypergraphWeightedDegree classMarkedCycleVertices (fun C:ClassMarkedCycle tail head ktail khead m π b A B=>w (classMarkedCycleAsMarked C)) v:=by
    unfold hypergraphWeightedDegree
    rw [←Equiv.sum_comp (hubMarkedCycleClassEquiv u A B hA hB)]
    rfl
  rw [hdeg,typed_class_degree_eq_omitted hAB w j v (by cases j <;> simpa only [hA,hB,ite_true,ite_false,Bool.false_eq_true] using hv)]
  congr 1
  funext x
  apply propext
  rcases x with ⟨t,x⟩
  simp only [typedClassSet_mem,hA,hB]

theorem hub_marked_restricted_degree_eq_potential [Fintype E] [Fintype K]
    (u:U) (hdis:∀ v,¬(H₀ v u∧Hₖ v u)) (PE:E→Prop) (PK:K→Prop)
    (hinj:Function.Injective (fun e:E=>(tail e,head e)))
    (hkinj:Function.Injective (fun e:K=>(ktail e,khead e)))
    (w:MarkedCycleTuple tail head ktail khead m π b→ℝ) (j:Bool) (v:V)
    (hv:if j then Hₖ v u else H₀ v u):
    hypergraphWeightedDegree (hubMarkedCycleVertices (H₀:=H₀) (Hₖ:=Hₖ) u)
      (fun C:HubMarkedCycle (fun e:{e // PE e}=>tail e.val) (fun e=>head e.val)
        (fun e:{e // PK e}=>ktail e.val) (fun e=>khead e.val) m π b H₀ Hₖ u=>
        w (markedCycleToLarger PE PK (hubCycleAsMarked u C))) v=
      typedMarkedPotentialLoad (H₀:=fun (_:V) (_:Unit)=>True) (Hₖ:=fun _ _=>True)
        (fun W=>w W.1) (Sum.elim PE PK) (fun j v (_:Unit)=>if j then Hₖ v u else H₀ v u) (Sum.inr (j,v,())):=by
  rw [hub_marked_degree_eq_omitted u hdis (fun C=>w (markedCycleToLarger PE PK C)) j v hv]
  rw [marked_restricted_typed_root_load PE PK hinj hkinj w]
  rw [marked_unit_potential_load w (Sum.elim PE PK) (fun j v (_:Unit)=>if j then Hₖ v u else H₀ v u) j v]

theorem hub_marked_degree_eq_potential [Fintype E] [Fintype K]
    (u:U) (hdis:∀ v,¬(H₀ v u∧Hₖ v u))
    (w:MarkedCycleTuple tail head ktail khead m π b→ℝ) (j:Bool) (v:V)
    (hv:if j then Hₖ v u else H₀ v u):
    hypergraphWeightedDegree (hubMarkedCycleVertices (H₀:=H₀) (Hₖ:=Hₖ) u) (fun C=>w (hubCycleAsMarked u C)) v=
      typedMarkedPotentialLoad (H₀:=fun (_:V) (_:Unit)=>True) (Hₖ:=fun _ _=>True)
        (fun W=>w W.1) (fun _=>True) (fun j v (_:Unit)=>if j then Hₖ v u else H₀ v u) (Sum.inr (j,v,())):=by
  rw [hub_marked_degree_eq_omitted u hdis w j v hv,marked_unit_potential_load]
  unfold resourceRootOmittedLoad
  apply Finset.sum_congr (by ext;simp)
  intro C _
  simp only [implies_true,true_and]
  split_ifs <;> rfl

end Oberwolfach
