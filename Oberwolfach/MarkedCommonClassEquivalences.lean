module

public import Oberwolfach.FixedClassMarkedCycles
public import Oberwolfach.MarkedCommonCycleTransfers

@[expose] public section

/-! Exact cycle and root-first-path identifications for two common hub
classes. These maps keep every ordered coordinate; no root membership is
introduced in the path family. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [DecidableEq V]
    {tail head:E→V} {ktail khead:K→V} {m b:ℕ} {π:Equiv.Perm V}
    {H₀ HK:V→U→Prop}

def commonMarkedCycleClassEquiv (u u':U) (A B:Finset V)
    (hA:∀ v,v∈A↔HK v u∧HK v u') (hB:∀ v,v∈B↔H₀ v u∧H₀ v u'):
    CommonMarkedCycle tail head ktail khead m π b H₀ HK u u'≃
      ClassMarkedCycle tail head ktail khead m π b A B where
  toFun C:=⟨C.val.val,C.val.property,
    (hA _).mpr ⟨C.property.1.1,C.property.2.1⟩,
    fun i=>(hB _).mpr ⟨C.property.1.2 i,C.property.2.2 i⟩⟩
  invFun C:=⟨⟨C.val,C.property.1⟩,
    ⟨((hA _).mp C.property.2.1).1,fun i=>((hB _).mp (C.property.2.2 i)).1⟩,
    ⟨((hA _).mp C.property.2.1).2,fun i=>((hB _).mp (C.property.2.2 i)).2⟩⟩
  left_inv _:=rfl
  right_inv _:=rfl

theorem common_marked_cycle_class_card (u u':U) (A B:Finset V)
    (hA:∀ v,v∈A↔HK v u∧HK v u') (hB:∀ v,v∈B↔H₀ v u∧H₀ v u'):
    Fintype.card (CommonMarkedCycle tail head ktail khead m π b H₀ HK u u')=
      Fintype.card (ClassMarkedCycle tail head ktail khead m π b A B):=
  Fintype.card_congr (commonMarkedCycleClassEquiv u u' A B hA hB)

def rootFirstCommonMarkedPathClassEquiv (u u':U) (A B:Finset V)
    (hA:∀ v,v∈A↔HK v u∧HK v u') (hB:∀ v,v∈B↔H₀ v u∧H₀ v u') (j:Bool) (v v':V):
    RootFirstCommonMarkedPath tail head ktail khead m π b H₀ HK j v v' u u'≃
      RootFirstCommonMarkedPath tail head ktail khead m π b
        (fun x (_:Unit)=>x∈B) (fun x (_:Unit)=>x∈A) j v v' () ():=
  Equiv.subtypeEquivRight (fun z=>by
    apply and_congr Iff.rfl
    apply and_congr Iff.rfl
    apply forall_congr'
    intro i
    cases h:rootFirstSpokeType m j i.succ <;> simp only [h,ite_true,ite_false,Bool.false_eq_true,and_self,hA,hB])

theorem root_first_common_marked_path_class_card (u u':U) (A B:Finset V)
    (hA:∀ v,v∈A↔HK v u∧HK v u') (hB:∀ v,v∈B↔H₀ v u∧H₀ v u') (j:Bool) (v v':V):
    Fintype.card (RootFirstCommonMarkedPath tail head ktail khead m π b H₀ HK j v v' u u')=
      Fintype.card (RootFirstCommonMarkedPath tail head ktail khead m π b
        (fun x (_:Unit)=>x∈B) (fun x (_:Unit)=>x∈A) j v v' () ()):=
  Fintype.card_congr (rootFirstCommonMarkedPathClassEquiv u u' A B hA hB j v v')

end Oberwolfach
