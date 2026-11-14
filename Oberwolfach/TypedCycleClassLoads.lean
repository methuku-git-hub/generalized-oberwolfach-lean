module

public import Oberwolfach.FixedClassMarkedCycles
public import Oberwolfach.RootOmittedLocalStability
public import Oberwolfach.Neighbourhoods

@[expose] public section

/-! Original-weight class loads with the tested typed vertex omitted.
The comparison is uniform over every ambient root, including roots absent
from both the old and new classes. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V E K:Type} [Fintype V] [DecidableEq V]
    {tail head:E→V} {ktail khead:K→V} {m:ℕ} {π:Equiv.Perm V} {b:ℕ}

 def typedClassSet (A B:Finset V):Finset (Bool×V):=
    A.image (fun x=>(true,x))∪B.image (fun x=>(false,x))

 theorem typedClassSet_mem (A B:Finset V) (j:Bool) (v:V):
    (j,v)∈typedClassSet A B↔if j then v∈A else v∈B:=by
  cases j <;> simp [typedClassSet]

 theorem typedClassSet_card (A B:Finset V):(typedClassSet A B).card=A.card+B.card:=by
  have hd:Disjoint (A.image (fun x=>(true,x))) (B.image (fun x=>(false,x))):=by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨v,_,rfl⟩:=Finset.mem_image.mp hx
    obtain ⟨w,_,h⟩:=Finset.mem_image.mp hy
    have hh:=congrArg Prod.fst h
    cases hh
  rw [typedClassSet,Finset.card_union_of_disjoint hd,
    Finset.card_image_of_injective _ (fun x y h=>congrArg Prod.snd h),
    Finset.card_image_of_injective _ (fun x y h=>congrArg Prod.snd h)]

 theorem typedClassSet_changed (A B A' B':Finset V):
    changed (typedClassSet A B) (typedClassSet A' B')=typedClassSet (changed A A') (changed B B'):=by
  ext x
  rcases x with ⟨j,v⟩
  simp only [changed,Finset.mem_union,Finset.mem_sdiff,typedClassSet_mem]
  cases j <;> simp

 def typedMarkedCycleVertices (C:MarkedCycleTuple tail head ktail khead m π b):Finset (Bool×V):=
    Finset.univ.image (fun i=>(markedPositionType i,C.val i))

 theorem typedMarkedCycleVertices_card (C:MarkedCycleTuple tail head ktail khead m π b):
    (typedMarkedCycleVertices C).card=m+1:=by
  have hi:Function.Injective (fun i=>(markedPositionType i,C.val i)):=fun i j h=>
    permutationSeparated_injective π b C.val C.property.1 (congrArg Prod.snd h)
  rw [typedMarkedCycleVertices,Finset.card_image_of_injective _ hi,Finset.card_univ,Fintype.card_fin]

 theorem typedMarkedCycleVertices_multiplicity (Y:Finset (Bool×V)):
    Fintype.card {C:MarkedCycleTuple tail head ktail khead m π b // typedMarkedCycleVertices C=Y}≤(m+1)^(m+1):=by
  apply tuple_resource_multiplicity (m+1) typedMarkedCycleVertices
    (fun C i=>(markedPositionType i,C.val i)) ?_ (fun _=>rfl) (fun C=>typedMarkedCycleVertices_card C) Y
  intro C D he
  apply Subtype.ext
  funext i
  exact congrArg Prod.snd (congrFun he i)

 theorem typedMarkedCycleVertices_subset (C:MarkedCycleTuple tail head ktail khead m π b) (A B:Finset V):
    typedMarkedCycleVertices C⊆typedClassSet A B↔C.val 0∈A∧∀ i:Fin m,C.val i.succ∈B:=by
  constructor
  · intro h
    constructor
    · have hh:=h (Finset.mem_image.mpr ⟨0,Finset.mem_univ _,rfl⟩)
      simpa only [typedClassSet_mem,markedPositionType,decide_true,ite_true] using hh
    · intro i
      have hh:=h (Finset.mem_image.mpr ⟨i.succ,Finset.mem_univ _,rfl⟩)
      simpa only [typedClassSet_mem,markedPositionType,Fin.succ_ne_zero,decide_false,Bool.false_eq_true,ite_false] using hh
  · intro h x hx
    obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hx
    refine Fin.cases ?_ (fun i=>?_) i
    · simpa only [typedClassSet_mem,markedPositionType,decide_true,ite_true] using h.1
    · simpa only [typedClassSet_mem,markedPositionType,Fin.succ_ne_zero,decide_false,Bool.false_eq_true,ite_false] using h.2 i

 def typedClassCycleEquiv (A B:Finset V):ClassMarkedCycle tail head ktail khead m π b A B≃
    {C:MarkedCycleTuple tail head ktail khead m π b // typedMarkedCycleVertices C⊆typedClassSet A B} where
  toFun C:=⟨classMarkedCycleAsMarked C,(typedMarkedCycleVertices_subset _ A B).mpr C.property.2⟩
  invFun C:=⟨C.val.val,⟨C.val.property,(typedMarkedCycleVertices_subset C.val A B).mp C.property⟩⟩
  left_inv _:=by apply Subtype.ext;rfl
  right_inv _:=by apply Subtype.ext;apply Subtype.ext;rfl

 theorem typed_class_root_membership {A B:Finset V} (hAB:Disjoint A B)
    (C:ClassMarkedCycle tail head ktail khead m π b A B) (j:Bool) (v:V)
    (hv:if j then v∈A else v∈B):
    (j,v)∈typedMarkedCycleVertices (classMarkedCycleAsMarked C)↔v∈classMarkedCycleVertices C:=by
  constructor
  · intro hh
    obtain ⟨i,_,hi⟩:=Finset.mem_image.mp hh
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,congrArg Prod.snd hi⟩
  · intro hh
    obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hh
    have hi:markedPositionType i=j:=by
      revert hv
      refine Fin.cases ?_ (fun k=>?_) i
      · cases j
        · intro hv;exact False.elim (Finset.disjoint_left.mp hAB C.property.2.1 hv)
        · intro _;simp [markedPositionType]
      · cases j
        · intro _;simp [markedPositionType]
        · intro hv;exact False.elim (Finset.disjoint_left.mp hAB hv (C.property.2.2 k))
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,Prod.ext hi rfl⟩

 theorem typed_class_degree_eq_omitted {A B:Finset V} (hAB:Disjoint A B)
    (w:MarkedCycleTuple tail head ktail khead m π b→ℝ) (j:Bool) (v:V)
    (hv:if j then v∈A else v∈B):
    hypergraphWeightedDegree classMarkedCycleVertices (fun C:ClassMarkedCycle tail head ktail khead m π b A B=>w (classMarkedCycleAsMarked C)) v=
      resourceRootOmittedLoad typedMarkedCycleVertices w (fun x=>x∈typedClassSet A B) (j,v):=by
  rw [resourceRootOmittedLoad_present _ _ _ _ ((typedClassSet_mem A B j v).mpr hv)]
  unfold hypergraphWeightedDegree
  have he:=Equiv.sum_comp (typedClassCycleEquiv (tail:=tail) (head:=head) (ktail:=ktail) (khead:=khead) (m:=m) (π:=π) (b:=b) A B)
    (fun C=>if (j,v)∈typedMarkedCycleVertices C.val then w C.val else 0)
  have hleft:(∑ C:ClassMarkedCycle tail head ktail khead m π b A B,if v∈classMarkedCycleVertices C then w (classMarkedCycleAsMarked C) else 0)=
      ∑ C:{C:MarkedCycleTuple tail head ktail khead m π b // typedMarkedCycleVertices C⊆typedClassSet A B},
        if (j,v)∈typedMarkedCycleVertices C.val then w C.val else 0:=by
    rw [←he]
    apply Finset.sum_congr rfl
    intro C _
    change (if v∈classMarkedCycleVertices C then w (classMarkedCycleAsMarked C) else 0)=_
    have hm:=typed_class_root_membership hAB C j v hv
    change (if v∈classMarkedCycleVertices C then w (classMarkedCycleAsMarked C) else 0)=
      (if (j,v)∈typedMarkedCycleVertices (classMarkedCycleAsMarked C) then w (classMarkedCycleAsMarked C) else 0)
    by_cases h:v∈classMarkedCycleVertices C
    · simp only [h,hm.mpr h,ite_true]
    · have hn: (j,v)∉typedMarkedCycleVertices (classMarkedCycleAsMarked C):=fun ht=>h (hm.mp ht)
      simp only [h,hn,ite_false]
  rw [hleft]
  have hs:=Finset.sum_subtype (F:=inferInstance)
    (p:=fun C:MarkedCycleTuple tail head ktail khead m π b=>typedMarkedCycleVertices C⊆typedClassSet A B)
    (Finset.univ.filter (fun C=>typedMarkedCycleVertices C⊆typedClassSet A B)) (fun _=>by simp)
    (fun C=>if (j,v)∈typedMarkedCycleVertices C then w C else 0)
  rw [←hs,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro C _
  have he : (∀ f∈typedMarkedCycleVertices C,f∈typedClassSet A B) ↔
      typedMarkedCycleVertices C⊆typedClassSet A B := Iff.rfl
  by_cases ht:typedMarkedCycleVertices C⊆typedClassSet A B <;>
    by_cases hv:(j,v)∈typedMarkedCycleVertices C <;>
      simp only [he,ht,hv,true_and,false_and,ite_true,ite_false]


 theorem typed_class_load_change (hm:1≤m)
    (w:MarkedCycleTuple tail head ktail khead m π b→ℝ) (B₀:ℝ) (hB:0≤B₀)
    (hw:∀ C,0≤w C∧w C≤B₀) (A B A' B':Finset V) (j:Bool) (v:V):
    |resourceRootOmittedLoad typedMarkedCycleVertices w (fun x=>x∈typedClassSet A B) (j,v)-
      resourceRootOmittedLoad typedMarkedCycleVertices w (fun x=>x∈typedClassSet A' B') (j,v)|≤
      (((changed A A').card:ℝ)+(changed B B').card)*((m+1)^(m+1):ℕ)*
        (2*(Fintype.card V:ℝ)+1)^(m-1)*B₀:=by
  have hh:=root_omitted_load_local_change typedMarkedCycleVertices (m+1) ((m+1)^(m+1)) (by omega)
    typedMarkedCycleVertices_card typedMarkedCycleVertices_multiplicity w B₀ hB hw
    (typedClassSet A B) (typedClassSet A' B') (j,v)
  have hd (P Q:Finset (Bool×V)):(P\Q).card+(Q\P).card=(changed P Q).card:=by
    have hdis:Disjoint (P\Q) (Q\P):=by
      apply Finset.disjoint_left.mpr
      intro x hx hy
      exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_sdiff.mp hy).1
    have he:changed P Q=(P\Q)∪(Q\P):=by
      ext x
      simp only [changed,Finset.mem_union,Finset.mem_sdiff]
    rw [he,Finset.card_union_of_disjoint hdis]
  rw [hd,typedClassSet_changed,typedClassSet_card] at hh
  have hcard:(((typedClassSet A B∪typedClassSet A' B').card:ℝ)+1)≤2*(Fintype.card V:ℝ)+1:=by
    have h:((typedClassSet A B∪typedClassSet A' B').card:ℝ)≤Fintype.card (Bool×V):=by
      exact_mod_cast Finset.card_le_univ (typedClassSet A B∪typedClassSet A' B')
    simpa only [Fintype.card_prod,Fintype.card_bool,Nat.cast_mul,Nat.cast_ofNat] using add_le_add h (le_refl (1:ℝ))
  have hpow:=pow_le_pow_left₀ (by positivity) hcard (m-1)
  have he:m+1-2=m-1:=by omega
  simp only [he,Nat.cast_add] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (by positivity)) hB)

end Oberwolfach
