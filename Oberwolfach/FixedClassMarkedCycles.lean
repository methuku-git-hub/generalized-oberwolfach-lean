module

public import Oberwolfach.MarkedFactorPhysical
public import Oberwolfach.MarkedArcPairs
public import Oberwolfach.MarkedTransformerWheelPacking

@[expose] public section

/-! Canonical marked cycles supported on two fixed ambient classes. Displayed
pairs are auxiliary directed endpoints; their physical images retain the
successor permutation on the marked head. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 11000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V E K:Type} [Fintype V] [DecidableEq V]
    {tail head:E→V} {ktail khead:K→V} {m:ℕ} {π:Equiv.Perm V} {b:ℕ}

 abbrev ClassMarkedCycle (tail head:E→V) (ktail khead:K→V) (m:ℕ) (π:Equiv.Perm V) (b:ℕ)
    (A B:Finset V):=HubMarkedCycle tail head ktail khead m π b (fun x (_:Unit)=>x∈B) (fun x (_:Unit)=>x∈A) ()

 def classMarkedCycleVertices {A B:Finset V} (C:ClassMarkedCycle tail head ktail khead m π b A B):Finset V:=Finset.univ.image C.val

 def classMarkedCycleAsMarked {A B:Finset V} (C:ClassMarkedCycle tail head ktail khead m π b A B):
    MarkedCycleTuple tail head ktail khead m π b:=⟨C.val,C.property.1⟩

 def classMarkedCyclePairs {A B:Finset V} (C:ClassMarkedCycle tail head ktail khead m π b A B):Finset (V×V):=
    Finset.univ.image (fun i=>(C.val i,C.val (finRotate (m+1) i)))

 theorem classMarkedCycle_supported {A B:Finset V} (C:ClassMarkedCycle tail head ktail khead m π b A B):
    classMarkedCycleVertices C⊆A∪B:=by
  intro v hv
  obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hv
  refine Fin.cases ?_ (fun j=>?_) i
  · exact Finset.mem_union_left _ C.property.2.1
  · exact Finset.mem_union_right _ (C.property.2.2 j)

 theorem classMarkedCycle_profile {A B:Finset V} (hAB:Disjoint A B)
    (C:ClassMarkedCycle tail head ktail khead m π b A B):
    (classMarkedCycleVertices C∩A).card=1∧(classMarkedCycleVertices C∩B).card=m:=by
  have hinj:=permutationSeparated_injective π b C.val C.property.1.1
  have hA:classMarkedCycleVertices C∩A={C.val 0}:=by
    ext v
    simp only [Finset.mem_inter,Finset.mem_singleton]
    constructor
    · rintro ⟨hv,ha⟩
      obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hv
      revert ha
      refine Fin.cases (fun _=>rfl) (fun j hj=>?_) i
      exact False.elim (Finset.disjoint_left.mp hAB hj (C.property.2.2 j))
    · intro hv;subst v
      exact ⟨Finset.mem_image.mpr ⟨0,Finset.mem_univ _,rfl⟩,C.property.2.1⟩
  have hB:classMarkedCycleVertices C∩B=Finset.univ.image (fun i:Fin m=>C.val i.succ):=by
    ext v
    simp only [Finset.mem_inter,Finset.mem_image,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨hv,hb⟩
      obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hv
      revert hb
      refine Fin.cases (fun hb=>?_) (fun j _=>⟨j,rfl⟩) i
      exact False.elim (Finset.disjoint_left.mp hAB C.property.2.1 hb)
    · rintro ⟨i,rfl⟩
      exact ⟨Finset.mem_image.mpr ⟨i.succ,Finset.mem_univ _,rfl⟩,C.property.2.2 i⟩
  rw [hA,hB,Finset.card_singleton]
  constructor
  · rfl
  · rw [Finset.card_image_of_injective _ (show Function.Injective (fun i:Fin m=>C.val i.succ) from
      fun i j hij=>Fin.succ_injective m (hinj hij)),Finset.card_univ,Fintype.card_fin]

 theorem classMarkedCycle_multiplicity (A B:Finset V) (Y:Finset V):
    Fintype.card {C:ClassMarkedCycle tail head ktail khead m π b A B // classMarkedCycleVertices C=Y}≤(m+1)^(m+1):=
  ambient_hubMarkedCycle_multiplicity (tail:=tail) (head:=head) (ktail:=ktail) (khead:=khead)
    (m:=m) (π:=π) (b:=b) (H₀:=fun x (_:Unit)=>x∈B) (Hₖ:=fun x (_:Unit)=>x∈A) () Y

 theorem classMarkedCycle_pairs_supported (hm:1≤m) {A B:Finset V}
    (C:ClassMarkedCycle tail head ktail khead m π b A B) (p:V×V) (hp:p∈classMarkedCyclePairs C):
    p.1≠p.2∧p.1∈classMarkedCycleVertices C∧p.2∈classMarkedCycleVertices C:=by
  obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hp
  exact ⟨marked_cycle_auxiliary_arc_nonloop hm (classMarkedCycleAsMarked C) i,
    Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩,
    Finset.mem_image.mpr ⟨finRotate (m+1) i,Finset.mem_univ _,rfl⟩⟩

 theorem classMarkedCycle_pairs_card {A B:Finset V}
    (C:ClassMarkedCycle tail head ktail khead m π b A B):(classMarkedCyclePairs C).card≤m+1:=by
  exact (Finset.card_image_le).trans (by simp)

 theorem classMarkedCycle_pairs_degree {A B:Finset V}
    (C:ClassMarkedCycle tail head ktail khead m π b A B) (v:V):
    ((classMarkedCyclePairs C).filter (fun p=>v=p.1∨v=p.2)).card≤2:=by
  have hinj:=permutationSeparated_injective π b C.val C.property.1.1
  let S:=Finset.univ.filter (fun i=>v=C.val i)
  let T:=Finset.univ.filter (fun i=>v=C.val (finRotate (m+1) i))
  have hS:S.card≤1:=Finset.card_le_one.mpr (by
    intro i hi j hj
    exact hinj ((Finset.mem_filter.mp hi).2.symm.trans (Finset.mem_filter.mp hj).2))
  have hT:T.card≤1:=Finset.card_le_one.mpr (by
    intro i hi j hj
    exact (finRotate (m+1)).injective (hinj ((Finset.mem_filter.mp hi).2.symm.trans (Finset.mem_filter.mp hj).2)))
  have he:(classMarkedCyclePairs C).filter (fun p=>v=p.1∨v=p.2)=
      (S∪T).image (fun i=>(C.val i,C.val (finRotate (m+1) i))):=by
    rw [classMarkedCyclePairs,Finset.filter_image]
    congr 1
    ext i
    simp only [S,T,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_union]
  rw [he]
  exact (Finset.card_image_le).trans ((Finset.card_union_le S T).trans (by omega))

 theorem classMarkedCycle_factor_physical_disjoint {A B:Finset V}
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (M N:Finset (ClassMarkedCycle tail head ktail khead m π b A B))
    (hdis:Disjoint (M.biUnion classMarkedCyclePairs) (N.biUnion classMarkedCyclePairs)):
    Disjoint (M.biUnion (fun C=>markedCyclePhysicalEdges tail head ktail khead m π b (classMarkedCycleAsMarked C)))
      (N.biUnion (fun C=>markedCyclePhysicalEdges tail head ktail khead m π b (classMarkedCycleAsMarked C))):=by
  apply Finset.disjoint_left.mpr
  intro e he hf
  obtain ⟨C,hC,he⟩:=Finset.mem_biUnion.mp he
  obtain ⟨D,hD,hf⟩:=Finset.mem_biUnion.mp hf
  obtain ⟨i,_,hi⟩:=Finset.mem_image.mp he
  obtain ⟨j,_,hj⟩:=Finset.mem_image.mp hf
  have hh:=marked_cycle_common_physical_endpoints hp (classMarkedCycleAsMarked C) (classMarkedCycleAsMarked D) i j (hi.trans hj.symm)
  exact Finset.disjoint_left.mp hdis
    (Finset.mem_biUnion.mpr ⟨C,hC,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩)
    (Finset.mem_biUnion.mpr ⟨D,hD,Finset.mem_image.mpr ⟨j,Finset.mem_univ _,Prod.ext hh.1.symm hh.2.symm⟩⟩)

end Oberwolfach
