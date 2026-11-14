module

public import Oberwolfach.MarkedFactorPhysical
public import Oberwolfach.GraphSelectionDegrees

@[expose] public section

/-! Row, hub and physical-degree bounds for arbitrary marked wheel families.
Physical heads use the ambient permutation; their contributions are counted
at inverse-permutation rows as well as at the rows themselves. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K I:Type} [Fintype V] [Fintype U] [Fintype I] [DecidableEq V] [DecidableEq U]
    {tail head:E→V} {ktail khead:K→V} {H₀ HK:V→U→Prop} {π:Equiv.Perm V} {b m:ℕ}

def markedWheelRows (C:MarkedWheel tail head ktail khead m π b H₀ HK):Finset V:=Finset.univ.image C.1.val

def markedWheelRimGraph (C:MarkedWheel tail head ktail khead m π b H₀ HK):SimpleGraph V:=
  physicalEdgeGraph (markedCyclePhysicalEdges tail head ktail khead m π b C.1)

def markedFamilyRim (C:I→MarkedWheel tail head ktail khead m π b H₀ HK):SimpleGraph V:=⨆ i,markedWheelRimGraph (C i)

def markedFamilySpokes (C:I→MarkedWheel tail head ktail khead m π b H₀ HK) (v:V) (u:U):Prop:=
  ∃ i,(C i).2.val=u∧v∈markedWheelRows (C i)

def markedFamilyRowLoad (C:I→MarkedWheel tail head ktail khead m π b H₀ HK) (v:V):ℕ:=
  (Finset.univ.filter (fun i=>v∈markedWheelRows (C i))).card

def markedFamilyHubLoad (C:I→MarkedWheel tail head ktail khead m π b H₀ HK) (u:U):ℕ:=
  (Finset.univ.filter (fun i=>(C i).2.val=u)).card

theorem markedWheelRows_card (C:MarkedWheel tail head ktail khead m π b H₀ HK):
    (markedWheelRows C).card=m+1:=by
  rw [markedWheelRows,Finset.card_image_of_injective _ (permutationSeparated_injective π b C.1.val C.1.property.1)]
  simp

theorem markedWheelRimGraph_degree (hb:1≤b) (C:MarkedWheel tail head ktail khead m π b H₀ HK) (v:V):
    (markedWheelRimGraph C).degree v≤2:=by
  have hsep (i k:Unit) (j:Fin m):C.1.val j.succ≠π (C.1.val 0):=by
    exact (permutationSeparated_successor_avoid π b hb C.1.val C.1.property.1 0 j.succ (Fin.succ_ne_zero j).symm).symm
  have hinj:Function.Injective (fun p:Unit×Fin (m+1)=>C.1.val p.2):=by
    intro x y he
    exact Prod.ext (Subsingleton.elim _ _) (permutationSeparated_injective π b C.1.val C.1.property.1 he)
  have he:markedCyclePhysicalEdges tail head ktail khead m π b C.1=
      Finset.univ.image (fun p:Unit×Fin (m+1)=>({C.1.val p.2,twistedTupleHead π C.1.val p.2}:Finset V)):=by
    ext e
    simp only [markedCyclePhysicalEdges,Finset.mem_image,Finset.mem_univ,true_and,Function.comp_apply,
      markedCycle_physical_pair,Prod.exists,exists_const]
  apply (physicalEdgeGraph_degree_le_incident _ v).trans
  rw [he]
  exact twisted_factor_incident_card π (fun _:Unit=>C.1.val) hinj hsep v

theorem markedWheelRimGraph_supported (C:MarkedWheel tail head ktail khead m π b H₀ HK):
    GraphSupportedOn (markedWheelRows C∪(markedWheelRows C).image π) (markedWheelRimGraph C):=by
  intro x y hxy
  obtain ⟨i,_,hi⟩:=Finset.mem_image.mp hxy.2
  simp only [Function.comp_apply,markedCycle_physical_pair] at hi
  have htail:C.1.val i∈markedWheelRows C:=Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
  have hhead:twistedTupleHead π C.1.val i∈markedWheelRows C∪(markedWheelRows C).image π:=by
    refine Fin.lastCases ?_ (fun j=>?_) i
    · simp only [twistedTupleHead,Fin.snoc_last]
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨C.1.val 0,Finset.mem_image.mpr ⟨0,Finset.mem_univ _,rfl⟩,rfl⟩)
    · simp only [twistedTupleHead,Fin.snoc_castSucc]
      exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨j.succ,Finset.mem_univ _,rfl⟩)
  have hsub:({C.1.val i,twistedTupleHead π C.1.val i}:Finset V)⊆markedWheelRows C∪(markedWheelRows C).image π:=by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl|hz
    · exact Finset.mem_union_left _ htail
    · rw [Finset.mem_singleton.mp hz]
      exact hhead
  exact ⟨hsub (by rw [hi];simp),hsub (by rw [hi];simp)⟩

theorem markedFamilyRowLoad_total (C:I→MarkedWheel tail head ktail khead m π b H₀ HK):
    ∑ v,markedFamilyRowLoad C v=Fintype.card I*(m+1):=by
  simp only [markedFamilyRowLoad,Finset.card_filter]
  rw [Finset.sum_comm]
  have hc (i:I):(∑ v:V,if v∈markedWheelRows (C i) then (1:ℕ) else 0)=m+1:=by
    rw [←Finset.card_filter]
    have he:Finset.univ.filter (fun v=>v∈markedWheelRows (C i))=markedWheelRows (C i):=by ext v;simp
    rw [he,markedWheelRows_card]
  simp only [hc,Finset.sum_const,Finset.card_univ,smul_eq_mul]

theorem markedFamilyRowLoad_saturated (C:I→MarkedWheel tail head ktail khead m π b H₀ HK) (K:ℕ):
    K*(Finset.univ.filter (fun v=>K≤markedFamilyRowLoad C v)).card≤Fintype.card I*(m+1):=by
  calc
    _=∑ v∈Finset.univ.filter (fun v=>K≤markedFamilyRowLoad C v),K:=by simp [Nat.mul_comm]
    _≤∑ v∈Finset.univ.filter (fun v=>K≤markedFamilyRowLoad C v),markedFamilyRowLoad C v:=
      Finset.sum_le_sum (fun v hv=>(Finset.mem_filter.mp hv).2)
    _≤∑ v,markedFamilyRowLoad C v:=Finset.sum_le_univ_sum_of_nonneg (fun _=>Nat.zero_le _)
    _=_:=markedFamilyRowLoad_total C

theorem markedFamilyRim_degree (hb:1≤b) (C:I→MarkedWheel tail head ktail khead m π b H₀ HK) (v:V):
    (markedFamilyRim C).degree v≤2*(markedFamilyRowLoad C v+markedFamilyRowLoad C (π.symm v)):=by
  have hh:=graph_iSup_global_degree_bound (fun i=>markedWheelRimGraph (C i))
    (fun i=>markedWheelRows (C i)∪(markedWheelRows (C i)).image π) 2
    (fun i=>markedWheelRimGraph_supported (C i)) (fun i v=>markedWheelRimGraph_degree hb (C i) v) v
  apply hh.trans
  apply Nat.mul_le_mul_left
  have he:Finset.univ.filter (fun i=>v∈markedWheelRows (C i)∪(markedWheelRows (C i)).image π)=
      (Finset.univ.filter (fun i=>v∈markedWheelRows (C i)))∪
      (Finset.univ.filter (fun i=>π.symm v∈markedWheelRows (C i))):=by
    ext i
    have hh:v∈(markedWheelRows (C i)).image π↔π.symm v∈markedWheelRows (C i):=by
      constructor
      · rintro hv
        obtain ⟨z,hz,he⟩:=Finset.mem_image.mp hv
        simpa only [←he,Equiv.symm_apply_apply] using hz
      · intro hv;exact Finset.mem_image.mpr ⟨π.symm v,hv,π.apply_symm_apply v⟩
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_union,hh]
  rw [he]
  exact Finset.card_union_le _ _

theorem markedFamilySpokes_row (C:I→MarkedWheel tail head ktail khead m π b H₀ HK) (v:V):
    (Finset.univ.filter (markedFamilySpokes C v)).card≤markedFamilyRowLoad C v:=by
  have he:Finset.univ.filter (markedFamilySpokes C v)=
      (Finset.univ.filter (fun i=>v∈markedWheelRows (C i))).image (fun i=>(C i).2.val):=by
    ext u;simp only [Finset.mem_filter,Finset.mem_univ,true_and,markedFamilySpokes,Finset.mem_image];tauto
  rw [he];exact Finset.card_image_le

theorem markedFamilySpokes_column (C:I→MarkedWheel tail head ktail khead m π b H₀ HK) (u:U):
    (Finset.univ.filter (fun v=>markedFamilySpokes C v u)).card≤markedFamilyHubLoad C u*(m+1):=by
  have he:Finset.univ.filter (fun v=>markedFamilySpokes C v u)=
      (Finset.univ.filter (fun i=>(C i).2.val=u)).biUnion (fun i=>markedWheelRows (C i)):=by
    ext v;simp only [Finset.mem_filter,Finset.mem_univ,true_and,markedFamilySpokes,Finset.mem_biUnion]
  rw [he]
  exact Finset.card_biUnion_le.trans (by simp only [markedWheelRows_card,Finset.sum_const,smul_eq_mul];rfl)

theorem markedFamilyRowLoad_snoc {n:ℕ} (C:Fin n→MarkedWheel tail head ktail khead m π b H₀ HK)
    (B:MarkedWheel tail head ktail khead m π b H₀ HK) (v:V):
    markedFamilyRowLoad (Fin.snoc C B) v=markedFamilyRowLoad C v+(if v∈markedWheelRows B then 1 else 0):=by
  simp only [markedFamilyRowLoad,Finset.card_filter,Fin.sum_univ_castSucc,Fin.snoc_castSucc,Fin.snoc_last]

end Oberwolfach
