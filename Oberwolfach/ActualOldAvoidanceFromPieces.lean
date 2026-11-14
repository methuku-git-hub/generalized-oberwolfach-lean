module

public import Oberwolfach.ActualOldDomainSplit
public import Oberwolfach.ActualFinalInteriorIdentification
public import Oberwolfach.ActualPrescribedBufferedMarkers

@[expose] public section
/-! To protect retained interval labels, it suffices to protect the actual
old pieces and the approximate-path marker images; final markers lie on the
removed full paths. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_old_outside_final_avoids_reserved_set
    {X V K J I:Type} [Fintype X] [DecidableEq X] [DecidableEq V]
    [Fintype K] [DecidableEq K] [DecidableEq J] [Fintype I]
    {F:SimpleGraph X} (hF:F.IsRegularOfDegree 2)
    (data:ActualResidualData (K:=K) (J:=J) F)
    (hCycle:data.t.biUnion (fun j=>(data.C j).support.toFinset)⊆data.Cembed)
    (ext:∀i:K,Fin (data.c*data.d+5)↪X)
    (hsupp:∀i∈data.s₁∪data.s₂,(data.P i).support=List.ofFn (ext i))
    (b:I≃{i // i∈data.s₁}) (inner:∀i:I,Fin (data.c*data.d+1)↪X)
    (hinner:∀i k,inner i k=ext (b i).val ⟨k.val+2,by omega⟩)
    (hactive:∀i:K,i∈data.s₁∨i∈data.s₂)
    (ψ:X→V) (Y:Finset V)
    (happrox:∀i∈data.s₂,∀j:Fin (data.d+1),bufferedMarker data.c data.d (ext i) j∈data.prescribed→
      ψ (bufferedMarker data.c data.d (ext i) j)∉Y)
    (hpiece:∀z:actualOldPieceIndex data,∀x∈(actualOldPieceWalk data z).support,ψ x∉Y):
    ∀x,x∈data.oldDomain→x∉bufferedPathFullDomain (fun _=>data.c*data.d) inner→ψ x∉Y:=by
  have hfinal:∀i∈data.s₁,∀j:Fin (data.d+1),bufferedMarker data.c data.d (ext i) j∈
      bufferedPathFullDomain (fun _=>data.c*data.d) inner:=by
    intro i hi j
    let a:I:=b.symm ⟨i,hi⟩
    have ha:(b a).val=i:=by dsimp [a];simp
    have hj:j.val≤data.d:=by have hh:=j.isLt;omega
    have hle:data.c*j.val≤data.c*data.d:=Nat.mul_le_mul_left data.c hj
    let k:Fin (data.c*data.d+1):=⟨data.c*j.val,by omega⟩
    unfold bufferedPathFullDomain
    apply Finset.mem_biUnion.mpr
    refine ⟨a,Finset.mem_univ _,Finset.mem_image.mpr ⟨k,Finset.mem_univ _,?_⟩⟩
    rw [hinner,ha]
    unfold bufferedMarker
    congr 1
    apply Fin.ext
    simp only [Fin.val_mk,k]
    omega
  have hsubset:=buffered_strict_interior_subset_domain (fun _=>data.c*data.d) inner
  have heq:=actual_final_interiors_eq_buffered_strict data b (fun i=>ext (b i).val) inner hinner
    (fun i=>hsupp (b i).val (Finset.mem_union_left _ (b i).property))
  have hold:=actual_old_domain_without_final_interiors data hF hCycle
  intro x hx hout
  have hnot:x∉data.additionalSelectedInteriors:=by
    rw [heq]
    exact fun h=>hout (hsubset h)
  have hx':x∈data.prescribed ∪ Finset.univ.biUnion (fun z:actualOldPieceIndex data=>(actualOldPieceWalk data z).support.toFinset):=by
    rw [←hold]
    exact Finset.mem_sdiff.mpr ⟨hx,hnot⟩
  rcases Finset.mem_union.mp hx' with hpres|hpieces
  · obtain ⟨⟨i,j⟩,_,hi⟩:=Finset.mem_image.mp (actual_prescribed_subset_buffered_markers data ext hsupp hpres)
    subst x
    rcases hactive i with hfinali|happroxi
    · exact False.elim (hout (hfinal i hfinali j))
    · exact happrox i happroxi j hpres
  · obtain ⟨z,_,hz⟩:=Finset.mem_biUnion.mp hpieces
    exact hpiece z x (List.mem_toFinset.mp hz)
end Oberwolfach
