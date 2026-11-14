module

public import Oberwolfach.BufferedMarkerAnchorEmbedding
public import Oberwolfach.ResidualActualData

@[expose] public section
/-! Every actual prescribed source vertex is one of the markers of its
original buffered parent path. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_prescribed_subset_buffered_markers
    {X K J:Type} [Fintype X] [DecidableEq X] [Fintype K] [DecidableEq K] [DecidableEq J]
    {G:SimpleGraph X} (data:ActualResidualData (K:=K) (J:=J) G)
    (ext:∀i:K,Fin (data.c*data.d+5)↪X)
    (hsupp:∀i∈data.s₁∪data.s₂,(data.P i).support=List.ofFn (ext i)):
    data.prescribed⊆Finset.univ.image (fun z:K×Fin (data.d+1)=>bufferedMarker data.c data.d (ext z.1) z.2):=by
  classical
  have hv:∀i∈data.s₁∪data.s₂,∀j:Fin (data.d+1),
      (data.P i).getVert (2+data.c*j.val)=bufferedMarker data.c data.d (ext i) j:=by
    intro i hi j
    have hj:j.val≤data.d:=by have hh:=j.isLt;omega
    have hm:=Nat.mul_le_mul_left data.c hj
    have hh:some ((data.P i).getVert (2+data.c*j.val))=(data.P i).support[2+data.c*j.val]? :=
      (data.P i).getVert_eq_support_getElem? (by rw [data.hlen i hi];omega)
    rw [hsupp i hi] at hh
    simpa only [List.getElem?_ofFn,dif_pos (show 2+data.c*j.val<data.c*data.d+5 by omega),Option.some.injEq,
      bufferedMarker] using hh
  intro x hx
  change x∈(data.s₁.biUnion (fun i=>{(data.P i).getVert 2,(data.P i).getVert (2+data.c*data.d)})) ∪
    (data.remaining ∩ data.s₂.biUnion (fun i=>(Finset.range (data.d+1)).image (fun j=>(data.P i).getVert (2+data.c*j)))) at hx
  rcases Finset.mem_union.mp hx with hfinal|happrox
  · obtain ⟨i,hi,hx⟩:=Finset.mem_biUnion.mp hfinal
    rcases Finset.mem_insert.mp hx with hx|hx
    · subst x
      apply Finset.mem_image.mpr
      refine ⟨(i,0),Finset.mem_univ _,?_⟩
      simpa only [Fin.val_zero,Nat.mul_zero,Nat.add_zero] using (hv i (Finset.mem_union_left _ hi) 0).symm
    · have hx':x=(data.P i).getVert (2+data.c*data.d):=Finset.mem_singleton.mp hx
      subst x
      apply Finset.mem_image.mpr
      refine ⟨(i,Fin.last data.d),Finset.mem_univ _,?_⟩
      simpa only [Fin.val_last] using (hv i (Finset.mem_union_left _ hi) (Fin.last data.d)).symm
  · obtain ⟨i,hi,hx⟩:=Finset.mem_biUnion.mp (Finset.mem_inter.mp happrox).2
    obtain ⟨j,hj,hx⟩:=Finset.mem_image.mp hx
    have hj':j<data.d+1:=Finset.mem_range.mp hj
    subst x
    apply Finset.mem_image.mpr
    refine ⟨(i,⟨j,hj'⟩),Finset.mem_univ _,?_⟩
    exact (hv i (Finset.mem_union_right _ hi) ⟨j,hj'⟩).symm
end Oberwolfach
