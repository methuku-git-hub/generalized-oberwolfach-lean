module

public import Oberwolfach.ActualBufferedFinalPathIdentification
public import Oberwolfach.BufferedStrictInteriorSet

@[expose] public section
/-! The actual final-path interiors are exactly the buffered strict interiors,
after reindexing the retained sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_final_interiors_eq_buffered_strict
    {X K J I:Type} [Fintype X] [DecidableEq X] [DecidableEq K] [DecidableEq J] [Fintype I]
    {F:SimpleGraph X} (data:ActualResidualData (K:=K) (J:=J) F)
    (b:I≃{i // i∈data.s₁})
    (ext:∀i:I,Fin (data.c*data.d+5)↪X) (inner:∀i:I,Fin (data.c*data.d+1)↪X)
    (hinner:∀i p,inner i p=ext i ⟨p.val+2,by omega⟩)
    (hsupp:∀i,(data.P (b i).val).support=List.ofFn (ext i)):
    data.additionalSelectedInteriors=bufferedPathStrictInterior (fun _=>data.c*data.d) inner:=by
  classical
  have hlocal:∀i:I,(data.path (.inl (b i))).support.toFinset\
      {data.start (.inl (b i)),data.finish (.inl (b i))}=
      ((Finset.univ.filter (fun p:Fin (data.c*data.d+1)=>0<p.val ∧ p.val<data.c*data.d)).image (inner i)):=by
    intro i
    obtain ⟨hs,hf,hp⟩:=actual_final_path_matches_buffered_sequence data (b i) (ext i) (inner i) (hinner i) (hsupp i)
    rw [hp,hs,hf,buffered_single_strict_interior_eq]
    congr 1
    ext x
    simp only [List.mem_toFinset,List.mem_ofFn,Finset.mem_image,Finset.mem_univ,true_and]
  unfold ActualResidualData.additionalSelectedInteriors bufferedPathStrictInterior
  ext x
  constructor
  · intro hx
    obtain ⟨j,_,hj⟩:=Finset.mem_biUnion.mp hx
    let i:=b.symm j
    apply Finset.mem_biUnion.mpr
    refine ⟨i,Finset.mem_univ _,?_⟩
    have hh:=hlocal i
    have hb:b i=j:=b.apply_symm_apply j
    rw [hb] at hh
    rw [←hh]
    exact hj
  · intro hx
    obtain ⟨i,_,hi⟩:=Finset.mem_biUnion.mp hx
    apply Finset.mem_biUnion.mpr
    refine ⟨b i,Finset.mem_univ _,?_⟩
    rw [hlocal i]
    exact hi
end Oberwolfach
