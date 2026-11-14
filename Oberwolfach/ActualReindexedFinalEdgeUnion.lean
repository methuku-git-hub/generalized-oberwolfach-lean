module

public import Oberwolfach.ActualFinalEdgeIdentification

@[expose] public section
/-! The retained marked indices and the residual data's selected indices may
be different presentations of the same family; the final edge union is
preserved by their explicit equivalence. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_reindexed_final_edge_union
    {X K J I:Type} [Fintype X] [DecidableEq X] [DecidableEq K] [DecidableEq J] [Fintype I]
    {F:SimpleGraph X} (data:ActualResidualData (K:=K) (J:=J) F)
    (b:I≃{i // i∈data.s₁})
    (ext:∀i:I,Fin (data.c*data.d+5)↪X) (inner:∀i:I,Fin (data.c*data.d+1)↪X)
    (hinner:∀i p,inner i p=ext i ⟨p.val+2,by omega⟩)
    (hsupp:∀i,(data.P (b i).val).support=List.ofFn (ext i))
    (p:∀i:I,F.Walk (inner i 0) (inner i (Fin.last (data.c*data.d))))
    (hp:∀i,(p i).support=List.ofFn (inner i)):
    (Finset.univ.biUnion (fun i:I=>(p i).edges.toFinset))=
      (Finset.univ.biUnion (fun i:{i // i∈data.s₁}=>(data.path (.inl i)).edges.toFinset)):=by
  ext edge
  constructor
  · intro h
    obtain ⟨i,_,hi⟩:=Finset.mem_biUnion.mp h
    apply Finset.mem_biUnion.mpr
    refine ⟨b i,Finset.mem_univ _,?_⟩
    rw [←actual_final_path_edge_set_matches_buffered_sequence data (b i) (ext i) (inner i) (hinner i) (hsupp i) (p i) (hp i)]
    exact hi
  · intro h
    obtain ⟨j,_,hj⟩:=Finset.mem_biUnion.mp h
    apply Finset.mem_biUnion.mpr
    refine ⟨b.symm j,Finset.mem_univ _,?_⟩
    have he:=actual_final_path_edge_set_matches_buffered_sequence data (b (b.symm j)) (ext (b.symm j)) (inner (b.symm j))
      (hinner (b.symm j)) (hsupp (b.symm j)) (p (b.symm j)) (hp (b.symm j))
    rw [he]
    rw [b.apply_symm_apply j]
    exact hj
end Oberwolfach
