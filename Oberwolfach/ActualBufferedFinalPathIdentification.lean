module

public import Oberwolfach.ResidualActualData
public import Oberwolfach.ResidualPathInterval

@[expose] public section
/-! The actual deleted final path is the central path in its buffered walk. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_final_path_matches_buffered_sequence
    {X K J:Type} [Fintype X] [DecidableEq X] [DecidableEq K] [DecidableEq J]
    {F:SimpleGraph X} (data:ActualResidualData (K:=K) (J:=J) F)
    (i:{i // i∈data.s₁})
    (ext:Fin (data.c*data.d+5)↪X)
    (inner:Fin (data.c*data.d+1)↪X)
    (hinner:∀p,inner p=ext ⟨p.val+2,by omega⟩)
    (hsupp:(data.P i.val).support=List.ofFn ext):
    data.start (.inl i)=inner 0 ∧
    data.finish (.inl i)=inner (Fin.last (data.c*data.d)) ∧
    (data.path (.inl i)).support=List.ofFn inner:=by
  have hlen:(data.P i.val).length=data.c*data.d+4:=
    data.hlen i.val (Finset.mem_union_left _ i.property)
  have hv:∀j:ℕ,(hj:j≤data.c*data.d+4)→(data.P i.val).getVert j=ext ⟨j,by omega⟩:=by
    intro j hj
    have hh:some ((data.P i.val).getVert j)=(data.P i.val).support[j]? :=
      (data.P i.val).getVert_eq_support_getElem? (by omega)
    rw [hsupp] at hh
    simpa only [List.getElem?_ofFn,dif_pos (show j<data.c*data.d+5 by omega),Option.some.injEq] using hh
  have hq:(data.path (.inl i)).length=data.c*data.d:=by
    change (walkInterval (data.P i.val) 2 (2+data.c*data.d) (by omega)).length=data.c*data.d
    rw [walk_interval_length _ _ _ _ (by omega)]
    omega
  have hqv:∀j:ℕ,(hj:j≤data.c*data.d)→(data.path (.inl i)).getVert j=inner ⟨j,by omega⟩:=by
    intro j hj
    change (walkInterval (data.P i.val) 2 (2+data.c*data.d) (by omega)).getVert j=inner ⟨j,by omega⟩
    rw [walk_interval_getVert _ _ _ _ j (by omega),hv (2+j) (by omega),hinner]
    congr 1
    apply Fin.ext
    simp only [Fin.val_mk]
    omega
  refine ⟨?_,?_,?_⟩
  · change (data.P i.val).getVert 2=inner 0
    rw [hv 2 (by omega),hinner]
    congr 1
  · change (data.P i.val).getVert (2+data.c*data.d)=inner (Fin.last (data.c*data.d))
    rw [hv (2+data.c*data.d) (by omega),hinner]
    congr 1
    apply Fin.ext
    simp only [Fin.val_mk,Fin.val_last]
    omega
  · apply List.ext_getElem
    · simp only [SimpleGraph.Walk.length_support,hq,List.length_ofFn]
    · intro j hj₁ hj₂
      have hj:j≤data.c*data.d:=by
        rw [SimpleGraph.Walk.length_support,hq] at hj₁
        omega
      have hh:some ((data.path (.inl i)).getVert j)=(data.path (.inl i)).support[j]? :=
        (data.path (.inl i)).getVert_eq_support_getElem? (by rw [hq];exact hj)
      rw [List.getElem?_eq_getElem hj₁] at hh
      have hh':(data.path (.inl i)).support[j]= (data.path (.inl i)).getVert j := (Option.some.inj hh).symm
      rw [hh',hqv j hj,List.getElem_ofFn]
end Oberwolfach
