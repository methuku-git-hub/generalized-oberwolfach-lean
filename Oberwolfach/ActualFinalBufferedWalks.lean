module

public import Oberwolfach.ActualBufferedFinalPathIdentification

@[expose] public section
/-! Reindex the actual final paths by the retained intervals and expose their
exact endpoints, lengths and buffered supports. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_final_buffered_walks
    {X K J I:Type} [Fintype X] [DecidableEq X] [DecidableEq K] [DecidableEq J]
    {F:SimpleGraph X} (data:ActualResidualData (K:=K) (J:=J) F)
    (b:I≃{i // i∈data.s₁}) (ext:∀i:I,Fin (data.c*data.d+5)↪X)
    (inner:∀i:I,Fin (data.c*data.d+1)↪X)
    (hinner:∀i p,inner i p=ext i ⟨p.val+2,by omega⟩)
    (hsupp:∀i,(data.P (b i).val).support=List.ofFn (ext i)):
    ∃p:∀i:I,F.Walk (inner i 0) (inner i (Fin.last (data.c*data.d))),
      (∀i,(p i).length=data.c*data.d) ∧ (∀i,(p i).support=List.ofFn (inner i)):=by
  let h:=fun i=>actual_final_path_matches_buffered_sequence data (b i) (ext i) (inner i) (hinner i) (hsupp i)
  let p:=fun i=>(data.path (.inl (b i))).copy (h i).1 (h i).2.1
  refine ⟨p,?_,?_⟩
  · intro i
    have hsup:(p i).support=List.ofFn (inner i):=by simpa [p] using (h i).2.2
    have hl:=congrArg List.length hsup
    simp only [SimpleGraph.Walk.length_support,List.length_ofFn] at hl
    omega
  · intro i
    simpa [p] using (h i).2.2
end Oberwolfach
