module

public import Oberwolfach.ActualFinalInteriorDeletion
public import Oberwolfach.ActualBufferedFinalPathIdentification
public import Oberwolfach.ActualResidualSumIndices

@[expose] public section
/-! The strict interiors of the first family of buffered paths are exactly
inside the deleted part of each actual residual graph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_sum_buffered_interiors_deleted
    {X A B J:Type} [Fintype X] [DecidableEq X] [Fintype A] [DecidableEq A] [DecidableEq B] [DecidableEq J]
    {F:SimpleGraph X} (data:ActualResidualData (K:=A⊕B) (J:=J) F)
    (hs:data.s₁=firstSumIndices)
    (ext:∀i:A⊕B,Fin (data.c*data.d+5)↪X)
    (inner:∀a:A,Fin (data.c*data.d+1)↪X)
    (hsupp:∀i,(data.P i).support=List.ofFn (ext i))
    (hinner:∀a k,inner a k=ext (.inl a) ⟨k.val+2,by omega⟩):
    Disjoint (bufferedPathStrictInterior (fun _:A=>data.c*data.d) inner) data.remaining:=by
  let ix (a:A):{i // i∈data.s₁}:=⟨.inl a,by rw [hs];simp [firstSumIndices]⟩
  have hh:∀a,data.start (.inl (ix a))=inner a 0 ∧
      data.finish (.inl (ix a))=inner a (Fin.last (data.c*data.d)) ∧
      (data.path (.inl (ix a))).support=List.ofFn (inner a):=by
    intro a
    exact actual_final_path_matches_buffered_sequence data (ix a) (ext (.inl a)) (inner a) (hinner a) (hsupp (.inl a))
  exact (actual_final_path_interiors_are_deleted data (fun _:A=>data.c*data.d) inner (fun a=>.inl (ix a))
    (fun a=>(hh a).1) (fun a=>(hh a).2.1) (fun a=>(hh a).2.2)).2

/-- The same conclusion with the path length presented by named parameters. -/
theorem actual_sum_buffered_interiors_deleted_with_parameters
    {X A B J:Type} [Fintype X] [DecidableEq X] [Fintype A] [DecidableEq A] [DecidableEq B] [DecidableEq J]
    {F:SimpleGraph X} (data:ActualResidualData (K:=A⊕B) (J:=J) F)
    (c d:ℕ) (hc:data.c=c) (hd:data.d=d) (hs:data.s₁=firstSumIndices)
    (ext:∀i:A⊕B,Fin (c*d+5)↪X) (inner:∀a:A,Fin (c*d+1)↪X)
    (hsupp:∀i,(data.P i).support=List.ofFn (ext i))
    (hinner:∀a k,inner a k=ext (.inl a) ⟨k.val+2,by omega⟩):
    Disjoint (bufferedPathStrictInterior (fun _:A=>c*d) inner) data.remaining:=by
  subst c
  subst d
  exact actual_sum_buffered_interiors_deleted data hs ext inner hsupp hinner
end Oberwolfach
