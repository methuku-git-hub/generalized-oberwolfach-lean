module

public import Oberwolfach.FiniteHighEventsCommon
public import Mathlib.Data.List.NodupEquivFin

@[expose] public section
/-! Two duplicate-free lists of equal length determine an injective map
sending each source vertex to the target in the same position. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {X V:Type} [DecidableEq X]

def prescribedListEmbedding (as:List X) (bs:List V)
    (hlen:as.length=bs.length) (ha:as.Nodup) (hb:bs.Nodup):
    {x // x∈as}↪V where
  toFun x:=bs.get ⟨(ha.getEquiv as).symm x |>.val,by
    have hh:=((ha.getEquiv as).symm x).isLt
    omega⟩
  inj' := by
    intro x y hxy
    apply (ha.getEquiv as).symm.injective
    apply Fin.ext
    have hh:=hb.get_inj_iff.mp hxy
    exact congrArg (fun i : Fin bs.length => i.val) hh

theorem prescribed_list_embedding_get (as:List X) (bs:List V)
    (hlen:as.length=bs.length) (ha:as.Nodup) (hb:bs.Nodup) (i:Fin as.length):
    prescribedListEmbedding as bs hlen ha hb ⟨as.get i,List.get_mem as i⟩=
      bs.get ⟨i.val,by omega⟩ := by
  change bs.get ⟨((ha.getEquiv as).symm ⟨as.get i,List.get_mem as i⟩).val,_⟩=_
  have hh:(ha.getEquiv as).symm ⟨as.get i,List.get_mem as i⟩=i:=(ha.getEquiv as).left_inv i
  simp only [hh]
end Oberwolfach
