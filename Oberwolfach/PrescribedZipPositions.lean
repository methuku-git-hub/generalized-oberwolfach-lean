module

public import Oberwolfach.PrescribedEmbeddingZipUpdate

@[expose] public section
/-! The paired update maps the source vertex at each position to the target
vertex at the same position. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {X V:Type} [DecidableEq X] [DecidableEq V]

theorem prescribed_zip_pair_mem (as:List X) (bs:List V)
    (hlen:as.length=bs.length) (i:Fin as.length):
    (as.get i,bs.get ⟨i.val,by omega⟩)∈as.zip bs := by
  apply List.mem_of_getElem? (i:=i.val)
  apply List.getElem?_zip_eq_some.mpr
  constructor
  · exact List.getElem?_eq_some_iff.mpr ⟨i.isLt,rfl⟩
  · exact List.getElem?_eq_some_iff.mpr ⟨by omega,rfl⟩

theorem prescribed_embedding_zip_update_at_position (as:List X) (bs:List V)
    (hlen:as.length=bs.length) (ha:as.Nodup) (hb:bs.Nodup)
    (A:Finset X) (f:X→V) (hinj:Set.InjOn f A)
    (hsource:∀ x∈as,x∉A) (htarget:∀ z∈bs,z∉A.image f)
    (i:Fin as.length):
    updatePairedImages f (as.zip bs) (as.get i)=bs.get ⟨i.val,by omega⟩ := by
  have h:=prescribed_embedding_zip_update as bs hlen ha hb A f hinj hsource htarget
  exact h.2.2 _ (prescribed_zip_pair_mem as bs hlen i)
end Oberwolfach
