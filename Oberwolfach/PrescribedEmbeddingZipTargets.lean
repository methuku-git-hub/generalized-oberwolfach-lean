module

public import Oberwolfach.PrescribedZipPositions

@[expose] public section
/-! Target-list properties transfer to every new source vertex. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {X V:Type} [DecidableEq X] [DecidableEq V]

theorem prescribed_embedding_zip_targets (as:List X) (bs:List V)
    (hlen:as.length=bs.length) (ha:as.Nodup) (hb:bs.Nodup)
    (A:Finset X) (f:X→V) (hinj:Set.InjOn f A)
    (hsource:∀ x∈as,x∉A) (htarget:∀ z∈bs,z∉A.image f)
    (P:V→Prop) (hP:∀ z∈bs,P z):
    ∀ u∈as,P (updatePairedImages f (as.zip bs) u) := by
  intro u hu
  obtain ⟨i,hi⟩:=List.mem_iff_get.mp hu
  have hp:=prescribed_embedding_zip_update_at_position as bs hlen ha hb A f hinj hsource htarget i
  have hz:bs.get ⟨i.val,by omega⟩∈bs:=List.get_mem _ _
  rw [←hi,hp]
  exact hP _ hz
end Oberwolfach
