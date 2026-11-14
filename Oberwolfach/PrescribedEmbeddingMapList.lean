module

public import Oberwolfach.PrescribedZipPositions

@[expose] public section
/-! The updated map sends the entire source list to the selected target list. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {X V:Type} [DecidableEq X] [DecidableEq V]

theorem prescribed_embedding_update_map_list (as:List X) (bs:List V)
    (hlen:as.length=bs.length) (ha:as.Nodup) (hb:bs.Nodup)
    (A:Finset X) (f:X→V) (hinj:Set.InjOn f A)
    (hsource:∀ x∈as,x∉A) (htarget:∀ z∈bs,z∉A.image f):
    as.map (updatePairedImages f (as.zip bs))=bs := by
  apply List.ext_getElem (by simpa using hlen)
  intro i hi hi'
  simp only [List.getElem_map]
  have hh:=prescribed_embedding_zip_update_at_position as bs hlen ha hb A f hinj hsource htarget ⟨i,by simpa using hi⟩
  exact hh
end Oberwolfach
