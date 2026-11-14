module

public import Oberwolfach.PrescribedEmbeddingZipUpdate

@[expose] public section
/-! The prescribed batch update has exactly the original and newly listed
images. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {X V:Type} [DecidableEq X] [DecidableEq V]

theorem prescribed_embedding_zip_image (as:List X) (bs:List V)
    (hlen:as.length=bs.length) (ha:as.Nodup) (hb:bs.Nodup)
    (A:Finset X) (f:X→V) (hinj:Set.InjOn f A)
    (hsource:∀x∈as,x∉A) (htarget:∀z∈bs,z∉A.image f):
    (A∪as.toFinset).image (updatePairedImages f (as.zip bs)) = A.image f∪bs.toFinset := by
  let g:=updatePairedImages f (as.zip bs)
  have h:=prescribed_embedding_zip_update as bs hlen ha hb A f hinj hsource htarget
  have hfst:(as.zip bs).map Prod.fst=as:=List.map_fst_zip hlen.le
  have hsnd:(as.zip bs).map Prod.snd=bs:=List.map_snd_zip hlen.ge
  ext z
  constructor
  · intro hz
    obtain ⟨x,hx,rfl⟩:=Finset.mem_image.mp hz
    rcases Finset.mem_union.mp hx with hx|hx
    · apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨x,hx,(h.2.1 x hx).symm⟩
    · have hx':x∈(as.zip bs).map Prod.fst:=by rw [hfst];exact List.mem_toFinset.mp hx
      obtain ⟨p,hp,hpx⟩:=List.mem_map.mp hx'
      apply Finset.mem_union_right
      apply List.mem_toFinset.mpr
      have he:g x=p.2:=by rw [←hpx];exact h.2.2 p hp
      change g x∈bs
      rw [he]
      exact (List.of_mem_zip hp).2
  · intro hz
    rcases Finset.mem_union.mp hz with hz|hz
    · obtain ⟨x,hx,rfl⟩:=Finset.mem_image.mp hz
      apply Finset.mem_image.mpr
      exact ⟨x,Finset.mem_union_left _ hx,h.2.1 x hx⟩
    · have hz':z∈(as.zip bs).map Prod.snd:=by rw [hsnd];exact List.mem_toFinset.mp hz
      obtain ⟨p,hp,hpz⟩:=List.mem_map.mp hz'
      apply Finset.mem_image.mpr
      refine ⟨p.1,Finset.mem_union_right _ ?_,?_⟩
      · apply List.mem_toFinset.mpr
        rw [←hfst]
        exact List.mem_map.mpr ⟨p,hp,rfl⟩
      · exact (h.2.2 p hp).trans hpz
end Oberwolfach
