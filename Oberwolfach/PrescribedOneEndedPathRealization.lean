module

public import Oberwolfach.PrescribedEmbeddingMapList
public import Oberwolfach.ExtendingListOneSidedPath

@[expose] public section
/-! Embed an ordered path from one previously assigned boundary, forwards or
backwards, while preserving all existing images. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {X V:Type} [Fintype V] [DecidableEq X] [DecidableEq V]

theorem prescribed_one_ended_path_realization
    (as:List X) (ha:as.Nodup) (A:Finset X) (f:X→V)
    (hinj:Set.InjOn f A) (hsource:∀ a∈as,a∉A)
    (a:X) (haA:a∈A) (S L:Finset V) (β:ℝ) (D:V→V→Prop)
    (hext:IsExtendingList D L β) (F:SimpleGraph V) (M:ℝ) (hM:0≤M)
    (hdeg:∀ v,(F.degree v:ℝ)≤M) (forward:Bool)
    (hbudget:((A.image f∪S).card:ℝ)+as.length+1+M<β*Fintype.card V):
    ∃ g:X→V,Set.InjOn g (↑(A∪as.toFinset):Set X) ∧ (∀ u∈A,g u=f u) ∧
    (∀ u∈as,g u∈L ∧ g u∉S) ∧ DirectedPathFrom D F forward (g a) (as.map g) := by
  let B:=A.image f∪S
  obtain ⟨ys,hyslen,hysnodup,hys,hpath⟩:=extending_list_embed_one_sided_path D L β hext F M hM hdeg forward as.length B (f a) hbudget
  have hlen:as.length=ys.length:=hyslen.symm
  have htarget:∀ z∈ys,z∉A.image f:=by
    intro z hz hmem
    exact (hys z hz).2.1 (Finset.mem_union_left S hmem)
  let g:=updatePairedImages f (as.zip ys)
  have hb:=prescribed_embedding_zip_update as ys hlen ha hysnodup A f hinj hsource htarget
  have hmap:=prescribed_embedding_update_map_list as ys hlen ha hysnodup A f hinj hsource htarget
  refine ⟨g,hb.1,hb.2.1,?_,?_⟩
  · intro u hu
    obtain ⟨i,hi⟩:=List.mem_iff_get.mp hu
    have hp:=prescribed_embedding_zip_update_at_position as ys hlen ha hysnodup A f hinj hsource htarget i
    have hz:ys.get ⟨i.val,by omega⟩∈ys:=List.get_mem _ _
    have hgood:=hys _ hz
    have hnotS:(ys.get ⟨i.val,by omega⟩)∉S:=fun h=>hgood.2.1 (Finset.mem_union_right _ h)
    rw [←hi]
    change updatePairedImages f (as.zip ys) (as.get i)∈L ∧
      updatePairedImages f (as.zip ys) (as.get i)∉S
    rw [hp]
    exact ⟨hgood.1,hnotS⟩
  · have hga:g a=f a:=hb.2.1 a haA
    rw [hga,hmap]
    exact hpath
end Oberwolfach
