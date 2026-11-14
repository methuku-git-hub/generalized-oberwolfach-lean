module

public import Oberwolfach.PrescribedEmbeddingMapList
public import Oberwolfach.PrescribedPathThroughFrom
public import Oberwolfach.ExtendingListPathEmbedding

@[expose] public section
/-! Embed an ordered path whose two distinct boundary vertices were already
assigned, preserving those assignments and avoiding the forbidden graph. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {X V:Type} [Fintype V] [DecidableEq X] [DecidableEq V]

theorem prescribed_two_ended_path_realization
    (as:List X) (ha:as.Nodup) (hne:1≤as.length) (A:Finset X) (f:X→V)
    (hinj:Set.InjOn f A) (hsource:∀ a∈as,a∉A)
    (a b:X) (haA:a∈A) (hbA:b∈A) (hab:a≠b)
    (S L:Finset V) (β:ℝ) (D:V→V→Prop) (hext:IsExtendingList D L β)
    (F:SimpleGraph V) (M:ℝ) (hM:0≤M) (hdeg:∀ v,(F.degree v:ℝ)≤M)
    (hbudget:((A.image f∪S).card:ℝ)+as.length+2+2*M<β*Fintype.card V):
    ∃ g:X→V,Set.InjOn g (↑(A∪as.toFinset):Set X) ∧ (∀ u∈A,g u=f u) ∧
    (∀ u∈as,g u∈L ∧ g u∉S) ∧
    DirectedPathFrom D F true (g a) ((as.map g)++[g b]) := by
  have hfa:f a≠f b:=by intro h;exact hab (hinj haA hbA h)
  let B:=A.image f∪S
  have hbudget':(B.card:ℝ)+((as.length-1)+1:ℕ)+2+2*M<β*Fintype.card V:=by
    have hh:as.length-1+1=as.length:=Nat.sub_add_cancel hne
    simpa [hh,B] using hbudget
  obtain ⟨ys,hyslen,hysnodup,hys,hpath⟩:=extending_list_embed_internal_path D L β hext F M hM hdeg (as.length-1) B (f a) (f b) hfa hbudget'
  have hlen:as.length=ys.length:=by rw [hyslen,Nat.sub_add_cancel hne]
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
    have hgb:g b=f b:=hb.2.1 b hbA
    rw [hga,hgb,hmap]
    exact prescribed_path_through_to_from D F (f b) ys (f a) hpath
end Oberwolfach
