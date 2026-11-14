module

public import Oberwolfach.PrescribedFreePathEmbedding
public import Oberwolfach.ExtendingListFreePath

@[expose] public section
/-! Realise an entire unprescribed source path while preserving an existing
partial injection and avoiding saturated labels and physical edges. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {X V:Type} [Fintype V] [DecidableEq X] [DecidableEq V]

theorem prescribed_free_path_realization
    (as:List X) (ha:as.Nodup) (hne:1≤as.length) (A:Finset X) (f:X→V)
    (hinj:Set.InjOn f A) (hsource:∀ a∈as,a∉A)
    (S L:Finset V) (β:ℝ) (D:V→V→Prop) (hext:IsExtendingList D L β)
    (F:SimpleGraph V) (M:ℝ) (hM:0≤M) (hdeg:∀ v,(F.degree v:ℝ)≤M)
    (hbudget:((A.image f∪S).card:ℝ)+as.length+2+M<β*Fintype.card V):
    ∃ g:X→V,Set.InjOn g (↑(A∪as.toFinset):Set X) ∧ (∀ a∈A,g a=f a) ∧
    (∀ a∈as,g a∈L ∧ g a∉S) ∧
    (∀ i:ℕ,∀ hi:i+1<as.length,
      D (g (as[i]'(by omega))) (g (as[i+1]'(by omega))) ∧
      ¬F.Adj (g (as[i]'(by omega))) (g (as[i+1]'(by omega)))) := by
  let B:=A.image f∪S
  obtain ⟨bs,hbslen,hbsnodup,hbs,hpath⟩:=extending_list_embed_free_path D L β hext F M hM hdeg true as.length hne B hbudget
  cases bs with
  | nil => simp at hbslen;omega
  | cons x xs =>
    have hlen:as.length=(x::xs).length:=hbslen.symm
    have htarget:∀ z∈x::xs,z∉A.image f:=by
      intro z hz hmem
      exact (hbs z hz).2 (Finset.mem_union_left S hmem)
    let g:=updatePairedImages f (as.zip (x::xs))
    have hh:=prescribed_free_path_from_ordered_vertices as x xs hlen ha hbsnodup A f hinj hsource htarget D F hpath
    refine ⟨g,hh.1,hh.2.1,?_,hh.2.2⟩
    intro a ha'
    obtain ⟨i,hi⟩:=List.mem_iff_get.mp ha'
    have hpos:=prescribed_embedding_zip_update_at_position as (x::xs) hlen ha hbsnodup A f hinj hsource htarget i
    have hmem:(x::xs).get ⟨i.val,by omega⟩∈x::xs:=List.get_mem _ _
    have hgood:=hbs _ hmem
    have hnotS:((x::xs).get ⟨i.val,by omega⟩)∉S:=fun h=>hgood.2 (Finset.mem_union_right _ h)
    rw [←hi]
    change updatePairedImages f (as.zip (x::xs)) (as.get i)∈L ∧
      updatePairedImages f (as.zip (x::xs)) (as.get i)∉S
    rw [hpos]
    exact ⟨hgood.1,hnotS⟩
end Oberwolfach
