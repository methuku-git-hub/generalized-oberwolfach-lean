module

public import Oberwolfach.PrescribedEmbeddingMapList
public import Oberwolfach.PrescribedEmbeddingZipTargets
public import Oberwolfach.ExtendingListPinnedCycle

@[expose] public section
/-! Embed an ordered cycle with exactly one already assigned vertex. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {X V:Type} [Fintype V] [DecidableEq X] [DecidableEq V]

theorem prescribed_pinned_cycle_realization
    (as:List X) (ha:as.Nodup) (hlen:2≤as.length) (A:Finset X) (f:X→V)
    (hinj:Set.InjOn f A) (hsource:∀ u∈as,u∉A) (a:X) (haA:a∈A)
    (S L:Finset V) (β:ℝ) (D:V→V→Prop) (hext:IsExtendingList D L β)
    (F:SimpleGraph V) (M:ℝ) (hM:0≤M) (hdeg:∀ v,(F.degree v:ℝ)≤M)
    (hbudget:((A.image f∪S).card:ℝ)+(as.length+1:ℕ)+2+2*M<β*Fintype.card V):
    ∃ g:X→V,Set.InjOn g (↑(A∪as.toFinset):Set X) ∧ (∀ u∈A,g u=f u) ∧
    (∀ u∈as,g u∈L ∧ g u∉S) ∧ DirectedPathThrough D F (g a) (g a) (as.map g) := by
  let B:=A.image f∪S
  obtain ⟨ys,hyslen,hysnodup,hys,hcycle⟩:=extending_list_embed_pinned_cycle D L β hext F M hM hdeg B (f a) (as.length+1) (by omega) hbudget
  have hlen':as.length=ys.length:=by simp [hyslen]
  have htarget:∀ z∈ys,z∉A.image f:=by
    intro z hz hmem
    exact (hys z hz).2.1 (Finset.mem_union_left S hmem)
  have hgood:∀ z∈ys,z∈L ∧ z∉S:=by
    intro z hz
    exact ⟨(hys z hz).1,fun h=>(hys z hz).2.1 (Finset.mem_union_right _ h)⟩
  let g:=updatePairedImages f (as.zip ys)
  have hb:=prescribed_embedding_zip_update as ys hlen' ha hysnodup A f hinj hsource htarget
  have hmap:=prescribed_embedding_update_map_list as ys hlen' ha hysnodup A f hinj hsource htarget
  have hnew:=prescribed_embedding_zip_targets as ys hlen' ha hysnodup A f hinj hsource htarget (fun z=>z∈L ∧ z∉S) hgood
  refine ⟨g,hb.1,hb.2.1,hnew,?_⟩
  have hga:g a=f a:=hb.2.1 a haA
  rw [hga,hmap]
  exact hcycle
end Oberwolfach
