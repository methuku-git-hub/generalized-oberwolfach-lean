module

public import Oberwolfach.PrescribedAugmentedOccurrenceBound

@[expose] public section
/-! The image load on a chosen set of hubs separates into prescribed images,
assigned matching endpoints, required targets and genuinely free images. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem completion_restricted_image_load
    {U V:Type} [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V]
    (X:U→Type) [∀w,Fintype (X w)] [∀w,DecidableEq (X w)]
    (H:Finset U) (B:∀w,Finset (X w)) (Φ g:∀w,X w→V)
    (Pre Required:U→Finset V) (M:U→Finset (V×V)) (K:SimpleGraph V)
    (hfixed:∀w x,x∈B w→Φ w x=g w x)
    (hforced:∀w,(B w).image (g w)=Pre w∪prescribedMatchingEndpoints (M w)∪Required w)
    (hsub:∀w,(M w).image prescribedArcPhysical⊆K.edgeFinset)
    (hpair:PairwisePhysicalDisjoint (fun w=>(M w).image prescribedArcPhysical)) (v:V):
    ((H.filter (fun w=>v∈Finset.univ.image (Φ w))).card:ℝ)≤
      ((H.filter (fun w=>v∈Pre w)).card:ℝ)+K.degree v+
      ((H.filter (fun w=>v∈Required w)).card+
      (H.filter (fun w=>∃x,x∉B w ∧ Φ w x=v)).card:ℝ) :=by
  let Ipre:=H.filter (fun w=>v∈Pre w)
  let Iend:=H.filter (fun w=>v∈prescribedMatchingEndpoints (M w))
  let Ireq:=H.filter (fun w=>v∈Required w)
  let Ifree:=H.filter (fun w=>∃x,x∉B w ∧ Φ w x=v)
  have hsubsets:H.filter (fun w=>v∈Finset.univ.image (Φ w))⊆(Ipre∪Iend)∪(Ireq∪Ifree):=by
    intro w hw
    have ⟨hwH,himage⟩:=Finset.mem_filter.mp hw
    obtain ⟨x,_,hx⟩:=Finset.mem_image.mp himage
    by_cases hb:x∈B w
    · have hg:v∈(B w).image (g w):=Finset.mem_image.mpr ⟨x,hb,(hfixed w x hb).symm.trans hx⟩
      rw [hforced w] at hg
      simp only [Finset.mem_union] at hg
      rcases hg with (hp|he)|hq
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hwH,hp⟩))
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hwH,he⟩))
      · exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hwH,hq⟩))
    · exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hwH,x,hb,hx⟩))
  have hend:Iend.card≤K.degree v:=by
    have hs:Iend⊆Finset.univ.filter (fun w=>v∈prescribedMatchingEndpoints (M w)):=by
      intro w hw
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hw).2⟩
    exact (Finset.card_le_card hs).trans (prescribed_matching_endpoint_occurrences M K hsub hpair v)
  have h1:=Finset.card_le_card hsubsets
  have h2:=Finset.card_union_le (Ipre∪Iend) (Ireq∪Ifree)
  have h3:=Finset.card_union_le Ipre Iend
  have h4:=Finset.card_union_le Ireq Ifree
  have hn:(H.filter (fun w=>v∈Finset.univ.image (Φ w))).card≤
      Ipre.card+K.degree v+Ireq.card+Ifree.card:=by omega
  have hr:((H.filter (fun w=>v∈Finset.univ.image (Φ w))).card:ℝ)≤
      (Ipre.card:ℝ)+K.degree v+Ireq.card+Ifree.card:=by exact_mod_cast hn
  dsimp only [Ipre,Iend,Ireq,Ifree] at hr
  linarith

theorem completion_restricted_image_load_outside
    {U V:Type} [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V]
    (X:U→Type) [∀w,Fintype (X w)] [∀w,DecidableEq (X w)]
    (H:Finset U) (B:∀w,Finset (X w)) (Φ g:∀w,X w→V)
    (Pre Required:U→Finset V) (M:U→Finset (V×V)) (K:SimpleGraph V)
    (hfixed:∀w x,x∈B w→Φ w x=g w x)
    (hforced:∀w,(B w).image (g w)=Pre w∪prescribedMatchingEndpoints (M w)∪Required w)
    (hsub:∀w,(M w).image prescribedArcPhysical⊆K.edgeFinset)
    (hpair:PairwisePhysicalDisjoint (fun w=>(M w).image prescribedArcPhysical))
    (A:Finset V) (hreq:∀w,Required w⊆A) (v:V) (hv:v∉A):
    ((H.filter (fun w=>v∈Finset.univ.image (Φ w))).card:ℝ)≤
      ((H.filter (fun w=>v∈Pre w)).card:ℝ)+K.degree v+
      ((H.filter (fun w=>∃x,x∉B w ∧ Φ w x=v)).card:ℝ) :=by
  have hz:H.filter (fun w=>v∈Required w)=∅:=by
    ext w
    simp only [Finset.mem_filter,Finset.notMem_empty,iff_false,not_and]
    intro _ hw
    exact hv (hreq w hw)
  have hh:=completion_restricted_image_load X H B Φ g Pre Required M K hfixed hforced hsub hpair v
  rw [hz] at hh
  simpa only [Finset.card_empty,Nat.cast_zero,zero_add] using hh
end Oberwolfach
