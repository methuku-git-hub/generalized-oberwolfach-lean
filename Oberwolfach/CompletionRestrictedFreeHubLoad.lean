module

public import Oberwolfach.CompletionRestrictedImageLoad

@[expose] public section
/-! Count the hubs with a free occurrence by the actual free occurrences,
without choosing any source vertex or changing the completion maps. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem completion_restricted_free_hub_load
    {U V:Type} [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V]
    (X:U→Type) [∀w,Fintype (X w)] [∀w,DecidableEq (X w)]
    (H:Finset U) (B:∀w,Finset (X w)) (Φ:∀w,X w→V) (v:V):
    ((H.filter (fun w=>∃x,x∉B w ∧ Φ w x=v)).card:ℝ)≤
      ((((Finset.univ.filter (fun z:(Σw,X w)=>z.2∉B z.1)).filter (fun z=>z.1∈H)).filter
        (fun z=>Φ z.1 z.2=v)).card:ℝ) :=by
  let T:Finset (Σw,X w):=((Finset.univ.filter (fun z:(Σw,X w)=>z.2∉B z.1)).filter (fun z=>z.1∈H)).filter
    (fun z=>Φ z.1 z.2=v)
  have heq:T.image Sigma.fst=H.filter (fun w=>∃x,x∉B w ∧ Φ w x=v):=by
    ext w
    constructor
    · intro hw
      obtain ⟨⟨i,x⟩,hx,hi⟩:=Finset.mem_image.mp hw
      change i=w at hi
      subst w
      simp only [T,Finset.mem_filter,Finset.mem_univ,true_and] at hx
      exact Finset.mem_filter.mpr ⟨hx.1.2,x,hx.1.1,hx.2⟩
    · intro hw
      obtain ⟨hwH,x,hx,hxv⟩:=Finset.mem_filter.mp hw
      apply Finset.mem_image.mpr
      refine ⟨⟨w,x⟩,?_,rfl⟩
      simp only [T,Finset.mem_filter,Finset.mem_univ,true_and]
      exact ⟨⟨hx,hwH⟩,hxv⟩
  have hc:(H.filter (fun w=>∃x,x∉B w ∧ Φ w x=v)).card≤T.card:=by
    rw [←heq]
    exact Finset.card_image_le
  exact_mod_cast hc

theorem completion_restricted_image_load_outside_from_occurrences
    {U V:Type} [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V]
    (X:U→Type) [∀w,Fintype (X w)] [∀w,DecidableEq (X w)]
    (H:Finset U) (B:∀w,Finset (X w)) (Φ g:∀w,X w→V)
    (Pre Required:U→Finset V) (M:U→Finset (V×V)) (K:SimpleGraph V)
    (hfixed:∀w x,x∈B w→Φ w x=g w x)
    (hforced:∀w,(B w).image (g w)=Pre w∪prescribedMatchingEndpoints (M w)∪Required w)
    (hsub:∀w,(M w).image prescribedArcPhysical⊆K.edgeFinset)
    (hpair:PairwisePhysicalDisjoint (fun w=>(M w).image prescribedArcPhysical))
    (A:Finset V) (hreq:∀w,Required w⊆A) (P Q T:ℝ)
    (hpre:∀v,((H.filter (fun w=>v∈Pre w)).card:ℝ)≤P)
    (hK:∀v,(K.degree v:ℝ)≤Q)
    (hfree:∀v,((((Finset.univ.filter (fun z:(Σw,X w)=>z.2∉B z.1)).filter (fun z=>z.1∈H)).filter
      (fun z=>Φ z.1 z.2=v)).card:ℝ)≤T):
    ∀v,v∉A→((H.filter (fun w=>v∈Finset.univ.image (Φ w))).card:ℝ)≤P+Q+T :=by
  intro v hv
  have hi:=completion_restricted_image_load_outside X H B Φ g Pre Required M K hfixed hforced hsub hpair A hreq v hv
  have hf:=completion_restricted_free_hub_load X H B Φ v
  linarith [hpre v,hK v,hfree v]
end Oberwolfach
