module

public import Oberwolfach.MarkedFiniteRemainderTransfer

@[expose] public section

/-! Fibre and endpoint incidence bounds under injective maps of the actual
finite edge sets. Roots outside the image contribute zero. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {A B V V':Type} [DecidableEq A] [DecidableEq B] [DecidableEq V] [DecidableEq V']

theorem finite_image_incidence_bound (S:Finset A) (f:A↪B) (g:V↪V')
    (tail head:A→V) (tail' head':B→V')
    (ht:∀ a∈S,tail' (f a)=g (tail a)) (hh:∀ a∈S,head' (f a)=g (head a))
    (b:ℝ) (hb:0≤b)
    (h:∀ v,((S.filter (fun a=>v=tail a∨v=head a)).card:ℝ)≤b):
    ∀ v,(((S.image f).filter (fun a=>v=tail' a∨v=head' a)).card:ℝ)≤b:=by
  intro v
  rw [Finset.filter_image,Finset.card_image_of_injective _ f.injective]
  by_cases hv:∃ w,g w=v
  · obtain ⟨w,rfl⟩:=hv
    have he:S.filter (fun a=>g w=tail' (f a)∨g w=head' (f a))=
        S.filter (fun a=>w=tail a∨w=head a):=by
      ext a
      simp only [Finset.mem_filter]
      apply and_congr_right
      intro ha
      rw [ht a ha,hh a ha]
      simp only [EmbeddingLike.apply_eq_iff_eq]
    rw [he]
    exact h w
  · have he:S.filter (fun a=>v=tail' (f a)∨v=head' (f a))=∅:=by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro a ha
      obtain ⟨ha,ht'|hh'⟩:=Finset.mem_filter.mp ha
      · exact hv ⟨tail a,(ht a ha).symm.trans ht'.symm⟩
      · exact hv ⟨head a,(hh a ha).symm.trans hh'.symm⟩
    rw [he,Finset.card_empty,Nat.cast_zero]
    exact hb

theorem finite_image_fibre_bound (S:Finset A) (f:A↪B) (g:V↪V')
    (tail:A→V) (tail':B→V') (ht:∀ a∈S,tail' (f a)=g (tail a))
    (b:ℝ) (hb:0≤b) (h:∀ v,((S.filter (fun a=>v=tail a)).card:ℝ)≤b):
    ∀ v,(((S.image f).filter (fun a=>v=tail' a)).card:ℝ)≤b:=by
  have hh:=finite_image_incidence_bound S f g tail tail tail' tail' ht ht b hb
    (fun v=>by simpa only [or_self] using h v)
  simpa only [or_self] using hh

end Oberwolfach
