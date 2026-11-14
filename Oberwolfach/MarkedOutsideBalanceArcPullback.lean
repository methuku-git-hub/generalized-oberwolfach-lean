module

public import Oberwolfach.MarkedOutsideBalance

@[expose] public section

/-! Pull outside balances through injective maps of the actual typed arc
identifiers. Directions, marked flags and the retained spoke set are fixed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K E' K':Type} [DecidableEq V] [DecidableEq U]
  [DecidableEq E] [DecidableEq K] [DecidableEq E'] [DecidableEq K']

theorem marked_outside_balance_arc_pullback
    (tail head:E→V) (ktail khead:K→V) (tail' head':E'→V) (ktail' khead':K'→V)
    (HK:V→U→Prop) (e:E↪E') (k:K↪K')
    (het:∀ a,tail' (e a)=tail a) (heh:∀ a,head' (e a)=head a)
    (hkt:∀ a,ktail' (k a)=ktail a) (hkh:∀ a,khead' (k a)=khead a)
    (A:Finset (E⊕K)) (S:Finset (V×U)) (m:ℕ) (X:Finset V) (Z:Finset U)
    (h:MarkedOutsideBalance tail' head' ktail' khead' HK
      (A.image (e.sumMap k)) S m X Z):
    MarkedOutsideBalance tail head ktail khead HK A S m X Z:=by
  have hi (p:E'⊕K'→Prop):((A.image (e.sumMap k)).filter p).card=
      (A.filter (fun a=>p ((e.sumMap k) a))).card:=by
    rw [Finset.filter_image,Finset.card_image_of_injective _ (e.sumMap k).injective]
  have ht (a:E⊕K):Sum.elim tail' ktail' ((e.sumMap k) a)=Sum.elim tail ktail a:=by
    cases a with
    | inl a=>exact het a
    | inr a=>exact hkt a
  have hh (a:E⊕K):Sum.elim head' khead' ((e.sumMap k) a)=Sum.elim head khead a:=by
    cases a with
    | inl a=>exact heh a
    | inr a=>exact hkh a
  have hm (a:E⊕K):markedArcType ((e.sumMap k) a)=markedArcType a:=by cases a <;> rfl
  simp only [←Set.ncard_coe_finset,Finset.coe_filter,Finset.coe_image] at hi
  constructor
  · intro v hv
    have hd:=h.directed v hv
    simp only [←Set.ncard_coe_finset,Finset.coe_filter,Finset.coe_image] at hd ⊢
    rw [hi,hi] at hd
    simpa only [hh,ht] using hd
  · intro v hv
    have hd:=h.row v hv
    simp only [←Set.ncard_coe_finset,Finset.coe_filter,Finset.coe_image] at hd ⊢
    rw [hi] at hd
    simpa only [hh] using hd
  · intro v hv
    have hd:=h.marked v hv
    simp only [←Set.ncard_coe_finset,Finset.coe_filter,Finset.coe_image] at hd ⊢
    rw [hi] at hd
    simpa only [hh,hm] using hd
  · exact h.hub

end Oberwolfach
