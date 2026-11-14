module

public import Oberwolfach.TypedMarkedIncidenceIndicators

@[expose] public section

/-! Fixed coefficients on potential wheels give exactly the actual restricted
rim and typed spoke loads. The parent may contain overlapping spoke types
and distinct directed occurrences with the same physical edge. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U] [Fintype E] [Fintype K]
  [DecidableEq V] [DecidableEq U]
  {tail head:E→V} {ktail khead:K→V} {m b:ℕ} {π:Equiv.Perm V}
  {H₀ HK H₀' HK':V→U→Prop}

theorem marked_wheel_sum_over_survivors (PE:E→Prop) (PK:K→Prop)
    (hH₀:∀ v u,H₀' v u→H₀ v u) (hHK:∀ v u,HK' v u→HK v u)
    (F:MarkedWheel tail head ktail khead m π b H₀ HK→ℝ):
    (∑ W:MarkedWheel (fun e:{e//PE e}=>tail e.val) (fun e=>head e.val)
      (fun e:{e//PK e}=>ktail e.val) (fun e=>khead e.val) m π b H₀' HK',
      F (markedWheelToLarger PE PK hH₀ hHK W))=
    ∑ W:MarkedWheel tail head ktail khead m π b H₀ HK,
      if MarkedWheelSurvives PE PK H₀' HK' W then F W else 0:=by
  let G:=fun W:MarkedWheel tail head ktail khead m π b H₀ HK=>
    if MarkedWheelSurvives PE PK H₀' HK' W then F W else 0
  have he:=finite_sum_restrict_of_zero (fun W=>MarkedWheelSurvives PE PK H₀' HK' W) G
    (by intro W hW;simp only [G,hW,ite_false])
  rw [he]
  rw [←(markedWheelRestrictionEquiv PE PK hH₀ hHK).sum_comp
    (fun W=>F (markedWheelToLarger PE PK hH₀ hHK W))]
  apply Finset.sum_congr rfl
  intro W _
  change F W.val=if MarkedWheelSurvives PE PK H₀' HK' W.val then F W.val else 0
  exact (if_pos W.property).symm

theorem typedMarkedPotentialLoad_surviving_sum (PE:E→Prop) (PK:K→Prop)
    (hE:Function.Injective (fun e:E=>(tail e,head e)))
    (hK:Function.Injective (fun e:K=>(ktail e,khead e)))
    (w:MarkedWheel tail head ktail khead m π b H₀ HK→ℝ)
    (e:(E⊕K)⊕(Bool×V×U))
    (he:Sum.elim (Sum.elim PE PK) (fun s=>if s.1 then HK' s.2.1 s.2.2 else H₀' s.2.1 s.2.2) e):
    typedMarkedPotentialLoad w (Sum.elim PE PK) (fun j v u=>if j then HK' v u else H₀' v u) e=
      ∑ W,if e∈typedMarkedOccurrenceResources W∧MarkedWheelSurvives PE PK H₀' HK' W then w W else 0:=by
  unfold typedMarkedPotentialLoad
  rw [resourceRootOmittedLoad_present _ _ _ _ he]
  apply Finset.sum_congr rfl
  intro W _
  have hs:=markedWheelSurvives_iff_typed_occurrences (H₀':=H₀') (Hₖ':=HK') PE PK hE hK W
  by_cases h:e∈typedMarkedOccurrenceResources W∧MarkedWheelSurvives PE PK H₀' HK' W
  · rw [if_pos h,if_pos ⟨h.1,hs.mp h.2⟩]
  · rw [if_neg h,if_neg (fun hh=>h ⟨hh.1,hs.mpr hh.2⟩)]

theorem typedMarkedPotentialLoad_restricted_rim (PE:E→Prop) (PK:K→Prop)
    (hE:Function.Injective (fun e:E=>(tail e,head e)))
    (hK:Function.Injective (fun e:K=>(ktail e,khead e)))
    (hH₀:∀ v u,H₀' v u→H₀ v u) (hHK:∀ v u,HK' v u→HK v u)
    (w:MarkedWheel tail head ktail khead m π b H₀ HK→ℝ)
    (e:{e//PE e}⊕{e//PK e}):
    typedMarkedPotentialLoad w (Sum.elim PE PK) (fun j v u=>if j then HK' v u else H₀' v u)
      (Sum.inl (Sum.map Subtype.val Subtype.val e))=
      markedWheelRimLoad (fun W=>w (markedWheelToLarger PE PK hH₀ hHK W)) e:=by
  have he:Sum.elim PE PK (Sum.map Subtype.val Subtype.val e):=by
    cases e with
    | inl e=>exact e.property
    | inr e=>exact e.property
  rw [typedMarkedPotentialLoad_surviving_sum (H₀':=H₀') (HK':=HK') PE PK hE hK w
    (Sum.inl (Sum.map Subtype.val Subtype.val e)) he]
  have hh:=marked_wheel_sum_over_survivors PE PK hH₀ hHK
    (fun W=>w W*markedCycleIncidence tail head ktail khead m W.1.val
      (Sum.map Subtype.val Subtype.val e))
  have hleft: (∑ W:MarkedWheel (fun e:{e//PE e}=>tail e.val) (fun e=>head e.val)
      (fun e:{e//PK e}=>ktail e.val) (fun e=>khead e.val) m π b H₀' HK',
      w (markedWheelToLarger PE PK hH₀ hHK W)*markedCycleIncidence tail head ktail khead m
        (markedWheelToLarger PE PK hH₀ hHK W).1.val (Sum.map Subtype.val Subtype.val e))=
      markedWheelRimLoad (fun W=>w (markedWheelToLarger PE PK hH₀ hHK W)) e:=by
    unfold markedWheelRimLoad
    apply Finset.sum_congr rfl
    intro W _
    cases e <;> rfl
  rw [hleft] at hh
  rw [hh]
  apply Finset.sum_congr rfl
  intro W _
  rw [markedCycleIncidence_canonical_indicator hE hK W.1]
  by_cases hs:MarkedWheelSurvives PE PK H₀' HK' W <;>
    by_cases hm:CanonicalMarkedArcMem W.1 (Sum.map Subtype.val Subtype.val e) <;>
    simp only [typedMarkedOccurrenceResources_rim,hs,hm,true_and,false_and,ite_true,ite_false,mul_one,mul_zero]

theorem typedMarkedPotentialLoad_restricted_spoke (PE:E→Prop) (PK:K→Prop)
    (hE:Function.Injective (fun e:E=>(tail e,head e)))
    (hK:Function.Injective (fun e:K=>(ktail e,khead e)))
    (hH₀:∀ v u,H₀' v u→H₀ v u) (hHK:∀ v u,HK' v u→HK v u)
    (w:MarkedWheel tail head ktail khead m π b H₀ HK→ℝ)
    (j:Bool) (v:V) (u:U) (he:if j then HK' v u else H₀' v u):
    typedMarkedPotentialLoad w (Sum.elim PE PK) (fun j v u=>if j then HK' v u else H₀' v u)
      (Sum.inr (j,v,u))=
      markedWheelSpokeLoad (fun W=>w (markedWheelToLarger PE PK hH₀ hHK W)) j v u:=by
  rw [typedMarkedPotentialLoad_surviving_sum (H₀':=H₀') (HK':=HK') PE PK hE hK w (Sum.inr (j,v,u)) he]
  have hh:=marked_wheel_sum_over_survivors PE PK hH₀ hHK
    (fun W=>w W*(if W.2.val=u then markedSpokeIndicator W.1.val j v else 0))
  change markedWheelSpokeLoad (fun W=>w (markedWheelToLarger PE PK hH₀ hHK W)) j v u=_ at hh
  rw [hh]
  apply Finset.sum_congr rfl
  intro W _
  rw [markedWheel_spoke_typed_indicator W j v u]
  by_cases hs:MarkedWheelSurvives PE PK H₀' HK' W <;>
    by_cases hm:Sum.inr (j,v,u)∈typedMarkedOccurrenceResources W <;>
    simp only [hs,hm,true_and,false_and,ite_true,ite_false,mul_one,mul_zero]

end Oberwolfach
