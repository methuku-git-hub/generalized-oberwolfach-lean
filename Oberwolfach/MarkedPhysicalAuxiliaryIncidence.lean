module

public import Oberwolfach.MarkedIncidentResources

@[expose] public section

/-! Bounds on actual physical resources imply bounds for both notions of
incidence. A marked arc with auxiliary head v has physical head π v. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U] [Fintype E] [Fintype K]
  [DecidableEq V] [DecidableEq U]

theorem marked_auxiliary_incident_physical_union
    (tail head:E→V) (ktail khead:K→V) (π:Equiv.Perm V) (H₀ HK:V→U→Prop)
    (physical:Bool) (x:V⊕U) (e:MarkedActiveEdge E K H₀ HK)
    (he:markedResourceIncident tail head ktail khead π H₀ HK physical x e):
    markedPhysicalIncident x (markedActivePhysical tail head ktail khead π H₀ HK e)∨
      markedPhysicalIncident (Sum.map π id x) (markedActivePhysical tail head ktail khead π H₀ HK e):=by
  cases x with
  | inl v=>
    cases e with
    | inl a=>
      cases a with
      | inl a=>
        exact Or.inl (by simpa [markedResourceIncident,markedPhysicalIncident,
          markedActivePhysical,markedPhysicalEdge,eq_comm] using he)
      | inr a=>
        cases physical with
        | true=>
          exact Or.inl (by simpa [markedResourceIncident,markedPhysicalIncident,
            markedActivePhysical,markedPhysicalEdge,eq_comm] using he)
        | false=>
          change ktail a=v∨khead a=v at he
          rcases he with he|he
          · left
            simp [markedPhysicalIncident,markedActivePhysical,markedPhysicalEdge,he]
          · right
            simp [markedPhysicalIncident,markedActivePhysical,markedPhysicalEdge,he]
    | inr vu=>
      left
      exact he
  | inr u=>
    cases e with
    | inl a=>cases a <;> exact False.elim he
    | inr vu=>exact Or.inl he

theorem marked_incidence_bound_from_physical_resources
    (tail head:E→V) (ktail khead:K→V) (π:Equiv.Perm V) (H₀ HK:V→U→Prop)
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (B:Finset (Finset V⊕(V×U))) (C:ℝ)
    (hB:∀ x,((B.filter (markedPhysicalIncident x)).card:ℝ)≤C)
    (physical:Bool) (x:V⊕U):
    (((markedIncidentEdges tail head ktail khead π H₀ HK physical x).filter
      (fun e=>markedActivePhysical tail head ktail khead π H₀ HK e∈B)).card:ℝ)≤2*C:=by
  let F:=markedActivePhysical tail head ktail khead π H₀ HK
  have hi:Function.Injective F:=markedActivePhysical_injective hp
  have hcard:((markedIncidentEdges tail head ktail khead π H₀ HK physical x).filter
      (fun e=>F e∈B)).card≤
      (B.filter (fun b=>markedPhysicalIncident x b∨markedPhysicalIncident (Sum.map π id x) b)).card:=by
    apply Finset.card_le_card_of_injOn F
    · intro e he
      obtain ⟨he,hB⟩:=Finset.mem_filter.mp he
      exact Finset.mem_filter.mpr ⟨hB,marked_auxiliary_incident_physical_union tail head ktail khead π H₀ HK physical x e
        (Finset.mem_filter.mp he).2⟩
    · intro a ha b hb hab
      exact hi hab
  rw [Finset.filter_or] at hcard
  have hc:=hcard.trans (Finset.card_union_le _ _)
  have hcR:(((markedIncidentEdges tail head ktail khead π H₀ HK physical x).filter (fun e=>F e∈B)).card:ℝ)≤
      (B.filter (markedPhysicalIncident x)).card+(B.filter (markedPhysicalIncident (Sum.map π id x))).card:=by
    exact_mod_cast hc
  linarith only [hcR,hB x,hB (Sum.map π id x)]

end Oberwolfach
