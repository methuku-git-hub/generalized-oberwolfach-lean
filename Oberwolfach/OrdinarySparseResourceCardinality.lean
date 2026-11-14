module

public import Oberwolfach.PrescribedPhysicalDegrees

@[expose] public section
/-! A prescribed ordinary edge set with bounded physical incidence has at
most the number of physical vertices times that bound. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_resource_count_from_incidence (E:Finset (Sym2 V⊕(V×U))) (D:ℕ)
    (hD:∀x:V⊕U,(E.filter (ordinaryResourceIncident x)).card≤D):
    E.card≤Fintype.card (V⊕U)*D:=by
  have hsub:E⊆Finset.univ.biUnion (fun x:V⊕U=>E.filter (ordinaryResourceIncident x)):=by
    intro e he
    cases e with
    | inl e=>
      induction e using Sym2.ind with
      | _ v w=>
        apply Finset.mem_biUnion.mpr
        refine ⟨Sum.inl v,Finset.mem_univ _,Finset.mem_filter.mpr ⟨he,?_⟩⟩
        change v∈s(v,w)
        simp
    | inr vu=>
      obtain ⟨v,u⟩:=vu
      apply Finset.mem_biUnion.mpr
      exact ⟨Sum.inl v,Finset.mem_univ _,Finset.mem_filter.mpr ⟨he,rfl⟩⟩
  calc
    E.card≤(Finset.univ.biUnion (fun x:V⊕U=>E.filter (ordinaryResourceIncident x))).card:=Finset.card_le_card hsub
    _≤∑x:V⊕U,(E.filter (ordinaryResourceIncident x)).card:=Finset.card_biUnion_le
    _≤∑_x:V⊕U,D:=Finset.sum_le_sum (fun x _=>hD x)
    _=Fintype.card (V⊕U)*D:=by simp
end Oberwolfach
