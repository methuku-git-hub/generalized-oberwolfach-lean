module

public import Oberwolfach.LongSelectedMarkedOrientationPreserved
public import Oberwolfach.MarkedCandidateChangeGraph

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [LinearOrder V] [Nonempty V] [Fintype U] [DecidableEq U] [Fintype Γ] [Fintype Color]
local instance eligibleIncomingDecEq : DecidableEq V := Classical.decEq V

def longEligibleResidualArc (M:V→V→ℕ) (Small OrdBad:SimpleGraph V) (e:V×V):Prop:=
  M e.1 e.2=1 ∧ ¬Small.Adj e.1 e.2 ∧ ¬OrdBad.Adj e.1 e.2

noncomputable def longEligibleInitialMarked
    (G:SimpleGraph V) (ω:Sym2 V→Fin 6×Bool) (M:V→V→ℕ) (Small OrdBad:SimpleGraph V)
    (Eligible:V×V→Prop):Finset {e:V×V // longEligibleResidualArc M Small OrdBad e}:=
  Finset.univ.filter (fun e=>sampledColourOrientation G ω 1 e.val.1 e.val.2=1 ∧ Eligible e.val)

theorem long_eligible_initial_marked_incoming_membership
    (G:SimpleGraph V) (ω:Sym2 V→Fin 6×Bool) (M:V→V→ℕ) (Small OrdBad:SimpleGraph V)
    (Eligible:V×V→Prop) (v x:V):
    x∈markedCandidateIncomingTails (longEligibleResidualArc M Small OrdBad)
      (longEligibleInitialMarked G ω M Small OrdBad Eligible) v ↔
      sampledColourOrientation G ω 1 x v=1 ∧ Eligible (x,v) ∧ longEligibleResidualArc M Small OrdBad (x,v) :=by
  constructor
  · intro hx
    obtain ⟨e,he,hx⟩:=Finset.mem_image.mp hx
    have hh:=(Finset.mem_filter.mp he)
    have hs:=(Finset.mem_filter.mp hh.1).2
    have heq:e.val=(x,v):=Prod.ext hx hh.2
    simpa only [heq] using And.intro hs.1 (And.intro hs.2 e.property)
  · rintro ⟨hsel,hel,hq⟩
    refine Finset.mem_image.mpr ⟨⟨(x,v),hq⟩,?_,rfl⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,hsel,hel⟩,rfl⟩

theorem long_eligible_marked_incoming_change_bound
    (G Del Small OrdBad Bad Loss:SimpleGraph V)
    (ω:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)
    (M:V→V→ℕ) (Eligible:V×V→Prop)
    (hcorrect:orientationDisagreementGraph (longPhysicalStateGraph G ω {0,1,2,3,4})
      (fun e=>(ω (Sum.inl e)).2) M≤Del)
    (hsmall:∀x y,sampledColourOrientation G (fun e=>ω (Sum.inl e)) 1 x y=1→Small.Adj x y→Loss.Adj x y)
    (hOrd:OrdBad≤Bad)
    (hEligible:∀x y,G.Adj x y→¬Eligible (x,y)→Bad.Adj x y):
    ∀v,((changed (markedRawIncomingTails G (fun e=>ω (Sum.inl e)) v)
      (markedCandidateIncomingTails (longEligibleResidualArc M Small OrdBad)
        (longEligibleInitialMarked G (fun e=>ω (Sum.inl e)) M Small OrdBad Eligible) v)).card:ℝ)≤
      (Del⊔Loss⊔Bad).degree v :=by
  intro v
  have hsub:changed (markedRawIncomingTails G (fun e=>ω (Sum.inl e)) v)
      (markedCandidateIncomingTails (longEligibleResidualArc M Small OrdBad)
        (longEligibleInitialMarked G (fun e=>ω (Sum.inl e)) M Small OrdBad Eligible) v) ⊆
      (Del⊔Loss⊔Bad).neighborFinset v:=by
    intro x hx
    apply ((Del⊔Loss⊔Bad).mem_neighborFinset v x).mpr
    have hc:x∈markedRawIncomingTails G (fun e=>ω (Sum.inl e)) v ↔
        sampledColourOrientation G (fun e=>ω (Sum.inl e)) 1 x v=1:=by simp [markedRawIncomingTails]
    have ht:=long_eligible_initial_marked_incoming_membership G (fun e=>ω (Sum.inl e)) M Small OrdBad Eligible v x
    have hraw:sampledColourOrientation G (fun e=>ω (Sum.inl e)) 1 x v=1:=by
      have h:=hx
      simp only [changed,Finset.mem_union,Finset.mem_sdiff] at h
      rcases h with h|h
      · exact hc.mp h.1
      · exact (ht.mp h.1).1
    have hG:G.Adj x v:=by
      by_contra h
      simp [sampledColourOrientation,h] at hraw
    by_contra hn
    have hDel:¬Del.Adj x v:=by intro h;apply hn;exact Or.inl (Or.inl h.symm)
    have hSmall:¬Small.Adj x v:=by intro h;apply hn;exact Or.inl (Or.inr ((hsmall x v hraw h).symm))
    have hBad:¬Bad.Adj x v:=by intro h;apply hn;exact Or.inr h.symm
    have hOrd':¬OrdBad.Adj x v:=fun h=>hBad (hOrd h)
    have hEl:Eligible (x,v):=by by_contra h;exact hBad (hEligible x v hG h)
    have hM:=long_selected_marked_direction_preserved G Del ω M hcorrect x v hraw hDel
    have hmem:=ht.mpr ⟨hraw,hEl,hM,hSmall,hOrd'⟩
    have hmemRaw:=hc.mpr hraw
    simp only [changed,Finset.mem_union,Finset.mem_sdiff] at hx
    tauto
  exact_mod_cast Finset.card_le_card hsub
end Oberwolfach
