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
local instance longMarkedResidualIncomingDecEq : DecidableEq V := Classical.decEq V

def longResidualHostArc (M:V→V→ℕ) (Small Ineligible:SimpleGraph V) (e:V×V):Prop:=
  M e.1 e.2=1 ∧ ¬Small.Adj e.1 e.2 ∧ ¬Ineligible.Adj e.1 e.2

noncomputable def longResidualInitialMarked
    (G:SimpleGraph V) (ω:Sym2 V→Fin 6×Bool) (M:V→V→ℕ) (Small Ineligible:SimpleGraph V):
    Finset {e:V×V // longResidualHostArc M Small Ineligible e}:=
  Finset.univ.filter (fun e=>sampledColourOrientation G ω 1 e.val.1 e.val.2=1)

theorem long_residual_initial_marked_incoming_membership
    (G:SimpleGraph V) (ω:Sym2 V→Fin 6×Bool) (M:V→V→ℕ) (Small Ineligible:SimpleGraph V) (v x:V):
    x∈markedCandidateIncomingTails (longResidualHostArc M Small Ineligible)
      (longResidualInitialMarked G ω M Small Ineligible) v ↔
      sampledColourOrientation G ω 1 x v=1 ∧ longResidualHostArc M Small Ineligible (x,v) :=by
  constructor
  · intro hx
    obtain ⟨e,he,hx⟩:=Finset.mem_image.mp hx
    have hh:=(Finset.mem_filter.mp he)
    have hsel:sampledColourOrientation G ω 1 e.val.1 e.val.2=1:=(Finset.mem_filter.mp hh.1).2
    constructor
    · simpa only [hx,hh.2] using hsel
    · have heq:e.val=(x,v):=Prod.ext hx hh.2
      simpa only [heq] using e.property
  · rintro ⟨hsel,hq⟩
    refine Finset.mem_image.mpr ⟨⟨(x,v),hq⟩,?_,rfl⟩
    apply Finset.mem_filter.mpr
    refine ⟨?_,rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hsel⟩

/-- All differences between raw marked incoming tails and those of the
actual residual host lie in the class deletion, the already embedded graph,
or the graph of physically ineligible pairs. -/
theorem long_residual_marked_incoming_change_bound
    (G Del Small Ineligible Loss:SimpleGraph V)
    (ω:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)
    (M:V→V→ℕ)
    (hcorrect:orientationDisagreementGraph (longPhysicalStateGraph G ω {0,1,2,3,4})
      (fun e=>(ω (Sum.inl e)).2) M≤Del)
    (hsmall:∀x y,sampledColourOrientation G (fun e=>ω (Sum.inl e)) 1 x y=1→Small.Adj x y→Loss.Adj x y):
    ∀v,((changed (markedRawIncomingTails G (fun e=>ω (Sum.inl e)) v)
      (markedCandidateIncomingTails (longResidualHostArc M Small Ineligible)
        (longResidualInitialMarked G (fun e=>ω (Sum.inl e)) M Small Ineligible) v)).card:ℝ)≤
      (Del⊔Loss⊔Ineligible).degree v :=by
  intro v
  have hsub:changed (markedRawIncomingTails G (fun e=>ω (Sum.inl e)) v)
      (markedCandidateIncomingTails (longResidualHostArc M Small Ineligible)
        (longResidualInitialMarked G (fun e=>ω (Sum.inl e)) M Small Ineligible) v) ⊆
      (Del⊔Loss⊔Ineligible).neighborFinset v:=by
    intro x hx
    apply ((Del⊔Loss⊔Ineligible).mem_neighborFinset v x).mpr
    have hc: x∈markedRawIncomingTails G (fun e=>ω (Sum.inl e)) v ↔
        sampledColourOrientation G (fun e=>ω (Sum.inl e)) 1 x v=1:=by simp [markedRawIncomingTails]
    have ht:=long_residual_initial_marked_incoming_membership G (fun e=>ω (Sum.inl e)) M Small Ineligible v x
    have hraw:sampledColourOrientation G (fun e=>ω (Sum.inl e)) 1 x v=1:=by
      have h := hx
      simp only [changed,Finset.mem_union,Finset.mem_sdiff] at h
      rcases h with h|h
      · exact hc.mp h.1
      · exact (ht.mp h.1).1
    by_contra hn
    have hDel:¬Del.Adj x v:=by intro h;apply hn;exact Or.inl (Or.inl h.symm)
    have hSmall:¬Small.Adj x v:=by intro h;apply hn;exact Or.inl (Or.inr ((hsmall x v hraw h).symm))
    have hIn:¬Ineligible.Adj x v:=by intro h;apply hn;exact Or.inr h.symm
    have hM:=long_selected_marked_direction_preserved G Del ω M hcorrect x v hraw hDel
    have hmem:x∈markedCandidateIncomingTails (longResidualHostArc M Small Ineligible)
        (longResidualInitialMarked G (fun e=>ω (Sum.inl e)) M Small Ineligible) v:=
      ht.mpr ⟨hraw,⟨hM,hSmall,hIn⟩⟩
    have hmemRaw:=hc.mpr hraw
    simp only [changed,Finset.mem_union,Finset.mem_sdiff] at hx
    tauto
  exact_mod_cast Finset.card_le_card hsub
end Oberwolfach
