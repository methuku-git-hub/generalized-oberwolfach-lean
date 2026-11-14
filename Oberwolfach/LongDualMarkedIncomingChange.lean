module

public import Oberwolfach.LongDualInitialMarked
public import Oberwolfach.LongSelectedMarkedOrientationPreserved

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [LinearOrder V] [Nonempty V] [Fintype U] [DecidableEq U] [Fintype Γ] [Fintype Color]
local instance dualChangeDecEq : DecidableEq V := Classical.decEq V

theorem long_dual_marked_incoming_change_bound
    (G Del Small Bad Loss:SimpleGraph V)
    (ω:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)
    (M:V→V→ℕ) (Ord Mark:V×V→Prop)
    (hcorrect:orientationDisagreementGraph (longPhysicalStateGraph G ω {0,1,2,3,4})
      (fun e=>(ω (Sum.inl e)).2) M≤Del)
    (hhost:∀x y,M x y=1→G.Adj x y)
    (hsmall:∀x y,sampledColourOrientation G (fun e=>ω (Sum.inl e)) 1 x y=1→Small.Adj x y→Loss.Adj x y)
    (hBad:∀x y,G.Adj x y→¬(Ord (x,y) ∧ Mark (x,y))→Bad.Adj x y):
    ∀v,((changed (markedRawIncomingTails G (fun e=>ω (Sum.inl e)) v)
      (markedCandidateIncomingTails (longEligibleResidualArc M Small ⊥)
        (longDualInitialMarked G (fun e=>ω (Sum.inl e)) M Small Ord Mark) v)).card:ℝ)≤
      (Del⊔Loss⊔Bad).degree v :=by
  intro v
  have hsub:changed (markedRawIncomingTails G (fun e=>ω (Sum.inl e)) v)
      (markedCandidateIncomingTails (longEligibleResidualArc M Small ⊥)
        (longDualInitialMarked G (fun e=>ω (Sum.inl e)) M Small Ord Mark) v) ⊆
      (Del⊔Loss⊔Bad).neighborFinset v:=by
    intro x hx
    apply ((Del⊔Loss⊔Bad).mem_neighborFinset v x).mpr
    have hc:x∈markedRawIncomingTails G (fun e=>ω (Sum.inl e)) v ↔
        sampledColourOrientation G (fun e=>ω (Sum.inl e)) 1 x v=1:=by simp [markedRawIncomingTails]
    have ht:=long_dual_initial_marked_membership G (fun e=>ω (Sum.inl e)) M Small Ord Mark v x
    by_contra hn
    have hDel:¬Del.Adj x v:=by intro h;apply hn;exact Or.inl (Or.inl h.symm)
    have hBad':¬Bad.Adj x v:=by intro h;apply hn;exact Or.inr h.symm
    have hraw:sampledColourOrientation G (fun e=>ω (Sum.inl e)) 1 x v=1:=by
      have h:=hx
      simp only [changed,Finset.mem_union,Finset.mem_sdiff] at h
      rcases h with h|h
      · exact hc.mp h.1
      · obtain ⟨hstate,hP⟩:=ht.mp h.1
        have hG:=hhost x v hP.1
        have hflex:Ord (x,v) ∧ Mark (x,v):=by by_contra hh;exact hBad' (hBad x v hG hh)
        rcases hstate with hstate|hstate
        · exact hstate.1
        · exact False.elim (hstate hflex.1)
    have hG:G.Adj x v:=by by_contra h;simp [sampledColourOrientation,h] at hraw
    have hflex:Ord (x,v) ∧ Mark (x,v):=by by_contra h;exact hBad' (hBad x v hG h)
    have hSmall:¬Small.Adj x v:=by intro h;apply hn;exact Or.inl (Or.inr ((hsmall x v hraw h).symm))
    have hM:=long_selected_marked_direction_preserved G Del ω M hcorrect x v hraw hDel
    have hmem:=ht.mpr ⟨Or.inl ⟨hraw,hflex.2⟩,hM,hSmall,by simp⟩
    have hmemRaw:=hc.mpr hraw
    simp only [changed,Finset.mem_union,Finset.mem_sdiff] at hx
    tauto
  exact_mod_cast Finset.card_le_card hsub
end Oberwolfach
