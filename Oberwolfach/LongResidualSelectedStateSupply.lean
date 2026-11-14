module

public import Oberwolfach.LongSampledStateOrientationPreserved
public import Oberwolfach.LongMarkedResidualIncomingChange

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [LinearOrder V] [Nonempty V] [Fintype U] [DecidableEq U] [Fintype Γ] [Fintype Color]
local instance supplyDecEq : DecidableEq V := Classical.decEq V

/-- Incoming raw selected-state arcs which do not survive in the residual
are incident with the same class deletion, new embedding loss, or ineligible graph. -/
theorem long_residual_selected_state_incoming_supply
    (G Del Small Bad Loss:SimpleGraph V)
    (ω:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)
    (M:V→V→ℕ) (j:Fin 6) (hj:j∈({0,1,2,3,4}:Finset (Fin 6)))
    (hcorrect:orientationDisagreementGraph (longPhysicalStateGraph G ω {0,1,2,3,4})
      (fun e=>(ω (Sum.inl e)).2) M≤Del)
    (hsmall:∀x y,sampledColourOrientation G (fun e=>ω (Sum.inl e)) j x y=1→Small.Adj x y→Loss.Adj x y):
    let P:=longResidualHostArc M Small Bad
    let C:Finset {e:V×V // P e}:=Finset.univ.filter (fun e=>sampledColourOrientation G (fun e=>ω (Sum.inl e)) j e.val.1 e.val.2=1)
    ∀v,(∑x,sampledColourOrientation G (fun e=>ω (Sum.inl e)) j x v) ≤
      (C.filter (fun e=>e.val.2=v)).card+(Del⊔Loss⊔Bad).degree v :=by
  intro P C v
  let Raw:Finset V:=Finset.univ.filter (fun x=>sampledColourOrientation G (fun e=>ω (Sum.inl e)) j x v=1)
  let Tail:=markedCandidateIncomingTails P C v
  have hsub:Raw⊆Tail∪(Del⊔Loss⊔Bad).neighborFinset v:=by
    intro x hx
    have hs:sampledColourOrientation G (fun e=>ω (Sum.inl e)) j x v=1:=(Finset.mem_filter.mp hx).2
    by_cases hbad:(Del⊔Loss⊔Bad).Adj x v
    · exact Finset.mem_union.mpr (Or.inr (((Del⊔Loss⊔Bad).mem_neighborFinset v x).mpr hbad.symm))
    · have hd:¬Del.Adj x v:=fun h=>hbad (Or.inl (Or.inl h))
      have hl:¬Loss.Adj x v:=fun h=>hbad (Or.inl (Or.inr h))
      have hb:¬Bad.Adj x v:=fun h=>hbad (Or.inr h)
      have hsm:¬Small.Adj x v:=fun h=>hl (hsmall x v hs h)
      have hm:=long_sampled_state_direction_preserved G Del ω M j hj hcorrect x v hs hd
      have hp:P (x,v):=⟨hm,hsm,hb⟩
      apply Finset.mem_union.mpr
      left
      apply Finset.mem_image.mpr
      refine ⟨⟨(x,v),hp⟩,?_,rfl⟩
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,hs⟩,rfl⟩
  have hcard:Raw.card≤Tail.card+(Del⊔Loss⊔Bad).degree v:=by
    have h₁:=Finset.card_le_card hsub
    have h₂:=Finset.card_union_le Tail ((Del⊔Loss⊔Bad).neighborFinset v)
    rw [SimpleGraph.card_neighborFinset_eq_degree] at h₂
    omega
  have hraw:Raw.card=∑x,sampledColourOrientation G (fun e=>ω (Sum.inl e)) j x v:=by
    unfold Raw
    rw [Finset.card_filter]
    apply Finset.sum_congr rfl
    intro x hx
    unfold sampledColourOrientation
    split_ifs <;> simp_all
  rw [hraw,marked_candidate_incoming_tails_card] at hcard
  exact hcard
end Oberwolfach
