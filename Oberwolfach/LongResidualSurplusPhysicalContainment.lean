module

public import Oberwolfach.LongPreparationPhysicalStates

@[expose] public section
/-! Every class-residual edge outside the selected reference lies in an
unused approximate state, an unassigned state, a short-spacing graph, or the
actual class-edit graph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_residual_surplus_physical_containment
    {V U Γ Color:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U] [Fintype Γ] [Fintype Color]
    (P S Used Small:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (σ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)
    (hUsed:Used≤Small):
    ((S\Small)\longSelectedPhysicalGraph P π d σ)≤
      ((longPhysicalStateGraph P σ {4} ⊔ (longPhysicalStateGraph P σ {2,3}\Used)) ⊔
        longPreparationIneligibleGraph P π d) ⊔ (S\longPhysicalStateGraph P σ {0,1,2,3,4}):=by
  intro x y h
  have hs:S.Adj x y:=h.1.1
  have hnotSmall:¬Small.Adj x y:=h.1.2
  have hnotSel:¬(longSelectedPhysicalGraph P π d σ).Adj x y:=h.2
  have hnotUsed:¬Used.Adj x y:=fun hu=>hnotSmall (hUsed hu)
  simp only [SimpleGraph.sup_adj]
  by_cases hstate:(longPhysicalStateGraph P σ {0,1,2,3,4}).Adj x y
  · have hP:P.Adj x y:=hstate.1
    have hcat:(σ (Sum.inl s(x,y))).1=0 ∨ (σ (Sum.inl s(x,y))).1=1 ∨
        (σ (Sum.inl s(x,y))).1=2 ∨ (σ (Sum.inl s(x,y))).1=3 ∨ (σ (Sum.inl s(x,y))).1=4:=by
      simpa [longPhysicalStateGraph] using hstate.2
    by_cases hbad:(longPreparationIneligibleGraph P π d).Adj x y
    · exact Or.inl (Or.inr hbad)
    · rcases hcat with hc|hc|hc|hc|hc
      · exact (hnotSel (selected_state_outside_ineligible_is_selected P π d σ x y hP hbad (Or.inl hc))).elim
      · exact (hnotSel (selected_state_outside_ineligible_is_selected P π d σ x y hP hbad (Or.inr hc))).elim
      · exact Or.inl (Or.inl (Or.inr ⟨⟨hP,by simp [longPhysicalStateGraph,hc]⟩,hnotUsed⟩))
      · exact Or.inl (Or.inl (Or.inr ⟨⟨hP,by simp [longPhysicalStateGraph,hc]⟩,hnotUsed⟩))
      · exact Or.inl (Or.inl (Or.inl ⟨hP,by simp [longPhysicalStateGraph,hc]⟩))
  · exact Or.inr ⟨hs,hstate⟩
end Oberwolfach
