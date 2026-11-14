module

public import Oberwolfach.GraphChangedDegreeSides

@[expose] public section
/-! A type-specific edit consists only of an underlying physical edit or an
edge whose type changed while the physical edge was retained. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem typed_change_contained_in_physical_and_retyping
    {V:Type} [Fintype V] [DecidableEq V] (Ref Now RefType NowType Retype:SimpleGraph V)
    (hRef:RefType≤Ref) (hNow:NowType≤Now)
    (hAgree:∀x y,Ref.Adj x y→Now.Adj x y→¬Retype.Adj x y→(RefType.Adj x y↔NowType.Adj x y)):
    ((RefType\NowType)⊔(NowType\RefType))≤((Ref\Now)⊔(Now\Ref))⊔Retype:=by
  intro x y h
  simp only [SimpleGraph.sup_adj,SimpleGraph.sdiff_adj] at h ⊢
  by_cases hr:Retype.Adj x y
  · exact Or.inr hr
  · left
    rcases h with ⟨ha,hna⟩|⟨hb,hnb⟩
    · have hRefEdge:=hRef ha
      by_cases hNowEdge:Now.Adj x y
      · exact (hna ((hAgree x y hRefEdge hNowEdge hr).mp ha)).elim
      · exact Or.inl ⟨hRefEdge,hNowEdge⟩
    · have hNowEdge:=hNow hb
      by_cases hRefEdge:Ref.Adj x y
      · exact (hnb ((hAgree x y hRefEdge hNowEdge hr).mpr hb)).elim
      · exact Or.inr ⟨hNowEdge,hRefEdge⟩

theorem graph_symmetric_difference_degree
    {V:Type} [Fintype V] [DecidableEq V] (A B:SimpleGraph V) (x:V):
    (((A\B)⊔(B\A)).degree x)=(changed (A.neighborFinset x) (B.neighborFinset x)).card:=by
  rw [←SimpleGraph.card_neighborFinset_eq_degree]
  congr 1
  ext y
  simp only [SimpleGraph.mem_neighborFinset,SimpleGraph.sup_adj,SimpleGraph.sdiff_adj,
    changed,Finset.mem_union,Finset.mem_sdiff]
end Oberwolfach
end
