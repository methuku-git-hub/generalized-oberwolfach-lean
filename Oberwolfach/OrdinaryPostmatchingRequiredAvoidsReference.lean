module

public import Oberwolfach.OrdinaryPostmatchingRequired

@[expose] public section
/-! All post-matching required edges lie outside the physical reference
layer, so new forced edges do not consume the fixed reference absorber. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_postmatching_required_avoids_reference
    {V:Type} [Fintype V] [DecidableEq V]
    (Target Sample Reference Bad Used:SimpleGraph V) (Inner:Finset V)
    (hRef:Reference≤Sample) (hBad:Disjoint Reference Bad):
    ordinaryPostmatchingRequired Target Sample Reference Bad Used Inner≤Target\Reference :=by
  intro v w h
  have hG:=h.1
  rcases hG with hG|hG
  · rcases hG with hG|hG
    · exact ⟨hG.1,fun href=>hG.2 (hRef href)⟩
    · exact ((spanningRestriction_adj (Target\Reference) Inner v w).mp hG).1
  · exact ⟨hG.1,fun href=>(disjoint_iff_inf_le.mp hBad) ⟨href,hG.2⟩⟩
end Oberwolfach
