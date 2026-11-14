module

public import Oberwolfach.InducedFractionalCycles

@[expose] public section
/-! A first piece that avoids the inner set contributes no inner edges. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {W:Type} [Fintype W] [DecidableEq W]

theorem graph_four_piece_inner_subset (G A B C D:SimpleGraph W) (Ω:Finset W)
    (hAsub:A≤G) (hA:Disjoint A (spanningRestriction G Ω)):
    spanningRestriction (((A⊔B)⊔C)⊔D) Ω≤
      (B⊔spanningRestriction C Ω)⊔spanningRestriction D Ω:=by
  intro a b hab
  have hh:=(spanningRestriction_adj _ _ _ _).mp hab
  rcases hh.1 with ((ha|hb)|hc)|hd
  · have hi:(spanningRestriction G Ω).Adj a b:=
      (spanningRestriction_adj _ _ _ _).mpr ⟨hAsub ha,hh.2.1,hh.2.2⟩
    exact ((disjoint_iff_inf_le.mp hA) ⟨ha,hi⟩).elim
  · exact Or.inl (Or.inl hb)
  · exact Or.inl (Or.inr ((spanningRestriction_adj _ _ _ _).mpr ⟨hc,hh.2.1,hh.2.2⟩))
  · exact Or.inr ((spanningRestriction_adj _ _ _ _).mpr ⟨hd,hh.2.1,hh.2.2⟩)
end Oberwolfach
