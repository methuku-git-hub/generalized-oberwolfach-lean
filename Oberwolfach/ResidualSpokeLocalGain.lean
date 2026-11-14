module

public import Oberwolfach.InnerRequiredTargets

@[expose] public section
/-! A new ordinary spoke in a protected vertex set is either an unfilled
local target or a retained-versus-raw label mismatch. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem residual_spoke_local_gain
    {V:Type} [Fintype V] [DecidableEq V]
    (A L Y Old R Hold:Finset V) (hOld:Disjoint (R\Y) Old):
    let Target:=A\(L∪Y∪Old)
    let Gain:=A∩((R\Y)\Hold)
    let Mismatch:=A∩(L\Hold);
    Gain⊆Target∪Mismatch ∧ Gain.card≤Target.card+Mismatch.card :=by
  intro Target Gain Mismatch
  have hsub:Gain⊆Target∪Mismatch:=by
    intro v hv
    have h:=Finset.mem_inter.mp hv
    have hR:=Finset.mem_sdiff.mp (Finset.mem_sdiff.mp h.2).1
    have hnHold: v∉Hold:=(Finset.mem_sdiff.mp h.2).2
    have hnOld:v∉Old:=by
      intro ho
      exact (Finset.disjoint_left.mp hOld) (Finset.mem_sdiff.mpr hR) ho
    by_cases hL:v∈L
    · apply Finset.mem_union_right
      exact Finset.mem_inter.mpr ⟨h.1,Finset.mem_sdiff.mpr ⟨hL,hnHold⟩⟩
    · apply Finset.mem_union_left
      exact Finset.mem_sdiff.mpr ⟨h.1,by simpa only [Finset.mem_union,not_or] using ⟨⟨hL,hR.2⟩,hnOld⟩⟩
  exact ⟨hsub,(Finset.card_le_card hsub).trans (Finset.card_union_le _ _)⟩
end Oberwolfach
