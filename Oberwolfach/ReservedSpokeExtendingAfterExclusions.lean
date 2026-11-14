module

public import Oberwolfach.ExtendingListStability

@[expose] public section
/-! Deleting the manuscript's inner and absorber-target vertices from each
reserved list preserves the extending property with the exact cardinal loss. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem extending_list_after_two_exclusions
    {V:Type} [Fintype V] [DecidableEq V] (D:V→V→Prop) (L I Z:Finset V)
    (β lam:ℝ) (hlam:0≤lam)
    (hbudget:lam*Fintype.card V+I.card+Z.card≤β*Fintype.card V)
    (hext:IsExtendingList D L β):IsExtendingList D (L\(I∪Z)) lam:=by
  have hsub:L\(L\(I∪Z))⊆I∪Z:=by intro x hx; simp only [Finset.mem_sdiff,Finset.mem_union] at *; tauto
  have hc:=Finset.card_le_card hsub
  have hu:=Finset.card_union_le I Z
  have hloss:((L\(L\(I∪Z))).card:ℝ)≤(I.card:ℝ)+Z.card:=by exact_mod_cast hc.trans hu
  apply extending_list_after_neighbourhood_changes D D L (L\(I∪Z)) β lam 0 ((I.card:ℝ)+Z.card)
    hlam (by norm_num) (by positivity) hloss
  · intro x; simp
  · intro x; simp
  · linarith
  · exact hext
end Oberwolfach
