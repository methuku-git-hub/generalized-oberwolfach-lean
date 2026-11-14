module

public import Oberwolfach.ExtendingListStability

@[expose] public section
/-! An extending list remains extending after deleting the old embedded
vertices, with the exact loss charged to their cardinality. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem extending_list_avoids_old_image
    {V:Type} [Fintype V] [DecidableEq V]
    (D:V→V→Prop) (L Old:Finset V) (β lam:ℝ)
    (hlam:0≤lam) (hbudget:lam*Fintype.card V+(Old.card:ℝ)≤β*Fintype.card V)
    (hext:IsExtendingList D L β):
    IsExtendingList D (L\Old) lam ∧ Disjoint (L\Old) Old:=by
  constructor
  · apply extending_list_after_neighbourhood_changes D D L (L\Old) β lam 0 (Old.card:ℝ) hlam (by norm_num) (by positivity) ?_ ?_ ?_ ?_ hext
    · have hh:(L\(L\Old)).card≤Old.card:=Finset.card_le_card (by
        intro x hx
        simp only [Finset.mem_sdiff,not_and,not_not] at hx
        exact hx.2 hx.1)
      exact_mod_cast hh
    · intro x;simp
    · intro x;simp
    · simpa using hbudget
  · exact Finset.sdiff_disjoint
end Oberwolfach
