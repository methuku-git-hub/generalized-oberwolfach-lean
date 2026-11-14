module

public import Oberwolfach.MarkedInnerSpokeColumnFromCorrection

@[expose] public section
/-! The protected inner spoke agreement and the measured inner losses bound
both kinds of boundary test on subsets of the protected domains. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_boundary_spoke_local_changes
    {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    (I A:Finset V) (J B:Finset U) (hAI:A⊆I) (hBJ:B⊆J)
    (H H':Bool→V→U→Prop) (δ:ℝ) (hδ:0≤δ)
    (hspoke:∀b v u,v∈I→u∈J→(H b v u↔H' b v u))
    (hrowOutside:∀v,v∉I→(∑u∈J,if ¬(H false v u↔H' false v u) then (1:ℝ) else 0)≤δ)
    (hmark:∀v u,H true v u↔H' true v u)
    (hnoNew:∀u v,v∈I→H' false v u→H false v u)
    (hloss:∀u,((I.filter (fun v=>H false v u ∧ ¬H' false v u)).card:ℝ)≤δ):
    (∀b v,(∑u∈B,if ¬(H b v u↔H' b v u) then (1:ℝ) else 0)≤δ) ∧
    (∀b u,(∑v∈A,if ¬(H b v u↔H' b v u) then (1:ℝ) else 0)≤δ) :=by
  constructor
  · intro b v
    by_cases hv:v∈I
    · have hz:(∑u∈B,if ¬(H b v u↔H' b v u) then (1:ℝ) else 0)=0:=by
        apply Finset.sum_eq_zero
        intro u hu
        simp [hspoke b v u hv (hBJ hu)]
      simpa only [hz] using hδ
    · cases b with
      | true =>
        have hz:(∑u∈B,if ¬(H true v u↔H' true v u) then (1:ℝ) else 0)=0:=by
          apply Finset.sum_eq_zero
          intro u hu
          simp [hmark v u]
        simpa only [hz] using hδ
      | false =>
        have hh:(∑u∈B,if ¬(H false v u↔H' false v u) then (1:ℝ) else 0)≤
          ∑u∈J,if ¬(H false v u↔H' false v u) then (1:ℝ) else 0:=
          Finset.sum_le_sum_of_subset_of_nonneg hBJ (by intro u _ _;split_ifs <;> norm_num)
        exact hh.trans (hrowOutside v hv)
  · intro b u
    have hh:(∑v∈A,if ¬(H b v u↔H' b v u) then (1:ℝ) else 0)≤
      ∑v∈I,if ¬(H b v u↔H' b v u) then (1:ℝ) else 0:=
      Finset.sum_le_sum_of_subset_of_nonneg hAI (by intro v _ _;split_ifs <;> norm_num)
    exact hh.trans (marked_inner_spoke_column_from_correction I H H' δ hδ hmark hnoNew hloss b u)
end Oberwolfach
