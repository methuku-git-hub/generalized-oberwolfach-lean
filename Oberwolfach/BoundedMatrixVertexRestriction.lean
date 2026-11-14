module

public import Oberwolfach.FiniteCenteredDomainRestriction

@[expose] public section

/-! Deleting vertices from a bounded adjacency matrix costs at most the
number removed at each retained row or column. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
variable {V W:Type*} [Fintype V] [Fintype W] [DecidableEq V]

theorem bounded_matrix_vertex_restriction (f:W↪V) (M:V→V→ℝ)
    (hM:∀ x y,|M x y|≤1) (x:W):
    |(∑ y:W,M (f x) (f y))-(∑ y:V,M (f x) y)|≤(Finset.univ\Finset.univ.image f).card∧
    |(∑ y:W,M (f y) (f x))-(∑ y:V,M y (f x))|≤(Finset.univ\Finset.univ.image f).card:=by
  have hout:=finite_bounded_sum_restriction (Finset.univ.image f) Finset.univ
    (Finset.subset_univ _) (M (f x)) (fun y _=>hM (f x) y)
  have hin:=finite_bounded_sum_restriction (Finset.univ.image f) Finset.univ
    (Finset.subset_univ _) (fun y=>M y (f x)) (fun y _=>hM y (f x))
  rw [Finset.sum_image (fun _ _ _ _ he=>f.injective he)] at hout hin
  exact ⟨hout,hin⟩

theorem finset_indicator_sum_change {X:Type*} (S:Finset X) (P Q:X→Prop) [DecidablePred P] [DecidablePred Q]:
    |(∑ x∈S,if Q x then (1:ℝ) else 0)-(∑ x∈S,if P x then (1:ℝ) else 0)|≤
      ∑ x∈S,if ¬(P x↔Q x) then (1:ℝ) else 0:=by
  classical
  rw [←Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro x hx
  by_cases hp:P x <;> by_cases hq:Q x <;> simp [hp,hq]

end Oberwolfach
