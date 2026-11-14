module

public import Oberwolfach.EdgeAssignmentSaturation

@[expose] public section
/-! Every step of the greedy assignment has an available index, with the
capacity loss counted from the actual already assigned edge set. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {E W:Type} [Fintype W] [DecidableEq E] [DecidableEq W]

theorem edge_assignment_available_index (S T:Finset E) (hTS:T⊆S) (f:E→W) (e:E)
    (L Bad:Finset W) (C:E→Prop) (K:ℕ) (hK:0<K)
    (hbudget:(Bad.card:ℝ)+((S.filter C).card:ℝ)+(S.card:ℝ)/K<(L.card:ℝ)):
    ∃ w∈L,w∉Bad ∧ (∀x∈T,C x→f x≠w) ∧ (T.filter (fun x=>f x=w)).card<K := by
  let Conf:=T.filter C
  let Sat:=Finset.univ.filter (fun w=>K≤(T.filter (fun x=>f x=w)).card)
  let Ex:=Bad∪Conf.image f∪Sat
  have hConf:(Conf.card:ℝ)≤(S.filter C).card:=by
    exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ hTS)
  have hsat0: (K:ℝ)*(Sat.card:ℝ)≤T.card:=assigned_indices_saturation T f K hK
  have hK':(0:ℝ)<K:=by exact_mod_cast hK
  have hsat:(Sat.card:ℝ)≤(S.card:ℝ)/K:=by
    have hT:(T.card:ℝ)≤S.card:=by exact_mod_cast Finset.card_le_card hTS
    apply (le_div_iff₀ hK').mpr
    nlinarith
  have hcard:Ex.card≤Bad.card+Conf.card+Sat.card:=by
    calc
      _ ≤ (Bad∪Conf.image f).card+Sat.card:=Finset.card_union_le _ _
      _ ≤ Bad.card+(Conf.image f).card+Sat.card:=Nat.add_le_add_right (Finset.card_union_le _ _) _
      _ ≤ Bad.card+Conf.card+Sat.card:=Nat.add_le_add_right (Nat.add_le_add_left Finset.card_image_le _) _
  have hcardR:(Ex.card:ℝ)≤Bad.card+Conf.card+Sat.card:=by exact_mod_cast hcard
  have hlt:(Ex.card:ℝ)<L.card:=by linarith
  have hnot:¬L⊆Ex:=by
    intro h
    have hh: (L.card:ℝ)≤Ex.card:=by exact_mod_cast Finset.card_le_card h
    linarith
  obtain ⟨w,hw,hnotw⟩:=Finset.not_subset.mp hnot
  have hBad:w∉Bad:=by intro h;exact hnotw (by simp [Ex,h])
  have hConfW:w∉Conf.image f:=by intro h;exact hnotw (by simp [Ex,h])
  have hSat:w∉Sat:=by intro h;exact hnotw (by simp [Ex,h])
  refine ⟨w,hw,hBad,?_,?_⟩
  · intro x hx hCx heq
    apply hConfW
    exact Finset.mem_image.mpr ⟨x,Finset.mem_filter.mpr ⟨hx,hCx⟩,heq⟩
  · have hn:¬K≤(T.filter (fun x=>f x=w)).card:=by simpa [Sat] using hSat
    omega
end Oberwolfach
