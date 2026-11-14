module

public import Oberwolfach.BoundaryLabelChanges

@[expose] public section

/-! Deterministic support bounds after later changes. Row and membership
losses are measured separately; pair intersections lose at most two row
changes. No new probabilistic event is asserted for a later choice. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V J:Type*} [Fintype V] [Fintype J] [DecidableEq V] [DecidableEq J]

theorem support_intersection_changes (A B A' B':Finset V):
    (changed (A∩B) (A'∩B')).card≤(changed A A').card+(changed B B').card := by
  have hs:changed (A∩B) (A'∩B')⊆changed A A'∪changed B B' := by
    intro v hv
    simp only [changed,Finset.mem_union,Finset.mem_sdiff,Finset.mem_inter] at hv ⊢
    tauto
  exact (Finset.card_le_card hs).trans (Finset.card_union_le _ _)

theorem support_bounds_after_changes (S S':J→Finset V) (R P M Lr Lc:ℝ)
    (hR:∀ j,((S j).card:ℝ)≤R)
    (hP:∀ i j,i≠j→((S i∩S j).card:ℝ)≤P)
    (hM:∀ v,((Finset.univ.filter (fun j=>v∈S j)).card:ℝ)≤M)
    (hrow:∀ j,((changed (S j) (S' j)).card:ℝ)≤Lr)
    (hcol:∀ v,((changed (Finset.univ.filter (fun j=>v∈S j))
      (Finset.univ.filter (fun j=>v∈S' j))).card:ℝ)≤Lc):
    (∀ j,((S' j).card:ℝ)≤R+Lr)∧
    (∀ i j,i≠j→((S' i∩S' j).card:ℝ)≤P+2*Lr)∧
    (∀ v,((Finset.univ.filter (fun j=>v∈S' j)).card:ℝ)≤M+Lc) := by
  refine ⟨?_,?_,?_⟩
  · intro j
    have hh:=(abs_le.mp ((card_difference_le_changed (S j) (S' j)).trans (hrow j))).1
    linarith [hR j]
  · intro i j hij
    have hc:((changed (S i∩S j) (S' i∩S' j)).card:ℝ)≤
        (changed (S i) (S' i)).card+(changed (S j) (S' j)).card:=by
      exact_mod_cast support_intersection_changes (S i) (S j) (S' i) (S' j)
    have hh:=(abs_le.mp ((card_difference_le_changed (S i∩S j) (S' i∩S' j)).trans hc)).1
    linarith [hP i j hij,hrow i,hrow j]
  · intro v
    have hh:=(abs_le.mp ((card_difference_le_changed _ _).trans (hcol v))).1
    linarith [hM v]

theorem support_selection_margins (S S':J→Finset V) (p n Lr Lc:ℝ)
    (hp:0≤p) (hp1:p≤1) (hn:0≤n)
    (hR:∀ j,((S j).card:ℝ)≤13*p*n)
    (hP:∀ i j,i≠j→((S i∩S j).card:ℝ)≤145*p^2*n)
    (hM:∀ v,((Finset.univ.filter (fun j=>v∈S j)).card:ℝ)≤13*p*n)
    (hrow:∀ j,((changed (S j) (S' j)).card:ℝ)≤Lr)
    (hcol:∀ v,((changed (Finset.univ.filter (fun j=>v∈S j))
      (Finset.univ.filter (fun j=>v∈S' j))).card:ℝ)≤Lc)
    (hLr:Lr≤p^2*n) (hLc:Lc≤p*n):
    (∀ j,((S' j).card:ℝ)≤14*p*n)∧
    (∀ i j,i≠j→((S' i∩S' j).card:ℝ)≤(14*p)^2*n)∧
    (∀ v,((Finset.univ.filter (fun j=>v∈S' j)).card:ℝ)≤14*p*n) := by
  obtain ⟨hr,hp',hm⟩:=support_bounds_after_changes S S' _ _ _ Lr Lc hR hP hM hrow hcol
  have hs:p^2*n≤p*n:=mul_le_mul_of_nonneg_right (by nlinarith : p^2≤p) hn
  refine ⟨?_,?_,?_⟩
  · intro j;linarith [hr j]
  · intro i j hij;have hh:=hp' i j hij;nlinarith [mul_nonneg (sq_nonneg p) hn]
  · intro v;linarith [hm v]

end Oberwolfach
