module

public import Oberwolfach.BoundarySupportChanges

@[expose] public section
/-! Two bounded spoke-row edits change a common-hub count by at most their
combined physical degree. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_boundary_hub_pair_count_stability
    (H H':V→U→Prop) (Z:Finset U) (a c:V) (L:ℝ)
    (ha:((changed (Finset.univ.filter (H a)) (Finset.univ.filter (H' a))).card:ℝ)≤L)
    (hc:((changed (Finset.univ.filter (H c)) (Finset.univ.filter (H' c))).card:ℝ)≤L):
    |((Z.filter (fun u=>H a u∧H c u)).card:ℝ)-
      ((Z.filter (fun u=>H' a u∧H' c u)).card:ℝ)|≤2*L:=by
  let A:=Z.filter (fun u=>H a u∧H c u)
  let B:=Z.filter (fun u=>H' a u∧H' c u)
  let Da:=changed (Finset.univ.filter (H a)) (Finset.univ.filter (H' a))
  let Dc:=changed (Finset.univ.filter (H c)) (Finset.univ.filter (H' c))
  have hsub:changed A B⊆Da∪Dc:=by
    intro u hu
    simp only [changed,Finset.mem_union,Finset.mem_sdiff,Finset.mem_filter,
      Finset.mem_univ,true_and,A,B,Da,Dc] at hu ⊢
    tauto
  have hcard:((changed A B).card:ℝ)≤(Da.card:ℝ)+Dc.card:=by
    exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_union_le Da Dc)
  have hh:=card_difference_le_changed A B
  dsimp only [A,B] at hh
  dsimp only [Da,Dc] at hcard
  exact hh.trans (by linarith only [hcard,ha,hc])
end Oberwolfach
