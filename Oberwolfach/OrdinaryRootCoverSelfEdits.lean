module

public import Oberwolfach.OrdinaryRootCoverNonrootEditBounds

@[expose] public section
/-! A small-load root cover changes its own parent rim and spoke rows by
at most its nonroot physical degree. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_root_cover_self_edits (Q F:SimpleGraph V) (H:V→U→Prop)
    (X T:Finset V) (Z W:Finset U) (r:ℕ) (η ell:ℝ)
    (D:OrdinaryRootCoverNonrootData Q F H X T Z W r η ell):
    let Q':=Q\D.rim;let H':=fun v u=>H v u∧¬D.spokes v u;
    (∀v∉T,((changed (Q'.neighborFinset v) (Q.neighborFinset v)).card:ℝ)≤ell) ∧
    (∀v∉T,((changed (Finset.univ.filter (H' v)) (Finset.univ.filter (H v))).card:ℝ)≤ell):=by
  intro Q' H'
  have hr:∀v∉T,((changed (Q.neighborFinset v) (Q.neighborFinset v)).card:ℝ)≤0:=by
    intro v hv;simp [changed]
  have hs:∀v∉T,((changed (Finset.univ.filter (H v)) (Finset.univ.filter (H v))).card:ℝ)≤0:=by
    intro v hv;simp [changed]
  have hc:∀u∉W,((changed (Finset.univ.filter (fun v=>H v u)) (Finset.univ.filter (fun v=>H v u))).card:ℝ)≤0:=by
    intro u hu;simp [changed]
  have he:=ordinary_root_cover_nonroot_edit_bounds Q Q F H H X T Z W r η ell 0 D hr hs hc
  constructor
  · intro v hv
    have hh:=he.1 v hv
    simp only [zero_add] at hh
    convert hh using 1 <;> simp only [changed,Finset.union_comm] <;> congr! 8 <;> exact Subsingleton.elim _ _
  · intro v hv
    have hh:=he.2.1 v hv
    simp only [zero_add] at hh
    convert hh using 1 <;> simp only [changed,Finset.union_comm] <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach
