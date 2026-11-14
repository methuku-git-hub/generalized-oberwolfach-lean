module

public import Oberwolfach.BoundarySupportChanges

@[expose] public section
/-! Two rim-neighborhood edits and one spoke-column edit change an ordinary
boundary extension count by at most the sum of their physical degrees. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_boundary_extension_count_stability
    (Q Q':SimpleGraph V) (H H':V→U→Prop) (X:Finset V) (a c:V) (u:U) (L:ℝ)
    (ha:((changed (Q.neighborFinset a) (Q'.neighborFinset a)).card:ℝ)≤L)
    (hc:((changed (Q.neighborFinset c) (Q'.neighborFinset c)).card:ℝ)≤L)
    (hu:((changed (Finset.univ.filter (fun v=>H v u)) (Finset.univ.filter (fun v=>H' v u))).card:ℝ)≤L):
    |((X.filter (fun v=>Q.Adj a v∧Q.Adj v c∧H v u)).card:ℝ)-
      ((X.filter (fun v=>Q'.Adj a v∧Q'.Adj v c∧H' v u)).card:ℝ)|≤3*L:=by
  let A:=X.filter (fun v=>Q.Adj a v∧Q.Adj v c∧H v u)
  let B:=X.filter (fun v=>Q'.Adj a v∧Q'.Adj v c∧H' v u)
  let Da:=changed (Q.neighborFinset a) (Q'.neighborFinset a)
  let Dc:=changed (Q.neighborFinset c) (Q'.neighborFinset c)
  let Du:=changed (Finset.univ.filter (fun v=>H v u)) (Finset.univ.filter (fun v=>H' v u))
  have hsub:changed A B⊆Da∪Dc∪Du:=by
    intro v hv
    simp only [changed,Finset.mem_union,Finset.mem_sdiff,Finset.mem_filter,
      Finset.mem_univ,true_and,SimpleGraph.mem_neighborFinset,A,B,Da,Dc,Du] at hv ⊢
    have hq:Q.Adj v c↔Q.Adj c v:=Q.adj_comm _ _
    have hq':Q'.Adj v c↔Q'.Adj c v:=Q'.adj_comm _ _
    tauto
  have hcard:((changed A B).card:ℝ)≤(Da.card:ℝ)+Dc.card+Du.card:=by
    have hh: (changed A B).card≤Da.card+Dc.card+Du.card:=
      (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
        (Nat.add_le_add_right (Finset.card_union_le _ _) _))
    exact_mod_cast hh
  have hh:=card_difference_le_changed A B
  dsimp only [A,B] at hh
  dsimp only [Da,Dc,Du] at hcard
  exact hh.trans (by linarith only [hcard,ha,hc,hu])
end Oberwolfach
