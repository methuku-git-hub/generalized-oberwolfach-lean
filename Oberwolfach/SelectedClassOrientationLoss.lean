module

public import Oberwolfach.ExpandedSampleOrientation
public import Oberwolfach.DirectedTwoPathsAfterEdits

@[expose] public section
/-! A stored selected direction is unchanged on every edge kept by the class
graph. Only selected edges missing from that graph can lose a two-path. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem selected_direction_preserved_on_class_edge
    {V:Type} [Fintype V] [LinearOrder V] (P S:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (ω:Sym2 V→Fin 6×Bool) (x y:V)
    (hraw:rawSelectedPhysicalRelation P π d ω x y) (hS:S.Adj x y):
    sampledOrientation S (fun e=>(ω e).2) x y=1:=by
  have h:=expanded_selected_relation_uses_sampled_orientation P π d ω x y hraw
  have hp:P.Adj x y:=((markedPhysicalRim_eq_one_iff P π (3*d) _ false x y).mp hraw).2.1
  simpa only [sampledOrientation,hS,hp,true_and] using h

theorem selected_class_two_paths_after_edits
    {V:Type} [Fintype V] [LinearOrder V] (P S:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (ω:Sym2 V→Fin 6×Bool) (b:ℝ) (hb:0≤b)
    (hlost:∀v,((Finset.univ.filter (fun w=>
      (rawSelectedPhysicalRelation P π d ω v w ∨ rawSelectedPhysicalRelation P π d ω w v) ∧ ¬S.Adj v w)).card:ℝ)≤b):
    ∀x y,(((Finset.univ.filter (fun z=>rawSelectedPhysicalRelation P π d ω x z ∧
      rawSelectedPhysicalRelation P π d ω z y)).card:ℝ)-2*b)≤
      ((Finset.univ.filter (fun z=>0<sampledOrientation S (fun e=>(ω e).2) x z ∧
        0<sampledOrientation S (fun e=>(ω e).2) z y ∧ S.Adj x z ∧ S.Adj z y)).card:ℝ):=by
  let Raw:=rawSelectedPhysicalRelation P π d ω
  let M:=sampledOrientation S (fun e=>(ω e).2)
  have hhost:∀x y,0<M x y→S.Adj x y:=by
    intro x y h
    by_contra hn
    simp [M,sampledOrientation,hn] at h
  have hchange:∀v,((Finset.univ.filter (fun w=>
      (Raw v w ∧ ¬0<M v w) ∨ (Raw w v ∧ ¬0<M w v))).card:ℝ)≤b:=by
    intro v
    apply le_trans ?_ (hlost v)
    exact_mod_cast (Finset.card_le_card (by
      intro w hw
      have hh:=(Finset.mem_filter.mp hw).2
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_,?_⟩
      · exact hh.elim (fun h=>Or.inl h.1) (fun h=>Or.inr h.1)
      · intro hS
        rcases hh with h|h
        · exact h.2 (by change 0<sampledOrientation S (fun e=>(ω e).2) v w;rw [selected_direction_preserved_on_class_edge P S π d ω v w h.1 hS];decide)
        · exact h.2 (by change 0<sampledOrientation S (fun e=>(ω e).2) w v;rw [selected_direction_preserved_on_class_edge P S π d ω w v h.1 hS.symm];decide)))
  exact directed_two_paths_after_edits S Raw M b hb hhost hchange
end Oberwolfach
