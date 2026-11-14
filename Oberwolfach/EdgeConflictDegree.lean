module

public import Oberwolfach.PrescribedTargetMatching

@[expose] public section
/-! A physical edge can conflict only with edges incident with one of its
endpoints. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

def edgeAssignmentConflict (e f:Sym2 V):Prop:=¬Disjoint e.toFinset f.toFinset

theorem edge_assignment_conflict_symmetric (e f:Sym2 V):
    edgeAssignmentConflict e f→edgeAssignmentConflict f e:=by
  intro h hdis
  exact h hdis.symm

theorem edge_assignment_conflicts_at_most (K:SimpleGraph V) (x y:V):
    ((K.edgeFinset.filter (edgeAssignmentConflict s(x,y))).card:ℝ)≤(K.degree x:ℝ)+K.degree y := by
  have hsub:K.edgeFinset.filter (edgeAssignmentConflict s(x,y))⊆K.incidenceFinset x∪K.incidenceFinset y:=by
    intro e he
    have heK:e∈K.edgeFinset:=(Finset.mem_filter.mp he).1
    have hc:edgeAssignmentConflict s(x,y) e:=(Finset.mem_filter.mp he).2
    have hxory:x∈e ∨ y∈e:=by
      by_contra h
      apply hc
      apply Finset.disjoint_left.mpr
      intro v hv hv'
      simp only [Sym2.toFinset_mk_eq,Finset.mem_insert,Finset.mem_singleton] at hv
      rcases hv with rfl|rfl
      · exact (not_or.mp h).1 (by simpa using hv')
      · exact (not_or.mp h).2 (by simpa using hv')
    rcases hxory with hx|hy
    · apply Finset.mem_union_left
      rw [SimpleGraph.incidenceFinset_eq_filter]
      exact Finset.mem_filter.mpr ⟨heK,hx⟩
    · apply Finset.mem_union_right
      rw [SimpleGraph.incidenceFinset_eq_filter]
      exact Finset.mem_filter.mpr ⟨heK,hy⟩
  have hn:(K.edgeFinset.filter (edgeAssignmentConflict s(x,y))).card≤K.degree x+K.degree y:=by
    calc
      _ ≤ (K.incidenceFinset x∪K.incidenceFinset y).card:=Finset.card_le_card hsub
      _ ≤ (K.incidenceFinset x).card+(K.incidenceFinset y).card:=Finset.card_union_le _ _
      _ = _:=by rw [SimpleGraph.card_incidenceFinset_eq_degree,SimpleGraph.card_incidenceFinset_eq_degree]
  exact_mod_cast hn
end Oberwolfach
