module

public import Oberwolfach.FiniteSequenceSimpleWalk

@[expose] public section
/-! Concatenate simple walks with the sole intersection at their join. -/
set_option autoImplicit false
namespace Oberwolfach

theorem simple_walk_append_of_disjoint_initial_support
    {V:Type*} {G:SimpleGraph V} {a b c:V} (p:G.Walk a b) (q:G.Walk b c)
    (hp:p.IsPath) (hq:q.IsPath)
    (hdis:∀x∈p.support.dropLast,x∉q.support):
    (p.append q).IsPath ∧ (p.append q).length=p.length+q.length ∧
      (p.append q).support=p.support.dropLast++q.support := by
  have hp0:p.support.Nodup:=by simpa only [SimpleGraph.Walk.isPath_def] using hp
  have hq0:q.support.Nodup:=by simpa only [SimpleGraph.Walk.isPath_def] using hq
  have hp':p.support.dropLast.Nodup:=List.Nodup.sublist p.support.dropLast_prefix.sublist hp0
  refine ⟨?_,by simp,SimpleGraph.Walk.support_append_eq_support_dropLast_append p q⟩
  rw [SimpleGraph.Walk.isPath_def,SimpleGraph.Walk.support_append_eq_support_dropLast_append]
  apply List.nodup_append.mpr
  refine ⟨hp',hq0,?_⟩
  intro x hx y hy he
  exact hdis x hx (he.symm ▸ hy)
end Oberwolfach
