module

public import Oberwolfach.PrescribedPathScheduleEdges
public import Oberwolfach.PrescribedPathDirectedEdges

@[expose] public section
/-! Splitting a cycle at two distinct prescribed vertices produces two
ordered paths, with no common vertex other than the two boundaries. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {X:Type} [DecidableEq X]

theorem prescribed_cycle_two_boundary_split (a b:X) (xs:List X)
    (ha:a∉xs) (hxs:xs.Nodup) (hb:b∈xs):
    ∃ pre post:List X,xs=pre++b::post ∧
      (a::pre++[b]).Nodup ∧ (b::post++[a]).Nodup ∧
      (∀ x,x∈(a::pre++[b])→x∈(b::post++[a])→x=a ∨ x=b) ∧
      prescribedOrderedPathEdges ((a::xs)++[a]) =
        prescribedOrderedPathEdges (a::pre++[b]) ∪ prescribedOrderedPathEdges (b::post++[a]) ∧
      prescribedDirectedPathEdges ((a::xs)++[a]) =
        prescribedDirectedPathEdges (a::pre++[b]) ∪ prescribedDirectedPathEdges (b::post++[a]) := by
  have hsplit:∀ l:List X,b∈l→∃ pre post:List X,l=pre++b::post:=by
    intro l
    induction l with
    | nil => simp
    | cons x xs ih =>
      intro h
      rcases List.mem_cons.mp h with h|h
      · subst x;exact ⟨[],xs,rfl⟩
      · obtain ⟨pre,post,he⟩:=ih h
        exact ⟨x::pre,post,by simp [he]⟩
  obtain ⟨pre,post,hxsEq⟩:=hsplit xs hb
  subst xs
  have hnparts:=List.nodup_append'.mp hxs
  have hbpre:b∉pre:=by
    intro h;exact (List.disjoint_left.mp hnparts.2.2 h) (by simp)
  have hbpost:b∉post:=(List.nodup_cons.mp hnparts.2.1).1
  have hpost:post.Nodup:=(List.nodup_cons.mp hnparts.2.1).2
  have hapre:a∉pre:=by intro h;exact ha (List.mem_append_left _ h)
  have hab:a≠b:=by intro he;subst a;exact ha (by simp)
  have hapost:a∉post:=by intro h;exact ha (by simp [h])
  have hleft:(a::pre++[b]).Nodup:=by
    simp only [List.cons_append]
    rw [List.nodup_cons]
    constructor
    · simp [hapre,hab]
    · apply List.nodup_append'.mpr
      refine ⟨hnparts.1,by simp,?_⟩
      apply List.disjoint_left.mpr
      intro x hx hy
      simp only [List.mem_singleton] at hy
      subst x;exact hbpre hx
  have hright:(b::post++[a]).Nodup:=by
    simp only [List.cons_append]
    rw [List.nodup_cons]
    constructor
    · simp [hbpost,Ne.symm hab]
    · apply List.nodup_append'.mpr
      refine ⟨hpost,by simp,?_⟩
      apply List.disjoint_left.mpr
      intro x hx hy
      simp only [List.mem_singleton] at hy
      subst x;exact hapost hx
  refine ⟨pre,post,rfl,hleft,hright,?_,?_,?_⟩
  · intro x hx hy
    simp only [List.cons_append,List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hx hy
    rcases hx with hx|hx|hx
    · exact Or.inl hx
    · rcases hy with hy|hy|hy
      · exact Or.inr hy
      · exact ((List.disjoint_left.mp hnparts.2.2 hx) (by simp [hy])).elim
      · exact Or.inl hy
    · exact Or.inr hx
  · simpa [List.cons_append,List.append_assoc] using
      prescribed_path_edges_pivot b (post++[a]) (a::pre)
  · simpa [List.cons_append,List.append_assoc] using
      prescribed_directed_path_edges_pivot b (post++[a]) (a::pre)
end Oberwolfach
