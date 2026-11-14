module

public import Oberwolfach.PrescribedPathDirectedEdges

@[expose] public section
/-! In a list whose possible arc tails (respectively heads) are distinct,
each vertex has at most one outgoing (respectively incoming) listed arc. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {X:Type} [DecidableEq X]

theorem prescribed_path_arc_tail_position:
    ∀ (xs:List X) (x y:X),(x,y)∈prescribedDirectedPathEdges xs→x∈xs.dropLast := by
  intro xs
  induction xs with
  | nil => intro x y h;simp [prescribedDirectedPathEdges] at h
  | cons a xs ih =>
    cases xs with
    | nil => intro x y h;simp [prescribedDirectedPathEdges] at h
    | cons b bs =>
      intro x y h
      simp only [prescribedDirectedPathEdges,Finset.mem_insert,Prod.mk.injEq] at h
      simp only [List.dropLast_cons_cons, List.mem_cons]
      rcases h with ⟨rfl,rfl⟩|h
      · exact Or.inl rfl
      · exact Or.inr (ih x y h)

theorem prescribed_path_arc_head_position:
    ∀ (xs:List X) (x y:X),(x,y)∈prescribedDirectedPathEdges xs→y∈xs.tail := by
  intro xs
  induction xs with
  | nil => intro x y h;simp [prescribedDirectedPathEdges] at h
  | cons a xs ih =>
    cases xs with
    | nil => intro x y h;simp [prescribedDirectedPathEdges] at h
    | cons b bs =>
      intro x y h
      simp only [prescribedDirectedPathEdges,Finset.mem_insert,Prod.mk.injEq] at h
      simp only [List.tail_cons,List.mem_cons]
      rcases h with ⟨rfl,rfl⟩|h
      · exact Or.inl rfl
      · exact Or.inr (ih x y h)

theorem prescribed_path_unique_successor:
    ∀ (xs:List X),xs.dropLast.Nodup→∀ x y z,
      (x,y)∈prescribedDirectedPathEdges xs→(x,z)∈prescribedDirectedPathEdges xs→y=z := by
  intro xs
  induction xs with
  | nil => intro _ x y z h;simp [prescribedDirectedPathEdges] at h
  | cons a xs ih =>
    cases xs with
    | nil => intro _ x y z h;simp [prescribedDirectedPathEdges] at h
    | cons b bs =>
      intro hn x y z h1 h2
      simp only [List.dropLast_cons_cons,List.nodup_cons] at hn
      simp only [prescribedDirectedPathEdges,Finset.mem_insert,Prod.mk.injEq] at h1 h2
      rcases h1 with h1|h1
      · rcases h1 with ⟨hx,hy⟩
        subst x
        subst y
        rcases h2 with h2|h2
        · exact h2.2.symm
        · exact (hn.1 (prescribed_path_arc_tail_position _ _ _ h2)).elim
      · rcases h2 with h2|h2
        · rcases h2 with ⟨hx,hz⟩
          subst x
          subst z
          exact (hn.1 (prescribed_path_arc_tail_position _ _ _ h1)).elim
        · exact ih hn.2 x y z h1 h2

theorem prescribed_path_unique_predecessor:
    ∀ (xs:List X),xs.tail.Nodup→∀ x y z,
      (y,x)∈prescribedDirectedPathEdges xs→(z,x)∈prescribedDirectedPathEdges xs→y=z := by
  intro xs
  induction xs with
  | nil => intro _ x y z h;simp [prescribedDirectedPathEdges] at h
  | cons a xs ih =>
    cases xs with
    | nil => intro _ x y z h;simp [prescribedDirectedPathEdges] at h
    | cons b bs =>
      intro hn x y z h1 h2
      simp only [List.tail_cons,List.nodup_cons] at hn
      simp only [prescribedDirectedPathEdges,Finset.mem_insert,Prod.mk.injEq] at h1 h2
      rcases h1 with h1|h1
      · rcases h1 with ⟨hy,hx⟩
        subst y
        subst x
        rcases h2 with h2|h2
        · exact h2.1.symm
        · exact (hn.1 (prescribed_path_arc_head_position _ _ _ h2)).elim
      · rcases h2 with h2|h2
        · rcases h2 with ⟨hz,hx⟩
          subst z
          subst x
          exact (hn.1 (prescribed_path_arc_head_position _ _ _ h1)).elim
        · exact ih hn.2 x y z h1 h2
end Oberwolfach
