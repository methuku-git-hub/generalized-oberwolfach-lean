module

public import Oberwolfach.PrescribedSourcePieces

@[expose] public section
/-! Ordered paths and cycles with distinct vertices have no loops. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {X:Type} [DecidableEq X]

def PrescribedSourcePiece.Shape (p:PrescribedSourcePiece X):Prop:=
  match p with
  | .path xs=>xs.Nodup
  | .cycle a xs=>(a::xs).Nodup ∧ 3≤(a::xs).length

theorem prescribed_path_no_loops:
    ∀ xs:List X,xs.Nodup→∀ x,(x,x)∉prescribedDirectedPathEdges xs := by
  intro xs
  induction xs with
  | nil => intro hn x;simp [prescribedDirectedPathEdges]
  | cons a xs ih =>
    cases xs with
    | nil => intro hn x;simp [prescribedDirectedPathEdges]
    | cons b bs =>
      intro hn x he
      have hh:=List.nodup_cons.mp hn
      simp only [prescribedDirectedPathEdges,Finset.mem_insert,Prod.mk.injEq] at he
      rcases he with ⟨ha,hb⟩|he
      · have hab:a=b:=ha.symm.trans hb
        exact hh.1 (by simp [hab])
      · exact ih hh.2 x he

theorem prescribed_path_append_fresh_no_loops (a:X):
    ∀ xs:List X,xs.Nodup→a∉xs→∀ x,(x,x)∉prescribedDirectedPathEdges (xs++[a]) := by
  intro xs
  induction xs with
  | nil => intro hn ha x;simp [prescribedDirectedPathEdges]
  | cons b xs ih =>
    intro hn ha x he
    have hb:=List.nodup_cons.mp hn
    have ha':a∉xs:=by intro h;exact ha (by simp [h])
    cases xs with
    | nil =>
      change (x,x)∈prescribedDirectedPathEdges [b,a] at he
      simp only [prescribedDirectedPathEdges,Finset.mem_insert,Finset.notMem_empty,or_false,Prod.mk.injEq] at he
      rcases he with ⟨h1,h2⟩
      have hab:b=a:=h1.symm.trans h2
      exact ha (by simp [hab])
    | cons c cs =>
      simp only [List.cons_append,prescribedDirectedPathEdges,Finset.mem_insert,Prod.mk.injEq] at he
      rcases he with ⟨h1,h2⟩|he
      · have hbc:b=c:=h1.symm.trans h2
        exact hb.1 (by simp [hbc])
      · exact ih hb.2 ha' x he

theorem prescribed_piece_no_loops (p:PrescribedSourcePiece X) (hp:p.Shape):
    ∀ x,(x,x)∉p.arcs := by
  cases p with
  | path xs =>exact prescribed_path_no_loops xs hp
  | cycle a xs =>
    intro x he
    have hanodup:=(List.nodup_cons.mp hp.1)
    cases xs with
    | nil => have hlen:=hp.2;norm_num at hlen
    | cons b bs =>
      simp only [PrescribedSourcePiece.arcs,List.cons_append,prescribedDirectedPathEdges,Finset.mem_insert,Prod.mk.injEq] at he
      rcases he with ⟨h1,h2⟩|he
      · have hab:a=b:=h1.symm.trans h2
        exact hanodup.1 (by simp [hab])
      · exact prescribed_path_append_fresh_no_loops a (b::bs) hanodup.2 hanodup.1 x he
end Oberwolfach
