module

public import Oberwolfach.PrescribedPieceShape
public import Oberwolfach.PrescribedPathArcUniqueness

@[expose] public section
/-! The arcs of a simple directed path or a directed cycle of length at
least three never contain both orientations of one physical edge. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {X:Type} [DecidableEq X]

theorem prescribed_nodup_path_no_reverse:
    ∀ xs:List X,xs.Nodup→∀ x y,(x,y)∈prescribedDirectedPathEdges xs→(y,x)∉prescribedDirectedPathEdges xs := by
  intro xs
  induction xs with
  | nil => intro hn x y h;simp [prescribedDirectedPathEdges] at h
  | cons a xs ih =>
    cases xs with
    | nil => intro hn x y h;simp [prescribedDirectedPathEdges] at h
    | cons b bs =>
      intro hn x y hxy hyx
      have ha: a∉b::bs:=(List.nodup_cons.mp hn).1
      have hn':(b::bs).Nodup:=(List.nodup_cons.mp hn).2
      simp only [prescribedDirectedPathEdges,Finset.mem_insert,Prod.mk.injEq] at hxy hyx
      rcases hxy with ⟨hxa,hyb⟩|hxy
      · subst x
        subst y
        rcases hyx with ⟨h1,h2⟩|hyx
        · exact ha (by simp [h1])
        · exact ha (prescribed_directed_path_edge_endpoints _ (b,a) hyx).2
      · rcases hyx with ⟨h1,h2⟩|hyx
        · have hx:a∈b::bs:=by simpa [h1] using (prescribed_directed_path_edge_endpoints _ (x,y) hxy).2
          exact ha hx
        · exact ih hn' x y hxy hyx

theorem prescribed_piece_no_reverse (p:PrescribedSourcePiece X) (hp:p.Shape):
    ∀ x y,(x,y)∈p.arcs→(y,x)∉p.arcs := by
  cases p with
  | path xs =>exact prescribed_nodup_path_no_reverse xs hp
  | cycle a xs =>
    cases xs with
    | nil =>have hh:=hp.2;norm_num at hh
    | cons b bs =>
      cases bs with
      | nil =>have hh:=hp.2;norm_num at hh
      | cons c cs =>
        intro x y hxy hyx
        have hn:(a::b::c::cs).Nodup:=hp.1
        have ha:a∉b::c::cs:=(List.nodup_cons.mp hn).1
        have htail:(b::c::cs).Nodup:=(List.nodup_cons.mp hn).2
        have htail':((b::c::cs)++[a]).Nodup:=by
          exact List.Nodup.append htail (by simp) (by simpa [List.disjoint_left] using ha)
        change (x,y)∈insert (a,b) (prescribedDirectedPathEdges ((b::c::cs)++[a])) at hxy
        change (y,x)∈insert (a,b) (prescribedDirectedPathEdges ((b::c::cs)++[a])) at hyx
        simp only [Finset.mem_insert,Prod.mk.injEq] at hxy hyx
        rcases hxy with ⟨hxa,hyb⟩|hxy
        · subst x
          subst y
          rcases hyx with ⟨h1,h2⟩|hyx
          · exact ha (by simp [h1])
          · have hbc:(b,c)∈prescribedDirectedPathEdges ((b::c::cs)++[a]):=by simp [prescribedDirectedPathEdges]
            have huniq:=prescribed_path_unique_successor ((b::c::cs)++[a]) ((List.dropLast_sublist _).nodup htail') b a c hyx hbc
            exact ha (by simp [huniq])
        · rcases hyx with ⟨h1,h2⟩|hyx
          · have hbc:(b,c)∈prescribedDirectedPathEdges ((b::c::cs)++[a]):=by simp [prescribedDirectedPathEdges]
            have hxy':(b,a)∈prescribedDirectedPathEdges ((b::c::cs)++[a]):=by simpa [h1,h2] using hxy
            have huniq:=prescribed_path_unique_successor ((b::c::cs)++[a]) ((List.dropLast_sublist _).nodup htail') b a c hxy' hbc
            exact ha (by simp [huniq])
          · exact prescribed_nodup_path_no_reverse _ htail' x y hxy hyx
end Oberwolfach
