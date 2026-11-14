module

public import Oberwolfach.PrescribedSourceFamilyInduction
public import Oberwolfach.PrescribedPieceArcUniqueness

@[expose] public section
/-! A vertex belongs to at most one source piece of each factor, so the
factor's represented source digraph has at most one predecessor and one
successor at every vertex. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I X:Type} [DecidableEq I] [DecidableEq X]

theorem prescribed_pairwise_rel_or_eq {A:Type} (R:A→A→Prop) (hsym:∀ a b,R a b→R b a):
    ∀ l:List A,l.Pairwise R→∀ a∈l,∀ b∈l,a=b ∨ R a b := by
  intro l
  induction l with
  | nil => intro h a ha;simp at ha
  | cons x xs ih =>
    intro h a ha b hb
    have hh:=List.pairwise_cons.mp h
    rcases List.mem_cons.mp ha with ha|ha
    · subst a
      rcases List.mem_cons.mp hb with hb|hb
      · subst b;exact Or.inl rfl
      · exact Or.inr (hh.1 b hb)
    · rcases List.mem_cons.mp hb with hb|hb
      · subst b;exact Or.inr (hsym x a (hh.1 a ha))
      · exact ih hh.2 a ha b hb

theorem prescribed_pieces_apart_symmetric (p q:I×PrescribedSourcePiece X):
    PrescribedPiecesApart p q→PrescribedPiecesApart q p := by
  intro h
  rcases h with h|h
  · exact Or.inl h.symm
  · exact Or.inr h.symm

theorem prescribed_source_family_unique_directions
    (Dsrc:I→X→X→Prop) (Fsrc:I→SimpleGraph X) (ps:List (I×PrescribedSourcePiece X))
    (hpieces:∀ p∈ps,p.2.Valid (Dsrc p.1) (Fsrc p.1)) (hapart:ps.Pairwise PrescribedPiecesApart)
    (hcoverA:∀ i x y,Dsrc i x y→∃ p∈ps,p.1=i ∧ (x,y)∈p.2.arcs):
    (∀ i x y z,Dsrc i x y→Dsrc i x z→y=z) ∧
    (∀ i x y z,Dsrc i y x→Dsrc i z x→y=z) := by
  constructor
  · intro i x y z hy hz
    obtain ⟨p,hp,hpi,hpy⟩:=hcoverA i x y hy
    obtain ⟨q,hq,hqi,hqz⟩:=hcoverA i x z hz
    have heq:p=q:=by
      rcases prescribed_pairwise_rel_or_eq PrescribedPiecesApart prescribed_pieces_apart_symmetric ps hapart p hp q hq with heq|hdis
      · exact heq
      · rcases hdis with hne|hdis
        · exact (hne (hpi.trans hqi.symm)).elim
        · have hpx: x∈p.2.vertices:=(prescribed_source_piece_arc_endpoints p.2 (x,y) hpy).1
          have hqx: x∈q.2.vertices:=(prescribed_source_piece_arc_endpoints q.2 (x,z) hqz).1
          exact ((Finset.disjoint_left.mp hdis (List.mem_toFinset.mpr hpx)) (List.mem_toFinset.mpr hqx)).elim
    subst q
    exact prescribed_piece_unique_successor p.2 (Dsrc p.1) (Fsrc p.1) (hpieces p hp) x y z hpy hqz
  · intro i x y z hy hz
    obtain ⟨p,hp,hpi,hpy⟩:=hcoverA i y x hy
    obtain ⟨q,hq,hqi,hqz⟩:=hcoverA i z x hz
    have heq:p=q:=by
      rcases prescribed_pairwise_rel_or_eq PrescribedPiecesApart prescribed_pieces_apart_symmetric ps hapart p hp q hq with heq|hdis
      · exact heq
      · rcases hdis with hne|hdis
        · exact (hne (hpi.trans hqi.symm)).elim
        · have hpx: x∈p.2.vertices:=(prescribed_source_piece_arc_endpoints p.2 (y,x) hpy).2
          have hqx: x∈q.2.vertices:=(prescribed_source_piece_arc_endpoints q.2 (z,x) hqz).2
          exact ((Finset.disjoint_left.mp hdis (List.mem_toFinset.mpr hpx)) (List.mem_toFinset.mpr hqx)).elim
    subst q
    exact prescribed_piece_unique_predecessor p.2 (Dsrc p.1) (Fsrc p.1) (hpieces p hp) x y z hpy hqz
end Oberwolfach
