module

public import Oberwolfach.PrescribedFamilyArcUniqueness
public import Oberwolfach.PrescribedPieceSourceArcs
public import Oberwolfach.PrescribedSourceDegree

@[expose] public section
/-! The degree-two hypothesis follows from the ordered path-and-cycle
representation and the physical interpretation of source arcs. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I X:Type} [Fintype I] [Fintype X] [DecidableEq I] [DecidableEq X]

theorem prescribed_source_degree_from_components
    (Q:I→SimpleGraph X) (Dsrc:I→X→X→Prop) (Fsrc:I→SimpleGraph X)
    (ps:List (I×PrescribedSourcePiece X))
    (hpieces:∀ p∈ps,p.2.Valid (Dsrc p.1) (Fsrc p.1))
    (hapart:ps.Pairwise PrescribedPiecesApart)
    (hDQ:∀ i x y,Dsrc i x y→(Q i).Adj x y)
    (hcoverE:∀ i e,e∈(Q i).edgeFinset→∃ p∈ps,p.1=i ∧ e∈p.2.edges)
    (hcoverA:∀ i x y,Dsrc i x y→∃ p∈ps,p.1=i ∧ (x,y)∈p.2.arcs):
    ∀ i x,(Q i).degree x≤2 := by
  have huniq:=prescribed_source_family_unique_directions Dsrc Fsrc ps hpieces hapart hcoverA
  intro i
  apply prescribed_source_degree_from_directions (Q i) (Dsrc i) ?_ (huniq.1 i) (huniq.2 i)
  intro x y
  constructor
  · intro hxy
    have he:s(x,y)∈(Q i).edgeFinset:=SimpleGraph.mem_edgeFinset.mpr hxy
    obtain ⟨p,hp,hpi,hpE⟩:=hcoverE i s(x,y) he
    rw [prescribed_piece_edges_are_arc_images] at hpE
    obtain ⟨e,he,hphys⟩:=Finset.mem_image.mp hpE
    rcases e with ⟨u,v⟩
    have ha:Dsrc i u v:=by
      have hh:=prescribed_piece_arc_source p.2 (Dsrc p.1) (Fsrc p.1) (hpieces p hp) (u,v) he
      simpa [hpi] using hh
    change s(u,v)=s(x,y) at hphys
    rcases Sym2.eq_iff.mp hphys with ⟨hu,hv⟩|⟨hu,hv⟩
    · subst u;subst v;exact Or.inl ha
    · subst u;subst v;exact Or.inr ha
  · intro hxy
    rcases hxy with hxy|hyx
    · exact hDQ i x y hxy
    · exact (hDQ i y x hyx).symm
end Oberwolfach
