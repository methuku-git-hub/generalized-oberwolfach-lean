module

public import Oberwolfach.PrescribedPositionOriginalBounds
public import Oberwolfach.PrescribedPositionSelectionNodup

@[expose] public section
/-! Apply the source-position selection with the original numerical bounds. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {X:Type} [Fintype X] [DecidableEq X]

theorem prescribed_outside_closed_neighbourhood (Q:SimpleGraph X) (A:Finset X) (v:X)
    (h:v∉prescribedClosedNeighbourhoods Q A):
    v∉A ∧ ∀ a∈A,¬Q.Adj a v := by
  constructor
  · intro hv
    apply h
    exact Finset.mem_biUnion.mpr ⟨v,hv,by simp [prescribedClosedNeighbourhood]⟩
  · intro a ha hav
    apply h
    apply Finset.mem_biUnion.mpr
    refine ⟨a,ha,?_⟩
    simp [prescribedClosedNeighbourhood,hav]

theorem prescribed_position_selection_original (Q:SimpleGraph X) (D:X→X→Prop)
    (hdeg:∀ x,Q.degree x≤2) (hrep:∀x y,Q.Adj x y→D x y ∨ D y x)
    (A:Finset X) (m z:ℕ) (hedges:Fintype.card X≤Q.edgeFinset.card+A.card)
    (hsize:8*A.card+8*m+4*z+10≤Fintype.card X):
    ∃ (es:List (X×X)) (vs:List X),es.length=m ∧ vs.length=z ∧
      (∀ e∈es,D e.1 e.2 ∧ Q.Adj e.1 e.2 ∧
        e.1∉prescribedClosedNeighbourhoods Q A ∧ e.2∉prescribedClosedNeighbourhoods Q A) ∧
      es.Pairwise (prescribedPairsApart Q) ∧
      (∀ v∈vs,v∉prescribedClosedNeighbourhoods Q A) ∧
      (∀ e∈es,∀ v∈vs,v∉prescribedPairClosed Q e) ∧
      vs.Pairwise (prescribedSinglesApart Q) ∧
      (es.flatMap prescribedPairVertices++vs).Nodup := by
  have hb:=prescribed_position_original_budgets Q hdeg A m z hedges hsize
  obtain ⟨es,vs,helen,hvlen,he,hpair,hv,hcross,hvs⟩:=
    prescribed_position_greedy_selection Q D hdeg hrep (prescribedClosedNeighbourhoods Q A) m z hb.1 hb.2
  refine ⟨es,vs,helen,hvlen,he,hpair,hv,hcross,hvs,?_⟩
  exact prescribed_selected_vertices_nodup Q es vs (fun e he' => (he e he').2.1) hpair hvs hcross
end Oberwolfach
