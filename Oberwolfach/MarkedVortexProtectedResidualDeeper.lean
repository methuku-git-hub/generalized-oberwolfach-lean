module

public import Oberwolfach.MarkedVortexProtectedDeeperEquality
public import Oberwolfach.InnerResidualSpokeExactAgreement

@[expose] public section
/-! Set-level protection of the corrected ordinary spokes gives exact equality
of both the sample and spoke relations at every deeper vortex level. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_vortex_protected_residual_deeper
    {G:SimpleGraph V} {D m:ℕ} {β ε:ℝ} (Q:Vortex U G D β ε m)
    (σ τ:RawMarkedOutcome V U Γ Color) (Y Old New End Outer R:U→Finset V)
    (Marked:V→U→Prop)
    (hrim:∀e:Sym2 V,e.toFinset⊆Q.extendedVertices 1→σ (Sum.inl e)=τ (Sum.inl e))
    (hinterval:∀e,σ (Sum.inr e)=τ (Sum.inr e))
    (hR:∀u,R u=Finset.univ\(Old u∪New u∪End u))
    (hOuterY:∀u,Disjoint (Outer u) (Y u))
    (hOuterOld:∀u,Disjoint (Outer u) (Old u))
    (hOuterEnd:∀u,Disjoint (Outer u) (End u))
    (hOuterNew:∀u∈Q.extendedIndices 1,∀v∈Q.extendedVertices 1,v∈Outer u→v∉New u)
    (hcover:∀u∈Q.extendedIndices 1,∀v∈Q.extendedVertices 1,v∉Outer u→v∉Y u→v∉Old u→v∈New u):
    let H:Bool→V→U→Prop:=fun b v u=>if b then Marked v u else v∈Outer u
    let H':Bool→V→U→Prop:=fun b v u=>if b then Marked v u else v∈R u\Y u;
    ∀ (i:ℕ), 1 ≤ i →
      rawMarkedRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i) σ=
      rawMarkedRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i) τ ∧
      (fun b v u=>H b (markedVortexVertexEmbedding Q i v) (markedVortexHubEmbedding Q i u))=
      (fun b v u=>H' b (markedVortexVertexEmbedding Q i v) (markedVortexHubEmbedding Q i u)):=by
  intro H H'
  have hagree:=inner_residual_spoke_exact_agreement (Q.extendedVertices 1) (Q.extendedIndices 1)
    Y Old New End Outer R hR hOuterY hOuterOld hOuterEnd hOuterNew hcover
  apply marked_vortex_protected_deeper_equality Q σ τ H H' hrim hinterval
  intro b v u hv hu
  cases b with
  | false => simpa only [H,H',Bool.false_eq_true,if_false] using (hagree u hu v hv).symm
  | true => simp only [H,H',if_true]
end Oberwolfach
