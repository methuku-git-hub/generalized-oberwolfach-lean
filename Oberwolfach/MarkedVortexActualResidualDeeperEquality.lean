module

public import Oberwolfach.RetainedMarkedRootUniformity
public import Oberwolfach.MarkedVortexProtectedDeeperEquality
public import Oberwolfach.RetainedMarkedSpokeGeometry
public import Oberwolfach.MarkedIntervalRootCardinality

@[expose] public section
/-! First-inner equality for the factor residual identifies every deeper
vortex restriction with the original retained sample. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]

theorem marked_vortex_actual_residual_deeper_equality
    {G:SimpleGraph V} {D m:ℕ} {β ε:ℝ} (Q:Vortex U G D β ε m)
    (π:Equiv.Perm V) (d:ℕ) (ρ:RawIntervalFamilyOutcome V U Bool Bool)
    (t:ℕ) (Jret:StartRetentionOutcome (rawStartHubSet π d ρ false) t)
    (σ τ:RawMarkedOutcome V U Bool Bool) (R:U→Finset V)
    (hrim:∀e:Sym2 V,e.toFinset⊆Q.extendedVertices 1→σ (Sum.inl e)=τ (Sum.inl e))
    (hinterval:∀e,σ (Sum.inr e)=τ (Sum.inr e))
    (hspoke:∀u∈Q.extendedIndices 1,∀v∈Q.extendedVertices 1,
      (v∈R u\markedIntervalRootSet π (fun _:retainedMarkedIndex π d ρ false t Jret u=>d) Subtype.val ↔
        retainedRawMarkedSpokes π d ρ false t Jret false false false v u)):
    let H:=retainedRawMarkedSpokes π d ρ false t Jret false false
    let H':Bool→V→U→Prop:=fun b v u=>if b then retainedRawMarkedSpokes π d ρ false t Jret false false true v u
      else v∈R u\markedIntervalRootSet π (fun _:retainedMarkedIndex π d ρ false t Jret u=>d) Subtype.val;
    ∀ (i:ℕ), 1 ≤ i →
      rawMarkedRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i) σ=
      rawMarkedRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i) τ ∧
      (fun b v u=>H b (markedVortexVertexEmbedding Q i v) (markedVortexHubEmbedding Q i u))=
      (fun b v u=>H' b (markedVortexVertexEmbedding Q i v) (markedVortexHubEmbedding Q i u)):=by
  intro H H'
  apply marked_vortex_protected_deeper_equality Q σ τ H H' hrim hinterval
  intro b v u hv hu
  cases b with
  | false => simpa only [H,H',Bool.false_eq_true,if_false] using (hspoke u hu v hv).symm
  | true => simp only [H,H',if_true]
end Oberwolfach
