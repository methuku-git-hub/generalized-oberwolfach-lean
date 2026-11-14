module

public import Oberwolfach.MarkedVortexFirstActiveExactRims
public import Oberwolfach.MarkedVortexProtectedDeeperEquality

@[expose] public section
/-! The single protected first-inner correction supplies both the exact
first-active rims and every deeper raw/spoke restriction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_vortex_protected_complete_agreement
    {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [LinearOrder V] [Nonempty V] [DecidableEq U]
    (G:SimpleGraph V) (D m:ℕ) (β ε:ℝ) (Q:Vortex U G D β ε m)
    (π:Equiv.Perm V) (hπ:∀i v,π v∈Q.extendedVertices i↔v∈Q.extendedVertices i)
    (d:ℕ) (σ τ:RawMarkedOutcome V U Γ Color) (H:Bool → V → U → Prop) (Hordinary:V → U → Prop)
    (hrim:∀e:Sym2 V,e.toFinset⊆Q.extendedVertices 1 → τ (Sum.inl e)=σ (Sum.inl e))
    (hinterval:∀e,σ (Sum.inr e)=τ (Sum.inr e))
    (hspoke:∀v u,v∈Q.extendedVertices 1 → u∈Q.extendedIndices 1 → (H false v u↔Hordinary v u)):
    let H':=fun b v u=>if b then H true v u else Hordinary v u
    let f:=markedVortexActiveVertexEmbedding Q 1
    let g:=markedVortexNonDeeperHubToPhysical Q 0
    let ρ:=markedVortexActivePermutation Q π hπ 1;
    rawMarkedPairRims (G.comap f) ρ d (rawMarkedRestrictPair f g τ)=
      rawMarkedPairRims (G.comap f) ρ d (rawMarkedRestrictPair f g σ) ∧
    ∀i:ℕ,1 ≤ i → 
      rawMarkedRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i) σ=
      rawMarkedRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i) τ ∧
      (fun b v u=>H b (markedVortexVertexEmbedding Q i v) (markedVortexHubEmbedding Q i u))=
      (fun b v u=>H' b (markedVortexVertexEmbedding Q i v) (markedVortexHubEmbedding Q i u)) :=by
  intro H' f g ρ
  refine ⟨marked_vortex_first_active_exact_rims G D m β ε Q π hπ d σ τ hrim,?_⟩
  apply marked_vortex_protected_deeper_equality Q σ τ H H'
  · intro e he;exact (hrim e he).symm
  · exact hinterval
  · intro b v u hv hu
    cases b with
    | false => simpa only [H',Bool.false_eq_true,ite_false] using hspoke v u hv hu
    | true => simp only [H',ite_true]
end Oberwolfach
