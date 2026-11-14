module

public import Oberwolfach.MarkedSelectFixedTerminalAbsorber
public import Oberwolfach.MarkedReferenceAbsorberDeletion
public import Oberwolfach.MarkedVortexInitialValidState

@[expose] public section
/-! Select the terminal reservoir in the corrected sample, then remove it
from the initial level while retaining the exact ambient remainder. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]
variable {G:SimpleGraph V} {D m:ℕ} {β ε:ℝ} (Q:Vortex U G D β ε m)

theorem marked_vortex_corrected_reserve_initial_state
    (π:Equiv.Perm V) (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (d r size a₀ b₀ e₀ f L:ℕ) (εabs gammaLoss sigmaLoss:ℝ)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (htypes:∀v u,¬(H false v u∧H true v u)):
    let E:=MarkedSampleArc G π (3*d) (fun e=>σ (Sum.inl e)) false
    let K:=MarkedSampleArc G π (3*d) (fun e=>σ (Sum.inl e)) true
    let S:=Finset.univ.filter (fun z:V×U=>H false z.1 z.2∨H true z.1 z.2)
    let Full:=markedFiniteResources (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) π Finset.univ S;
    MarkedRemainderDivisible (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) (H true) Finset.univ S (r+4)→
    MarkedReservedTerminalAbsorberProperty (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) (H false) (H true) π (3*d) r size a₀ b₀ e₀ f εabs→
    (Q.extendedVertices (L+1)).card+(Q.extendedIndices (L+1)).card≤size→
    ((Q.extendedVertices 1).card:ℝ)≤εabs*Fintype.card V+f→
    ((Q.extendedIndices 1).card:ℝ)≤εabs*Fintype.card V+f→
    (e₀:ℝ)≤gammaLoss→(e₀:ℝ)≤sigmaLoss→
    ∃ C:MarkedSupportedEdgeSet (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) π U,
      C.edges.card≤e₀ ∧ C.rows.card≤a₀ ∧ C.hubs.card≤b₀ ∧
      C.edges.filter (markedInnerResource (Q.extendedVertices 1) (Q.extendedIndices 1))=∅ ∧
      MarkedFixedTerminalAbsorber G π d (r+4) σ H C.edges
        (Q.extendedVertices (L+1)) (Q.extendedIndices (L+1)) ∧
    ∃ T:MarkedReferenceDeletion (G.comap (markedVortexVertexEmbedding Q 0))
      (markedVortexPermutation Q π hπ 0) d
      (rawMarkedRestrictPair (markedVortexVertexEmbedding Q 0) (markedVortexHubEmbedding Q 0) σ),
      T.Valid (fun b x u=>H b x.val u.val) (r+4) (markedVortexInnerVertices Q 0)
        (markedVortexInnerHubs Q 0) gammaLoss sigmaLoss ∧
      (T.remaining (fun b x u=>H b x.val u.val)).image
        (markedResourceEmbedding (markedVortexVertexEmbedding Q 0).toEmbedding
          (markedVortexHubEmbedding Q 0))=Full\C.edges :=by
  intro E K S Full hdiv hprop hsize hV hU hγ hσ
  obtain ⟨C,hdis,hCe,hCr,hCh,havoid,hfixed⟩:=marked_select_fixed_terminal_absorber
    G π d r size a₀ b₀ e₀ f εabs σ H hprop
    (Q.extendedVertices (L+1)) (Q.extendedVertices 1) (Q.extendedVertices 1)
    (Q.extendedIndices (L+1)) (Q.extendedIndices 1) (Q.extendedIndices 1)
    hsize (Q.extendedVertices_subset (by omega)) (Q.extendedIndices_subset (by omega))
    (Finset.Subset.refl _) (Finset.Subset.refl _) (hπ 1) hV hU ∅ (by simp)
  have hdec:= (marked_fixed_terminal_absorber_supported_in_host G π d (r+4) σ H C.edges
    (Q.extendedVertices (L+1)) (Q.extendedIndices (L+1)) hfixed).1
  have hcg:(C.edges.card:ℝ)≤gammaLoss:=(Nat.cast_le.mpr hCe).trans hγ
  have hcs:(C.edges.card:ℝ)≤sigmaLoss:=(Nat.cast_le.mpr hCe).trans hσ
  obtain ⟨D₀,hvalid,hremoved,hremain⟩:=marked_reference_absorber_deletion G π d (r+4) σ H
    (Q.extendedVertices 1) (Q.extendedIndices 1) gammaLoss sigmaLoss htypes hdiv C.edges hdec havoid hcg hcs
  obtain ⟨T,hT,_,hTr⟩:=marked_vortex_initial_valid_state Q π hπ d (r+4) σ H gammaLoss sigmaLoss D₀ hvalid
  exact ⟨C,hCe,hCr,hCh,havoid,hfixed,T,hT,hTr.trans hremain⟩
end Oberwolfach
