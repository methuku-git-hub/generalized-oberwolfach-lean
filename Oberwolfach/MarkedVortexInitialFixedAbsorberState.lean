module

public import Oberwolfach.MarkedVortexInitialValidState
public import Oberwolfach.MarkedFixedTerminalAbsorberOriginal
public import Oberwolfach.MarkedReferenceAbsorberDeletion

@[expose] public section
/-! Construct the initial physical remainder from the actual fixed
terminal absorber and transport it to the initial fixed vortex level. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]
variable {G:SimpleGraph V} {D m:ℕ} {β ε:ℝ} (Q:Vortex U G D β ε m)

theorem marked_vortex_initial_fixed_absorber_state
    (π:Equiv.Perm V) (hπ:∀ k x,π x∈Q.extendedVertices k↔x∈Q.extendedVertices k)
    (d c:ℕ) (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (Reserve:Finset (Finset V⊕(V×U))) (Xterm:Finset V) (Zterm:Finset U) (γ σloss:ℝ)
    (habs:MarkedFixedTerminalAbsorber G π d c σ H Reserve Xterm Zterm)
    (hH:∀ v u,¬(H false v u∧H true v u)):
    let E:=MarkedSampleArc G π (3*d) (fun e=>σ (Sum.inl e)) false
    let K:=MarkedSampleArc G π (3*d) (fun e=>σ (Sum.inl e)) true
    let S:=Finset.univ.filter (fun z:V×U=>H false z.1 z.2∨H true z.1 z.2)
    let Full:=markedFiniteResources (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) π Finset.univ S;
    MarkedRemainderDivisible (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) (H true) Finset.univ S c→
    Reserve.filter (markedInnerResource (Q.extendedVertices 1) (Q.extendedIndices 1))=∅→
    (Reserve.card:ℝ)≤γ→(Reserve.card:ℝ)≤σloss→
    ∃ D₀:MarkedReferenceDeletion G π d σ,
      D₀.Valid H c (Q.extendedVertices 1) (Q.extendedIndices 1) γ σloss ∧ D₀.removed=Reserve ∧
    ∃ T:MarkedReferenceDeletion (G.comap (markedVortexVertexEmbedding Q 0))
      (markedVortexPermutation Q π hπ 0) d
      (rawMarkedRestrictPair (markedVortexVertexEmbedding Q 0) (markedVortexHubEmbedding Q 0) σ),
      T.Valid (fun b x u=>H b x.val u.val) c (markedVortexInnerVertices Q 0)
        (markedVortexInnerHubs Q 0) γ σloss ∧
      T.removed.image (markedResourceEmbedding (markedVortexVertexEmbedding Q 0).toEmbedding
        (markedVortexHubEmbedding Q 0))=Reserve ∧
      (T.remaining (fun b x u=>H b x.val u.val)).image
        (markedResourceEmbedding (markedVortexVertexEmbedding Q 0).toEmbedding (markedVortexHubEmbedding Q 0))=
      Full\Reserve:=by
  intro E K S Full hdiv hEmpty hγ hσ
  have hdec:HasResourceDecomposition
      (fun W:MarkedWheel (fun e:E=>e.val.1) (fun e=>e.val.2) (fun e:K=>e.val.1) (fun e=>e.val.2)
        c π (3*d) (H false) (H true)=>markedWheelPhysicalResources W) Reserve:=
    (marked_fixed_terminal_absorber_supported_in_host G π d c σ H Reserve Xterm Zterm habs).1
  obtain ⟨D₀,hValid,hRemoved,hRemain⟩:=marked_reference_absorber_deletion G π d c σ H
    (Q.extendedVertices 1) (Q.extendedIndices 1) γ σloss hH hdiv Reserve hdec hEmpty hγ hσ
  obtain ⟨T,hTvalid,hTremoved,hTremain⟩:=
    marked_vortex_initial_valid_state Q π hπ d c σ H γ σloss D₀ hValid
  exact ⟨D₀,hValid,hRemoved,T,hTvalid,hTremoved.trans hRemoved,hTremain.trans hRemain⟩
end Oberwolfach
