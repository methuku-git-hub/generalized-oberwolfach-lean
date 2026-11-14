module

public import Oberwolfach.MarkedVortexCorrectedRemainderDecomposition
public import Oberwolfach.MarkedCorrectedReserveSupport
public import Oberwolfach.MarkedCorrectionAbsorberOriginal

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]
variable {G:SimpleGraph V} {D m:ℕ} {β ε:ℝ} (Q:Vortex U G D β ε m)
theorem marked_vortex_corrected_fixed_completion
    (π:Equiv.Perm V) (hπ:∀ k x,π x∈Q.extendedVertices k↔x∈Q.extendedVertices k)
    (d c n:ℕ) (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (γ σloss:ℕ→ℝ):
    let P:=fun i=>G.comap (markedVortexVertexEmbedding Q i)
    let ρ:=fun i=>markedVortexPermutation Q π hπ i
    let σi:=fun i=>rawMarkedRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i) σ
    let Hi:=fun i b (v:markedVortexVertexType Q i) (u:markedVortexHubType Q i)=>H b v.val u.val
    let State:=fun i=>MarkedReferenceDeletion (P i) (ρ i) d (σi i)
    let Good:=fun i (T:State i)=>T.Valid (Hi i) c (markedVortexInnerVertices Q i)
      (markedVortexInnerHubs Q i) (γ i) (σloss i)
    let F:=fun i=>markedResourceEmbedding (markedVortexVertexEmbedding Q i).toEmbedding (markedVortexHubEmbedding Q i)
    let B:=fun i (T:State i)=>(T.remaining (Hi i)).image (F i)
    let E₀:=MarkedSampleArc G π (3*d) (fun e=>σ (Sum.inl e)) false
    let K₀:=MarkedSampleArc G π (3*d) (fun e=>σ (Sum.inl e)) true
    let R₀:=fun W:MarkedWheel (fun e:E₀=>e.val.1) (fun e=>e.val.2) (fun e:K₀=>e.val.1) (fun e=>e.val.2)
      c π (3*d) (H false) (H true)=>markedWheelPhysicalResources W
    let S₀:=Finset.univ.filter (fun z:V×U=>H false z.1 z.2∨H true z.1 z.2)
    let Full:=markedFiniteResources (fun e:E₀=>e.val.1) (fun e=>e.val.2)
      (fun e:K₀=>e.val.1) (fun e=>e.val.2) π Finset.univ S₀;
    (∀ i<n,∀ T:State i,Good i T→∃ Tnext:State (i+1),Good (i+1) Tnext ∧
      B (i+1) Tnext⊆B i T ∧ HasResourceDecomposition R₀ (B i T\B (i+1) Tnext))→
    ∀ (T₀:State 0),Good 0 T₀→∀ (D₀:MarkedReferenceDeletion G π d σ) (Reserve:Finset (Finset V⊕(V×U))),
    B 0 T₀=D₀.remaining H\Reserve→
    D₀.removed.filter (markedInnerResource (Q.extendedVertices 1) (Q.extendedIndices 1))=∅→
    1≤n→
    MarkedFixedTerminalAbsorber G π d c
      (rawMarkedDeleteRims σ (markedSampleArcSetGraph G π d σ D₀.arcs).edgeFinset)
      (markedDeletePhysicalSpokes H (markedFiniteSpokeGraph D₀.spokes)) Reserve
      (Q.extendedVertices n) (Q.extendedIndices n)→
    HasResourceDecomposition R₀ (D₀.remaining H):=by
  intro P ρ σi Hi State Good F B E₀ K₀ R₀ S₀ Full hstep T₀ hT₀ D₀ Reserve hremain hprotected hn habs
  have hsub:=marked_corrected_reserve_subset_remaining G π d c σ H D₀ Reserve
    (Q.extendedVertices n) (Q.extendedIndices n) habs
  have horiginal:=marked_correction_absorber_fixed_original G π d c σ H D₀ Reserve
    (Q.extendedVertices 1) (Q.extendedVertices n) (Q.extendedIndices 1) (Q.extendedIndices n)
    (hπ 1) (Q.extendedVertices_subset hn) (Q.extendedIndices_subset hn) hprotected habs
  exact marked_vortex_corrected_remainder_decomposition Q π hπ d c n σ H γ σloss
    hstep T₀ hT₀ D₀ Reserve hremain hsub horiginal
end Oberwolfach
