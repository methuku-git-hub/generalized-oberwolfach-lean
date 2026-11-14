module

public import Oberwolfach.MarkedVortexRestrictionChain
public import Oberwolfach.MarkedReferencePackingRemaining

@[expose] public section
/-! The actual cover-down packing removes exactly its physical resources,
also after lifting the state and the remainder to the original host. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]
variable {G:SimpleGraph V} {D m:ℕ} {β ε:ℝ} (Q:Vortex U G D β ε m)

theorem marked_vortex_step_physical_conservation (i:ℕ)
    (π:Equiv.Perm V) (hπ:∀ k x,π x∈Q.extendedVertices k↔x∈Q.extendedVertices k)
    (d c:ℕ) (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop):
    let P:=G.comap (markedVortexVertexEmbedding Q i)
    let ρ:=markedVortexPermutation Q π hπ i
    let σi:=rawMarkedRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i) σ
    let Hi:=fun b (v:markedVortexVertexType Q i) (u:markedVortexHubType Q i)=>H b v.val u.val
    let E:=MarkedSampleArc P ρ (3*d) (fun e=>σi (Sum.inl e)) false
    let K:=MarkedSampleArc P ρ (3*d) (fun e=>σi (Sum.inl e)) true
    let S:=Finset.univ.filter (fun z:markedVortexVertexType Q i×markedVortexHubType Q i=>Hi false z.1 z.2∨Hi true z.1 z.2)
    let F:=markedResourceEmbedding (markedVortexVertexEmbedding Q i).toEmbedding (markedVortexHubEmbedding Q i);
    ∀ (T:MarkedReferenceDeletion P ρ d σi)
      (M:Finset (MarkedWheel (fun e:E=>e.val.1) (fun e=>e.val.2) (fun e:K=>e.val.1) (fun e=>e.val.2)
        c ρ (3*d) (Hi false) (Hi true))),
    (∀ Y∈M,∀ Z∈M,Y≠Z→Disjoint (markedWheelPhysicalResources Y) (markedWheelPhysicalResources Z))→
    M.biUnion markedWheelArcs⊆Finset.univ\T.arcs→M.biUnion markedWheelSpokePairs⊆S\T.spokes→
    let L:=markedFiniteResources (fun e:E=>e.val.1) (fun e=>e.val.2) (fun e:K=>e.val.1) (fun e=>e.val.2) ρ
      (Finset.univ\(T.arcs∪M.biUnion markedWheelArcs)) (S\(T.spokes∪M.biUnion markedWheelSpokePairs))
    let E₀:=MarkedSampleArc G π (3*d) (fun e=>σ (Sum.inl e)) false
    let K₀:=MarkedSampleArc G π (3*d) (fun e=>σ (Sum.inl e)) true;
    L.image F⊆(T.remaining Hi).image F ∧
    L=T.remaining Hi\M.biUnion markedWheelPhysicalResources ∧
    (M.biUnion markedWheelPhysicalResources).image F=(T.remaining Hi).image F\L.image F ∧
    HasResourceDecomposition
      (fun W:MarkedWheel (fun e:E₀=>e.val.1) (fun e=>e.val.2) (fun e:K₀=>e.val.1) (fun e=>e.val.2)
        c π (3*d) (H false) (H true)=>markedWheelPhysicalResources W)
      ((T.remaining Hi).image F\L.image F):=by
  intro P ρ σi Hi E K S F T M hM hA hS L E₀ K₀
  have hdec:(fun (a b:markedVortexVertexType Q i)=>Classical.propDecidable (a=b))=
      (inferInstance:DecidableEq (markedVortexVertexType Q i)):=by
    apply Subsingleton.elim
  change (fun (a b:markedVortexVertexType Q i)=>Classical.propDecidable (a=b)) =
    (fun (a b:markedVortexVertexType Q i)=>Subtype.instDecidableEq a b) at hdec
  have hM':=hM
  have hA':=hA
  have hS':=hS
  try rw [←hdec] at hM'
  try rw [←hdec] at hA'
  try rw [←hdec] at hS'
  have hstep:=marked_reference_state_step_decomposition P ρ d c σi Hi T M hM' hA' hS'
  rw [hdec] at hstep
  have hres:=marked_reference_packing_resources_subset_remaining P ρ d c σi Hi T M hA' hS'
  rw [hdec] at hres
  have hL:L=T.remaining Hi\M.biUnion markedWheelPhysicalResources:=hstep.1
  have hcovered:T.remaining Hi\L=M.biUnion markedWheelPhysicalResources:=by
    rw [hL]
    ext z
    have hh:=fun hz=>hres (x:=z) hz
    simp only [Finset.mem_sdiff]
    tauto
  have hlocal:=hstep.2.2
  have hambient:=marked_vortex_ambient_decomposition_lift Q i π hπ d c σ H (T.remaining Hi\L) hlocal
  refine ⟨Finset.image_subset_image hstep.2.1,?_,?_,?_⟩
  · exact hL
  · rw [←hcovered,Finset.image_sdiff _ _ F.injective]
  · rw [←Finset.image_sdiff _ _ F.injective]
    exact hambient
end Oberwolfach
