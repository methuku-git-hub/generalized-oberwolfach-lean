module

public import Oberwolfach.MarkedVortexAbsorbingIteration
public import Oberwolfach.MarkedTerminalRemainderSurvival

@[expose] public section
/-! The terminal remainder can be specified in the original host: disjointness
from all covered layers supplies its representation after cumulative deletion. -/
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

theorem marked_vortex_iteration_with_original_terminal_remainder
    (π:Equiv.Perm V) (hπ:∀ k x,π x∈Q.extendedVertices k↔x∈Q.extendedVertices k)
    (d c n:ℕ) (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop):
    let P:=fun i=>G.comap (markedVortexVertexEmbedding Q i)
    let ρ:=fun i=>markedVortexPermutation Q π hπ i
    let σi:=fun i=>rawMarkedRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i) σ
    let Hi:=fun i b (v:markedVortexVertexType Q i) (u:markedVortexHubType Q i)=>H b v.val u.val
    let E:=fun i=>MarkedSampleArc (P i) (ρ i) (3*d) (fun e=>σi i (Sum.inl e)) false
    let K:=fun i=>MarkedSampleArc (P i) (ρ i) (3*d) (fun e=>σi i (Sum.inl e)) true
    let S:=fun i=>Finset.univ.filter (fun z:markedVortexVertexType Q i×markedVortexHubType Q i=>Hi i false z.1 z.2∨Hi i true z.1 z.2)
    let F:=fun i=>markedResourceEmbedding (markedVortexVertexEmbedding Q i).toEmbedding (markedVortexHubEmbedding Q i);
    ∀ (T:∀ i,MarkedReferenceDeletion (P i) (ρ i) d (σi i))
      (M:∀ i,Finset (MarkedWheel (fun e:E i=>e.val.1) (fun e=>e.val.2)
        (fun e:K i=>e.val.1) (fun e=>e.val.2) c (ρ i) (3*d) (Hi i false) (Hi i true))),
    (∀ i,i<n→∀ Y∈M i,∀ Z∈M i,Y≠Z→Disjoint (markedWheelPhysicalResources Y) (markedWheelPhysicalResources Z))→
    (∀ i,i<n→(M i).biUnion markedWheelArcs⊆Finset.univ\(T i).arcs)→
    (∀ i,i<n→(M i).biUnion markedWheelSpokePairs⊆S i\(T i).spokes)→
    let L:=fun i=>markedFiniteResources (fun e:E i=>e.val.1) (fun e=>e.val.2)
      (fun e:K i=>e.val.1) (fun e=>e.val.2) (ρ i)
      (Finset.univ\((T i).arcs∪(M i).biUnion markedWheelArcs)) (S i\((T i).spokes∪(M i).biUnion markedWheelSpokePairs))
    let B:=fun i=>((T i).remaining (Hi i)).image (F i)
    let C:=fun i=>((M i).biUnion markedWheelPhysicalResources).image (F i)
    let E₀:=MarkedSampleArc G π (3*d) (fun e=>σ (Sum.inl e)) false
    let K₀:=MarkedSampleArc G π (3*d) (fun e=>σ (Sum.inl e)) true
    let R₀:=fun W:MarkedWheel (fun e:E₀=>e.val.1) (fun e=>e.val.2) (fun e:K₀=>e.val.1) (fun e=>e.val.2)
      c π (3*d) (H false) (H true)=>markedWheelPhysicalResources W;
    (∀ i,i<n→(L i).image (F i)=B (i+1))→
    ∀ (Full Reserve:Finset (Finset V⊕(V×U))),
    Reserve⊆Full→B 0=Full\Reserve→
    MarkedUniversalTerminalDeletionAbsorber G π d c σ H Reserve
      (Q.extendedVertices n) (Q.extendedIndices n)→
    (∀ i,i<n→∀ v∈Q.extendedVertices n,∀ u∈Q.extendedIndices n,Sum.inr (v,u)∉C i)→
    ∀ (A₀:Finset (E₀⊕K₀)) (S₀:Finset (V×U)),
    (∀ a∈A₀,Sum.elim (fun e:E₀=>e.val.1) (fun e:K₀=>e.val.1) a∈Q.extendedVertices n∧
      Sum.elim (fun e:E₀=>e.val.2) (fun e:K₀=>e.val.2) a∈Q.extendedVertices n)→
    (∀ z∈S₀,z.1∈Q.extendedVertices n∧z.2∈Q.extendedIndices n∧(H false z.1 z.2∨H true z.1 z.2))→
    MarkedRemainderDivisible (fun e:E₀=>e.val.1) (fun e=>e.val.2)
      (fun e:K₀=>e.val.1) (fun e=>e.val.2) (H true) A₀ S₀ c→
    B n=markedFiniteResources (fun e:E₀=>e.val.1) (fun e=>e.val.2)
      (fun e:K₀=>e.val.1) (fun e=>e.val.2) π A₀ S₀→
    HasResourceDecomposition R₀ Full:=by
  intro P ρ σi Hi E K S F T M hpack hA hS L B C E₀ K₀ R₀ hnext Full Reserve hReserve hInitial habs hTerminal A₀ S₀ hAterm hSterm hdiv hBn
  have hstep:∀ i,i<n→(L i).image (F i)⊆B i ∧ C i=B i\(L i).image (F i):=by
    intro i hi
    have h:=marked_vortex_step_physical_conservation Q i π hπ d c σ H (T i) (M i)
      (hpack i hi) (hA i hi) (hS i hi)
    exact ⟨h.1,h.2.2.1⟩
  have hB:∀ i,i<n→B (i+1)⊆B i:=by
    intro i hi
    rw [←hnext i hi]
    exact (hstep i hi).1
  have hC:∀ i,i<n→C i=B i\B (i+1):=by
    intro i hi
    rw [←hnext i hi]
    exact (hstep i hi).2
  have hCsub:∀ i,i<n→C i⊆B i\B (i+1):=by
    intro i hi;rw [hC i hi]
  have hdis:Disjoint (B n) ((Finset.range n).biUnion C):=
    (finite_resource_layers_terminal_disjoint B C n hB hCsub).symm
  rw [hBn] at hdis
  obtain ⟨A',hA',hS',hdiv',hres'⟩:=marked_terminal_remainder_survives_cumulative_deletion
    G π d c σ H ((Finset.range n).biUnion C) (Q.extendedVertices n) (Q.extendedIndices n)
    A₀ S₀ hAterm hSterm hdiv hdis
  have hBn':B n=markedFiniteResources
      (fun e:MarkedSampleArc G π (3*d) (fun e=>rawMarkedDeleteRims σ
        (physicalEdgeGraph (markedReservedRimPairs ((Finset.range n).biUnion C))).edgeFinset (Sum.inl e)) false=>e.val.1)
      (fun e=>e.val.2)
      (fun e:MarkedSampleArc G π (3*d) (fun e=>rawMarkedDeleteRims σ
        (physicalEdgeGraph (markedReservedRimPairs ((Finset.range n).biUnion C))).edgeFinset (Sum.inl e)) true=>e.val.1)
      (fun e=>e.val.2) π A' S₀:=hBn.trans hres'.symm
  exact marked_vortex_iteration_with_cumulative_deletion Q π hπ d c n σ H T M
    hpack hA hS hnext Full Reserve hReserve hInitial habs hTerminal A' S₀ hA' hS' hdiv' hBn'
end Oberwolfach
