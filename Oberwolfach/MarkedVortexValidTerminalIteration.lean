module

public import Oberwolfach.MarkedVortexOriginalTerminal
public import Oberwolfach.MarkedVortexTerminalStateRepresentation

@[expose] public section
/-! Finish the finite marked iteration from the actual valid final state,
without separately postulating its typed ambient representation. -/
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

theorem marked_vortex_iteration_from_valid_terminal_state
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
    ∀ (X:Finset (markedVortexVertexType Q n)) (Z:Finset (markedVortexHubType Q n))
      (γ σloss:ℝ),
    (T n).Valid (Hi n) c X Z γ σloss→HasResourceDecomposition R₀ Full:=by
  intro P ρ σi Hi E K S F T M hpack hA hS L B C E₀ K₀ R₀ hnext Full Reserve hReserve hInitial habs hTerminal X Z γ σloss hvalid
  obtain ⟨A₀,S₀,hAterm,hSterm,hdiv,hBn⟩:=
    marked_vortex_valid_terminal_state_representation Q n π hπ d c σ H (T n) X Z γ σloss hvalid
  exact marked_vortex_iteration_with_original_terminal_remainder Q π hπ d c n σ H T M
    hpack hA hS hnext Full Reserve hReserve hInitial habs hTerminal A₀ S₀ hAterm hSterm hdiv hBn
end Oberwolfach
