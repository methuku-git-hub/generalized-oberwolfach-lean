module

public import Oberwolfach.MarkedVortexPhysicalIteration
public import Oberwolfach.MarkedTerminalAbsorberAmbientLift
public import Oberwolfach.MarkedVortexCumulativeProtection

@[expose] public section
/-! Complete actual vortex packings using a terminal decomposition that also
covers the preselected reserve. -/
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

theorem marked_vortex_physical_iteration_with_absorber
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
    HasResourceDecomposition R₀ (Reserve∪B n)→HasResourceDecomposition R₀ Full:=by
  intro P ρ σi Hi E K S F T M hpack hA hS L B C E₀ K₀ R₀ hnext Full Reserve hReserve hInitial hterm
  have hstep:∀ i,i<n→(L i).image (F i)⊆B i ∧
      C i=B i\(L i).image (F i) ∧ HasResourceDecomposition R₀ (B i\(L i).image (F i)):=by
    intro i hi
    have h:=marked_vortex_step_physical_conservation Q i π hπ d c σ H (T i) (M i)
      (hpack i hi) (hA i hi) (hS i hi)
    exact ⟨h.1,h.2.2.1,h.2.2.2⟩
  have hB:∀ i,i<n→B (i+1)⊆B i:=by
    intro i hi
    rw [←hnext i hi]
    exact (hstep i hi).1
  have hC:∀ i,i<n→C i=B i\B (i+1):=by
    intro i hi
    rw [←hnext i hi]
    exact (hstep i hi).2.1
  have hdec:∀ i,i<n→HasResourceDecomposition R₀ (C i):=by
    intro i hi
    rw [hC i hi,←hnext i hi]
    exact (hstep i hi).2.2
  exact finite_resource_layers_with_terminal_absorber R₀ B C Full Reserve n hB hC hdec hReserve hInitial hterm
theorem marked_vortex_iteration_with_preselected_terminal_absorber
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
    ∀ (DR:SimpleGraph V) (DS:SimpleGraph (V⊕U)),
    (∀ x y,Sum.inl ({x,y}:Finset V)∈Reserve→¬DR.Adj x y)→
    (∀ v u,Sum.inr (v,u)∈Reserve→¬DS.Adj (Sum.inl v) (Sum.inr u))→
    (∀ v∈Q.extendedVertices n,∀ u∈Q.extendedIndices n,¬DS.Adj (Sum.inl v) (Sum.inr u))→
    let σ':=rawMarkedDeleteRims σ DR.edgeFinset
    let H':=markedDeletePhysicalSpokes H DS
    let E':=MarkedSampleArc G π (3*d) (fun e=>σ' (Sum.inl e)) false
    let K':=MarkedSampleArc G π (3*d) (fun e=>σ' (Sum.inl e)) true
    let t':=fun e:E'=>e.val.1
    let h':=fun e:E'=>e.val.2
    let kt':=fun e:K'=>e.val.1
    let kh':=fun e:K'=>e.val.2;
    ∀ (A:Finset (E'⊕K')) (S':Finset (V×U)),
    (∀ a∈A,Sum.elim t' kt' a∈Q.extendedVertices n∧Sum.elim h' kh' a∈Q.extendedVertices n)→
    (∀ z∈S',z.1∈Q.extendedVertices n∧z.2∈Q.extendedIndices n∧(H' false z.1 z.2∨H' true z.1 z.2))→
    MarkedRemainderDivisible t' h' kt' kh' (H' true) A S' c→
    B n=markedFiniteResources t' h' kt' kh' π A S'→
    HasResourceDecomposition R₀ Full:=by
  intro P ρ σi Hi E K S F T M hpack hA hS L B C E₀ K₀ R₀ hnext Full Reserve hReserve hInitial habs DR DS hR hSavoid hXZ σ' H' E' K' t' h' kt' kh' A S' hAterm hSterm hdiv hBn
  have hterm:=marked_terminal_absorber_decomposition_lift G π d c σ H Reserve
    (Q.extendedVertices n) (Q.extendedIndices n) habs DR DS hR hSavoid hXZ
    A S' hAterm hSterm hdiv
  rw [←hBn] at hterm
  exact marked_vortex_physical_iteration_with_absorber Q π hπ d c n σ H T M
    hpack hA hS hnext Full Reserve hReserve hInitial hterm
theorem marked_vortex_iteration_with_cumulative_deletion
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
    let Covered:=(Finset.range n).biUnion C
    let DR:=physicalEdgeGraph (markedReservedRimPairs Covered)
    let DS:=markedFiniteSpokeGraph (markedReservedSpokePairs Covered);
    let σ':=rawMarkedDeleteRims σ DR.edgeFinset
    let H':=markedDeletePhysicalSpokes H DS
    let E':=MarkedSampleArc G π (3*d) (fun e=>σ' (Sum.inl e)) false
    let K':=MarkedSampleArc G π (3*d) (fun e=>σ' (Sum.inl e)) true
    let t':=fun e:E'=>e.val.1
    let h':=fun e:E'=>e.val.2
    let kt':=fun e:K'=>e.val.1
    let kh':=fun e:K'=>e.val.2;
    ∀ (A:Finset (E'⊕K')) (S':Finset (V×U)),
    (∀ a∈A,Sum.elim t' kt' a∈Q.extendedVertices n∧Sum.elim h' kh' a∈Q.extendedVertices n)→
    (∀ z∈S',z.1∈Q.extendedVertices n∧z.2∈Q.extendedIndices n∧(H' false z.1 z.2∨H' true z.1 z.2))→
    MarkedRemainderDivisible t' h' kt' kh' (H' true) A S' c→
    B n=markedFiniteResources t' h' kt' kh' π A S'→
    HasResourceDecomposition R₀ Full:=by
  intro P ρ σi Hi E K S F T M hpack hA hS L B C E₀ K₀ R₀ hnext Full Reserve hReserve hInitial habs hTerminal Covered DR DS σ' H' E' K' t' h' kt' kh' A S' hAterm hSterm hdiv hBn
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
  have hp:=marked_resource_layers_cumulative_deletion_protects B C n Full Reserve
    (Q.extendedVertices n) (Q.extendedIndices n) hB hC hInitial hTerminal
  exact marked_vortex_iteration_with_preselected_terminal_absorber Q π hπ d c n σ H T M
    hpack hA hS hnext Full Reserve hReserve hInitial habs DR DS hp.1 hp.2.1 hp.2.2
    A S' hAterm hSterm hdiv hBn
end Oberwolfach
