module

public import Oberwolfach.MarkedVortexStepConservation

@[expose] public section
/-! Assemble actual wheel packings on a fixed vortex. Each next state must
represent the preceding physical remainder; no separate layer partition is
assumed. -/
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

theorem marked_vortex_physical_iteration
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
    HasResourceDecomposition R₀ (B n)→HasResourceDecomposition R₀ (B 0):=by
  intro P ρ σi Hi E K S F T M hpack hA hS L B C E₀ K₀ R₀ hnext hterm
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
  exact finite_resource_layer_decompositions R₀ B C n hB hC hdec hterm
/-- Finite layer decompositions combine with a reserved absorber whose
terminal decomposition covers the reserve together with the last remainder. -/
theorem finite_resource_layers_with_terminal_absorber {X W:Type} [DecidableEq X] [DecidableEq W]
    (F:W→Finset X) (B R:ℕ→Finset X) (Full Reserve:Finset X) (n:ℕ)
    (hB:∀ i,i<n→B (i+1)⊆B i)
    (hR:∀ i,i<n→R i=B i\B (i+1))
    (hdec:∀ i,i<n→HasResourceDecomposition F (R i))
    (hReserve:Reserve⊆Full) (hInitial:B 0=Full\Reserve)
    (hterminal:HasResourceDecomposition F (Reserve∪B n)):
    HasResourceDecomposition F Full:=by
  have hsub:∀ i,i<n→R i⊆B i\B (i+1):=by intro i hi;rw [hR i hi]
  have hpair:=finite_resource_layers_disjoint B R n hB hsub
  have hterminalDis:=finite_resource_layers_terminal_disjoint B R n hB hsub
  have hpart:=finite_resource_layers_partition B R n hB hR
  have hlast:B n⊆B 0:=finite_resource_prefix_subset B n hB 0 n (Nat.zero_le _) le_rfl
  have hreserveDis:Disjoint ((Finset.range n).biUnion R) Reserve:=by
    apply Finset.disjoint_left.mpr
    intro z hz hzR
    have hzB:z∈B 0:=by rw [←hpart];exact Finset.mem_union_left _ hz
    rw [hInitial] at hzB
    exact (Finset.mem_sdiff.mp hzB).2 hzR
  have hdis:Disjoint ((Finset.range n).biUnion R) (Reserve∪B n):=
    Finset.disjoint_union_right.mpr ⟨hreserveDis,hterminalDis⟩
  have hlayers:HasResourceDecomposition F ((Finset.range n).biUnion R):=by
    apply resource_decomposition_biUnion F R (Finset.range n)
    · intro i hi;exact hdec i (Finset.mem_range.mp hi)
    · intro i hi j hj hne;exact hpair i (Finset.mem_range.mp hi) j (Finset.mem_range.mp hj) hne
  have hfull:=resource_decomposition_union F ((Finset.range n).biUnion R) (Reserve∪B n) hlayers hterminal hdis
  have heq:((Finset.range n).biUnion R)∪(Reserve∪B n)=Full:=by
    ext z
    have hsubR:=fun hz=>hReserve (x:=z) hz
    have hsubN:=fun hz=>hlast (x:=z) hz
    have hp:=congrArg (fun A:Finset X=>z∈A) hpart
    rw [hInitial] at hp
    simp only [Finset.mem_union,Finset.mem_sdiff] at hp ⊢
    tauto
  rwa [heq] at hfull
end Oberwolfach

