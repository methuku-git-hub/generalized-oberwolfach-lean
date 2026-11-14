module

public import Oberwolfach.MarkedVortexFixedAbsorberCompleteFromSteps
public import Oberwolfach.MarkedSelectFixedTerminalAbsorber

@[expose] public section
/-! Select one fixed absorber and run all valid marked vortex steps on the
same fixed sample. The analytic step-existence property remains explicit. -/
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

theorem marked_vortex_completion_from_selected_absorber
    (π:Equiv.Perm V) (hπ:∀ k x,π x∈Q.extendedVertices k↔x∈Q.extendedVertices k)
    (d l n:ℕ) (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (γ σloss:ℕ→ℝ):
    let P:=fun i=>G.comap (markedVortexVertexEmbedding Q i)
    let ρ:=fun i=>markedVortexPermutation Q π hπ i
    let σi:=fun i=>rawMarkedRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i) σ
    let Hi:=fun i b (v:markedVortexVertexType Q i) (u:markedVortexHubType Q i)=>H b v.val u.val
    let State:=fun i=>MarkedReferenceDeletion (P i) (ρ i) d (σi i)
    let Good:=fun i (T:State i)=>T.Valid (Hi i) (l+4) (markedVortexInnerVertices Q i)
      (markedVortexInnerHubs Q i) (γ i) (σloss i)
    let F:=fun i=>markedResourceEmbedding (markedVortexVertexEmbedding Q i).toEmbedding (markedVortexHubEmbedding Q i)
    let B:=fun i (T:State i)=>(T.remaining (Hi i)).image (F i)
    let E₀:=MarkedSampleArc G π (3*d) (fun e=>σ (Sum.inl e)) false
    let K₀:=MarkedSampleArc G π (3*d) (fun e=>σ (Sum.inl e)) true
    let R₀:=fun W:MarkedWheel (fun e:E₀=>e.val.1) (fun e=>e.val.2) (fun e:K₀=>e.val.1) (fun e=>e.val.2)
      (l+4) π (3*d) (H false) (H true)=>markedWheelPhysicalResources W
    let S₀:=Finset.univ.filter (fun z:V×U=>H false z.1 z.2∨H true z.1 z.2)
    let Full:=markedFiniteResources (fun e:E₀=>e.val.1) (fun e=>e.val.2)
      (fun e:K₀=>e.val.1) (fun e=>e.val.2) π Finset.univ S₀;
    (∀ i<n,∀ T:State i,Good i T→∃ Tnext:State (i+1),Good (i+1) Tnext ∧
      B (i+1) Tnext⊆B i T ∧ HasResourceDecomposition R₀ (B i T\B (i+1) Tnext))→
    ∀ (size a₀ b₀ e₀ f:ℕ) (εabs:ℝ),
    MarkedReservedTerminalAbsorberProperty (fun e:E₀=>e.val.1) (fun e=>e.val.2)
      (fun e:K₀=>e.val.1) (fun e=>e.val.2) (H false) (H true) π (3*d) l size a₀ b₀ e₀ f εabs→
    1≤n→(Q.extendedVertices n).card+(Q.extendedIndices n).card≤size→
    ((Q.extendedVertices 1).card:ℝ)≤εabs*Fintype.card V+f→
    ((Q.extendedIndices 1).card:ℝ)≤εabs*Fintype.card V+f→
    (e₀:ℝ)≤γ 0→(e₀:ℝ)≤σloss 0→
    (∀ v u,¬(H false v u∧H true v u))→
    MarkedRemainderDivisible (fun e:E₀=>e.val.1) (fun e=>e.val.2)
      (fun e:K₀=>e.val.1) (fun e=>e.val.2) (H true) Finset.univ S₀ (l+4)→
    ∀ F₀:Finset (Finset V⊕(V×U)),F₀.card≤f→
    ∃ C:MarkedSupportedEdgeSet (fun e:E₀=>e.val.1) (fun e=>e.val.2)
      (fun e:K₀=>e.val.1) (fun e=>e.val.2) π U,
      Disjoint C.edges F₀∧C.edges.card≤e₀∧C.rows.card≤a₀∧C.hubs.card≤b₀∧
      C.edges.filter (markedInnerResource (Q.extendedVertices 1) (Q.extendedIndices 1))=∅∧
      HasResourceDecomposition R₀ Full:=by
  intro P ρ σi Hi State Good F B E₀ K₀ R₀ S₀ Full hstep size a₀ b₀ e₀ f εabs hprop hn hsize hW hB hγ hσ hH hdiv F₀ hF
  have hX:Q.extendedVertices n⊆Q.extendedVertices 1:=Q.extendedVertices_subset (by omega)
  have hZ:Q.extendedIndices n⊆Q.extendedIndices 1:=Q.extendedIndices_subset (by omega)
  obtain ⟨C,hF₀,hCe,hCr,hCu,hEmpty,hAbs⟩:=marked_select_fixed_terminal_absorber G π d l size a₀ b₀ e₀ f εabs σ H hprop
    (Q.extendedVertices n) (Q.extendedVertices 1) (Q.extendedVertices 1)
    (Q.extendedIndices n) (Q.extendedIndices 1) (Q.extendedIndices 1)
    hsize hX hZ (Finset.Subset.rfl) (Finset.Subset.rfl) (hπ 1) hW hB F₀ hF
  have hCe':(C.edges.card:ℝ)≤e₀:=by exact_mod_cast hCe
  have hdec:=marked_vortex_fixed_absorber_complete_from_steps Q π hπ d (l+4) n σ H γ σloss
    hstep C.edges hAbs hH hdiv hEmpty (hCe'.trans hγ) (hCe'.trans hσ)
  exact ⟨C,hF₀,hCe,hCr,hCu,hEmpty,hdec⟩
end Oberwolfach
