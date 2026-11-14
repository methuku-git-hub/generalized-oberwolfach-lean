module

public import Oberwolfach.MarkedVortexTerminalStateRepresentation
public import Oberwolfach.MarkedFixedTerminalAbsorberOriginal
public import Oberwolfach.ReindexedResourceIteration

@[expose] public section
/-! Iterate valid states on the actual vortex and absorb the last remainder
in the original fixed host. The one-step condition is the conclusion of the
verified cover-down step, not a construction of its probabilistic inputs. -/
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

theorem marked_vortex_iteration_after_protected_correction
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
    ∀ (T₀:State 0),Good 0 T₀→∀ (Reserve:Finset (Finset V⊕(V×U))),
    Disjoint Reserve (B 0 T₀)→
    MarkedFixedTerminalAbsorber G π d c σ H Reserve (Q.extendedVertices n) (Q.extendedIndices n)→
    HasResourceDecomposition R₀ (Reserve∪B 0 T₀):=by
  intro P ρ σi Hi State Good F B E₀ K₀ R₀ S₀ Full hstep T₀ hT₀ Reserve hdis habs
  have hfinish:∀ T:State n,Good n T→B n T⊆B 0 T₀→HasResourceDecomposition R₀ (Reserve∪B n T):=by
    intro T hT hsub
    obtain ⟨A,S,hA,hS,hdiv,hB⟩:=marked_vortex_valid_terminal_state_representation Q n π hπ d c σ H
      T (markedVortexInnerVertices Q n) (markedVortexInnerHubs Q n) (γ n) (σloss n) hT
    have hB':B n T=markedFiniteResources (fun e:E₀=>e.val.1) (fun e=>e.val.2)
      (fun e:K₀=>e.val.1) (fun e=>e.val.2) π A S:=hB
    rw [hB']
    exact (habs A S hA hS hdiv).2.2
  exact reindexed_resource_iteration_absorption R₀ State B Good n hstep T₀ hT₀ Reserve hdis hfinish
end Oberwolfach
