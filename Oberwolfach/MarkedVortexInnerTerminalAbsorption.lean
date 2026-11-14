module

public import Oberwolfach.MarkedVortexInnerTerminalRemainderLift
public import Oberwolfach.MarkedFixedTerminalAbsorberOriginal

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 20000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]
variable {G:SimpleGraph V} {D m:ℕ} {β ε:ℝ} (Q:Vortex U G D β ε m)
theorem marked_vortex_inner_terminal_remainder_absorbed
    (i:ℕ) (π:Equiv.Perm V) (hπ:∀ k x,π x∈Q.extendedVertices k↔x∈Q.extendedVertices k)
    (d c:ℕ) (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop):
    let P:=G.comap (markedVortexVertexEmbedding Q i)
    let ρ:=markedVortexPermutation Q π hπ i
    let σi:=rawMarkedRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i) σ
    let Hi:=fun b (v:markedVortexVertexType Q i) (u:markedVortexHubType Q i)=>H b v.val u.val
    let E:=MarkedSampleArc P ρ (3*d) (fun e=>σi (Sum.inl e)) false
    let K:=MarkedSampleArc P ρ (3*d) (fun e=>σi (Sum.inl e)) true
    let E₀:=MarkedSampleArc G π (3*d) (fun e=>σ (Sum.inl e)) false
    let K₀:=MarkedSampleArc G π (3*d) (fun e=>σ (Sum.inl e)) true;
    ∀ (A:Finset (E⊕K)) (S:Finset (markedVortexVertexType Q i×markedVortexHubType Q i)),
    (∀ a∈A,Sum.elim (fun e:E=>e.val.1) (fun e:K=>e.val.1) a∈markedVortexInnerVertices Q i ∧
      Sum.elim (fun e:E=>e.val.2) (fun e:K=>e.val.2) a∈markedVortexInnerVertices Q i)→
    (∀ z∈S,z.1∈markedVortexInnerVertices Q i∧z.2∈markedVortexInnerHubs Q i∧(Hi false z.1 z.2∨Hi true z.1 z.2))→
    MarkedRemainderDivisible (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) (Hi true) A S c→
    ∀ Reserve:Finset (Finset V⊕(V×U)),
    MarkedFixedTerminalAbsorber G π d c σ H Reserve (Q.extendedVertices (i+1)) (Q.extendedIndices (i+1))→
    HasResourceDecomposition
      (fun W:MarkedWheel (fun e:E₀=>e.val.1) (fun e=>e.val.2)
        (fun e:K₀=>e.val.1) (fun e=>e.val.2) c π (3*d) (H false) (H true)=>markedWheelPhysicalResources W)
      (Reserve∪(markedFiniteResources (fun e:E=>e.val.1) (fun e=>e.val.2)
        (fun e:K=>e.val.1) (fun e=>e.val.2) ρ A S).image
          (markedResourceEmbedding (markedVortexVertexEmbedding Q i).toEmbedding (markedVortexHubEmbedding Q i))) :=by
  intro P ρ σi Hi E K E₀ K₀ A S hA hS hdiv Reserve habs
  obtain ⟨A₀,S₀,hA₀,hS₀,hdiv₀,hres⟩:=marked_vortex_inner_terminal_remainder_lift Q i π hπ d c σ H A S hA hS hdiv
  rw [hres]
  exact (habs A₀ S₀ hA₀ hS₀ hdiv₀).2.2
end Oberwolfach
