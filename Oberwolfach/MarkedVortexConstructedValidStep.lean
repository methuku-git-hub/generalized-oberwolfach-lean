module

public import Oberwolfach.MarkedVortexNextValidState
public import Oberwolfach.MarkedVortexStepConservation

@[expose] public section
/-! The actual cover-down packing and its quantitative remainder estimates
produce a valid next state and a decomposition of the physical layer removed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]
variable {G:SimpleGraph V} {D m:ℕ} {β ε:ℝ} (Q:Vortex U G D β ε m)

theorem marked_vortex_constructed_valid_step
    (i:ℕ) (π:Equiv.Perm V) (hπ:∀ k x,π x∈Q.extendedVertices k↔x∈Q.extendedVertices k)
    (d c:ℕ) (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop):
    letI : DecidableEq (markedVortexVertexType Q i):=fun a b=>Classical.propDecidable (a=b)
    letI : DecidableEq (markedVortexVertexType Q (i+1)):=fun a b=>Classical.propDecidable (a=b)
    let P:=fun j=>G.comap (markedVortexVertexEmbedding Q j)
    let ρ:=fun j=>markedVortexPermutation Q π hπ j
    let σj:=fun j=>rawMarkedRestrictPair (markedVortexVertexEmbedding Q j) (markedVortexHubEmbedding Q j) σ
    let Hj:=fun j b (v:markedVortexVertexType Q j) (u:markedVortexHubType Q j)=>H b v.val u.val
    let E:=MarkedSampleArc (P i) (ρ i) (3*d) (fun e=>σj i (Sum.inl e)) false
    let K:=MarkedSampleArc (P i) (ρ i) (3*d) (fun e=>σj i (Sum.inl e)) true
    let S:=Finset.univ.filter (fun z:markedVortexVertexType Q i×markedVortexHubType Q i=>Hj i false z.1 z.2∨Hj i true z.1 z.2)
    let I:=markedVortexInnerVertices Q i
    let J:=markedVortexInnerHubs Q i
    let Tdeep:=markedVortexDeeperVertices Q i
    let Wdeep:=markedVortexDeeperHubs Q i;
    ∀ (State:MarkedReferenceDeletion (P i) (ρ i) d (σj i))
      (M:Finset (MarkedWheel (fun e:E=>e.val.1) (fun e=>e.val.2)
        (fun e:K=>e.val.1) (fun e=>e.val.2) c (ρ i) (3*d) (Hj i false) (Hj i true))),
    (∀ X∈M,∀ Y∈M,X≠Y→Disjoint (markedWheelPhysicalResources X) (markedWheelPhysicalResources Y))→
    M.biUnion markedWheelArcs⊆Finset.univ\State.arcs→
    M.biUnion markedWheelSpokePairs⊆S\State.spokes→
    let AR:=Finset.univ\(State.arcs∪M.biUnion markedWheelArcs)
    let SR:=S\(State.spokes∪M.biUnion markedWheelSpokePairs);
    (∀ a∈AR,Sum.elim (fun a:E=>a.val.1) (fun a:K=>a.val.1) a∈I∧
      Sum.elim (fun a:E=>a.val.2) (fun a:K=>a.val.2) a∈I)→
    (∀ z∈SR,z.1∈I∧z.2∈J)→
    MarkedRemainderDivisible (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) (Hj i true) AR SR c→
    ∀ γ σloss:ℝ,
    let B:=markedFiniteResources (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) (ρ i) Finset.univ S
    let L:=markedFiniteResources (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) (ρ i) AR SR
    let F:=B.filter (markedInnerResource I J)\L;
    F.filter (markedInnerResource Tdeep Wdeep)=∅→
    (∀ physical x,(((markedIncidentEdges (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) (ρ i) (Hj i false) (Hj i true) physical x).filter
      (fun e=>markedActivePhysical (fun e:E=>e.val.1) (fun e=>e.val.2)
        (fun e:K=>e.val.1) (fun e=>e.val.2) (ρ i) (Hj i false) (Hj i true) e∈F)).card:ℝ)≤γ)→
    (∀ physical x,(((markedIncidentEdges (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) (ρ i) (Hj i false) (Hj i true) physical x).filter
      (fun e=>markedActivePhysical (fun e:E=>e.val.1) (fun e=>e.val.2)
        (fun e:K=>e.val.1) (fun e=>e.val.2) (ρ i) (Hj i false) (Hj i true) e∈F.filter (markedStarResource Tdeep Wdeep))).card:ℝ)≤σloss)→
    let E₀:=MarkedSampleArc G π (3*d) (fun e=>σ (Sum.inl e)) false
    let K₀:=MarkedSampleArc G π (3*d) (fun e=>σ (Sum.inl e)) true
    let R₀:=fun W:MarkedWheel (fun e:E₀=>e.val.1) (fun e=>e.val.2)
      (fun e:K₀=>e.val.1) (fun e=>e.val.2) c π (3*d) (H false) (H true)=>markedWheelPhysicalResources W
    let Fcur:=markedResourceEmbedding (markedVortexVertexEmbedding Q i).toEmbedding (markedVortexHubEmbedding Q i)
    let Fnext:=markedResourceEmbedding (markedVortexVertexEmbedding Q (i+1)).toEmbedding (markedVortexHubEmbedding Q (i+1));
    ∃ Tnext:MarkedReferenceDeletion (P (i+1)) (ρ (i+1)) d (σj (i+1)),
      Tnext.Valid (Hj (i+1)) c (markedVortexInnerVertices Q (i+1))
        (markedVortexInnerHubs Q (i+1)) γ σloss ∧
      (Tnext.remaining (Hj (i+1))).image Fnext⊆(State.remaining (Hj i)).image Fcur ∧
      HasResourceDecomposition R₀ ((State.remaining (Hj i)).image Fcur\(Tnext.remaining (Hj (i+1))).image Fnext):=by
  intro P ρ σj Hj E K S I J Tdeep Wdeep State M hpack hA hS AR SR hAR hSR hdiv γ σloss B L F hDeep hInc hStar E₀ K₀ R₀ Fcur Fnext
  have hEq:(fun (a b:markedVortexVertexType Q i)=>Classical.propDecidable (a=b))=
      (fun (a b:markedVortexVertexType Q i)=>Subtype.instDecidableEq a b):=by
    apply Subsingleton.elim
  have hSRsub:SR⊆S:=by
    intro z hz
    dsimp only [SR] at hz
    rw [hEq] at hz
    exact (Finset.mem_sdiff.mp hz).1
  obtain ⟨Tnext,hValid,hnext⟩:=marked_vortex_cover_down_next_valid_state Q i π hπ d c σ H
    AR SR hSRsub hAR hSR hdiv γ σloss hDeep hInc hStar
  have hp:=hpack
  have ha:=hA
  have hs:=hS
  try rw [hEq] at hp
  try rw [hEq] at ha
  try rw [hEq] at hs
  have hstep:=marked_vortex_step_physical_conservation Q i π hπ d c σ H State M hp ha hs
  try rw [←hEq] at hstep
  refine ⟨Tnext,hValid,?_,?_⟩
  · rw [←hnext]
    exact hstep.1
  · rw [←hnext]
    exact hstep.2.2.2
end Oberwolfach
