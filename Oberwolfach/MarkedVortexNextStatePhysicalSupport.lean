module

public import Oberwolfach.MarkedVortexNextStateAfterPacking
public import Oberwolfach.MarkedFiniteResourceSupport

@[expose] public section
/-! The actual one-step complement has an exact next-level deletion state
once its typed arcs and spokes are supported on the next vortex pair. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 16384
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]
variable {G:SimpleGraph V} {D m:ℕ} {β ε:ℝ} (Q:Vortex U G D β ε m)

theorem marked_vortex_next_state_from_physical_support
    (i:ℕ) (π:Equiv.Perm V) (hπ:∀ k x,π x∈Q.extendedVertices k↔x∈Q.extendedVertices k)
    (d c:ℕ) (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop):
    let P:=fun j=>G.comap (markedVortexVertexEmbedding Q j)
    let ρ:=fun j=>markedVortexPermutation Q π hπ j
    let σj:=fun j=>rawMarkedRestrictPair (markedVortexVertexEmbedding Q j) (markedVortexHubEmbedding Q j) σ
    let Hj:=fun j b (v:markedVortexVertexType Q j) (u:markedVortexHubType Q j)=>H b v.val u.val
    let E:=MarkedSampleArc (P i) (ρ i) (3*d) (fun e=>σj i (Sum.inl e)) false
    let K:=MarkedSampleArc (P i) (ρ i) (3*d) (fun e=>σj i (Sum.inl e)) true
    let S:=Finset.univ.filter (fun z:markedVortexVertexType Q i×markedVortexHubType Q i=>Hj i false z.1 z.2∨Hj i true z.1 z.2)
    let f:=markedVortexNestedVertex Q i (i+1) (by omega)
    let g:=markedVortexNestedHub Q i (i+1) (by omega);
    ∀ (T:MarkedReferenceDeletion (P i) (ρ i) d (σj i))
      (M:Finset (MarkedWheel (fun e:E=>e.val.1) (fun e=>e.val.2)
        (fun e:K=>e.val.1) (fun e=>e.val.2) c (ρ i) (3*d) (Hj i false) (Hj i true))),
    let Arem:=Finset.univ\(T.arcs∪M.biUnion markedWheelArcs)
    let Srem:=S\(T.spokes∪M.biUnion markedWheelSpokePairs);
    (∀ z∈markedFiniteResources (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) (ρ i) Arem Srem,
      markedInnerResource (markedVortexInnerVertices Q i) (markedVortexInnerHubs Q i) z)→
    ∃ Tnext:MarkedReferenceDeletion (P (i+1)) (ρ (i+1)) d (σj (i+1)),
      (markedFiniteResources (fun e:E=>e.val.1) (fun e=>e.val.2) (fun e:K=>e.val.1) (fun e=>e.val.2)
        (ρ i) Arem Srem).image (markedResourceEmbedding (markedVortexVertexEmbedding Q i).toEmbedding (markedVortexHubEmbedding Q i))=
      (Tnext.remaining (Hj (i+1))).image
        (markedResourceEmbedding (markedVortexVertexEmbedding Q (i+1)).toEmbedding (markedVortexHubEmbedding Q (i+1))):=by
  intro P ρ σj Hj E K S f g T M Arem Srem hinner
  have hI:∀ x,ρ i x∈markedVortexInnerVertices Q i↔x∈markedVortexInnerVertices Q i:=by
    intro x
    simp only [markedVortexInnerVertices,Finset.mem_filter,Finset.mem_univ,true_and]
    exact hπ (i+1) x.val
  have hs:=(markedFiniteResources_support_iff (fun e:E=>e.val.1) (fun e=>e.val.2)
    (fun e:K=>e.val.1) (fun e=>e.val.2) (ρ i) Arem Srem
    (markedVortexInnerVertices Q i) (markedVortexInnerHubs Q i) hI).mp hinner
  have himg:=marked_vortex_nested_next_images Q i
  rw [←himg.1] at hs
  rw [←himg.2] at hs
  exact marked_vortex_next_state_after_packing Q i π hπ d c σ H T M hs.1 hs.2
end Oberwolfach
