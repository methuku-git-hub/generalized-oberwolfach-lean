module

public import Oberwolfach.MarkedVortexNextStateExact

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

theorem marked_vortex_next_state_after_packing
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
    (∀ a∈Arem,Sum.elim (fun a:E=>a.val.1) (fun a:K=>a.val.1) a∈Finset.univ.image f∧
      Sum.elim (fun a:E=>a.val.2) (fun a:K=>a.val.2) a∈Finset.univ.image f)→
    (∀ z∈Srem,z.1∈Finset.univ.image f∧z.2∈Finset.univ.image g)→
    ∃ Tnext:MarkedReferenceDeletion (P (i+1)) (ρ (i+1)) d (σj (i+1)),
      (markedFiniteResources (fun e:E=>e.val.1) (fun e=>e.val.2) (fun e:K=>e.val.1) (fun e=>e.val.2)
        (ρ i) Arem Srem).image (markedResourceEmbedding (markedVortexVertexEmbedding Q i).toEmbedding (markedVortexHubEmbedding Q i))=
      (Tnext.remaining (Hj (i+1))).image
        (markedResourceEmbedding (markedVortexVertexEmbedding Q (i+1)).toEmbedding (markedVortexHubEmbedding Q (i+1))):=by
  intro P ρ σj Hj E K S f g T M Arem Srem hA hS
  have hh:∀ z∈Srem,z.1∈Finset.univ.image f∧z.2∈Finset.univ.image g∧
      (Hj i false z.1 z.2∨Hj i true z.1 z.2):=by
    intro z hz
    have hzS:z∈S:=(Finset.mem_sdiff.mp hz).1
    exact ⟨(hS z hz).1,(hS z hz).2,(Finset.mem_filter.mp hzS).2⟩
  obtain ⟨Tnext,hnext⟩:=marked_vortex_next_state_exact Q i π hπ d σ H Arem Srem hA hh
  exact ⟨Tnext,hnext.symm⟩
end Oberwolfach
