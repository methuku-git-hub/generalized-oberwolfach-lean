module

public import Oberwolfach.MarkedVortexRestrictionChain

@[expose] public section
/-! The actual nested vortex embeddings, graph restrictions, raw outcomes and
spoke relations form one finite coherent chain for an arbitrary fixed sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]
variable {G:SimpleGraph V} {D m:ℕ} {β ε:ℝ}

structure MarkedVortexFiniteSampleChain (Q:Vortex U G D β ε m)
    (π:Equiv.Perm V) (hπ:∀ i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop) (count:ℕ) (hc:0<count) where
  nextV : ∀ (i j:Fin count), j.val=i.val+1 → markedVortexVertexType Q j.val ↪o markedVortexVertexType Q i.val
  nextU : ∀ (i j:Fin count), j.val=i.val+1 → markedVortexHubType Q j.val ↪ markedVortexHubType Q i.val
  intoV : ∀ i:Fin count,markedVortexVertexType Q i.val ↪o markedVortexVertexType Q 0
  intoU : ∀ i:Fin count,markedVortexHubType Q i.val ↪ markedVortexHubType Q 0
  nextComm : ∀ i j hj v,nextV i j hj (markedVortexPermutation Q π hπ j.val v)=markedVortexPermutation Q π hπ i.val (nextV i j hj v)
  ambientComm : ∀ i v,intoV i (markedVortexPermutation Q π hπ i.val v)=markedVortexPermutation Q π hπ 0 (intoV i v)
  nextVimage : ∀ i j hj,Finset.univ.image (nextV i j hj)=markedVortexInnerVertices Q i.val
  nextUimage : ∀ i j hj,Finset.univ.image (nextU i j hj)=markedVortexInnerHubs Q i.val
  nextVdeeper : ∀ i j hj v,nextV i j hj v∈markedVortexDeeperVertices Q i.val ↔ v∈markedVortexInnerVertices Q j.val
  nextUdeeper : ∀ i j hj u,nextU i j hj u∈markedVortexDeeperHubs Q i.val ↔ u∈markedVortexInnerHubs Q j.val
  nextGraph : ∀ i j hj,G.comap (markedVortexVertexEmbedding Q j.val)=(G.comap (markedVortexVertexEmbedding Q i.val)).comap (nextV i j hj)
  nextOutcome : ∀ i j hj,rawMarkedRestrictPair (markedVortexVertexEmbedding Q j.val) (markedVortexHubEmbedding Q j.val) σ=
    rawMarkedRestrictPair (nextV i j hj) (nextU i j hj) (rawMarkedRestrictPair (markedVortexVertexEmbedding Q i.val) (markedVortexHubEmbedding Q i.val) σ)
  nextSpokes : ∀ i j hj,(fun b v u=>H b (markedVortexVertexEmbedding Q j.val v) (markedVortexHubEmbedding Q j.val u))=
    (fun b v u=>H b (markedVortexVertexEmbedding Q i.val (nextV i j hj v)) (markedVortexHubEmbedding Q i.val (nextU i j hj u)))
  ambientGraph : ∀ i,G.comap (markedVortexVertexEmbedding Q i.val)=(G.comap (markedVortexVertexEmbedding Q 0)).comap (intoV i)
  ambientOutcome : ∀ i,rawMarkedRestrictPair (markedVortexVertexEmbedding Q i.val) (markedVortexHubEmbedding Q i.val) σ=
    rawMarkedRestrictPair (intoV i) (intoU i) (rawMarkedRestrictPair (markedVortexVertexEmbedding Q 0) (markedVortexHubEmbedding Q 0) σ)
  ambientSpokes : ∀ i,(fun b v u=>H b (markedVortexVertexEmbedding Q i.val v) (markedVortexHubEmbedding Q i.val u))=
    (fun b v u=>H b (markedVortexVertexEmbedding Q 0 (intoV i v)) (markedVortexHubEmbedding Q 0 (intoU i u)))
  composeV : ∀ i j hj v,intoV j v=intoV i (nextV i j hj v)
  composeU : ∀ i j hj u,intoU j u=intoU i (nextU i j hj u)
  firstV : ∀ v,intoV ⟨0,hc⟩ v=v
  firstU : ∀ u,intoU ⟨0,hc⟩ u=u

noncomputable def marked_vortex_finite_sample_chain
    (Q:Vortex U G D β ε m) (π:Equiv.Perm V)
    (hπ:∀ i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop) (count:ℕ) (hc:0<count):
    MarkedVortexFiniteSampleChain Q π hπ σ H count hc := by
  refine ⟨(fun i j hj=>markedVortexNestedVertex Q i.val j.val (by omega)),
    (fun i j hj=>markedVortexNestedHub Q i.val j.val (by omega)),
    (fun i=>markedVortexNestedVertex Q 0 i.val (by omega)),
    (fun i=>markedVortexNestedHub Q 0 i.val (by omega)), ?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro i j hj v; exact marked_vortex_nested_commutes Q π hπ i.val j.val (by omega) v
  · intro i v; exact marked_vortex_nested_commutes Q π hπ 0 i.val (by omega) v
  · intro i j hj; rcases j with ⟨j,hjbound⟩; dsimp only at hj; subst j
    exact (marked_vortex_nested_next_images Q i.val).1
  · intro i j hj; rcases j with ⟨j,hjbound⟩; dsimp only at hj; subst j
    exact (marked_vortex_nested_next_images Q i.val).2
  · intro i j hj v; rcases j with ⟨j,hjbound⟩; dsimp only at hj; subst j
    exact (marked_vortex_nested_next_deeper Q i.val).1 v
  · intro i j hj u; rcases j with ⟨j,hjbound⟩; dsimp only at hj; subst j
    exact (marked_vortex_nested_next_deeper Q i.val).2 u
  · intro i j hj; exact marked_vortex_nested_graph Q i.val j.val (by omega)
  · intro i j hj; exact (marked_vortex_nested_raw_restriction Q i.val j.val (by omega) σ).symm
  · intro i j hj; exact (marked_vortex_nested_spokes Q i.val j.val (by omega) H).symm
  · intro i; exact marked_vortex_nested_graph Q 0 i.val (by omega)
  · intro i; exact (marked_vortex_nested_raw_restriction Q 0 i.val (by omega) σ).symm
  · intro i; exact (marked_vortex_nested_spokes Q 0 i.val (by omega) H).symm
  · intro i j hj v; exact (marked_vortex_nested_vertex_comp Q 0 i.val j.val (by omega) (by omega) (by omega) v).symm
  · intro i j hj u; exact (marked_vortex_nested_hub_comp Q 0 i.val j.val (by omega) (by omega) (by omega) u).symm
  · intro v; apply Subtype.ext; rfl
  · intro u; apply Subtype.ext; rfl
theorem marked_vortex_finite_sample_chain_exists
    (Q:Vortex U G D β ε m) (π:Equiv.Perm V)
    (hπ:∀ i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop) (count:ℕ) (hc:0<count):
    Nonempty (MarkedVortexFiniteSampleChain Q π hπ σ H count hc) :=
  ⟨marked_vortex_finite_sample_chain Q π hπ σ H count hc⟩
end Oberwolfach
