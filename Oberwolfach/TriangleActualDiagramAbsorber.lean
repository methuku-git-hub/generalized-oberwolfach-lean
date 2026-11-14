module

public import Oberwolfach.TriangleFourTransformerAbsorber
public import Oberwolfach.OrdinaryDiagramAssemblyBounds

@[expose] public section
/-! Instantiate the four-transformer construction on the actual finite
ordinary absorber diagram. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem triangle_actual_diagram_absorber (β:ℝ) (hβ:0<β):
  ∃ ε₀:ℝ,0<ε₀ ∧ ∀ q:ℕ,∃ N₀ K₀:ℕ,
  ∀ (V U:Type) [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U],
    N₀≤Fintype.card V→K₀≤Fintype.card U→
  ∀ (Q:SimpleGraph V) (H:V→U→Prop) (M:ℕ)
    (original:Finset (Sym2 V⊕(V×U))) (A W R₀:Finset V) (B₀ O:Finset U)
    (D:OrdinaryHostDiagram 3 M Q ⊥ H original A W R₀ B₀ O)
    (L:Finset (Sym2 V⊕(V×U))),
    5*M≤q→(ordinaryResourceRows L).card≤q→(ordinaryResourceHubs L).card≤q→
    (∀ i,D.D i⊆L)→ ordinaryRootResources (R₀∪W) B₀⊆L→
    (∀ v,(3/4+β)*(Fintype.card V:ℝ)≤(Q.degree v:ℝ))→
  ∀ ε:ℝ,0≤ε→ε≤ε₀→
    (∀ u,(((Finset.univ:Finset V).filter (fun v=>¬H v u)).card:ℝ)≤ε*(Fintype.card V:ℝ))→
    (∀ v,(((Finset.univ:Finset U).filter (fun u=>¬H v u)).card:ℝ)≤ε*(Fintype.card U:ℝ))→
  ∃ T:Fin 4→Finset (Sym2 V⊕(V×U)),
    (∀ i,IsResourceTransformer (ordinaryWheelResources (P:=Q) (F:=⊥) (Hbase:=H) (r:=3))
      (ordinaryHostResources (D.T i).G (D.T i).K)
      (transformerImageResources (D.T i).G (D.T i).K (D.T i).φ (D.T i).ψ) (T i) ∧
      T i⊆ordinaryHostResources Q H ∧
      (ordinaryResourceRows (T i)).card+(ordinaryResourceHubs (T i)).card≤K₀ ∧ Disjoint (T i) L) ∧
    (∀ i j,i≠j→Disjoint (T i) (T j)) ∧
    IsResourceAbsorber (ordinaryWheelResources (P:=Q) (F:=⊥) (Hbase:=H) (r:=3)) original
      (ordinaryDiagramAbsorberEdges D T) ∧
    ordinaryDiagramAbsorberEdges D T⊆ordinaryHostResources Q H ∧
    (ordinaryResourceRows (ordinaryDiagramAbsorberEdges D T)).card≤q+4*K₀ ∧
    (ordinaryResourceHubs (ordinaryDiagramAbsorberEdges D T)).card≤q+4*K₀ ∧
    Disjoint (ordinaryDiagramAbsorberEdges D T) (ordinaryRootResources (R₀∪W) B₀) :=by
  obtain ⟨ε₀,hε₀,hbase⟩:=triangle_four_resource_transformer_absorber β hβ
  refine ⟨ε₀,hε₀,?_⟩
  intro q
  obtain ⟨N₀,K₀,hfour⟩:=hbase q
  refine ⟨N₀,K₀,?_⟩
  intro V U _ _ _ _ hn hU Q H M original A W R₀ B₀ O D L hM hLr hLu hL hrootL hdeg ε hε hεsmall hnearV hnearU
  let G:Fin 4→SimpleGraph V:=fun i=>(D.T i).G
  let H₀:Fin 4→V→U→Prop:=fun i=>(D.T i).K
  let φ:Fin 4→V→V:=fun i=>(D.T i).φ
  let ψ:Fin 4→U→U:=fun i=>(D.T i).ψ
  let S:=ordinaryResourceRows L
  let B:=ordinaryResourceHubs L
  have hsrc (i:Fin 4):ordinaryHostResources (G i) (H₀ i)⊆L:=by
    dsimp [G,H₀]
    rw [D.source]
    fin_cases i <;> simp only [Matrix.cons_val_zero,Matrix.cons_val_succ] <;> exact hL _
  have hsupp:∀ i v u,H₀ i v u→v∈S∧u∈B:=by
    intro i v u h
    have he:Sum.inr (v,u)∈L:=hsrc i ((ordinaryHostResources_spoke _ _ _ _).mpr h)
    exact ⟨Finset.mem_biUnion.mpr ⟨_,he,by simp [S,ordinaryResourceRows]⟩,
      Finset.mem_biUnion.mpr ⟨_,he,by simp [B,ordinaryResourceHubs]⟩⟩
  have hfirst:finiteFiveAt D.D 0=original∪D.extra:=by simpa [finiteFiveAt] using D.first
  have hD:∀ i,i≤4→finiteFiveAt D.D i⊆L:=by
    intro i hi
    rw [show finiteFiveAt D.D i=D.D ⟨i,by omega⟩ from finiteFiveAt_apply D.D ⟨i,by omega⟩]
    exact hL _
  have hDhost:∀ i,i≤4→finiteFiveAt D.D i⊆ordinaryHostResources Q H:=by
    intro i hi
    rw [show finiteFiveAt D.D i=D.D ⟨i,by omega⟩ from finiteFiveAt_apply D.D ⟨i,by omega⟩]
    exact D.host _
  have hfinal:HasResourceDecomposition (ordinaryWheelResources (P:=Q) (F:=⊥) (Hbase:=H) (r:=3)) (finiteFiveAt D.D 4):=by
    simpa [finiteFiveAt] using D.last_decomp
  have hBroot:∀ i (e:{e:V×U // H₀ i e.1 e.2}),e.val.2∈D.hubs∧ψ i e.val.2∈D.hubs:=by
    intro i e
    exact D.active_hubs i ⟨e.val.2,⟨e.val.1,e.property⟩⟩
  obtain ⟨T,hT,hdis,habs,hbounds⟩:=hfour V U hn hU G Q H₀ H φ ψ D.rows D.hubs
    (fun _=>S) (fun _=>B) L (D.rows_card.trans hM) (D.hubs_card.trans hM) hLr hLu
    (fun _=>⟨hLr,hLu⟩) hsupp (fun i=>(D.T i).balance) (fun i=>(D.T i).div)
    (fun i=>(D.T i).roots) (fun i=>(D.T i).disjointRows) (fun i=>(D.T i).disjointHubs)
    (fun i=>(D.T i).sourceRim) (fun i=>(D.T i).targetRim) (fun i=>(D.T i).rimInj)
    (fun i=>(D.T i).spokeInj) (fun i=>(D.T i).hostSpokes) hBroot hdeg ε hε hεsmall hnearV hnearU
    (finiteFiveAt D.D) original D.extra hfirst D.first_disjoint D.extra_decomp hfinal D.chain_endpoints D.chain_disjoint hD hDhost
  refine ⟨T,hT,hdis,habs,hbounds.1,hbounds.2.1,hbounds.2.2,?_⟩
  change Disjoint (D.extra∪transformerChainEdges (finiteFiveAt D.D) (finiteTransformerAt T) 4∪D.D 4) _
  rw [←show finiteFiveAt D.D 4=D.D 4 from finiteFiveAt_apply D.D (4:Fin 5)]
  apply resource_absorber_chain_avoids _ _ _ _ _ D.extra_avoid _ _ (by omega)
  · intro i hi
    rw [show finiteTransformerAt T i=T ⟨i,hi⟩ from finiteTransformerAt_apply T ⟨i,hi⟩]
    exact ((hT ⟨i,hi⟩).2.2.2).mono_right hrootL
  · intro i hi hi4
    rw [show finiteFiveAt D.D i=D.D ⟨i,by omega⟩ from finiteFiveAt_apply D.D ⟨i,by omega⟩]
    exact D.avoid _ (by intro h;have hh:=congrArg Fin.val h;dsimp at hh;omega)
end Oberwolfach
