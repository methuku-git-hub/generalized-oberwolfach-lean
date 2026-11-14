module

public import Oberwolfach.TriangleTransformerFiniteResource
public import Oberwolfach.OrdinaryResourceSubgraphs

@[expose] public section
/-! Convert the uniform triangle resource transformer to the actual rim
and spoke subgraph, with both decompositions and its vertex-order bound. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem triangle_transformer_extended_graph_uniform
    (β:ℝ) (hβ:0<β):
    ∃ ε₀:ℝ,0<ε₀ ∧ ∀ q:ℕ,∃ N₀ K₀:ℕ,
    ∀ (V U:Type) [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U],
    N₀≤Fintype.card V→K₀≤Fintype.card U→
    ∀ (G Q:SimpleGraph V) (H₀ H:V→U→Prop) (φ:V→V) (ψ:U→U)
    (R W R₀:Finset V) (B B₀:Finset U) (hRW:R⊆W)
    (hbalance:∀ v,G.degree v=2*((Finset.univ:Finset U).filter (H₀ v)).card)
    (hdiv:∀ u,3∣((Finset.univ:Finset V).filter (fun v=>H₀ v u)).card)
    (hroot:∀ v∈G.support,v∈R∧φ v∈R)
    (hcross:∀ v∈G.support,∀ w∈G.support,φ v≠w)
    (hu:∀ u,(∃v,H₀ v u)→u≠ψ u)
    (hQ:G≤Q) (hφQ:∀ v w,G.Adj v w→Q.Adj (φ v) (φ w))
    (hφedge:Function.Injective (fun e:G.edgeFinset=>s(φ e.val.out.1,φ e.val.out.2)))
    (hψedge:Function.Injective (fun e:{e:V×U // H₀ e.1 e.2}=>(φ e.val.1,ψ e.val.2)))
    (hH:∀ v u,H₀ v u→H v u∧H (φ v) (ψ u))
    (hB:∀ e:{e:V×U // H₀ e.1 e.2},e.val.2∈B∧ψ e.val.2∈B)
    (hdeg:∀ v,(3/4+β)*(Fintype.card V:ℝ)≤(Q.degree v:ℝ))
    (ε:ℝ) (hε:0≤ε) (hεsmall:ε≤ε₀)
    (hnearV:∀ u,(((Finset.univ:Finset V).filter (fun v=>¬H v u)).card:ℝ)≤ε*(Fintype.card V:ℝ))
    (hnearU:∀ v,(((Finset.univ:Finset U).filter (fun u=>¬H v u)).card:ℝ)≤ε*(Fintype.card U:ℝ))
    (hR₀:R₀.card≤q) (hB₀:B₀.card≤q) (hsupport:∀ v u,H₀ v u→v∈R₀∧u∈B₀)
    (hw:W.card≤3*q) (hr:R.card≤3*q) (hb:B.card≤3*q),
    ∃ T:Finset (Sym2 V⊕(V×U)),
      IsResourceTransformer (ordinaryWheelResources (P:=Q) (F:=⊥) (Hbase:=H) (r:=3))
        (ordinaryHostResources G H₀) (transformerImageResources G H₀ φ ψ) T ∧
      T⊆ordinaryHostResources Q H ∧
      (ordinaryPhysicalGraph (ordinaryResourceRim Q T) (fun v u=>Sum.inr (v,u)∈T)).support.toFinset.card≤K₀ ∧
      (∀ v∈R,∀ w∈R,Sum.inl s(v,w)∉T) ∧
      (∀ v∈R,∀ z∈B,Sum.inr (v,z)∉T) ∧
      (∀ v∈ordinaryResourceRows T,v∈W→v∈R) ∧
      (∀ z∈ordinaryResourceHubs T,z∈B→∃ u,(∃x,H₀ x u) ∧ (z=u∨z=ψ u)) ∧
      let L':=ordinaryResourceRim Q (transformerImageResources G H₀ φ ψ)
      let H₁:V→U→Prop:=fun v u=>Sum.inr (v,u)∈transformerImageResources G H₀ φ ψ
      let P:=ordinaryResourceRim Q T
      let S:V→U→Prop:=fun v u=>Sum.inr (v,u)∈T
      P≤Q ∧ (∀ v u,S v u→H v u) ∧ Disjoint P G ∧ Disjoint P L' ∧
      (∀ v u,¬(S v u∧H₀ v u)) ∧ (∀ v u,¬(S v u∧H₁ v u)) ∧
      HasResourceDecomposition (ordinaryWheelResources (P:=Q) (F:=⊥) (Hbase:=H) (r:=3))
        (ordinaryHostResources (P⊔G) (fun v u=>S v u∨H₀ v u)) ∧
      HasResourceDecomposition (ordinaryWheelResources (P:=Q) (F:=⊥) (Hbase:=H) (r:=3))
        (ordinaryHostResources (P⊔L') (fun v u=>S v u∨H₁ v u)) :=by
  obtain ⟨ε₀,hε₀,huniform⟩:=triangle_transformer_finite_resource_uniform β hβ
  refine ⟨ε₀,hε₀,?_⟩
  intro q
  obtain ⟨N₀,K₀,hbase⟩:=huniform q
  refine ⟨N₀,K₀,?_⟩
  intro V U _ _ _ _ hn hm G Q H₀ H φ ψ R W R₀ B B₀ hRW hbalance hdiv hroot hcross hu hQ hφQ hφedge hψedge hH hB hdeg ε hε hεsmall hnearV hnearU hR₀ hB₀ hsupport hw hr hb
  obtain ⟨T,hT,hTS,hcard,hRroot,hSroot,hRavoid,hHavoid⟩:=hbase V U hn hm G Q H₀ H φ ψ R W R₀ B B₀
    hRW hbalance hdiv hroot hcross hu hQ hφQ hφedge hψedge hH hB hdeg ε hε hεsmall hnearV hnearU hR₀ hB₀ hsupport hw hr hb
  let Im:=transformerImageResources G H₀ φ ψ
  let L':=ordinaryResourceRim Q Im
  let H₁:V→U→Prop:=fun v u=>Sum.inr (v,u)∈Im
  have himage:Im⊆ordinaryHostResources Q H:=transformer_image_resources_subhost G Q H₀ H φ ψ hφQ
    (fun v u hv=>(hH v u hv).2)
  have heq:ordinaryHostResources L' H₁=Im:=(ordinary_resource_subgraph Q H Im himage).2.2
  have hT':IsResourceTransformer (ordinaryWheelResources (P:=Q) (F:=⊥) (Hbase:=H) (r:=3))
      (ordinaryHostResources G H₀) (ordinaryHostResources L' H₁) T:=by rw [heq];exact hT
  have hgraph:=ordinary_transformer_graph_realization Q ⊥ G L' H H₀ H₁ 3 T hTS hT'
  have hrows (v w:V) (he:Sum.inl s(v,w)∈T):v∈ordinaryResourceRows T∧w∈ordinaryResourceRows T:=by
    constructor <;> apply Finset.mem_biUnion.mpr
    · exact ⟨Sum.inl s(v,w),he,by simp⟩
    · exact ⟨Sum.inl s(v,w),he,by simp⟩
  have hsp (v:V) (u:U) (he:Sum.inr (v,u)∈T):v∈ordinaryResourceRows T∧u∈ordinaryResourceHubs T:=by
    constructor <;> apply Finset.mem_biUnion.mpr
    · exact ⟨Sum.inr (v,u),he,by simp⟩
    · exact ⟨Sum.inr (v,u),he,by simp⟩
  have horder: (ordinaryPhysicalGraph (ordinaryResourceRim Q T) (fun v u=>Sum.inr (v,u)∈T)).support.toFinset.card≤K₀:=
    (ordinary_resource_subgraph_order Q H T hTS (ordinaryResourceRows T) (ordinaryResourceHubs T) hrows hsp).trans hcard
  exact ⟨T,hT,hTS,horder,hRroot,hSroot,hRavoid,hHavoid,hgraph⟩
end Oberwolfach
