module

public import Oberwolfach.TriangleSequentialTransformers
public import Oberwolfach.OrdinaryRecursiveBudgetSelection
public import Oberwolfach.OrdinaryFiniteTransformerAssembly
public import Oberwolfach.OrdinaryFiniteAbsorberBounds

@[expose] public section
/-! Choose a bounded sequence of triangle transformers in one host, with
thresholds fixed before the host and avoidance of all earlier resources. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem triangle_four_resource_transformer_absorber (β:ℝ) (hβ:0<β):
    ∃ ε₀:ℝ,0<ε₀ ∧ ∀ q:ℕ,∃ N₀ K₀:ℕ,
    ∀ (V U:Type) [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U],
    N₀≤Fintype.card V→K₀≤Fintype.card U→
    ∀ (G:Fin 4→SimpleGraph V) (Q:SimpleGraph V) (H₀:Fin 4→V→U→Prop) (H:V→U→Prop)
      (φ:Fin 4→V→V) (ψ:Fin 4→U→U) (R:Finset V) (B:Finset U)
      (R₀:Fin 4→Finset V) (B₀:Fin 4→Finset U) (L:Finset (Sym2 V⊕(V×U))),
    R.card≤q→B.card≤q→(ordinaryResourceRows L).card≤q→(ordinaryResourceHubs L).card≤q→
    (∀ i,(R₀ i).card≤q ∧ (B₀ i).card≤q) →
    (∀ i v u,H₀ i v u→v∈R₀ i∧u∈B₀ i) →
    (∀ i v,(G i).degree v=2*((Finset.univ:Finset U).filter (H₀ i v)).card) →
    (∀ i u,3∣((Finset.univ:Finset V).filter (fun v=>H₀ i v u)).card) →
    (∀ i,∀ v∈(G i).support,v∈R∧φ i v∈R) →
    (∀ i,∀ v∈(G i).support,∀ w∈(G i).support,φ i v≠w) →
    (∀ i u,(∃v,H₀ i v u)→u≠ψ i u) →
    (∀ i,G i≤Q) → (∀ i v w,(G i).Adj v w→Q.Adj (φ i v) (φ i w)) →
    (∀ i,Function.Injective (fun e:(G i).edgeFinset=>s(φ i e.val.out.1,φ i e.val.out.2))) →
    (∀ i,Function.Injective (fun e:{e:V×U // H₀ i e.1 e.2}=>(φ i e.val.1,ψ i e.val.2))) →
    (∀ i v u,H₀ i v u→H v u∧H (φ i v) (ψ i u)) →
    (∀ i (e:{e:V×U // H₀ i e.1 e.2}),e.val.2∈B∧ψ i e.val.2∈B) →
    (∀ v,(3/4+β)*(Fintype.card V:ℝ)≤(Q.degree v:ℝ)) →
    ∀ ε:ℝ,0≤ε→ε≤ε₀→
    (∀ u,(((Finset.univ:Finset V).filter (fun v=>¬H v u)).card:ℝ)≤ε*(Fintype.card V:ℝ)) →
    (∀ v,(((Finset.univ:Finset U).filter (fun u=>¬H v u)).card:ℝ)≤ε*(Fintype.card U:ℝ)) →
    ∀ (D:ℕ→Finset (Sym2 V⊕(V×U))) (original extra:Finset (Sym2 V⊕(V×U))),
    D 0=original∪extra→Disjoint original extra→
    HasResourceDecomposition (ordinaryWheelResources (P:=Q) (F:=⊥) (Hbase:=H) (r:=3)) extra→
    HasResourceDecomposition (ordinaryWheelResources (P:=Q) (F:=⊥) (Hbase:=H) (r:=3)) (D 4)→
    (∀ j:Fin 4,
      (ordinaryHostResources (G j) (H₀ j)=D j.val∧transformerImageResources (G j) (H₀ j) (φ j) (ψ j)=D (j.val+1))∨
      (ordinaryHostResources (G j) (H₀ j)=D (j.val+1)∧transformerImageResources (G j) (H₀ j) (φ j) (ψ j)=D j.val))→
    (∀ i,i≤4→∀ j,j≤4→i≠j→Disjoint (D i) (D j))→
    (∀ i,i≤4→D i⊆L)→
    (∀ i,i≤4→D i⊆ordinaryHostResources Q H)→
    ∃ T:Fin 4→Finset (Sym2 V⊕(V×U)),
      (∀ i,IsResourceTransformer (ordinaryWheelResources (P:=Q) (F:=⊥) (Hbase:=H) (r:=3))
        (ordinaryHostResources (G i) (H₀ i)) (transformerImageResources (G i) (H₀ i) (φ i) (ψ i)) (T i) ∧
        T i⊆ordinaryHostResources Q H ∧
        (ordinaryResourceRows (T i)).card+(ordinaryResourceHubs (T i)).card≤K₀ ∧ Disjoint (T i) L) ∧
      (∀ i j,i≠j→Disjoint (T i) (T j)) ∧
      IsResourceAbsorber (ordinaryWheelResources (P:=Q) (F:=⊥) (Hbase:=H) (r:=3)) original
        (extra∪transformerChainEdges D (finiteTransformerAt T) 4∪D 4) ∧
      let C:=extra∪transformerChainEdges D (finiteTransformerAt T) 4∪D 4;
      C⊆ordinaryHostResources Q H ∧ (ordinaryResourceRows C).card≤q+4*K₀ ∧
        (ordinaryResourceHubs C).card≤q+4*K₀ :=by
  obtain ⟨ε₀,hε₀,hbase⟩:=triangle_sequential_resource_transformers β hβ
  refine ⟨ε₀,hε₀,?_⟩
  intro q
  obtain ⟨N₀,K₀,hseq⟩:=hbase q 4
  refine ⟨N₀,K₀,?_⟩
  intro V U _ _ _ _ hn hU G Q H₀ H φ ψ R B R₀ B₀ L hR hB hLr hLu hsize hsupp hbalance hdiv hroot hcross hu hQ hφQ hφedge hψedge hH hBroot hdeg ε hε hεsmall hnearV hnearU D original extra hfirst hattach hextra hfinal hends hDD hD hDhost
  obtain ⟨T,hT,hdis⟩:=hseq V U hn hU G Q H₀ H φ ψ R B R₀ B₀ L hR hB hLr hLu hsize hsupp hbalance hdiv hroot hcross hu hQ hφQ hφedge hψedge hH hBroot hdeg ε hε hεsmall hnearV hnearU
  refine ⟨T,hT,hdis,?_,?_⟩
  · exact finite_four_transformer_absorber _ D
      (fun j=>ordinaryHostResources (G j) (H₀ j))
      (fun j=>transformerImageResources (G j) (H₀ j) (φ j) (ψ j)) T original extra L
      hfirst hattach hextra hfinal (fun j=>(hT j).1) hends hDD hdis
      (fun j=>(hT j).2.2.2) hD
  · exact finite_four_absorber_bounds D T original extra L (ordinaryHostResources Q H) q K₀
      hfirst hD hDhost (fun i=>(hT i).2.1) hLr hLu (fun i=>(hT i).2.2.1)
end Oberwolfach
