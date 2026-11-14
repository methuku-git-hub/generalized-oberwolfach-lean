module

public import Oberwolfach.TriangleTransformerFiniteResource
public import Oberwolfach.OrdinaryRecursiveBudgetSelection

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

theorem triangle_sequential_resource_transformers (β:ℝ) (hβ:0<β):
    ∃ ε₀:ℝ,0<ε₀ ∧ ∀ q l:ℕ,∃ N₀ K₀:ℕ,
    ∀ (V U:Type) [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U],
    N₀≤Fintype.card V→K₀≤Fintype.card U→
    ∀ (G:Fin l→SimpleGraph V) (Q:SimpleGraph V) (H₀:Fin l→V→U→Prop) (H:V→U→Prop)
      (φ:Fin l→V→V) (ψ:Fin l→U→U) (R:Finset V) (B:Finset U)
      (R₀:Fin l→Finset V) (B₀:Fin l→Finset U) (L:Finset (Sym2 V⊕(V×U))),
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
    ∃ T:Fin l→Finset (Sym2 V⊕(V×U)),
      (∀ i,IsResourceTransformer (ordinaryWheelResources (P:=Q) (F:=⊥) (Hbase:=H) (r:=3))
        (ordinaryHostResources (G i) (H₀ i)) (transformerImageResources (G i) (H₀ i) (φ i) (ψ i)) (T i) ∧
        T i⊆ordinaryHostResources Q H ∧
        (ordinaryResourceRows (T i)).card+(ordinaryResourceHubs (T i)).card≤K₀ ∧ Disjoint (T i) L) ∧
      (∀ i j,i≠j→Disjoint (T i) (T j)) :=by
  obtain ⟨ε₀,hε₀,hbase⟩:=triangle_transformer_finite_resource_uniform β hβ
  refine ⟨ε₀,hε₀,?_⟩
  intro q l
  choose N K hK using hbase
  let budget:=ordinaryRecursiveBudget q K
  let stage:Fin l→ℕ:=fun i=>q+budget i.val
  let N₀:=Finset.univ.sup (fun i:Fin l=>N (stage i))
  let K₀:=Finset.univ.sup (fun i:Fin l=>K (stage i))
  refine ⟨N₀,K₀,?_⟩
  intro V U _ _ _ _ hn hU G Q H₀ H φ ψ R B R₀ B₀ L hR hB hLr hLu hsize hsupp hbalance hdiv hroot hcross hu hQ hφQ hφedge hψedge hH hBroot hdeg ε hε hεsmall hnearV hnearU
  let P:Fin l→Finset (Sym2 V⊕(V×U))→Prop:=fun i T=>
    IsResourceTransformer (ordinaryWheelResources (P:=Q) (F:=⊥) (Hbase:=H) (r:=3))
      (ordinaryHostResources (G i) (H₀ i)) (transformerImageResources (G i) (H₀ i) (φ i) (ψ i)) T ∧
      T⊆ordinaryHostResources Q H
  obtain ⟨T,hT,hdis⟩:=ordinary_sequential_recursive_budget_selection l q K L hLr hLu P (by
    intro i L' hr hu'
    let W:=R∪ordinaryResourceRows L'
    let C:=B∪ordinaryResourceHubs L'
    have hW:W.card≤3*stage i:=by
      have hh:=Finset.card_union_le R (ordinaryResourceRows L')
      dsimp [W,stage,budget] at *
      omega
    have hC:C.card≤3*stage i:=by
      have hh:=Finset.card_union_le B (ordinaryResourceHubs L')
      dsimp [C,stage,budget] at *
      omega
    have hR':R.card≤3*stage i:=by dsimp [stage];omega
    have hR₀:(R₀ i).card≤stage i:=by have hh:=(hsize i).1;dsimp [stage];omega
    have hB₀:(B₀ i).card≤stage i:=by have hh:=(hsize i).2;dsimp [stage];omega
    have hn':N (stage i)≤Fintype.card V:=(Finset.le_sup (s:=Finset.univ) (f:=fun i:Fin l=>N (stage i)) (Finset.mem_univ i)).trans hn
    have hU':K (stage i)≤Fintype.card U:=(Finset.le_sup (s:=Finset.univ) (f:=fun i:Fin l=>K (stage i)) (Finset.mem_univ i)).trans hU
    obtain ⟨T,htrans,hhost,hcard,hRR,hRC,havoidR,havoidC⟩:=hK (stage i) V U hn' hU'
      (G i) Q (H₀ i) H (φ i) (ψ i) R W (R₀ i) C (B₀ i) Finset.subset_union_left
      (hbalance i) (hdiv i) (hroot i) (hcross i) (hu i) (hQ i) (hφQ i) (hφedge i) (hψedge i) (hH i)
      (fun e=>⟨Finset.mem_union_left _ (hBroot i e).1,Finset.mem_union_left _ (hBroot i e).2⟩)
      hdeg ε hε hεsmall hnearV hnearU hR₀ hB₀ (hsupp i) hW hR' hC
    have hdis:Disjoint T L':=by
      apply ordinary_transformer_forbidden_edges T L' R W C
        Finset.subset_union_right Finset.subset_union_right
      · intro v hv w he
        apply havoidR v _ hv
        exact Finset.mem_biUnion.mpr ⟨Sum.inl s(v,w),he,by simp⟩
      · intro v hv u he
        apply havoidR v _ hv
        exact Finset.mem_biUnion.mpr ⟨Sum.inr (v,u),he,by simp⟩
      · exact hRR
      · exact hRC
    exact ⟨T,⟨htrans,hhost⟩,hcard,hdis⟩)
  refine ⟨T,?_,hdis⟩
  intro i
  have hk:K (stage i)≤K₀:=Finset.le_sup (s:=Finset.univ) (f:=fun i:Fin l=>K (stage i)) (Finset.mem_univ i)
  exact ⟨(hT i).1.1,(hT i).1.2,(hT i).2.1.trans hk,(hT i).2.2⟩
end Oberwolfach
