module

public import Oberwolfach.TriangleFinitePairTransformer
public import Oberwolfach.OrdinaryProfileTransformerCompletion

@[expose] public section
/-! Convert the finite-pair triangle resource transformer to actual
extended rim/spoke subgraphs and their two wheel decompositions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem triangle_finite_pair_extended_transformer (β:ℝ) (hβ:0<β):
    ∃ ε₀:ℝ,0<ε₀ ∧ ∀ q:ℕ,∃ N₀ K₀:ℕ,
    ∀ (V₀ U₀ V₁ U₁ V U:Type) [Fintype V₀] [DecidableEq V₀] [Fintype U₀] [DecidableEq U₀]
      [Fintype V₁] [DecidableEq V₁] [Fintype U₁] [DecidableEq U₁]
      [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U],
    N₀≤Fintype.card V→K₀≤Fintype.card U→
    ∀ (G₀:SimpleGraph V₀) (Hsrc:V₀→U₀→Prop) (G₁:SimpleGraph V₁) (Htgt:V₁→U₁→Prop)
      (i:V₀↪V) (j:V₁↪V) (k:U₀↪U) (l:U₁↪U) (f:V₀→V₁) (g:U₀→U₁)
      (Q:SimpleGraph V) (H:V→U→Prop) (ZV:Finset V) (ZU:Finset U),
    Fintype.card V₀≤q → Fintype.card U₀≤q → Fintype.card V₁≤q → Fintype.card U₁≤q →
    ZV.card≤q → ZU.card≤q →
    (∀ v,G₀.degree v=2*(Finset.univ.filter (Hsrc v)).card) →
    (∀ u,3∣(Finset.univ.filter (fun v=>Hsrc v u)).card) →
    Set.InjOn (ordinaryPairResourceMap f g) (ordinaryHostResources G₀ Hsrc) →
    (ordinaryHostResources G₀ Hsrc).image (ordinaryPairResourceMap f g)=ordinaryHostResources G₁ Htgt →
    (∀ v w,i v≠j w) → (∀ u u',k u≠l u') →
    G₀.map i≤Q → G₁.map j≤Q →
    (∀ v u,Hsrc v u→H (i v) (k u)) → (∀ v u,Htgt v u→H (j v) (l u)) →
    (∀ v,(3/4+β)*(Fintype.card V:ℝ)≤(Q.degree v:ℝ)) →
    ∀ ε:ℝ,0≤ε→ε≤ε₀→
    (∀ u,(((Finset.univ:Finset V).filter (fun v=>¬H v u)).card:ℝ)≤ε*(Fintype.card V:ℝ)) →
    (∀ v,(((Finset.univ:Finset U).filter (fun u=>¬H v u)).card:ℝ)≤ε*(Fintype.card U:ℝ)) →
    let G:=G₀.map i
    let H₀:=ordinaryMappedSpokes Hsrc i k
    let P:=G₁.map j
    let H₁:=ordinaryMappedSpokes Htgt j l
    let R:Finset V:=(Finset.univ.image i)∪(Finset.univ.image j)
    let B:Finset U:=(Finset.univ.image k)∪(Finset.univ.image l)
    ∃ T:Finset (Sym2 V⊕(V×U)),
      T⊆ordinaryHostResources Q H ∧
      (ordinaryPhysicalGraph (ordinaryResourceRim Q T) (fun v u=>Sum.inr (v,u)∈T)).support.toFinset.card≤K₀ ∧
      (∀ v∈R,∀ w∈R,Sum.inl s(v,w)∉T) ∧
      (∀ v∈R,∀ z∈B,Sum.inr (v,z)∉T) ∧
      (∀ v∈ordinaryResourceRows T,v∈ZV→v∈R) ∧
      (∀ z∈ordinaryResourceHubs T,z∈ZU→z∈B) ∧
      let D:=ordinaryResourceRim Q T
      let S:V→U→Prop:=fun v u=>Sum.inr (v,u)∈T
      D≤Q ∧ (∀ v u,S v u→H v u) ∧
      Disjoint D G ∧ Disjoint D P ∧
      (∀ v u,¬(S v u∧H₀ v u)) ∧ (∀ v u,¬(S v u∧H₁ v u)) ∧
      HasOrdinaryWheelDecomposition (D⊔G) (fun v u=>S v u∨H₀ v u) 3 ∧
      HasOrdinaryWheelDecomposition (D⊔P) (fun v u=>S v u∨H₁ v u) 3 :=by
  obtain ⟨ε₀,hε₀,huniform⟩:=triangle_finite_pair_transformer β hβ
  refine ⟨ε₀,hε₀,?_⟩
  intro q
  obtain ⟨N₀,K₀,hbase⟩:=huniform q
  refine ⟨N₀,K₀,?_⟩
  intro V₀ U₀ V₁ U₁ V U _ _ _ _ _ _ _ _ _ _ _ _ hn hm
    G₀ Hsrc G₁ Htgt i j k l f g Q H ZV ZU hV₀ hU₀ hV₁ hU₁ hZV hZU hbalance hdiv hinj him hdisV hdisU hsrcQ htgtQ hsrcH htgtH hdeg ε hε hεsmall hnearV hnearU G H₀ P H₁ R B
  obtain ⟨T,hT,hTQ,hcard,hrootR,hrootS,havoidR,havoidU⟩:=hbase V₀ U₀ V₁ U₁ V U hn hm
    G₀ Hsrc G₁ Htgt i j k l f g Q H ZV ZU hV₀ hU₀ hV₁ hU₁ hZV hZU hbalance hdiv hinj him hdisV hdisU hsrcQ htgtQ hsrcH htgtH hdeg ε hε hεsmall hnearV hnearU
  have hgraph:=ordinary_transformer_graph_realization Q ⊥ G P H H₀ H₁ 3 T hTQ hT
  obtain ⟨hQ,hH,hDG,hDP,hSH₀,hSH₁,hdec₀,hdec₁⟩:=hgraph
  refine ⟨T,hTQ,hcard,hrootR,hrootS,havoidR,havoidU,hQ,hH,hDG,hDP,hSH₀,hSH₁,?_,?_⟩
  · exact ordinary_host_decomposition_forget _ hdec₀
  · exact ordinary_host_decomposition_forget _ hdec₁
end Oberwolfach
