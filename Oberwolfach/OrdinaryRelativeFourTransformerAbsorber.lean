module

public import Oberwolfach.OrdinaryRelativeTransformerFamily
public import Oberwolfach.OrdinaryFiniteTransformerAssembly

@[expose] public section

/-! The four actual transformers of an embedded ordinary diagram are
constructed from the original profiles, then assembled into an absorber.
The finite diagram's embeddings and its end decomposition remain explicit
inputs; transformer existence and mutual edge-disjointness are conclusions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
set_option maxHeartbeats 22000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {Tpl:Type} [Fintype Tpl] [DecidableEq Tpl]

 theorem ordinary_relative_four_transformer_absorber (r:ℕ) (hr:3≤r)
    (Tpls:Tpl→VertexAbsorberTemplate r) (β a b B₀:ℝ)
    (hβ:0<β) (ha:0<a) (hb:0<b) (hB₀:0<B₀):
    ∃ η ε:ℝ,0<η∧0<ε∧ε≤β/4∧∀ m:ℕ,∃ t:ℕ,1≤t∧∀ f:ℕ,∀ d:ℝ,0≤d→
      ∃ n₀:ℕ,
      ∀ (V U:Type) [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U],
      n₀≤Fintype.card V→
      ∀ (G:Fin 4→SimpleGraph V) (Q F:SimpleGraph V) (H₀:Fin 4→V→U→Prop) (H:V→U→Prop) (φ:Fin 4→V→V) (ψ:Fin 4→U→U)
      (A Z R W:Finset V) (B:Finset U) (L:Finset (Sym2 V⊕(V×U))),
      A=Finset.univ\Z→(Z.card:ℝ)≤ε*Fintype.card V→
      ordinaryResourceRows L⊆W→ ordinaryResourceHubs L⊆B→R⊆W→
      R.card≤m→W.card≤f→(B.card:ℝ)≤ε*Fintype.card V+f→
      (∀ j:Fin 4,∀ v,(G j).degree v=2*((Finset.univ:Finset U).filter (H₀ j v)).card)→
      (∀ j:Fin 4,∀ u,r∣((Finset.univ:Finset V).filter (fun v=>H₀ j v u)).card)→
      (∀ j:Fin 4,∀ u,((Finset.univ:Finset V).filter (fun v=>H₀ j v u)).card≤m)→
      (∀ j:Fin 4,Fintype.card {u:U // ∃ v,H₀ j v u}≤m)→
      (∀ j:Fin 4,∀ v∈(G j).support,v∈R∧φ j v∈R)→
      (∀ j:Fin 4,∀ v∈(G j).support,∀ w∈(G j).support,φ j v≠w)→
      (∀ j:Fin 4,∀ u,(∃ v,H₀ j v u)→u≠ψ j u)→
      (∀ j:Fin 4,G j≤Q)→(∀ j:Fin 4,∀ v w,(G j).Adj v w→Q.Adj (φ j v) (φ j w))→
      (∀ j:Fin 4,Function.Injective (fun i:(G j).edgeFinset=>s(φ j i.val.out.1,φ j i.val.out.2)))→
      (∀ j:Fin 4,Function.Injective (fun i:{e:V×U // H₀ j e.1 e.2}=>(φ j i.val.1,ψ j i.val.2)))→
      (∀ j:Fin 4,∀ v u,H₀ j v u→H v u∧H (φ j v) (ψ j u))→
      (∀ j:Fin 4,∀ e:{e:V×U // H₀ j e.1 e.2},e.val.2∈B∧ψ j e.val.2∈B)→
      (∀ j:Fin 4,∀ v w,(G j).Adj v w→∀ a∈({v,w,φ j v,φ j w}:Finset V),
        ∀ c∈({v,w,φ j v,φ j w}:Finset V),¬F.Adj a c)→
      (∀ v,(F.degree v:ℝ)≤d)→
      (∀ v w,β*Fintype.card V≤((Q.neighborFinset v∩Q.neighborFinset w).card:ℝ))→
      (∀ u u' v w,β*Fintype.card V≤(((Finset.univ.filter (fun a=>H a u∧H a u'))∩Q.neighborFinset v∩Q.neighborFinset w).card:ℝ))→
      (r=4→∀ v w x,β*Fintype.card V≤((Q.neighborFinset v∩Q.neighborFinset w∩Q.neighborFinset x).card:ℝ))→
      (r=3→∀ w x y z,β*Fintype.card V≤((Finset.univ.filter (fun a=>Q.Adj w a∧Q.Adj x a∧Q.Adj y a∧Q.Adj z a)).card:ℝ))→
      (r=3→∀ u u' w x y z,β*Fintype.card V≤((Finset.univ.filter (fun a=>H a u∧H a u'∧Q.Adj w a∧Q.Adj x a∧Q.Adj y a∧Q.Adj z a)).card:ℝ))→
      (∀ T:Finset V,T.card≤r+6→(∀ v∈T,∀ w∈T,¬F.Adj v w)→
        β*Fintype.card V≤((common Finset.univ T (fun v=>Finset.univ.filter (H v))).card:ℝ))→
      (∀ j:Fin 4,∀ i:{u:U // ∃ v,H₀ j v u},β*Fintype.card V≤
        ((Finset.univ.filter (fun a=>H a i.val∧H a (ψ j i.val))).card:ℝ))→
      ∀ w:∀ j:Fin 4,∀ i:{u:U // ∃ v,H₀ j v u},
        LocalOrdinaryCycle Q F (Finset.univ.filter (fun a=>H a i.val∧H a (ψ j i.val))) r→ℝ,
      (∀ j i C,b/(Fintype.card V:ℝ)^(r-1)≤w j i C∧w j i C≤B₀/(Fintype.card V:ℝ)^(r-1))→
      (∀ j:Fin 4,∀ i:{u:U // ∃ v,H₀ j v u},∀ v∈Finset.univ.filter (fun a=>H a i.val∧H a (ψ j i.val)),
        |1-hypergraphWeightedDegree localOrdinaryVertices (w j i) v|≤η)→
      (∀ j:Fin 4,∀ i:{u:U // ∃ v,H₀ j v u},∀ X:Finset V,X⊆Finset.univ.filter (fun a=>H a i.val∧H a (ψ j i.val))→X.card=r→
        a*(Fintype.card V:ℝ)^(r*r)≤Fintype.card
          (LabelledAbsorberFamily (localOrdinaryVertices (Q:=Q) (F:=F)
            (T:=Finset.univ.filter (fun a=>H a i.val∧H a (ψ j i.val))) (r:=r)) Tpls X))→
      ∀ (D:ℕ→Finset (Sym2 V⊕(V×U))) (original extra:Finset (Sym2 V⊕(V×U))),
      D 0=original∪extra→Disjoint original extra→
      HasResourceDecomposition (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=r)) extra→
      HasResourceDecomposition (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=r)) (D 4)→
      (∀ j:Fin 4,
        (ordinaryHostResources (G j) (H₀ j)=D j.val∧transformerImageResources (G j) (H₀ j) (φ j) (ψ j)=D (j.val+1))∨
        (ordinaryHostResources (G j) (H₀ j)=D (j.val+1)∧transformerImageResources (G j) (H₀ j) (φ j) (ψ j)=D j.val))→
      (∀ i,i≤4→∀ j,j≤4→i≠j→Disjoint (D i) (D j))→
      (∀ i,i≤4→D i⊆L)→
      ∃ K:Fin 4→Finset (Sym2 V⊕(V×U)),
        (∀ j,IsResourceTransformer (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=r))
          (ordinaryHostResources (G j) (H₀ j)) (transformerImageResources (G j) (H₀ j) (φ j) (ψ j)) (K j) ∧
          K j⊆ordinaryHostResources Q H ∧ ordinaryResourceRows (K j)⊆R∪A ∧
          (∀ v∈ordinaryResourceRows (K j),v∈W→v∈R) ∧
          (∀ u∈ordinaryResourceHubs (K j),u∈B→∃ i:{u:U // ∃ v,H₀ j v u},u=i.val∨u=ψ j i.val) ∧
          (ordinaryResourceRows (K j)).card≤m*r*(t+5*m) ∧
          (ordinaryResourceHubs (K j)).card≤m*(m+2) ∧ Disjoint (K j) L) ∧
        (∀ i j,i≠j→Disjoint (K i) (K j)) ∧
        (ordinaryResourceRows (Finset.univ.biUnion K)).card≤4*(m*r*(t+5*m)) ∧
        (ordinaryResourceHubs (Finset.univ.biUnion K)).card≤4*(m*(m+2)) ∧
        IsResourceAbsorber (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=r)) original
          (extra∪transformerChainEdges D (finiteTransformerAt K) 4∪D 4) := by
  obtain ⟨η,ε,hη,hε,hεβ,hfamily⟩:=ordinary_relative_transformer_family r hr Tpls β a b B₀ hβ ha hb hB₀
  refine ⟨η,ε,hη,hε,hεβ,?_⟩
  intro m
  obtain ⟨t,ht,hfamily⟩:=hfamily m 4
  refine ⟨t,ht,?_⟩
  intro f d hd
  obtain ⟨n₀,hfamily⟩:=hfamily f d hd
  refine ⟨n₀,?_⟩
  intro V U _ _ _ _ hn G Q F H₀ H φ ψ A Z R W B L hA hZ hrows hhubs hRW hRcard hWcard hBcard
    hbalance hdiv hq hnU hroot hcross hu hQ hφQ hφedge hψedge hH hB hFroots hF
    hcount hpair hthree hfour hspfour hhub hT w hw herr habs D original extra hfirst hattach hextra hfinal hends hDD hD
  obtain ⟨K,hK,hdis,hrow,hhubc⟩:=hfamily V U hn G Q F H₀ H φ ψ A Z R W B L hA hZ hrows hhubs hRW hRcard hWcard hBcard
    hbalance hdiv hq hnU hroot hcross hu hQ hφQ hφedge hψedge hH hB hFroots hF
    hcount hpair hthree hfour hspfour hhub hT w hw herr habs
  refine ⟨K,hK,hdis,hrow,hhubc,?_⟩
  exact finite_four_transformer_absorber _ D
    (fun j=>ordinaryHostResources (G j) (H₀ j))
    (fun j=>transformerImageResources (G j) (H₀ j) (φ j) (ψ j)) K original extra L
    hfirst hattach hextra hfinal (fun j=>(hK j).1) hends hDD hdis
    (fun j=>(hK j).2.2.2.2.2.2.2) hD

end Oberwolfach
