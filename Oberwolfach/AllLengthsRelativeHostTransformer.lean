module

public import Oberwolfach.OrdinaryRelativeHostTransformer
public import Oberwolfach.TriangleRelativeHostTransformer

@[expose] public section

/-! Combine the two proved geometric constructions. Four row neighbours
are required exactly in the triangular branch; the larger-cycle branch
retains its original two- and three-neighbour hypotheses. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {Tpl:Type} [Fintype Tpl] [DecidableEq Tpl]

 theorem all_lengths_relative_host_transformer (r:ℕ) (hr:3≤r)
    (Tpls:Tpl→VertexAbsorberTemplate r) (β a b B₀:ℝ)
    (hβ:0<β) (ha:0<a) (hb:0<b) (hB₀:0<B₀):
    ∃ η ε:ℝ,0<η∧0<ε∧ε≤β/4∧∀ m:ℕ,∃ t:ℕ,1≤t∧∀ f:ℕ,∀ d:ℝ,0≤d→
      ∃ n₀:ℕ,
      ∀ (V U:Type) [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U],
      n₀≤Fintype.card V→
      ∀ (G Q F:SimpleGraph V) (H₀ H:V→U→Prop) (φ:V→V) (ψ:U→U)
      (A Z R W:Finset V) (B:Finset U) (L:Finset (Sym2 V⊕(V×U))),
      A=Finset.univ\Z→(Z.card:ℝ)≤ε*Fintype.card V→
      ordinaryResourceRows L⊆W→ ordinaryResourceHubs L⊆B→R⊆W→
      R.card≤m→W.card≤f→(B.card:ℝ)≤ε*Fintype.card V+f→
      (∀ v,G.degree v=2*((Finset.univ:Finset U).filter (H₀ v)).card)→
      (∀ u,r∣((Finset.univ:Finset V).filter (fun v=>H₀ v u)).card)→
      (∀ u,((Finset.univ:Finset V).filter (fun v=>H₀ v u)).card≤m)→
      Fintype.card {u:U // ∃ v,H₀ v u}≤m→
      (∀ v∈G.support,v∈R∧φ v∈R)→
      (∀ v∈G.support,∀ w∈G.support,φ v≠w)→
      (∀ u,(∃ v,H₀ v u)→u≠ψ u)→
      G≤Q→(∀ v w,G.Adj v w→Q.Adj (φ v) (φ w))→
      Function.Injective (fun i:G.edgeFinset=>s(φ i.val.out.1,φ i.val.out.2))→
      Function.Injective (fun i:{e:V×U // H₀ e.1 e.2}=>(φ i.val.1,ψ i.val.2))→
      (∀ v u,H₀ v u→H v u∧H (φ v) (ψ u))→
      (∀ e:{e:V×U // H₀ e.1 e.2},e.val.2∈B∧ψ e.val.2∈B)→
      (∀ v w,G.Adj v w→∀ a∈({v,w,φ v,φ w}:Finset V),
        ∀ c∈({v,w,φ v,φ w}:Finset V),¬F.Adj a c)→
      (∀ v,(F.degree v:ℝ)≤d)→
      (∀ v w,β*Fintype.card V≤((Q.neighborFinset v∩Q.neighborFinset w).card:ℝ))→
      (∀ u u' v w,β*Fintype.card V≤(((Finset.univ.filter (fun a=>H a u∧H a u'))∩Q.neighborFinset v∩Q.neighborFinset w).card:ℝ))→
      (r=4→∀ v w x,β*Fintype.card V≤((Q.neighborFinset v∩Q.neighborFinset w∩Q.neighborFinset x).card:ℝ))→
      (r=3→∀ w x y z,β*Fintype.card V≤((Finset.univ.filter (fun a=>Q.Adj w a∧Q.Adj x a∧Q.Adj y a∧Q.Adj z a)).card:ℝ))→
      (r=3→∀ u u' w x y z,β*Fintype.card V≤((Finset.univ.filter (fun a=>H a u∧H a u'∧Q.Adj w a∧Q.Adj x a∧Q.Adj y a∧Q.Adj z a)).card:ℝ))→
      (∀ T:Finset V,T.card≤r+6→(∀ v∈T,∀ w∈T,¬F.Adj v w)→
        β*Fintype.card V≤((common Finset.univ T (fun v=>Finset.univ.filter (H v))).card:ℝ))→
      (∀ i:{u:U // ∃ v,H₀ v u},β*Fintype.card V≤
        ((Finset.univ.filter (fun a=>H a i.val∧H a (ψ i.val))).card:ℝ))→
      ∀ w:∀ i:{u:U // ∃ v,H₀ v u},
        LocalOrdinaryCycle Q F (Finset.univ.filter (fun a=>H a i.val∧H a (ψ i.val))) r→ℝ,
      (∀ i C,b/(Fintype.card V:ℝ)^(r-1)≤w i C∧w i C≤B₀/(Fintype.card V:ℝ)^(r-1))→
      (∀ i:{u:U // ∃ v,H₀ v u},∀ v∈Finset.univ.filter (fun a=>H a i.val∧H a (ψ i.val)),
        |1-hypergraphWeightedDegree localOrdinaryVertices (w i) v|≤η)→
      (∀ i:{u:U // ∃ v,H₀ v u},∀ X:Finset V,X⊆Finset.univ.filter (fun a=>H a i.val∧H a (ψ i.val))→X.card=r→
        a*(Fintype.card V:ℝ)^(r*r)≤Fintype.card
          (LabelledAbsorberFamily (localOrdinaryVertices (Q:=Q) (F:=F)
            (T:=Finset.univ.filter (fun a=>H a i.val∧H a (ψ i.val))) (r:=r)) Tpls X))→
      ∃ N:Finset V,∃ K:Finset (Sym2 V⊕(V×U)),
        N.card≤m*r*(t+5*m)∧
        IsResourceTransformer (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=r))
          (ordinaryHostResources G H₀) (transformerImageResources G H₀ φ ψ) K∧
        K⊆ordinaryHostResources Q H∧
        (∀ v v',Sum.inl s(v,v')∈K→v∈N∧v'∈N)∧
        (∀ v a,Sum.inr (v,a)∈K→v∈N)∧
        (∀ v∈R,∀ v'∈R,Sum.inl s(v,v')∉K)∧
        (∀ v∈R,∀ a∈B,Sum.inr (v,a)∉K)∧
        ∃ B':Finset U,B'.card≤m*(m+2)∧
          (∀ v a,Sum.inr (v,a)∈K→a∈B')∧
          (∀ v∈W,∀ v',Sum.inl s(v,v')∈K→v∈R)∧
          (∀ v∈W,∀ a,Sum.inr (v,a)∈K→v∈R)∧
          (∀ v a,Sum.inr (v,a)∈K→a∈B→∃ i:{u:U // ∃ v,H₀ v u},a=i.val∨a=ψ i.val)∧
          (ordinaryPhysicalGraph (ordinaryResourceRim Q K) (fun v u=>Sum.inr (v,u)∈K)).support.toFinset.card≤
            m*(r*(t+5*m)+m+2)∧N⊆R∪A∧Disjoint K L  := by
  by_cases hr3:r=3
  · subst r
    obtain ⟨η,ε,hη,hε,hεβ,hbase⟩:=triangular_relative_host_transformer Tpls β a b B₀ hβ ha hb hB₀
    refine ⟨η,ε,hη,hε,hεβ,?_⟩
    intro m
    obtain ⟨t,ht,hbase⟩:=hbase m
    refine ⟨t,ht,?_⟩
    intro f d hd
    obtain ⟨n₀,hbase⟩:=hbase f d hd
    refine ⟨n₀,?_⟩
    intro V U _ _ _ _ hn G Q F H₀ H φ ψ A Z R W B L hA hZ hrows hhubs hRW hRcard hWcard hBcard
      hbalance hdiv hq hnU hroot hcross hu hQ hφQ hφedge hψedge hH hB hFroots hF
      hcount hpair hthree hfour hspfour hhub hT w hw herr habs
    exact hbase V U hn G Q F H₀ H φ ψ A Z R W B L hA hZ hrows hhubs hRW hRcard hWcard hBcard
      hbalance hdiv hq hnU hroot hcross hu hQ hφQ hφedge hψedge hH hB hFroots hF
      (hfour rfl) (hspfour rfl) hhub hT w hw herr habs
  · obtain ⟨η,ε,hη,hε,hεβ,hbase⟩:=ordinary_relative_host_transformer r (by omega) Tpls β a b B₀ hβ ha hb hB₀
    refine ⟨η,ε,hη,hε,hεβ,?_⟩
    intro m
    obtain ⟨t,ht,hbase⟩:=hbase m
    refine ⟨t,ht,?_⟩
    intro f d hd
    obtain ⟨n₀,hbase⟩:=hbase f d hd
    refine ⟨n₀,?_⟩
    intro V U _ _ _ _ hn G Q F H₀ H φ ψ A Z R W B L hA hZ hrows hhubs hRW hRcard hWcard hBcard
      hbalance hdiv hq hnU hroot hcross hu hQ hφQ hφedge hψedge hH hB hFroots hF
      hcount hpair hthree hfour hspfour hhub hT w hw herr habs
    exact hbase V U hn G Q F H₀ H φ ψ A Z R W B L hA hZ hrows hhubs hRW hRcard hWcard hBcard
      hbalance hdiv hq hnU hroot hcross hu hQ hφQ hφedge hψedge hH hB hFroots hF
      hcount hpair hthree hhub hT w hw herr habs

end Oberwolfach
