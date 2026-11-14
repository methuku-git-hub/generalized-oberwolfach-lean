module

public import Oberwolfach.AllLengthsRelativeHostTransformer
public import Oberwolfach.OrdinarySequentialResourceSelection

@[expose] public section

/-! All transformers of a finite diagram are constructed in the same host,
with mutually disjoint physical edges and the original fixed cycle weights.
The common threshold includes the full accumulated row and hub allowances. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {Tpl:Type} [Fintype Tpl] [DecidableEq Tpl]

 theorem ordinary_relative_transformer_family (r:ℕ) (hr:3≤r)
    (Tpls:Tpl→VertexAbsorberTemplate r) (β a b B₀:ℝ)
    (hβ:0<β) (ha:0<a) (hb:0<b) (hB₀:0<B₀):
    ∃ η ε:ℝ,0<η∧0<ε∧ε≤β/4∧∀ m l:ℕ,∃ t:ℕ,1≤t∧∀ f:ℕ,∀ d:ℝ,0≤d→
      ∃ n₀:ℕ,
      ∀ (V U:Type) [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U],
      n₀≤Fintype.card V→
      ∀ (G:Fin l→SimpleGraph V) (Q F:SimpleGraph V) (H₀:Fin l→V→U→Prop) (H:V→U→Prop) (φ:Fin l→V→V) (ψ:Fin l→U→U)
      (A Z R W:Finset V) (B:Finset U) (L:Finset (Sym2 V⊕(V×U))),
      A=Finset.univ\Z→(Z.card:ℝ)≤ε*Fintype.card V→
      ordinaryResourceRows L⊆W→ ordinaryResourceHubs L⊆B→R⊆W→
      R.card≤m→W.card≤f→(B.card:ℝ)≤ε*Fintype.card V+f→
      (∀ j:Fin l,∀ v,(G j).degree v=2*((Finset.univ:Finset U).filter (H₀ j v)).card)→
      (∀ j:Fin l,∀ u,r∣((Finset.univ:Finset V).filter (fun v=>H₀ j v u)).card)→
      (∀ j:Fin l,∀ u,((Finset.univ:Finset V).filter (fun v=>H₀ j v u)).card≤m)→
      (∀ j:Fin l,Fintype.card {u:U // ∃ v,H₀ j v u}≤m)→
      (∀ j:Fin l,∀ v∈(G j).support,v∈R∧φ j v∈R)→
      (∀ j:Fin l,∀ v∈(G j).support,∀ w∈(G j).support,φ j v≠w)→
      (∀ j:Fin l,∀ u,(∃ v,H₀ j v u)→u≠ψ j u)→
      (∀ j:Fin l,G j≤Q)→(∀ j:Fin l,∀ v w,(G j).Adj v w→Q.Adj (φ j v) (φ j w))→
      (∀ j:Fin l,Function.Injective (fun i:(G j).edgeFinset=>s(φ j i.val.out.1,φ j i.val.out.2)))→
      (∀ j:Fin l,Function.Injective (fun i:{e:V×U // H₀ j e.1 e.2}=>(φ j i.val.1,ψ j i.val.2)))→
      (∀ j:Fin l,∀ v u,H₀ j v u→H v u∧H (φ j v) (ψ j u))→
      (∀ j:Fin l,∀ e:{e:V×U // H₀ j e.1 e.2},e.val.2∈B∧ψ j e.val.2∈B)→
      (∀ j:Fin l,∀ v w,(G j).Adj v w→∀ a∈({v,w,φ j v,φ j w}:Finset V),
        ∀ c∈({v,w,φ j v,φ j w}:Finset V),¬F.Adj a c)→
      (∀ v,(F.degree v:ℝ)≤d)→
      (∀ v w,β*Fintype.card V≤((Q.neighborFinset v∩Q.neighborFinset w).card:ℝ))→
      (∀ u u' v w,β*Fintype.card V≤(((Finset.univ.filter (fun a=>H a u∧H a u'))∩Q.neighborFinset v∩Q.neighborFinset w).card:ℝ))→
      (r=4→∀ v w x,β*Fintype.card V≤((Q.neighborFinset v∩Q.neighborFinset w∩Q.neighborFinset x).card:ℝ))→
      (r=3→∀ w x y z,β*Fintype.card V≤((Finset.univ.filter (fun a=>Q.Adj w a∧Q.Adj x a∧Q.Adj y a∧Q.Adj z a)).card:ℝ))→
      (r=3→∀ u u' w x y z,β*Fintype.card V≤((Finset.univ.filter (fun a=>H a u∧H a u'∧Q.Adj w a∧Q.Adj x a∧Q.Adj y a∧Q.Adj z a)).card:ℝ))→
      (∀ T:Finset V,T.card≤r+6→(∀ v∈T,∀ w∈T,¬F.Adj v w)→
        β*Fintype.card V≤((common Finset.univ T (fun v=>Finset.univ.filter (H v))).card:ℝ))→
      (∀ j:Fin l,∀ i:{u:U // ∃ v,H₀ j v u},β*Fintype.card V≤
        ((Finset.univ.filter (fun a=>H a i.val∧H a (ψ j i.val))).card:ℝ))→
      ∀ w:∀ j:Fin l,∀ i:{u:U // ∃ v,H₀ j v u},
        LocalOrdinaryCycle Q F (Finset.univ.filter (fun a=>H a i.val∧H a (ψ j i.val))) r→ℝ,
      (∀ j i C,b/(Fintype.card V:ℝ)^(r-1)≤w j i C∧w j i C≤B₀/(Fintype.card V:ℝ)^(r-1))→
      (∀ j:Fin l,∀ i:{u:U // ∃ v,H₀ j v u},∀ v∈Finset.univ.filter (fun a=>H a i.val∧H a (ψ j i.val)),
        |1-hypergraphWeightedDegree localOrdinaryVertices (w j i) v|≤η)→
      (∀ j:Fin l,∀ i:{u:U // ∃ v,H₀ j v u},∀ X:Finset V,X⊆Finset.univ.filter (fun a=>H a i.val∧H a (ψ j i.val))→X.card=r→
        a*(Fintype.card V:ℝ)^(r*r)≤Fintype.card
          (LabelledAbsorberFamily (localOrdinaryVertices (Q:=Q) (F:=F)
            (T:=Finset.univ.filter (fun a=>H a i.val∧H a (ψ j i.val))) (r:=r)) Tpls X))→
      ∃ K:Fin l→Finset (Sym2 V⊕(V×U)),
        (∀ j,IsResourceTransformer (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=r))
          (ordinaryHostResources (G j) (H₀ j)) (transformerImageResources (G j) (H₀ j) (φ j) (ψ j)) (K j) ∧
          K j⊆ordinaryHostResources Q H ∧ ordinaryResourceRows (K j)⊆R∪A ∧
          (∀ v∈ordinaryResourceRows (K j),v∈W→v∈R) ∧
          (∀ u∈ordinaryResourceHubs (K j),u∈B→∃ i:{u:U // ∃ v,H₀ j v u},u=i.val∨u=ψ j i.val) ∧
          (ordinaryResourceRows (K j)).card≤m*r*(t+5*m) ∧
          (ordinaryResourceHubs (K j)).card≤m*(m+2) ∧ Disjoint (K j) L) ∧
        (∀ i j,i≠j→Disjoint (K i) (K j)) ∧
        (ordinaryResourceRows (Finset.univ.biUnion K)).card≤l*(m*r*(t+5*m)) ∧
        (ordinaryResourceHubs (Finset.univ.biUnion K)).card≤l*(m*(m+2)) := by
  obtain ⟨η,ε,hη,hε,hεβ,hbase⟩:=all_lengths_relative_host_transformer r hr Tpls β a b B₀ hβ ha hb hB₀
  refine ⟨η,ε,hη,hε,hεβ,?_⟩
  intro m l
  obtain ⟨t,ht,hbase⟩:=hbase m
  refine ⟨t,ht,?_⟩
  intro f d hd
  let rowBound:=m*r*(t+5*m)
  let hubBound:=m*(m+2)
  let f':=f+l*(rowBound+hubBound)
  obtain ⟨n₀,hbase⟩:=hbase f' d hd
  refine ⟨n₀,?_⟩
  intro V U _ _ _ _ hn G Q F H₀ H φ ψ A Z R W B L hA hZ hrows hhubs hRW hRcard hWcard hBcard
    hbalance hdiv hq hnU hroot hcross hu hQ hφQ hφedge hψedge hH hB hFroots hF
    hcount hpair hthree hfour hspfour hhub hT w hw herr habs
  let P:=fun (j:Fin l) (K:Finset (Sym2 V⊕(V×U)))=>
    IsResourceTransformer (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=r))
      (ordinaryHostResources (G j) (H₀ j)) (transformerImageResources (G j) (H₀ j) (φ j) (ψ j)) K ∧
      K⊆ordinaryHostResources Q H ∧ ordinaryResourceRows K⊆R∪A ∧
      (∀ v∈ordinaryResourceRows K,v∈W→v∈R) ∧
      (∀ u∈ordinaryResourceHubs K,u∈B→∃ i:{u:U // ∃ v,H₀ j v u},u=i.val∨u=ψ j i.val)
  obtain ⟨K,hK,hdis,hrow,hhubc⟩:=ordinary_sequential_resource_selection l f rowBound hubBound
    (ε*Fintype.card V+f) W B L hWcard hBcard hrows hhubs P (by
    intro W' B' L' hWW hBB hW' hB' hrows' hhubs' j
    have hW'':W'.card≤f':=hW'.trans (by dsimp [f'];rw [Nat.mul_add];omega)
    have hB'':(B'.card:ℝ)≤ε*Fintype.card V+f':=by
      have hle:(f+l*hubBound:ℕ)≤f':=by dsimp [f'];rw [Nat.mul_add];omega
      have hle':(f:ℝ)+l*hubBound≤f':=by exact_mod_cast hle
      linarith only [hB',hle']
    obtain ⟨N,K,hNc,htrans,hhost,hrim,hspoke,hRR,hRB,Bnew,hBc,hKh,hrW,hsW,hUB,horder,hNA,hKL⟩:=
      hbase V U hn (G j) Q F (H₀ j) H (φ j) (ψ j) A Z R W' B' L'
        hA hZ hrows' hhubs' (hRW.trans hWW) hRcard hW'' hB''
        (hbalance j) (hdiv j) (hq j) (hnU j) (hroot j) (hcross j) (hu j)
        (hQ j) (hφQ j) (hφedge j) (hψedge j) (hH j)
        (fun e=>⟨hBB (hB j e).1,hBB (hB j e).2⟩) (hFroots j) hF hcount hpair hthree hfour hspfour hhub
        (hT j) (w j) (hw j) (herr j) (habs j)
    have hrN:=ordinaryResourceRows_subset K N hrim hspoke
    have hhN:=ordinaryResourceHubs_subset K Bnew hKh
    refine ⟨K,⟨htrans,hhost,hrN.trans hNA,?_,?_⟩,(Finset.card_le_card hrN).trans hNc,
      (Finset.card_le_card hhN).trans hBc,hKL⟩
    · intro v hv hvW
      obtain ⟨e,he,hve⟩:=Finset.mem_biUnion.mp hv
      cases e with
      | inl e=>
        induction e using Sym2.ind with
        | _ x y=>
          have hv':v=x∨v=y:=by simpa using hve
          rcases hv' with hx|hy
          · subst x;exact hrW v (hWW hvW) y he
          · subst y;exact hrW v (hWW hvW) x (by simpa only [Sym2.eq_swap] using he)
      | inr p=>
        have hv':v=p.1:=by simpa using hve
        rw [hv'] at hvW ⊢
        exact hsW p.1 (hWW hvW) p.2 he
    · intro u hu huB
      obtain ⟨e,he,hue⟩:=Finset.mem_biUnion.mp hu
      cases e with
      | inl e=>simp at hue
      | inr p=>
        have hu':u=p.2:=by simpa using hue
        rw [hu'] at huB ⊢
        exact hUB p.1 p.2 he (hBB huB))
  refine ⟨K,?_,hdis,hrow,hhubc⟩
  intro j
  obtain ⟨⟨h1,h2,h3,h4,h5⟩,h6,h7,h8⟩:=hK j
  exact ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩

end Oberwolfach
