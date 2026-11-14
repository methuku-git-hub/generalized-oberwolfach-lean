module

public import Oberwolfach.OrdinaryTransformerFromProfiles
public import Oberwolfach.OrdinaryTransformerEdgeRealization
public import Oberwolfach.OrdinaryBalancedRootCounts
public import Oberwolfach.OrdinaryResourceSubgraphs

@[expose] public section

/-! A complete ordinary r >= 4 transformer from explicit common-neighbour
inequalities and the fixed cycle-weight/absorber profiles. Every path,
incidence permutation, edge wheel, vertex wheel and hub trade is constructed.
Its row/hub size bound is independent of the forbidden-set allowance. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
set_option synthInstance.maxSize 512
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
open scoped BigOperators
variable {Tpl:Type} [Fintype Tpl] [DecidableEq Tpl]

 theorem ordinary_profile_host_transformer (r:ℕ) (hr:4≤r)
    (Tpls:Tpl→VertexAbsorberTemplate r) (α b₀ B₀:ℝ) (hα:0<α) (hb₀:0<b₀) (hB₀:0<B₀):
    ∃ η:ℝ,0<η∧∀ q nU:ℕ,∃ t:ℕ,1≤t∧∀ F₀ d:ℝ,0≤F₀→0≤d→
      ∃ k₀:ℝ,1<k₀∧
      ∀ (V U:Type) [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U],
      ∀ (G Q F:SimpleGraph V) (H₀ H:V→U→Prop) (φ:V→V) (ψ:U→U)
      (A R W:Finset V) (B:Finset U),R⊆W→
      (∀ v,G.degree v=2*((Finset.univ:Finset U).filter (H₀ v)).card)→
      (∀ u,r∣((Finset.univ:Finset V).filter (fun v=>H₀ v u)).card)→
      (∀ u,((Finset.univ:Finset V).filter (fun v=>H₀ v u)).card≤q)→
      Fintype.card {u:U // ∃ v,H₀ v u}≤nU→
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
      (∀ v,(F.degree v:ℝ)≤d)→∀ c cH:ℝ,
      (∀ v w,c≤((A∩Q.neighborFinset v∩Q.neighborFinset w).card:ℝ))→
      (∀ u u' v w,c≤(((A.filter (fun a=>H a u∧H a u'))∩Q.neighborFinset v∩Q.neighborFinset w).card:ℝ))→
      (r=4→∀ v w x,c≤(((A∩Q.neighborFinset v)∩Q.neighborFinset w∩Q.neighborFinset x).card:ℝ))→
      W.card+((R.card:ℝ)+(G.edgeFinset.card+Fintype.card {e:V×U // H₀ e.1 e.2})*(r-1:ℕ)+r+7)*(d+1)<c→
      W.card+(G.edgeFinset.card+Fintype.card {e:V×U // H₀ e.1 e.2})*(r-1:ℕ)+
        Fintype.card (Σ v,G.neighborSet v)*r+((r:ℝ)+4)*(d+1)<c→
      W.card+(G.edgeFinset.card+Fintype.card {e:V×U // H₀ e.1 e.2})*(r-1:ℕ)+
        2*(r:ℝ)*Fintype.card (Σ v,G.neighborSet v)≤F₀→
      (∀ T:Finset V,T.card≤r+6→(∀ v∈T,∀ w∈T,¬F.Adj v w)→
        cH≤((common (Finset.univ:Finset U) T (fun v=>Finset.univ.filter (H v))).card:ℝ))→
      B.card+G.edgeFinset.card<cH→
      ∀ k:{u:U // ∃ v,H₀ v u}→ℝ,
      (∀ i,k₀≤k i)→
      (∀ i,((A.filter (fun a=>H a i.val∧H a (ψ i.val))).card:ℝ)=r*k i)→
      ∀ w:∀ i,LocalOrdinaryCycle Q F (A.filter (fun a=>H a i.val∧H a (ψ i.val))) r→ℝ,
      (∀ i C,b₀/(k i)^(r-1)≤w i C∧w i C≤B₀/(k i)^(r-1))→
      (∀ i,∀ v∈A.filter (fun a=>H a i.val∧H a (ψ i.val)),
        |1-hypergraphWeightedDegree localOrdinaryVertices (w i) v|≤η)→
      (∀ i,∀ X:Finset V,X⊆A.filter (fun a=>H a i.val∧H a (ψ i.val))→X.card=r→
        α*(k i)^(r*r)≤Fintype.card
          (LabelledAbsorberFamily (localOrdinaryVertices (Q:=Q) (F:=F)
            (T:=A.filter (fun a=>H a i.val∧H a (ψ i.val))) (r:=r)) Tpls X))→
      ∃ N:Finset V,∃ K:Finset (Sym2 V⊕(V×U)),
        N.card≤nU*r*(t+5*q)∧
        IsResourceTransformer (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=r))
          (ordinaryHostResources G H₀) (transformerImageResources G H₀ φ ψ) K∧
        K⊆ordinaryHostResources Q H∧
        (∀ v v',Sum.inl s(v,v')∈K→v∈N∧v'∈N)∧
        (∀ v a,Sum.inr (v,a)∈K→v∈N)∧
        (∀ v∈R,∀ v'∈R,Sum.inl s(v,v')∉K)∧
        (∀ v∈R,∀ a∈B,Sum.inr (v,a)∉K)∧
        ∃ B':Finset U,B'.card≤nU*(q+2)∧
          (∀ v a,Sum.inr (v,a)∈K→a∈B')∧
          (∀ v∈W,∀ v',Sum.inl s(v,v')∈K→v∈R)∧
          (∀ v∈W,∀ a,Sum.inr (v,a)∈K→v∈R)∧
          (∀ v a,Sum.inr (v,a)∈K→a∈B→∃ i:{u:U // ∃ v,H₀ v u},a=i.val∨a=ψ i.val)∧
          (ordinaryPhysicalGraph (ordinaryResourceRim Q K) (fun v u=>Sum.inr (v,u)∈K)).support.toFinset.card≤
            nU*(r*(t+5*q)+q+2)∧N⊆R∪A:=by
  obtain ⟨η,hη,hbase⟩:=ordinary_transformer_from_paths_and_profiles r (by omega) Tpls α b₀ B₀ hα hb₀ hB₀
  refine ⟨η,hη,?_⟩
  intro q nU
  obtain ⟨t,ht,hbase⟩:=hbase q nU
  refine ⟨t,ht,?_⟩
  intro F₀ d hF₀ hd
  obtain ⟨k₀,hk₀,hbase⟩:=hbase F₀ d hF₀ hd
  refine ⟨k₀,hk₀,?_⟩
  intro V U _ _ _ _ G Q F H₀ H φ ψ A R W B hRW hbalance hdiv hq hnU hroot hcross hu hQ hφQ
    hφedge hψedge hH hB hFroots hF c cH hcount hpair hthree hpathbudget hvertexbudget hWbudget hhubs hhubBudget
    k hk hT w hw herr habs
  obtain ⟨E⟩:=ordinary_transformer_edge_realization G Q F H₀ H φ ψ r hr A R W B
    hbalance hroot hcross hQ hφQ hφedge hψedge hH hFroots d c cH hd hF hcount
    (fun i=>hpair i.val.2 (ψ i.val.2)) hthree hpathbudget hhubs hhubBudget
  have hWcard:(E.buffer.card:ℝ)≤W.card+(G.edgeFinset.card+Fintype.card {e:V×U // H₀ e.1 e.2})*(r-1:ℕ):=by
    exact_mod_cast E.buffer_card
  have hvbudget:E.buffer.card+Fintype.card (Σ v,G.neighborSet v)*r+((r:ℝ)+4)*(d+1)<c:=by
    linarith only [hWcard,hvertexbudget]
  have hwbudget:E.buffer.card+2*(r:ℝ)*Fintype.card (Σ v,G.neighborSet v)≤F₀:=by
    linarith only [hWcard,hWbudget]
  have hsingle:∀ u v w,c≤(((A.filter (fun x=>H x u))∩Q.neighborFinset v∩Q.neighborFinset w).card:ℝ):=by
    intro u v w
    simpa only [and_self] using hpair u u v w
  have hZT (i:{u:U // ∃ v,H₀ v u}):
      transformerSpokeRows Q H₀ (fun j=>E.path (.inr j)) i.val⊆A.filter (fun a=>H a i.val∧H a (ψ i.val)):=by
    intro v hv
    obtain ⟨j,hj,hv⟩:=(transformerSpokeRows_mem Q H₀ _ i.val v).mp hv
    have hh:=E.spoke_hubs j v hv
    rw [hj] at hh
    exact Finset.mem_filter.mpr ⟨(E.path_location _ _ hv).1,hh⟩
  obtain ⟨N,K,hNc,hK,hKQ,hKr,hKs,hRr,hRs,B',hBc,hBh,havoid,hHavoid,hNloc⟩:=hbase V U G Q F H₀ H φ ψ E.b E.σ E.shifted E.path A R E.buffer B
    (hRW.trans E.contains_old) hbalance hdiv hq hnU hroot hcross hu hφQ hφedge hψedge hB
    E.isPath (fun _=>E.positive) (fun he=>by omega) (fun he=>by omega) E.spoke_length
    (fun i v hv=>⟨E.contains_paths i v hv,(E.path_location i v hv).2.2⟩)
    E.path_disjoint E.path_separated E.root_separated E.rim_ends E.spoke_ends hF c (fun _=>hsingle)
    (fun _=>hvbudget) hwbudget E.rim E.spoke (fun i=>A.filter (fun a=>H a i.val∧H a (ψ i.val)))
    k hk (fun i v hv=>(Finset.mem_filter.mp hv).2) hT hZT w hw herr habs

  have hav:=havoid W E.contains_old (fun i v hv=>(E.path_location i v hv).2.1)
  have hc:=balanced_root_edge_counts G H₀ hbalance q nU hq hnU
  have hNbound:N.card≤nU*r*(t+5*q):=by
    rw [←hc.1,hc.2.1] at hNc
    have hm:=Nat.mul_le_mul_left (4*r) hc.2.2
    nlinarith only [hNc,hm]
  have hBbound:B'.card≤nU*(q+2):=by nlinarith only [hBc,hc.2.2]
  refine ⟨N,K,hNbound,hK,hKQ,hKr,hKs,hRr,hRs,B',hBbound,hBh,hav.1,hav.2,hHavoid,?_,?_⟩
  · have hh:=ordinary_resource_subgraph_order Q H K hKQ N B' hKr (fun v u he=>⟨hKs v u he,hBh v u he⟩)
    nlinarith only [hh,hNbound,hBbound]
  · exact hNloc (fun i v hv=>(Finset.mem_filter.mp hv).1) (fun i v hv=>(E.path_location i v hv).1)

end Oberwolfach
