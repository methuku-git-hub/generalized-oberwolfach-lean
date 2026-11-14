module

public import Oberwolfach.OrdinaryParentProfileHostTransformer
public import Oberwolfach.OrdinaryRelativeTransformerBudgets

@[expose] public section

/-! The ordinary relative transformer with all local numerical margins
discharged. The deletion tolerance precedes the root size, conflict degree
and bounded forbidden-set allowance; the order bound precedes the allowance.
The original profiles and probability laws are unchanged. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
set_option maxHeartbeats 28000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {Tpl:Type} [Fintype Tpl] [DecidableEq Tpl]

 theorem ordinary_relative_host_transformer (r:ℕ) (hr:4≤r)
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
            m*(r*(t+5*m)+m+2)∧N⊆R∪A∧Disjoint K L := by
  obtain ⟨η,ε₀,hη,hε₀,hε₀β,hbase⟩:=ordinary_parent_profile_host_transformer r hr Tpls β a b B₀ hβ ha hb hB₀
  let ε:=min ε₀ (β/4)
  have hε:0<ε:=by dsimp [ε];positivity
  have hε₀':ε≤ε₀:=min_le_left _ _
  have hεβ:ε≤β/4:=min_le_right _ _
  refine ⟨η,ε,hη,hε,hεβ,?_⟩
  intro m
  obtain ⟨t,ht,hbase⟩:=hbase m m
  refine ⟨t,ht,?_⟩
  intro f d hd
  let F₀:ℝ:=f+2*(m*m)*(r-1:ℕ)+4*(r:ℝ)*(m*m)
  have hF₀:0≤F₀:=by dsimp [F₀];positivity
  obtain ⟨N₀,hbase⟩:=hbase F₀ d hF₀ hd
  obtain ⟨N₁,hbudgets⟩:=ordinary_relative_transformer_budgets β ε d hβ hd hεβ r m f
  refine ⟨max N₀ N₁,?_⟩
  intro V U _ _ _ _ hn G Q F H₀ H φ ψ A Z R W B L hA hZ hrows hhubs hRW hRcard hWcard hBcard
    hbalance hdiv hq hnU hroot hcross hu hQ hφQ hφedge hψedge hH hB hFroots hF
    hcount hpair hthree hhub hT w hw herr habs
  have hn0:0≤(Fintype.card V:ℝ):=by positivity
  have hZ₀:(Z.card:ℝ)≤ε₀*Fintype.card V:=hZ.trans (mul_le_mul_of_nonneg_right hε₀' hn0)
  have hZhalf:(Z.card:ℝ)≤(β/2)*Fintype.card V:=by
    have he:=mul_le_mul_of_nonneg_right hεβ hn0
    nlinarith only [hZ,he,mul_nonneg hβ.le hn0]
  have hlower (S:Finset V) (hS:β*Fintype.card V≤(S.card:ℝ)):
      (β/2)*Fintype.card V≤((S\Z).card:ℝ):=by
    have hh:(S.card:ℝ)≤(S\Z).card+Z.card:=by
      exact_mod_cast Finset.card_le_card_sdiff_add_card (s:=S) (t:=Z)
    linarith only [hS,hh,hZhalf]
  have hcount':∀ v w,(β/2)*Fintype.card V≤((A∩Q.neighborFinset v∩Q.neighborFinset w).card:ℝ):=by
    intro v w
    have he:(Q.neighborFinset v∩Q.neighborFinset w)\Z=A∩Q.neighborFinset v∩Q.neighborFinset w:=by
      ext x;simp [hA];tauto
    simpa only [he] using hlower _ (hcount v w)
  have hpair':∀ u u' v w,(β/2)*Fintype.card V≤(((A.filter (fun a=>H a u∧H a u'))∩Q.neighborFinset v∩Q.neighborFinset w).card:ℝ):=by
    intro u u' v w
    have he:((Finset.univ.filter (fun a=>H a u∧H a u'))∩Q.neighborFinset v∩Q.neighborFinset w)\Z=
        (A.filter (fun a=>H a u∧H a u'))∩Q.neighborFinset v∩Q.neighborFinset w:=by
      ext x;simp [hA];tauto
    simpa only [he] using hlower _ (hpair u u' v w)
  have hthree':r=4→∀ v w x,(β/2)*Fintype.card V≤((A∩Q.neighborFinset v∩Q.neighborFinset w∩Q.neighborFinset x).card:ℝ):=by
    intro hr4 v w x
    have he:(Q.neighborFinset v∩Q.neighborFinset w∩Q.neighborFinset x)\Z=
        A∩Q.neighborFinset v∩Q.neighborFinset w∩Q.neighborFinset x:=by
      ext a;simp [hA];tauto
    simpa only [he] using hlower _ (hthree hr4 v w x)
  obtain ⟨he,hs,hebound⟩:=balanced_root_edge_counts G H₀ hbalance m m hq hnU
  have hsbound:Fintype.card {e:V×U // H₀ e.1 e.2}≤m*m:=by rwa [←he]
  have hvbound:Fintype.card (Σ v,G.neighborSet v)≤2*(m*m):=by rw [hs];exact Nat.mul_le_mul_left _ hebound
  obtain ⟨hb₁,hb₂,hb₃,hb₄⟩:=hbudgets (Fintype.card V) ((le_max_right _ _).trans hn)
    W.card R.card B.card G.edgeFinset.card (Fintype.card {e:V×U // H₀ e.1 e.2})
    (Fintype.card (Σ v,G.neighborSet v)) hWcard hRcard hebound hsbound hvbound hBcard
  apply hbase V U ((le_max_left _ _).trans hn) G Q F H₀ H φ ψ A Z R W B L hA hZ₀ hrows hhubs hRW
    hbalance hdiv hq hnU hroot hcross hu hQ hφQ hφedge hψedge hH hB hFroots hF
    ((β/2)*Fintype.card V) ((β/2)*Fintype.card V) hcount' hpair' hthree' hb₁ hb₂ hb₃
    (fun T hTc hTF=>(show (β/2)*Fintype.card V≤β*Fintype.card V by nlinarith only [mul_nonneg hβ.le hn0]).trans (hhub T hTc hTF))
    hb₄ hT w hw herr habs

end Oberwolfach
