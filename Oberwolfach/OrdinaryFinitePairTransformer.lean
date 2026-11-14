module

public import Oberwolfach.OrdinaryParentProfileHostTransformer
public import Oberwolfach.OrdinaryAmbientMapGeometry
public import Oberwolfach.OrdinaryEmbeddedRootBounds
public import Oberwolfach.OrdinaryTransformerMapInputs

@[expose] public section

/-! Apply the actual transformer to embedded finite graph pairs. The
finite physical-edge bijection discharges both edge-injectivity hypotheses;
no injectivity of its row or hub maps is assumed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
set_option maxHeartbeats 26000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {Tpl:Type} [Fintype Tpl] [DecidableEq Tpl]

 theorem ordinary_finite_pair_transformer (r:ℕ) (hr:4≤r)
    (Tpls:Tpl→VertexAbsorberTemplate r) (β a b B₀:ℝ)
    (hβ:0<β) (ha:0<a) (hb:0<b) (hB₀:0<B₀):
    ∃ η ε:ℝ,0<η∧0<ε∧ε≤β/2∧∀ q nU:ℕ,∃ t:ℕ,1≤t∧∀ F₀ d:ℝ,0≤F₀→0≤d→
      ∃ n₀:ℕ,
      ∀ (V₀ U₀ V₁ U₁ V U:Type) [Fintype V₀] [DecidableEq V₀] [Fintype U₀] [DecidableEq U₀]
      [Fintype V₁] [DecidableEq V₁] [Fintype U₁] [DecidableEq U₁]
      [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U],n₀≤Fintype.card V→
      ∀ (G₀:SimpleGraph V₀) (Hsrc:V₀→U₀→Prop) (G₁:SimpleGraph V₁) (Htgt:V₁→U₁→Prop)
      (i:V₀↪V) (j:V₁↪V) (s:U₀↪U) (t':U₁↪U) (f:V₀→V₁) (g:U₀→U₁)
      (Q F:SimpleGraph V) (H:V→U→Prop),
      (∀ v,G₀.degree v=2*(Finset.univ.filter (Hsrc v)).card)→
      (∀ u,r∣(Finset.univ.filter (fun v=>Hsrc v u)).card)→
      Fintype.card V₀≤q→Fintype.card U₀≤nU→
      Set.InjOn (ordinaryPairResourceMap f g) (ordinaryHostResources G₀ Hsrc)→
      (ordinaryHostResources G₀ Hsrc).image (ordinaryPairResourceMap f g)=ordinaryHostResources G₁ Htgt→
      (∀ v w,i v≠j w)→(∀ u u',s u≠t' u')→
      (∀ v w,¬F.Adj (i v) (j w))→
      (∀ v w,Q.Adj v w→¬F.Adj v w)→
      G₀.map i≤Q→G₁.map j≤Q→
      (∀ v u,Hsrc v u→H (i v) (s u))→(∀ v u,Htgt v u→H (j v) (t' u))→
      let G:=G₀.map i
  letI : DecidableRel G.Adj := fun v w=>Classical.propDecidable (G.Adj v w)
      let H₀:=ordinaryMappedSpokes Hsrc i s
      let φ:=ordinaryAmbientMap i j f
      let ψ:=ordinaryAmbientMap s t' g
      ∀       (A Z R W:Finset V) (B:Finset U) (L:Finset (Sym2 V⊕(V×U))),
      A=Finset.univ\Z→(Z.card:ℝ)≤ε*Fintype.card V→
      ordinaryResourceRows L⊆W→ ordinaryResourceHubs L⊆B→R⊆W→
      (∀ v,i v∈R)→(∀ v,j v∈R)→(∀ u,s u∈B)→(∀ u,t' u∈B)→
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
        N.card≤nU*r*(t+5*q)∧
        IsResourceTransformer (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=r))
          (ordinaryHostResources G H₀) (ordinaryHostResources (G₁.map j) (ordinaryMappedSpokes Htgt j t')) K∧
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
            nU*(r*(t+5*q)+q+2)∧N⊆R∪A∧Disjoint K L := by
  obtain ⟨η,ε,hη,hε,hεβ,hbase⟩ := ordinary_parent_profile_host_transformer r hr Tpls β a b B₀ hβ ha hb hB₀
  refine ⟨η,ε,hη,hε,hεβ,?_⟩
  intro q nU
  obtain ⟨t,ht,hbase⟩:=hbase q nU
  refine ⟨t,ht,?_⟩
  intro F₀ d hF₀ hd
  obtain ⟨n₀,hbase⟩:=hbase F₀ d hF₀ hd
  refine ⟨n₀,?_⟩
  intro V₀ U₀ V₁ U₁ V U _ _ _ _ _ _ _ _ _ _ _ _ hn G₀ Hsrc G₁ Htgt i j s t' f g Q F H
    hbalance hdiv hq hnU hinj him hdisV hdisU hcross hQF hsrcQ htgtQ hsrcH htgtH
  dsimp only
  intro A Z R W B L hA hZ hrows hhubs hRW hiR hjR hsB htB hF c cH hcount hpair hthree
    hpathbudget hvertexbudget hWbudget hhub hhubBudget hT w hw herr habs
  let G:=G₀.map i
  letI : DecidableRel G.Adj := fun v w=>Classical.propDecidable (G.Adj v w)
  let K₀:=ordinaryMappedSpokes Hsrc i s
  let P:=G₁.map j
  let K₁:=ordinaryMappedSpokes Htgt j t'
  let φ:=ordinaryAmbientMap i j f
  let ψ:=ordinaryAmbientMap s t' g
  obtain ⟨hinj',him'⟩:=ordinaryAmbient_resource_bijection G₀ Hsrc G₁ Htgt i j s t' f g hinj him
  have hrim:∀ v w,G.Adj v w→P.Adj (φ v) (φ w):=
    ordinary_resource_image_rim_hom _ _ _ _ _ _ him'
  have hspoke:∀ v u,K₀ v u→K₁ (φ v) (ψ u):=
    ordinary_resource_image_spoke_hom _ _ _ _ _ _ him'
  have hHsrc:∀ v u,K₀ v u→H v u:=by
    rintro v u ⟨x,y,h,rfl,rfl⟩;exact hsrcH x y h
  have hHtgt:∀ v u,K₁ v u→H v u:=by
    rintro v u ⟨x,y,h,rfl,rfl⟩;exact htgtH x y h
  have hB:∀ e:{e:V×U // K₀ e.1 e.2},e.val.2∈B∧ψ e.val.2∈B:=by
    rintro ⟨⟨v,u⟩,x,y,h,hv,hu⟩
    dsimp only at hu ⊢
    rw [←hu]
    dsimp only [ψ]
    rw [ordinaryAmbientMap_apply]
    exact ⟨hsB y,htB (g y)⟩
  have hFroots:=ordinaryAmbientMap_edge_roots_separated G₀ F i j f
    (fun x y h=>hQF _ _ (hsrcQ ((SimpleGraph.map_adj i G₀ _ _).mpr ⟨x,y,h,rfl,rfl⟩)))
    (fun x y h=>hQF _ _ (htgtQ (by
      have hh:=hrim (i x) (i y) ((SimpleGraph.map_adj i G₀ _ _).mpr ⟨x,y,h,rfl,rfl⟩)
      simpa only [φ,ordinaryAmbientMap_apply] using hh))) hcross
  have hbalance' : ∀ v,G.degree v=2*(Finset.univ.filter (K₀ v)).card := by
    intro v
    simpa only [←SimpleGraph.ncard_neighborSet] using ordinary_pair_embedding_balance G₀ Hsrc i s hbalance v
  have him₀ : transformerImageResources G K₀ φ ψ=ordinaryHostResources P K₁ := by
    convert him' using 1 <;> congr!
  have hresult:=hbase V U hn G Q F K₀ H φ ψ A Z R W B L hA hZ hrows hhubs hRW
    (by intro v;simpa only [←SimpleGraph.ncard_neighborSet] using hbalance' v)
    (ordinary_pair_embedding_divisibility Hsrc i s r hdiv)
    (fun u=>(ordinary_embedded_spoke_column_bound Hsrc i s u).trans hq)
    ((ordinary_embedded_active_hub_bound Hsrc i s).trans hnU)
    (ordinaryAmbientMap_support_location G₀ i j f R hiR hjR)
    (ordinaryAmbientMap_disjoint_support G₀ i j f hdisV)
    (ordinaryAmbientMap_active_hub_ne Hsrc i s t' g hdisU)
    hsrcQ (fun v w h=>htgtQ (hrim v w h))
    (@ordinary_resource_map_rim_injective V U _ _ _ _ G (fun v w=>Classical.propDecidable (G.Adj v w)) K₀ φ ψ hinj')
    (ordinary_resource_map_spoke_injective _ _ _ _ hinj')
    (fun v u h=>⟨hHsrc v u h,hHtgt _ _ (hspoke v u h)⟩)
    hB hFroots hF c cH hcount hpair hthree hpathbudget hvertexbudget hWbudget hhub hhubBudget hT w hw herr habs
  rw [him₀] at hresult
  exact hresult

end Oberwolfach
