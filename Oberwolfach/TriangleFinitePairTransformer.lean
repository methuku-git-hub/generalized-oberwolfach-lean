module

public import Oberwolfach.TriangleTransformerExtendedGraph
public import Oberwolfach.OrdinaryAmbientMapGeometry
public import Oberwolfach.OrdinaryEmbeddedRootBounds
public import Oberwolfach.OrdinaryTransformerMapInputs

@[expose] public section
/-! Apply the uniform triangle transformer to a part-preserving,
edge-bijective map between disjoint finite embedded root graphs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 22000000
set_option synthInstance.maxSize 2048
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem triangle_finite_pair_transformer (β:ℝ) (hβ:0<β):
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
      IsResourceTransformer (ordinaryWheelResources (P:=Q) (F:=⊥) (Hbase:=H) (r:=3))
        (ordinaryHostResources G H₀) (ordinaryHostResources P H₁) T ∧
      T⊆ordinaryHostResources Q H ∧
      (ordinaryPhysicalGraph (ordinaryResourceRim Q T) (fun v u=>Sum.inr (v,u)∈T)).support.toFinset.card≤K₀ ∧
      (∀ v∈R,∀ w∈R,Sum.inl s(v,w)∉T) ∧
      (∀ v∈R,∀ z∈B,Sum.inr (v,z)∉T) ∧
      (∀ v∈ordinaryResourceRows T,v∈ZV→v∈R) ∧
      (∀ z∈ordinaryResourceHubs T,z∈ZU→z∈B) :=by
  obtain ⟨ε₀,hε₀,huniform⟩:=triangle_transformer_finite_resource_uniform β hβ
  refine ⟨ε₀,hε₀,?_⟩
  intro q
  obtain ⟨N₀,K₀,hbase⟩:=huniform q
  refine ⟨N₀,K₀,?_⟩
  intro V₀ U₀ V₁ U₁ V U _ _ _ _ _ _ _ _ _ _ _ _ hn hm
    G₀ Hsrc G₁ Htgt i j k l f g Q H ZV ZU hV₀ hU₀ hV₁ hU₁ hZV hZU hbalance hdiv hinj him hdisV hdisU hsrcQ htgtQ hsrcH htgtH hdeg ε hε hεsmall hnearV hnearU G H₀ P H₁ R B
  letI : DecidableRel G.Adj := fun v w=>Classical.propDecidable (G.Adj v w)
  let φ:=ordinaryAmbientMap i j f
  let ψ:=ordinaryAmbientMap k l g
  let R₀:Finset V:=Finset.univ.image i
  let B₀:Finset U:=Finset.univ.image k
  let W:=R∪ZV
  let C:=B∪ZU
  have hiR:∀v,i v∈R:=fun v=>Finset.mem_union_left _ (Finset.mem_image.mpr ⟨v,Finset.mem_univ _,rfl⟩)
  have hjR:∀v,j v∈R:=fun v=>Finset.mem_union_right _ (Finset.mem_image.mpr ⟨v,Finset.mem_univ _,rfl⟩)
  have hkC:∀u,k u∈C:=fun u=>Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨u,Finset.mem_univ _,rfl⟩))
  have hlC:∀u,l u∈C:=fun u=>Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨u,Finset.mem_univ _,rfl⟩))
  obtain ⟨hinj',him'⟩:=ordinaryAmbient_resource_bijection G₀ Hsrc G₁ Htgt i j k l f g hinj him
  have hrim:∀ v w,G.Adj v w→P.Adj (φ v) (φ w):=ordinary_resource_image_rim_hom _ _ _ _ _ _ him'
  have hspoke:∀ v u,H₀ v u→H₁ (φ v) (ψ u):=ordinary_resource_image_spoke_hom _ _ _ _ _ _ him'
  have hHsrc:∀ v u,H₀ v u→H v u:=by
    rintro v u ⟨x,y,h,rfl,rfl⟩;exact hsrcH x y h
  have hHtgt:∀ v u,H₁ v u→H v u:=by
    rintro v u ⟨x,y,h,rfl,rfl⟩;exact htgtH x y h
  have hB:∀ e:{e:V×U // H₀ e.1 e.2},e.val.2∈C∧ψ e.val.2∈C:=by
    rintro ⟨⟨v,u⟩,x,y,h,hv,hu⟩
    dsimp only at hu ⊢
    rw [←hu]
    dsimp only [ψ]
    rw [ordinaryAmbientMap_apply]
    exact ⟨hkC y,hlC (g y)⟩
  have hbalance':∀ v,G.degree v=2*(Finset.univ.filter (H₀ v)).card:=by
    intro v
    simpa only [←SimpleGraph.ncard_neighborSet] using ordinary_pair_embedding_balance G₀ Hsrc i k hbalance v
  have hR₀:R₀.card≤q:=by
    have hc:(Finset.univ.image i).card≤Fintype.card V₀:=by simpa using (Finset.card_image_le (s:=(Finset.univ:Finset V₀)) (f:=i))
    exact hc.trans hV₀
  have hB₀:B₀.card≤q:=by
    have hc:(Finset.univ.image k).card≤Fintype.card U₀:=by simpa using (Finset.card_image_le (s:=(Finset.univ:Finset U₀)) (f:=k))
    exact hc.trans hU₀
  have hR₁:(Finset.univ.image j).card≤q:=by
    have hc:(Finset.univ.image j).card≤Fintype.card V₁:=by simpa using (Finset.card_image_le (s:=(Finset.univ:Finset V₁)) (f:=j))
    exact hc.trans hV₁
  have hB₁:(Finset.univ.image l).card≤q:=by
    have hc:(Finset.univ.image l).card≤Fintype.card U₁:=by simpa using (Finset.card_image_le (s:=(Finset.univ:Finset U₁)) (f:=l))
    exact hc.trans hU₁
  have hR:R.card≤3*q:=by
    have hc:=Finset.card_union_le (Finset.univ.image i) (Finset.univ.image j)
    dsimp [R,R₀] at *;omega
  have hW:W.card≤3*q:=by
    have hc:=Finset.card_union_le R ZV
    have hr0:(Finset.univ.image i).card≤q:=hR₀
    have hc':=Finset.card_union_le (Finset.univ.image i) (Finset.univ.image j)
    dsimp [W,R] at *;omega
  have hC:C.card≤3*q:=by
    have hc:=Finset.card_union_le B ZU
    have hb0:(Finset.univ.image k).card≤q:=hB₀
    have hc':=Finset.card_union_le (Finset.univ.image k) (Finset.univ.image l)
    dsimp [C,B] at *;omega
  have hsupp:∀ v u,H₀ v u→v∈R₀∧u∈B₀:=by
    rintro v u ⟨x,y,h,rfl,rfl⟩
    exact ⟨Finset.mem_image.mpr ⟨x,Finset.mem_univ _,rfl⟩,Finset.mem_image.mpr ⟨y,Finset.mem_univ _,rfl⟩⟩
  have hIm:transformerImageResources G H₀ φ ψ=ordinaryHostResources P H₁:=by
    convert him' using 1 <;> congr!
  obtain ⟨T,hT,hTQ,hcard,hrootR,hrootS,havoidR,havoidU⟩:=hbase V U hn hm G Q H₀ H φ ψ R W R₀ C B₀
    Finset.subset_union_left hbalance' (ordinary_pair_embedding_divisibility Hsrc i k 3 hdiv)
    (ordinaryAmbientMap_support_location G₀ i j f R hiR hjR)
    (ordinaryAmbientMap_disjoint_support G₀ i j f hdisV)
    (ordinaryAmbientMap_active_hub_ne Hsrc i k l g hdisU)
    hsrcQ (fun v w h=>htgtQ (hrim v w h))
    (@ordinary_resource_map_rim_injective V U _ _ _ _ G (fun v w=>Classical.propDecidable (G.Adj v w)) H₀ φ ψ hinj')
    (ordinary_resource_map_spoke_injective _ _ _ _ hinj')
    (fun v u h=>⟨hHsrc v u h,hHtgt _ _ (hspoke v u h)⟩) hB hdeg ε hε hεsmall hnearV hnearU
    hR₀ hB₀ hsupp hW hR hC
  refine ⟨T,?_,hTQ,?_,hrootR,?_,?_,?_⟩
  · simpa only [hIm] using hT
  · exact (ordinary_resource_subgraph_order Q H T hTQ (ordinaryResourceRows T) (ordinaryResourceHubs T)
      (by intro v w he;constructor <;> apply Finset.mem_biUnion.mpr <;> exact ⟨Sum.inl s(v,w),he,by simp⟩)
      (by intro v u he;constructor <;> apply Finset.mem_biUnion.mpr <;> exact ⟨Sum.inr (v,u),he,by simp⟩)).trans hcard
  · intro v hv z hz
    exact hrootS v hv z (Finset.mem_union_left _ hz)
  · intro v hv hz
    exact havoidR v hv (Finset.mem_union_right _ hz)
  · intro z hz hzZ
    obtain ⟨u,⟨v,hu⟩,hzu|hzu⟩:=havoidU z hz (Finset.mem_union_right _ hzZ)
    · rcases hsupp v u hu with ⟨_,huB⟩
      exact Finset.mem_union_left _ (hzu ▸ huB)
    · obtain ⟨x,y,h,hx,hy⟩:=hu
      rw [←hy] at hzu
      have hψ:ψ (k y)=l (g y):=ordinaryAmbientMap_apply k l g y
      have hz':z=l (g y):=hzu.trans hψ
      exact hz' ▸ Finset.mem_union_right _ (Finset.mem_image.mpr ⟨g y,Finset.mem_univ _,rfl⟩)
end Oberwolfach
