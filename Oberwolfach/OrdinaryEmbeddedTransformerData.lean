module

public import Oberwolfach.OrdinaryEmbeddingGeometry
public import Oberwolfach.OrdinaryEmbeddedRootBounds
public import Oberwolfach.OrdinaryAmbientMapGeometry
public import Oberwolfach.OrdinaryTransformerMapInputs

@[expose] public section

/-! The hypotheses of an ambient transformer derived from a finite
physical-edge bijection and two actual embeddings. Noninjective vertex maps
are permitted; injectivity is required and proved only on physical edges. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V₀ U₀ V₁ U₁ V U:Type}
    [Fintype V₀] [Fintype U₀] [Fintype V₁] [Fintype U₁] [Fintype V] [Fintype U]
    [DecidableEq V₀] [DecidableEq U₀] [DecidableEq V₁] [DecidableEq U₁] [DecidableEq V] [DecidableEq U]

theorem ordinary_embedded_transformer_data
    (G₀:SimpleGraph V₀) (Hs:V₀→U₀→Prop) (G₁:SimpleGraph V₁) (Ht:V₁→U₁→Prop)
    (Q F:SimpleGraph V) (H:V→U→Prop)
    (e₀:OrdinaryPairHostEmbedding G₀ Hs Q H) (e₁:OrdinaryPairHostEmbedding G₁ Ht Q H)
    (f:V₀→V₁) (g:U₀→U₁) (r m:ℕ) (R:Finset V) (B:Finset U)
    (hbal:∀ v,G₀.degree v=2*(Finset.univ.filter (Hs v)).card)
    (hdiv:∀ u,r∣(Finset.univ.filter (fun v=>Hs v u)).card)
    (hV:Fintype.card V₀≤m) (hU:Fintype.card U₀≤m)
    (hinj:Set.InjOn (ordinaryPairResourceMap f g) (ordinaryHostResources G₀ Hs))
    (him:(ordinaryHostResources G₀ Hs).image (ordinaryPairResourceMap f g)=ordinaryHostResources G₁ Ht)
    (hdisV:∀ v w,e₀.row v≠e₁.row w) (hdisU:∀ u u',e₀.hub u≠e₁.hub u')
    (hcross:∀ v w,¬F.Adj (e₀.row v) (e₁.row w))
    (hQF:∀ v w,Q.Adj v w→¬F.Adj v w)
    (hR₀:∀ v,e₀.row v∈R) (hR₁:∀ v,e₁.row v∈R)
    (hB₀:∀ u,e₀.hub u∈B) (hB₁:∀ u,e₁.hub u∈B) :
    let G:=G₀.map e₀.row
    let K:=ordinaryMappedSpokes Hs e₀.row e₀.hub
    let φ:=ordinaryAmbientMap e₀.row e₁.row f
    let ψ:=ordinaryAmbientMap e₀.hub e₁.hub g
    (∀ v,G.degree v=2*(Finset.univ.filter (K v)).card)∧
    (∀ u,r∣(Finset.univ.filter (fun v=>K v u)).card)∧
    (∀ u,(Finset.univ.filter (fun v=>K v u)).card≤m)∧
    Fintype.card {u:U // ∃ v,K v u}≤m∧
    (∀ v∈G.support,v∈R∧φ v∈R)∧
    (∀ v∈G.support,∀ w∈G.support,φ v≠w)∧
    (∀ u,(∃ v,K v u)→u≠ψ u)∧G≤Q∧
    (∀ v w,G.Adj v w→Q.Adj (φ v) (φ w))∧
    Function.Injective (fun i:G.edgeFinset=>s(φ i.val.out.1,φ i.val.out.2))∧
    Function.Injective (fun i:{p:V×U // K p.1 p.2}=>(φ i.val.1,ψ i.val.2))∧
    (∀ v u,K v u→H v u∧H (φ v) (ψ u))∧
    (∀ i:{p:V×U // K p.1 p.2},i.val.2∈B∧ψ i.val.2∈B)∧
    (∀ v w,G.Adj v w→∀ a∈({v,w,φ v,φ w}:Finset V),∀ b∈({v,w,φ v,φ w}:Finset V),¬F.Adj a b)∧
    transformerImageResources G K φ ψ=e₁.resources := by
  dsimp only
  let G:=G₀.map e₀.row
  let K:=ordinaryMappedSpokes Hs e₀.row e₀.hub
  let P:=G₁.map e₁.row
  let K₁:=ordinaryMappedSpokes Ht e₁.row e₁.hub
  let φ:=ordinaryAmbientMap e₀.row e₁.row f
  let ψ:=ordinaryAmbientMap e₀.hub e₁.hub g
  obtain ⟨hinj',him'⟩:=ordinaryAmbient_resource_bijection G₀ Hs G₁ Ht e₀.row e₁.row e₀.hub e₁.hub f g hinj him
  have hrim:∀ v w,G.Adj v w→P.Adj (φ v) (φ w):=
    ordinary_resource_image_rim_hom _ _ _ _ _ _ him'
  have hspoke:∀ v u,K v u→K₁ (φ v) (ψ u):=
    ordinary_resource_image_spoke_hom _ _ _ _ _ _ him'
  have hHsrc:∀ v u,K v u→H v u:=by
    rintro v u ⟨x,y,h,rfl,rfl⟩;exact e₀.spoke x y h
  have hHtgt:∀ v u,K₁ v u→H v u:=by
    rintro v u ⟨x,y,h,rfl,rfl⟩;exact e₁.spoke x y h
  have hB:∀ i:{p:V×U // K p.1 p.2},i.val.2∈B∧ψ i.val.2∈B:=by
    rintro ⟨⟨v,u⟩,x,y,h,hv,hu⟩
    dsimp only at hu ⊢
    rw [←hu]
    dsimp only [ψ]
    rw [ordinaryAmbientMap_apply]
    exact ⟨hB₀ y,hB₁ (g y)⟩
  have hFroots:=ordinaryAmbientMap_edge_roots_separated G₀ F e₀.row e₁.row f
    (fun x y h=>hQF _ _ (e₀.rim x y h))
    (fun x y h=>hQF _ _ (e₁.map_le (by
      have hh:=hrim (e₀.row x) (e₀.row y) ((SimpleGraph.map_adj e₀.row G₀ _ _).mpr ⟨x,y,h,rfl,rfl⟩)
      simpa only [φ,ordinaryAmbientMap_apply] using hh))) hcross
  refine ⟨?_,ordinary_pair_embedding_divisibility Hs e₀.row e₀.hub r hdiv,
    (fun u=>(ordinary_embedded_spoke_column_bound Hs e₀.row e₀.hub u).trans hV),
    (ordinary_embedded_active_hub_bound Hs e₀.row e₀.hub).trans hU,
    ordinaryAmbientMap_support_location G₀ e₀.row e₁.row f R hR₀ hR₁,
    ordinaryAmbientMap_disjoint_support G₀ e₀.row e₁.row f hdisV,
    ordinaryAmbientMap_active_hub_ne Hs e₀.row e₀.hub e₁.hub g hdisU,e₀.map_le,
    (fun v w h=>e₁.map_le (hrim v w h)),
    ordinary_resource_map_rim_injective _ _ _ _ hinj',
    ordinary_resource_map_spoke_injective _ _ _ _ hinj',
    (fun v u h=>⟨hHsrc v u h,hHtgt _ _ (hspoke v u h)⟩),hB,hFroots,?_⟩
  · intro v
    simpa only [←SimpleGraph.ncard_neighborSet] using ordinary_pair_embedding_balance G₀ Hs e₀.row e₀.hub hbal v
  · exact him'

end Oberwolfach
