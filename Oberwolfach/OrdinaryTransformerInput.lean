module

public import Oberwolfach.OrdinaryEmbeddedTransformerData

@[expose] public section

/-! Exact data used by the ordinary relative transformer. All conditions
refer to the actual ambient rim graph, spoke relation, and vertex maps. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

structure OrdinaryTransformerInput (r m:ℕ) (Q F:SimpleGraph V) (H:V→U→Prop)
    (R:Finset V) (B:Finset U) where
  G : SimpleGraph V
  K : V→U→Prop
  φ : V→V
  ψ : U→U
  balance : ∀ v,G.degree v=2*(Finset.univ.filter (K v)).card
  div : ∀ u,r∣(Finset.univ.filter (fun v=>K v u)).card
  column : ∀ u,(Finset.univ.filter (fun v=>K v u)).card≤m
  hubs : Fintype.card {u:U // ∃ v,K v u}≤m
  roots : ∀ v∈G.support,v∈R∧φ v∈R
  disjointRows : ∀ v∈G.support,∀ w∈G.support,φ v≠w
  disjointHubs : ∀ u,(∃ v,K v u)→u≠ψ u
  sourceRim : G≤Q
  targetRim : ∀ v w,G.Adj v w→Q.Adj (φ v) (φ w)
  rimInj : Function.Injective (fun i:G.edgeFinset=>s(φ i.val.out.1,φ i.val.out.2))
  spokeInj : Function.Injective (fun i:{p:V×U // K p.1 p.2}=>(φ i.val.1,ψ i.val.2))
  hostSpokes : ∀ v u,K v u→H v u∧H (φ v) (ψ u)
  hubRoots : ∀ i:{p:V×U // K p.1 p.2},i.val.2∈B∧ψ i.val.2∈B
  separation : ∀ v w,G.Adj v w→∀ a∈({v,w,φ v,φ w}:Finset V),
    ∀ b∈({v,w,φ v,φ w}:Finset V),¬F.Adj a b

variable {V₀ U₀ V₁ U₁:Type} [Fintype V₀] [Fintype U₀] [Fintype V₁] [Fintype U₁]
    [DecidableEq V₀] [DecidableEq U₀] [DecidableEq V₁] [DecidableEq U₁]

theorem ordinary_embedded_transformer_input
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
    ∃ T:OrdinaryTransformerInput r m Q F H R B,
      ordinaryHostResources T.G T.K=e₀.resources∧
      transformerImageResources T.G T.K T.φ T.ψ=e₁.resources := by
  obtain ⟨hbal',hdiv',hcol,hhubs,hroots,hdv,hdu,hs,ht,hi,hj,hsp,hbr,hsep,him'⟩ :=
    ordinary_embedded_transformer_data G₀ Hs G₁ Ht Q F H e₀ e₁ f g r m R B
      hbal hdiv hV hU hinj him hdisV hdisU hcross hQF hR₀ hR₁ hB₀ hB₁
  exact ⟨⟨G₀.map e₀.row,ordinaryMappedSpokes Hs e₀.row e₀.hub,
    ordinaryAmbientMap e₀.row e₁.row f,ordinaryAmbientMap e₀.hub e₁.hub g,
    (by intro v;simpa only [←SimpleGraph.ncard_neighborSet] using hbal' v),hdiv',hcol,hhubs,hroots,hdv,hdu,hs,ht,(by
      exact @ordinary_resource_map_rim_injective V U _ _ _ _ (G₀.map e₀.row)
        (fun v w=>Classical.propDecidable ((G₀.map e₀.row).Adj v w))
        (ordinaryMappedSpokes Hs e₀.row e₀.hub)
        (ordinaryAmbientMap e₀.row e₁.row f) (ordinaryAmbientMap e₀.hub e₁.hub g)
        (ordinaryAmbient_resource_bijection G₀ Hs G₁ Ht e₀.row e₁.row e₀.hub e₁.hub f g hinj him).1),hj,hsp,hbr,hsep⟩,rfl,him'⟩

end Oberwolfach
