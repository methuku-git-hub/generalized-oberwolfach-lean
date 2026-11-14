module

public import Oberwolfach.OrdinaryFreshExpansionEmbedding
public import Oberwolfach.OrdinaryFreshComparisonAttachment
public import Oberwolfach.OrdinaryResourceEndpointSets

@[expose] public section

/-! Injective finite graph-pair embeddings in an ordinary host. Freshness
and separation are explicit predicates on every row and hub label, including
unused labels; graph and physical-edge representations are not identified. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V₀ U₀ V U E J:Type}
    [Fintype V₀] [Fintype U₀] [Fintype V] [Fintype U] [Fintype E] [Fintype J]
    [DecidableEq V₀] [DecidableEq U₀] [DecidableEq V] [DecidableEq U]

structure OrdinaryPairHostEmbedding (G₀:SimpleGraph V₀) (H₀:V₀→U₀→Prop)
    (Q:SimpleGraph V) (H:V→U→Prop) where
  row : V₀↪V
  hub : U₀↪U
  rim : ∀ a b,G₀.Adj a b→Q.Adj (row a) (row b)
  spoke : ∀ a b,H₀ a b→H (row a) (hub b)

def OrdinaryPairHostEmbedding.IsFresh {G₀:SimpleGraph V₀} {H₀:V₀→U₀→Prop}
    {Q:SimpleGraph V} {H:V→U→Prop}
    (e:OrdinaryPairHostEmbedding G₀ H₀ Q H) (F:SimpleGraph V)
    (A W R:Finset V) (B:Finset U) : Prop :=
  (∀ a,e.row a∈A∧e.row a∉W∧e.row a∉R∧∀ z∈R,¬F.Adj (e.row a) z)∧
  (∀ a,e.hub a∉B)∧(∀ a b,¬F.Adj (e.row a) (e.row b))

def OrdinaryPairHostEmbedding.resources {G₀:SimpleGraph V₀} {H₀:V₀→U₀→Prop}
    {Q:SimpleGraph V} {H:V→U→Prop} (e:OrdinaryPairHostEmbedding G₀ H₀ Q H) :
    Finset (Sym2 V⊕(V×U)) :=
  ordinaryHostResources (G₀.map e.row) (ordinaryMappedSpokes H₀ e.row e.hub)

theorem OrdinaryPairHostEmbedding.resources_subset {G₀:SimpleGraph V₀} {H₀:V₀→U₀→Prop}
    {Q:SimpleGraph V} {H:V→U→Prop} (e:OrdinaryPairHostEmbedding G₀ H₀ Q H) :
    e.resources⊆ordinaryHostResources Q H := by
  intro x hx
  cases x with
  | inl x=>
    induction x using Sym2.ind with
    | _ v w=>
      rw [OrdinaryPairHostEmbedding.resources,ordinaryHostResources_rim,SimpleGraph.mem_edgeSet,SimpleGraph.map_adj] at hx
      obtain ⟨a,b,hab,rfl,rfl⟩:=hx
      exact (ordinaryHostResources_rim _ _ _).mpr (e.rim a b hab)
  | inr p=>
    rcases p with ⟨v,u⟩
    obtain ⟨a,b,hab,rfl,rfl⟩:=(ordinaryHostResources_spoke _ _ _ _).mp hx
    exact (ordinaryHostResources_spoke _ _ _ _).mpr (e.spoke a b hab)

theorem OrdinaryPairHostEmbedding.resource_rows {G₀:SimpleGraph V₀} {H₀:V₀→U₀→Prop}
    {Q:SimpleGraph V} {H:V→U→Prop} (e:OrdinaryPairHostEmbedding G₀ H₀ Q H) :
    ordinaryResourceRows e.resources⊆Finset.univ.image e.row := by
  apply ordinaryResourceRows_subset
  · intro v w hvw
    obtain ⟨a,b,hab,rfl,rfl⟩:=(SimpleGraph.map_adj _ _ _ _).mp
      ((ordinaryHostResources_rim _ _ _).mp hvw)
    exact ⟨Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩,Finset.mem_image.mpr ⟨b,Finset.mem_univ _,rfl⟩⟩
  · intro v u h
    obtain ⟨a,b,hab,rfl,rfl⟩:=(ordinaryHostResources_spoke _ _ _ _).mp h
    exact Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩

theorem OrdinaryPairHostEmbedding.resource_hubs {G₀:SimpleGraph V₀} {H₀:V₀→U₀→Prop}
    {Q:SimpleGraph V} {H:V→U→Prop} (e:OrdinaryPairHostEmbedding G₀ H₀ Q H) :
    ordinaryResourceHubs e.resources⊆Finset.univ.image e.hub := by
  apply ordinaryResourceHubs_subset
  intro v u h
  obtain ⟨a,b,hab,rfl,rfl⟩:=(ordinaryHostResources_spoke _ _ _ _).mp h
  exact Finset.mem_image.mpr ⟨b,Finset.mem_univ _,rfl⟩

theorem ordinary_fresh_expansion_pair_embedding (Q F:SimpleGraph V) (H:V→U→Prop)
    (A W R:Finset V) (B:Finset U) (x y:E→V₀) (v:J→V₀) (u:J→U₀)
    (r:ℕ) (hr:3≤r) (d c cH:ℝ) (hd:0≤d) (hF:∀ v,(F.degree v:ℝ)≤d)
    (hA:c≤(A.card:ℝ)) (hU:cH≤(Fintype.card U:ℝ))
    (hcount:∀ v w,c≤((A∩Q.neighborFinset v∩Q.neighborFinset w).card:ℝ))
    (hpair:∀ a b v w,c≤(((A.filter (fun z=>H z a∧H z b))∩Q.neighborFinset v∩Q.neighborFinset w).card:ℝ))
    (hhub:∀ T:Finset V,T.card≤r→(∀ v∈T,∀ w∈T,¬F.Adj v w)→
      cH≤((common Finset.univ T (fun v=>Finset.univ.filter (H v))).card:ℝ))
    (hbudget:W.card+((R.card:ℝ)+Fintype.card V₀+Fintype.card (E⊕J)*r+r+6)*(d+1)<c)
    (hB:(B.card:ℝ)+Fintype.card U₀+Fintype.card (E⊕J)<cH) :
    ∃ e:OrdinaryPairHostEmbedding
      (ordinaryExpansionRim (J:=J) (SimpleGraph.cycleGraph r) ⟨0,by omega⟩ ⟨r-1,by omega⟩ x y)
      (ordinaryExpansionSpokes (E:=E) ⟨0,by omega⟩ v u) Q H,
      e.IsFresh F A W R B := by
  obtain ⟨f,g,hf,hg,hF',hQ,hH⟩:=ordinary_fresh_expansion_embedding Q F H A W R B x y v u r hr d c cH hd hF hA hU hcount hpair hhub hbudget hB
  exact ⟨⟨f,g,hQ,hH⟩,hf,hg,hF'⟩

end Oberwolfach
