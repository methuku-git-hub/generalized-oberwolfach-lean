module

public import Oberwolfach.OrdinaryDecompositionEdges
public import Oberwolfach.FractionalRelabeling

@[expose] public section

/-! Actual graph pairs and physical edge maps under injective row and
hub embeddings. Rim and spoke edge types remain distinct. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U V' U' : Type*} [Fintype V] [Fintype U] [Fintype V'] [Fintype U']
    [DecidableEq V] [DecidableEq U] [DecidableEq V'] [DecidableEq U']

def ordinaryPairResourceEmbedding (φ : V ↪ V') (ψ : U ↪ U') : (Sym2 V⊕(V×U)) ↪ (Sym2 V'⊕(V'×U')) where
  toFun := Sum.map (Sym2.map φ) (Prod.map φ ψ)
  inj' := by
    intro a b h
    cases a with
    | inl a =>
      cases b with
      | inl b => exact congrArg Sum.inl (Sym2.map.injective φ.injective (Sum.inl.inj h))
      | inr b => cases h
    | inr a =>
      cases b with
      | inl b => cases h
      | inr b =>
        have he := Sum.inr.inj h
        exact congrArg Sum.inr (Prod.ext (φ.injective (congrArg Prod.fst he)) (ψ.injective (congrArg Prod.snd he)))

def ordinaryMappedSpokes (H : V → U → Prop) (φ : V ↪ V') (ψ : U ↪ U') : V' → U' → Prop :=
  fun a b => ∃ v u,H v u ∧ φ v=a ∧ ψ u=b

theorem ordinaryMappedSpokes_apply (H : V → U → Prop) (φ : V ↪ V') (ψ : U ↪ U') (v : V) (u : U) :
    ordinaryMappedSpokes H φ ψ (φ v) (ψ u) ↔ H v u := by
  constructor
  · rintro ⟨v',u',h,he,he'⟩
    rw [φ.injective he,ψ.injective he'] at h
    exact h
  · exact fun h => ⟨v,u,h,rfl,rfl⟩

theorem ordinaryHostResources_embedding_image (G : SimpleGraph V) (H : V → U → Prop)
    (φ : V ↪ V') (ψ : U ↪ U') :
    (ordinaryHostResources G H).image (ordinaryPairResourceEmbedding φ ψ)=
      ordinaryHostResources (G.map φ) (ordinaryMappedSpokes H φ ψ) := by
  ext e
  constructor
  · intro him
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp him
    cases a with
    | inl a =>
      induction a using Sym2.ind with
      | _ v w =>
        rw [ordinaryHostResources_rim] at ha
        exact (ordinaryHostResources_rim _ _ _).mpr (SimpleGraph.map_adj_apply.mpr ha)
    | inr a =>
      rcases a with ⟨v,u⟩
      exact (ordinaryHostResources_spoke _ _ _ _).mpr
        ⟨v,u,(ordinaryHostResources_spoke _ _ _ _).mp ha,rfl,rfl⟩
  · intro he
    cases e with
    | inl e =>
      induction e using Sym2.ind with
      | _ a b =>
        rw [ordinaryHostResources_rim,SimpleGraph.mem_edgeSet,SimpleGraph.map_adj] at he
        obtain ⟨v,w,hvw,hv,hw⟩ := he
        refine Finset.mem_image.mpr ⟨.inl s(v,w),(ordinaryHostResources_rim _ _ _).mpr hvw,?_⟩
        change Sum.inl s(φ v,φ w)=Sum.inl s(a,b)
        rw [hv,hw]
    | inr p =>
      rcases p with ⟨a,b⟩
      obtain ⟨v,u,hvu,hv,hu⟩ := (ordinaryHostResources_spoke _ _ _ _).mp he
      refine Finset.mem_image.mpr ⟨.inr (v,u),(ordinaryHostResources_spoke _ _ _ _).mpr hvu,?_⟩
      change Sum.inr (φ v,ψ u)=Sum.inr (a,b)
      rw [hv,hu]

def universalOrdinaryWheelEmbedding {r : ℕ} (φ : V ↪ V') (ψ : U ↪ U')
    (W : UniversalOrdinaryWheel V U r) : UniversalOrdinaryWheel V' U' r :=
  ⟨(⟨⟨(ordinaryWheelRim W).map φ,W.val.1.val.property.map φ⟩,le_top⟩,ψ (ordinaryWheelHub W)),
    fun _ _ => trivial,fun _ _ _ _ => not_false⟩

theorem universalOrdinaryWheelEmbedding_resources {r : ℕ} (φ : V ↪ V') (ψ : U ↪ U')
    (W : UniversalOrdinaryWheel V U r) :
    ordinaryWheelResources (universalOrdinaryWheelEmbedding φ ψ W)=
      (ordinaryWheelResources W).image (ordinaryPairResourceEmbedding φ ψ) := by
  ext e
  constructor
  · intro he
    cases e with
    | inl e =>
      induction e using Sym2.ind with
      | _ a b =>
        rw [ordinaryWheelResources_rim] at he
        change ((ordinaryWheelRim W).map φ).Adj a b at he
        obtain ⟨v,w,hvw,hv,hw⟩ := (SimpleGraph.map_adj _ _ _ _).mp he
        refine Finset.mem_image.mpr ⟨.inl s(v,w),(ordinaryWheelResources_rim _ _).mpr hvw,?_⟩
        change Sum.inl s(φ v,φ w)=Sum.inl s(a,b)
        rw [hv,hw]
    | inr p =>
      rcases p with ⟨a,b⟩
      rw [ordinaryWheelResources_spoke] at he
      have hh : ψ (ordinaryWheelHub W)=b := he.1
      have hs : a∈((ordinaryWheelRim W).map φ).support := he.2
      rw [SimpleGraph.support_map] at hs
      obtain ⟨v,hv,hva⟩ := hs
      refine Finset.mem_image.mpr ⟨.inr (v,ordinaryWheelHub W),(ordinaryWheelResources_spoke _ _ _).mpr ⟨rfl,hv⟩,?_⟩
      change Sum.inr (φ v,ψ (ordinaryWheelHub W))=Sum.inr (a,b)
      rw [hva,hh]
  · intro he
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp he
    cases a with
    | inl a =>
      induction a using Sym2.ind with
      | _ v w =>
        rw [ordinaryWheelResources_rim] at ha
        apply (ordinaryWheelResources_rim _ _).mpr
        change ((ordinaryWheelRim W).map φ).Adj (φ v) (φ w)
        exact SimpleGraph.map_adj_apply.mpr ha
    | inr p =>
      rcases p with ⟨v,u⟩
      rw [ordinaryWheelResources_spoke] at ha
      apply (ordinaryWheelResources_spoke _ _ _).mpr
      refine ⟨congrArg ψ ha.1,?_⟩
      change φ v∈((ordinaryWheelRim W).map φ).support
      rw [SimpleGraph.support_map]
      exact ⟨v,ha.2,rfl⟩

end Oberwolfach
