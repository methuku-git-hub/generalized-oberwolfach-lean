module

public import Oberwolfach.OrdinaryExpansionSpokeMaps
public import Oberwolfach.OrdinaryDecompositionEdges

@[expose] public section

/-! Exact physical rim/spoke resource images for the collapse map.
This supplies both surjectivity and multiplicity one to transformer callers. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V V' U U' E J W : Type}
variable [Fintype V] [Fintype V'] [Fintype U] [Fintype U'] [Fintype E] [Fintype J] [Fintype W]
variable [DecidableEq V] [DecidableEq V'] [DecidableEq U] [DecidableEq U']
    [DecidableEq E] [DecidableEq J] [DecidableEq W]

def expansionResourceMap (f : V → V') (g : U → U') :
    (Sym2 (ExpansionRow V E J W) ⊕ (ExpansionRow V E J W × ExpansionHub U E J)) →
    (Sym2 (ExpansionRow V' E J W) ⊕ (ExpansionRow V' E J W × ExpansionHub U' E J)) :=
  Sum.map (Sym2.map (expansionRowMap f)) (Prod.map (expansionRowMap f) (expansionHubMap g))

theorem ordinaryExpansion_resources_image (C : SimpleGraph W) (z o : W) (x y : E → V)
    (v : J → V) (u : J → U) (f : V → V') (g : U → U') :
    (ordinaryHostResources (ordinaryExpansionRim C z o x y) (ordinaryExpansionSpokes z v u)).image
      (expansionResourceMap f g)=
    ordinaryHostResources (ordinaryExpansionRim C z o (f ∘ x) (f ∘ y))
      (ordinaryExpansionSpokes z (f ∘ v) (g ∘ u)) := by
  ext e
  constructor
  · intro himage
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp himage
    cases e with
    | inl e =>
      rw [ordinaryHostResources_rim] at he
      induction e using Sym2.ind with
      | _ a b =>
        apply (ordinaryHostResources_rim _ _ _).mpr
        exact ordinaryExpansion_rim_hom C z o x y f a b he
    | inr p =>
      rcases p with ⟨a,b⟩
      rw [ordinaryHostResources_spoke] at he
      exact (ordinaryHostResources_spoke _ _ _ _).mpr (ordinaryExpansion_spoke_hom z v u f g a b he)
  · intro he
    cases e with
    | inl e =>
      rw [ordinaryHostResources_rim] at he
      induction e using Sym2.ind with
      | _ a b =>
        obtain ⟨a',b',hab,ha,hb⟩ := ordinaryExpansion_rim_preimage C z o x y f a b he
        refine Finset.mem_image.mpr ⟨.inl s(a',b'),(ordinaryHostResources_rim _ _ _).mpr hab,?_⟩
        change Sum.inl s(expansionRowMap f a',expansionRowMap f b')=Sum.inl s(a,b)
        rw [ha,hb]
    | inr p =>
      rcases p with ⟨a,b⟩
      rw [ordinaryHostResources_spoke] at he
      obtain ⟨a',b',hab,ha,hb⟩ := ordinaryExpansion_spoke_preimage z v u f g a b he
      refine Finset.mem_image.mpr ⟨.inr (a',b'),(ordinaryHostResources_spoke _ _ _ _).mpr hab,?_⟩
      change Sum.inr (expansionRowMap f a',expansionHubMap g b')=Sum.inr (a,b)
      rw [ha,hb]

theorem ordinaryExpansion_resources_injective (C : SimpleGraph W) (z o : W) (hzo : z≠o)
    (x y : E → V) (v : J → V) (u : J → U) (f : V → V') (g : U → U') :
    Set.InjOn (expansionResourceMap (E:=E) (J:=J) (W:=W) f g)
      (ordinaryHostResources (ordinaryExpansionRim C z o x y) (ordinaryExpansionSpokes z v u)) := by
  intro e he e' he' hh
  cases e with
  | inl e =>
    cases e' with
    | inr p => cases hh
    | inl e' =>
      rw [Finset.mem_coe,ordinaryHostResources_rim] at he he'
      exact congrArg Sum.inl (ordinaryExpansion_rim_edge_injective C z o hzo x y f he he' (Sum.inl.inj hh))
  | inr p =>
    cases e' with
    | inl e' => cases hh
    | inr q =>
      rcases p with ⟨a,b⟩;rcases q with ⟨c,d⟩
      rw [Finset.mem_coe,ordinaryHostResources_spoke] at he he'
      exact congrArg Sum.inr (ordinaryExpansion_spoke_injective z v u f g he he' (Sum.inr.inj hh))

end Oberwolfach
