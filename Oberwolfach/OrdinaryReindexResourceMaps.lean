module

public import Oberwolfach.OrdinaryExpansionReindex

@[expose] public section

/-! Exact physical resource bijections under reindexing. This identifies
the two central expansions when their original edge counts agree. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E E' J J' W : Type}
    [Fintype V] [Fintype U] [Fintype E] [Fintype E'] [Fintype J] [Fintype J'] [Fintype W]
    [DecidableEq V] [DecidableEq U] [DecidableEq E] [DecidableEq E'] [DecidableEq J] [DecidableEq J'] [DecidableEq W]

def expansionReindexResource (e : E≃E') (j : J≃J') :
    (Sym2 (ExpansionRow V E J W)⊕(ExpansionRow V E J W×ExpansionHub U E J)) →
    (Sym2 (ExpansionRow V E' J' W)⊕(ExpansionRow V E' J' W×ExpansionHub U E' J')) :=
  Sum.map (Sym2.map (expansionReindexRow e j))
    (Prod.map (expansionReindexRow e j) (expansionReindexHub e j))

theorem expansionReindexResource_injective (e : E≃E') (j : J≃J') :
    Function.Injective (expansionReindexResource (V:=V) (U:=U) (W:=W) e j) := by
  intro a b h
  cases a with
  | inl a =>
    cases b with
    | inl b => exact congrArg Sum.inl (Sym2.map.injective (expansionReindexRow e j).injective (Sum.inl.inj h))
    | inr b => cases h
  | inr a =>
    cases b with
    | inl b => cases h
    | inr b =>
      have hh := Sum.inr.inj h
      exact congrArg Sum.inr (Prod.ext ((expansionReindexRow e j).injective (congrArg Prod.fst hh))
        ((expansionReindexHub e j).injective (congrArg Prod.snd hh)))

theorem ordinaryExpansion_reindex_resources (C : SimpleGraph W) (z o : W)
    (x y : E → V) (v : J → V) (u : J → U) (e : E≃E') (j : J≃J') :
    (ordinaryHostResources (ordinaryExpansionRim C z o x y) (ordinaryExpansionSpokes z v u)).image
      (expansionReindexResource e j)=
      ordinaryHostResources (ordinaryExpansionRim C z o (x∘e.symm) (y∘e.symm))
        (ordinaryExpansionSpokes z (v∘j.symm) (u∘j.symm)) := by
  ext a
  constructor
  · intro ha
    obtain ⟨a,hmem,rfl⟩ := Finset.mem_image.mp ha
    cases a with
    | inl a =>
      induction a using Sym2.ind with
      | _ b c =>
        rw [ordinaryHostResources_rim] at hmem
        exact (ordinaryHostResources_rim _ _ _).mpr ((ordinaryExpansion_reindex_rim C z o x y e j b c).mpr hmem)
    | inr p =>
      rcases p with ⟨b,c⟩
      rw [ordinaryHostResources_spoke] at hmem
      exact (ordinaryHostResources_spoke _ _ _ _).mpr ((ordinaryExpansion_reindex_spoke z v u e j b c).mpr hmem)
  · intro ha
    cases a with
    | inl a =>
      induction a using Sym2.ind with
      | _ b c =>
        obtain ⟨b,rfl⟩ := (expansionReindexRow (V:=V) (W:=W) e j).surjective b
        obtain ⟨c,rfl⟩ := (expansionReindexRow (V:=V) (W:=W) e j).surjective c
        rw [ordinaryHostResources_rim] at ha
        exact Finset.mem_image.mpr ⟨.inl s(b,c),(ordinaryHostResources_rim _ _ _).mpr
          ((ordinaryExpansion_reindex_rim C z o x y e j b c).mp ha),rfl⟩
    | inr p =>
      rcases p with ⟨b,c⟩
      obtain ⟨b,rfl⟩ := (expansionReindexRow (V:=V) (W:=W) e j).surjective b
      obtain ⟨c,rfl⟩ := (expansionReindexHub (U:=U) e j).surjective c
      rw [ordinaryHostResources_spoke] at ha
      exact Finset.mem_image.mpr ⟨.inr (b,c),(ordinaryHostResources_spoke _ _ _ _).mpr
        ((ordinaryExpansion_reindex_spoke z v u e j b c).mp ha),rfl⟩

theorem ordinaryExpansion_common_central_resources
    (C : SimpleGraph W) (z o : W) (hzo : z≠o)
    (x y : E → V) (v : J → V) (u : J → U) (e : E≃E') (j : J≃J') :
    let S := ordinaryHostResources (ordinaryExpansionRim C z o x y) (ordinaryExpansionSpokes z v u)
    let T := ordinaryHostResources (ordinaryExpansionRim (J:=J') C z o (fun _ : E' => ()) (fun _ => ()))
      (ordinaryExpansionSpokes (E:=E') z (fun _ : J' => ()) (fun _ => ()))
    let f := expansionReindexResource (V:=Unit) (U:=Unit) (W:=W) e j ∘
      expansionResourceMap (E:=E) (J:=J) (W:=W) (fun _ : V => ()) (fun _ : U => ())
    Set.InjOn f S ∧ S.image f=T := by
  dsimp only
  constructor
  · intro a ha b hb he
    exact ordinaryExpansion_resources_injective C z o hzo x y v u _ _ ha hb
      (expansionReindexResource_injective e j he)
  · rw [←Finset.image_image,ordinaryExpansion_resources_image,ordinaryExpansion_reindex_resources]

end Oberwolfach
