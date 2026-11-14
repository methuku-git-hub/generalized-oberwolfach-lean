module

public import Oberwolfach.OrdinaryActiveResources

@[expose] public section

/-! Incidence with actual rim and hub vertices. A leftover degree counts
uncovered physical edges; auxiliary wheel positions are not counted. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def ordinaryResourceIncident {V U : Type*} : V⊕U → Sym2 V⊕(V×U) → Prop
  | Sum.inl v,Sum.inl e => v∈e
  | Sum.inl v,Sum.inr (x,_) => v=x
  | Sum.inr _,Sum.inl _ => False
  | Sum.inr u,Sum.inr (_,y) => u=y

def ordinaryIncidentEdges {V U : Type*} [Fintype V] [Fintype U]
    (Q : SimpleGraph V) (H : V → U → Prop) (x : V⊕U) : Finset (OrdinaryActiveEdge Q H) :=
  Finset.univ.filter (fun e=>ordinaryResourceIncident x e.val)

theorem ordinaryActiveEdge_card_bound {V U : Type*} [Fintype V] [Fintype U]
    (Q : SimpleGraph V) (H : V → U → Prop) :
    Fintype.card (OrdinaryActiveEdge Q H)≤Fintype.card V^2+Fintype.card V*Fintype.card U := by
  have hsym : Fintype.card (Sym2 V)≤Fintype.card V*Fintype.card V := by
    have hs : Function.Surjective (fun xy : V×V=>s(xy.1,xy.2)) := by
      intro e
      induction e using Sym2.ind with
      | _ x y => exact ⟨(x,y),rfl⟩
    simpa only [Fintype.card_prod] using Fintype.card_le_of_surjective _ hs
  have hsub := Fintype.card_subtype_le (fun e=>ordinaryResourceState Q H e=true)
  simp only [Fintype.card_sum,Fintype.card_prod] at hsub
  nlinarith

theorem ordinaryIncidentEdges_card_bound {V U : Type*} [Fintype V] [Fintype U]
    [DecidableEq V] [DecidableEq U]
    (Q : SimpleGraph V) (H : V → U → Prop) (x : V⊕U) :
    (ordinaryIncidentEdges Q H x).card≤Fintype.card V+Fintype.card U := by
  classical
  let S := ordinaryIncidentEdges Q H x
  have hmap : (S.image Subtype.val).card=S.card := Finset.card_image_of_injective _ Subtype.val_injective
  cases x with
  | inl v =>
    let f : V⊕U → Sym2 V⊕(V×U) := Sum.elim (fun z=>Sum.inl s(v,z)) (fun u=>Sum.inr (v,u))
    have hsub : S.image Subtype.val⊆Finset.univ.image f := by
      intro e he
      obtain ⟨ee,hee,rfl⟩ := Finset.mem_image.mp he
      have hi : ordinaryResourceIncident (Sum.inl v) ee.val := (Finset.mem_filter.mp hee).2
      rcases ee with ⟨e,he⟩
      cases e with
      | inl e =>
        obtain ⟨z,hz⟩ := Sym2.mem_iff_exists.mp hi
        exact Finset.mem_image.mpr ⟨Sum.inl z,Finset.mem_univ _,by simp only [f,Sum.elim_inl,hz]⟩
      | inr e =>
        rcases e with ⟨z,u⟩
        change v=z at hi
        subst z
        exact Finset.mem_image.mpr ⟨Sum.inr u,Finset.mem_univ _,rfl⟩
    rw [← hmap]
    exact (Finset.card_le_card hsub).trans (by simpa only [Finset.card_univ,Fintype.card_sum] using Finset.card_image_le (s:=Finset.univ) (f:=f))
  | inr u =>
    let f : V → Sym2 V⊕(V×U) := fun v=>Sum.inr (v,u)
    have hsub : S.image Subtype.val⊆Finset.univ.image f := by
      intro e he
      obtain ⟨ee,hee,rfl⟩ := Finset.mem_image.mp he
      have hi : ordinaryResourceIncident (Sum.inr u) ee.val := (Finset.mem_filter.mp hee).2
      rcases ee with ⟨e,he⟩
      cases e with
      | inl e => exact hi.elim
      | inr e =>
        rcases e with ⟨v,z⟩
        change u=z at hi
        subst z
        exact Finset.mem_image.mpr ⟨v,Finset.mem_univ _,rfl⟩
    rw [← hmap]
    exact ((Finset.card_le_card hsub).trans (by simpa only [Finset.card_univ] using Finset.card_image_le (s:=Finset.univ) (f:=f))).trans (Nat.le_add_right _ _)

theorem ordinaryActiveResources_matching_physical {V U : Type*} [Fintype V] [Fintype U]
    [DecidableEq V] [DecidableEq U] {Q F : SimpleGraph V} {H : V → U → Prop} {r : ℕ}
    (M : Finset (OrdinaryWheel Q F H r))
    (hM : ∀ W∈M,∀ Z∈M,W≠Z → Disjoint (ordinaryActiveResources W) (ordinaryActiveResources Z)) :
    ∀ W∈M,∀ Z∈M,W≠Z → Disjoint (ordinaryWheelResources W) (ordinaryWheelResources Z) := by
  intro W hW Z hZ hne
  apply Finset.disjoint_left.mpr
  intro e he hf
  let e' : OrdinaryActiveEdge Q H := ⟨e,ordinaryWheelResources_present W e he⟩
  exact Finset.disjoint_left.mp (hM W hW Z hZ hne)
    ((ordinaryActiveResources_mem W e').mpr he) ((ordinaryActiveResources_mem Z e').mpr hf)

end Oberwolfach
