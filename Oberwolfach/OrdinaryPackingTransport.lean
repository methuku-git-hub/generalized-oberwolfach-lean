module

public import Oberwolfach.OrdinaryWheelRestriction
public import Oberwolfach.OrdinaryIncidentResources

@[expose] public section

/-! Physical incident sets and transport of a packing from a smaller host. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V U : Type*} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

def ordinaryPhysicalIncidentEdges (Q : SimpleGraph V) (H : V → U → Prop)
    (x : V⊕U) : Finset (Sym2 V⊕(V×U)) :=
  Finset.univ.filter (fun e=>ordinaryResourceState Q H e=true ∧ ordinaryResourceIncident x e)

theorem ordinaryIncidentEdges_image (Q : SimpleGraph V) (H : V → U → Prop) (x : V⊕U) :
    (ordinaryIncidentEdges Q H x).image Subtype.val=ordinaryPhysicalIncidentEdges Q H x := by
  ext e
  simp only [ordinaryIncidentEdges,ordinaryPhysicalIncidentEdges,Finset.mem_image,
    Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨⟨a,ha⟩,hx,rfl⟩
    exact ⟨ha,hx⟩
  · rintro ⟨ha,hx⟩
    exact ⟨⟨e,ha⟩,hx,rfl⟩

theorem ordinaryActiveResources_image {Q F : SimpleGraph V} {H : V → U → Prop} {r : ℕ}
    (W : OrdinaryWheel Q F H r) :
    (ordinaryActiveResources W).image Subtype.val=ordinaryWheelResources W := by
  ext e
  simp only [Finset.mem_image,ordinaryActiveResources_mem]
  constructor
  · rintro ⟨a,ha,rfl⟩;exact ha
  · intro he
    exact ⟨⟨e,ordinaryWheelResources_present W e he⟩,he,rfl⟩

theorem ordinary_leftover_card_physical {Q F : SimpleGraph V} {H : V → U → Prop} {r : ℕ}
    (M : Finset (OrdinaryWheel Q F H r)) (x : V⊕U) :
    (ordinaryIncidentEdges Q H x \ M.biUnion ordinaryActiveResources).card=
      (ordinaryPhysicalIncidentEdges Q H x \ M.biUnion ordinaryWheelResources).card := by
  have hh := Finset.card_image_of_injective
    (ordinaryIncidentEdges Q H x \ M.biUnion ordinaryActiveResources) Subtype.val_injective
  rw [Finset.image_sdiff _ _ Subtype.val_injective,ordinaryIncidentEdges_image,
    Finset.biUnion_image] at hh
  simp only [ordinaryActiveResources_image] at hh
  exact hh.symm

theorem ordinaryPhysicalIncidentEdges_rim (Q : SimpleGraph V) (H : V → U → Prop) (v : V) :
    ordinaryPhysicalIncidentEdges Q H (Sum.inl v)=
      (Q.incidenceFinset v).image Sum.inl ∪
      (Finset.univ.filter (H v)).image (fun u=>Sum.inr (v,u)) := by
  ext e
  cases e with
  | inl e =>
    simp only [ordinaryPhysicalIncidentEdges,Finset.mem_filter,Finset.mem_univ,true_and,
      ordinaryResourceState,Sum.elim_inl,decide_eq_true_eq,ordinaryResourceIncident,
      Finset.mem_union,Finset.mem_image,Sum.inl.injEq,Sum.inr_ne_inl,and_false,exists_false,
      or_false,exists_eq_right,SimpleGraph.mem_incidenceFinset]
    rfl
  | inr vu =>
    rcases vu with ⟨z,u⟩
    simp only [ordinaryPhysicalIncidentEdges,Finset.mem_filter,Finset.mem_univ,true_and,
      ordinaryResourceState,Sum.elim_inr,decide_eq_true_eq,ordinaryResourceIncident,
      Finset.mem_union,Finset.mem_image,Sum.inl_ne_inr,and_false,exists_false,false_or,
      Sum.inr.injEq,Prod.mk.injEq]
    constructor
    · rintro ⟨h,rfl⟩;exact ⟨u,h,rfl,rfl⟩
    · rintro ⟨a,h,rfl,rfl⟩;exact ⟨h,rfl⟩

theorem ordinaryPhysicalIncidentEdges_hub (Q : SimpleGraph V) (H : V → U → Prop) (u : U) :
    ordinaryPhysicalIncidentEdges Q H (Sum.inr u)=
      (Finset.univ.filter (fun v=>H v u)).image (fun v=>Sum.inr (v,u)) := by
  ext e
  cases e with
  | inl e => simp [ordinaryPhysicalIncidentEdges,ordinaryResourceIncident]
  | inr vu =>
    rcases vu with ⟨v,a⟩
    simp only [ordinaryPhysicalIncidentEdges,Finset.mem_filter,Finset.mem_univ,true_and,
      ordinaryResourceState,Sum.elim_inr,decide_eq_true_eq,ordinaryResourceIncident,
      Finset.mem_image,Sum.inr.injEq,Prod.mk.injEq]
    constructor
    · rintro ⟨h,rfl⟩;exact ⟨v,h,rfl,rfl⟩
    · rintro ⟨z,h,rfl,rfl⟩;exact ⟨h,rfl⟩

theorem ordinaryPhysicalIncidentEdges_rim_card (Q : SimpleGraph V) (H : V → U → Prop) (v : V) :
    (ordinaryPhysicalIncidentEdges Q H (Sum.inl v)).card=
      Q.degree v+(Finset.univ.filter (H v)).card := by
  rw [ordinaryPhysicalIncidentEdges_rim,Finset.card_union_of_disjoint]
  · rw [Finset.card_image_of_injective _ Sum.inl_injective,
      Finset.card_image_of_injective _ (by intro a b he;simpa using he),
      SimpleGraph.card_incidenceFinset_eq_degree]
  · apply Finset.disjoint_left.mpr
    intro e he hf
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp he
    obtain ⟨b,hb,hb'⟩ := Finset.mem_image.mp hf
    exact Sum.inr_ne_inl hb'

theorem ordinaryPhysicalIncidentEdges_hub_card (Q : SimpleGraph V) (H : V → U → Prop) (u : U) :
    (ordinaryPhysicalIncidentEdges Q H (Sum.inr u)).card=
      (Finset.univ.filter (fun v=>H v u)).card := by
  rw [ordinaryPhysicalIncidentEdges_hub]
  exact Finset.card_image_of_injective _ (by intro a b he;simpa using he)

theorem ordinaryPhysicalIncidentEdges_delete (Q D : SimpleGraph V) (H E : V → U → Prop)
    (x : V⊕U) :
    ordinaryPhysicalIncidentEdges (Q\D) (fun v u=>H v u ∧ ¬E v u) x=
      ordinaryPhysicalIncidentEdges Q H x \ ordinaryPhysicalIncidentEdges D E x := by
  ext e
  simp only [ordinaryPhysicalIncidentEdges,Finset.mem_filter,Finset.mem_univ,true_and,
    Finset.mem_sdiff]
  cases e with
  | inl e =>
    induction e using Sym2.ind with
    | _ v w =>
      simp only [ordinaryResourceState,Sum.elim_inl,decide_eq_true_eq,SimpleGraph.mem_edgeSet,
        SimpleGraph.sdiff_adj]
      tauto
  | inr vu =>
    simp only [ordinaryResourceState,Sum.elim_inr,decide_eq_true_eq]
    tauto

theorem finset_uncovered_le_after_deletion {α : Type*} [DecidableEq α]
    (S D C : Finset α) : (S\C).card≤((S\D)\C).card+D.card := by
  calc
    _ ≤ (((S\D)\C)∪D).card := by
      apply Finset.card_le_card
      intro e he
      simp only [Finset.mem_sdiff,Finset.mem_union] at *
      tauto
    _ ≤ _ := Finset.card_union_le _ _

theorem ordinary_packing_transport {P Q F : SimpleGraph V} {Hbase H : V → U → Prop} {r : ℕ}
    (hQ : Q≤P) (hH : ∀ v u,H v u → Hbase v u)
    (M : Finset (OrdinaryWheel Q F H r))
    (hM : ∀ W∈M,∀ Z∈M,W≠Z → Disjoint (ordinaryWheelResources W) (ordinaryWheelResources Z)) :
    let M' := M.image (ordinaryWheelToLarger (F:=F) (r:=r) hQ hH)
    (∀ W∈M',∀ Z∈M',W≠Z → Disjoint (ordinaryWheelResources W) (ordinaryWheelResources Z)) ∧
    M'.biUnion ordinaryWheelResources=M.biUnion ordinaryWheelResources := by
  constructor
  · intro W hW Z hZ hne
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hW
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hZ
    exact hM w hw z hz (by intro he;exact hne (congrArg _ he))
  · rw [Finset.image_biUnion]
    rfl

end Oberwolfach
