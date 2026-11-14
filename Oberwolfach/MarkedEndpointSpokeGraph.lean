module

public import Oberwolfach.OrdinaryBoundaryGraph
public import Oberwolfach.MarkedEndpointAssignments

@[expose] public section

/-! Physical spoke graphs of the two marked endpoint assignments. Labels
may occur twice among the typed indices; the degree estimate retains that
multiplicity instead of assuming injectivity of the label maps. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Y : Type} [Fintype V] [Fintype U] [Fintype Y] [DecidableEq V] [DecidableEq U]

def markedEndpointSpokes (a x : Y→V) (u : Y↪U) (v : V) (w : U) : Prop :=
  ∃ y,u y=w ∧ (a y=v ∨ x y=v)

def markedEndpointSpokeGraph (a x : Y→V) (u : Y↪U) : SimpleGraph (V⊕U) :=
  ordinaryPhysicalGraph ⊥ (markedEndpointSpokes a x u)

theorem marked_endpoint_spoke_row_bound (a x : Y→V) (u : Y↪U) (M : ℕ)
    (ha : ∀ v,Fintype.card {y // a y=v}≤M)
    (hx : ∀ v,Fintype.card {y // x y=v}≤M) (v : V) :
    (markedEndpointSpokeGraph a x u).degree (Sum.inl v)≤2*M := by
  let A := Finset.univ.filter (fun y=>a y=v)
  let X := Finset.univ.filter (fun y=>x y=v)
  have hs : (markedEndpointSpokeGraph a x u).neighborFinset (Sum.inl v)⊆
      (A.image (fun y=>Sum.inr (u y)))∪(X.image (fun y=>Sum.inr (u y))) := by
    intro z hz
    have hh := (SimpleGraph.mem_neighborFinset _ _ _).mp hz
    cases z with
    | inl w=>exact False.elim hh
    | inr w=>
      obtain ⟨y,hy,hyA|hyX⟩ := hh
      · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨y,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hyA⟩,congrArg Sum.inr hy⟩)
      · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨y,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hyX⟩,congrArg Sum.inr hy⟩)
  have ha' : A.card≤M := by simpa only [A,Fintype.card_subtype] using ha v
  have hx' : X.card≤M := by simpa only [X,Fintype.card_subtype] using hx v
  rw [←SimpleGraph.card_neighborFinset_eq_degree]
  calc
    _ ≤ _ := Finset.card_le_card hs
    _ ≤ (A.image (fun y=>Sum.inr (u y))).card+(X.image (fun y=>Sum.inr (u y))).card := Finset.card_union_le _ _
    _ ≤ A.card+X.card := Nat.add_le_add (Finset.card_image_le) (Finset.card_image_le)
    _ ≤ 2*M := by omega

theorem marked_endpoint_spoke_hub_bound (a x : Y→V) (u : Y↪U) (w : U) :
    (markedEndpointSpokeGraph a x u).degree (Sum.inr w)≤2 := by
  rw [←SimpleGraph.card_neighborFinset_eq_degree]
  by_cases hw : ∃ y,u y=w
  · obtain ⟨y,hy⟩ := hw
    have hs : (markedEndpointSpokeGraph a x u).neighborFinset (Sum.inr w)⊆
        {Sum.inl (a y),Sum.inl (x y)} := by
      intro z hz
      have hh := (SimpleGraph.mem_neighborFinset _ _ _).mp hz
      cases z with
      | inr w'=>exact False.elim hh
      | inl v=>
        obtain ⟨y',hy',hh⟩ := hh
        have he : y'=y := u.injective (hy'.trans hy.symm)
        subst y'
        simpa only [Finset.mem_insert,Finset.mem_singleton,Sum.inl.injEq,eq_comm] using hh
    exact (Finset.card_le_card hs).trans Finset.card_le_two
  · have he : (markedEndpointSpokeGraph a x u).neighborFinset (Sum.inr w)=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro z hz
      have hh := (SimpleGraph.mem_neighborFinset _ _ _).mp hz
      cases z with
      | inr w'=>exact hh
      | inl v=>obtain ⟨y,hy,_⟩:=hh;exact hw ⟨y,hy⟩
    rw [he];simp

theorem marked_endpoint_spoke_degree (a x : Y→V) (u : Y↪U)
    (ha : ∀ v,Fintype.card {y // a y=v}≤2)
    (hx : ∀ v,Fintype.card {y // x y=v}≤2) (z : V⊕U) :
    (markedEndpointSpokeGraph a x u).degree z≤4 := by
  cases z with
  | inl v=>exact marked_endpoint_spoke_row_bound a x u 2 ha hx v
  | inr w=>exact (marked_endpoint_spoke_hub_bound a x u w).trans (by omega)

theorem marked_endpoint_spoke_support (a x : Y→V) (u : Y↪U) (A : Finset V) (B : Finset U)
    (ha : ∀ y,a y∈A) (hx : ∀ y,x y∈A) (hu : ∀ y,u y∈B) :
    GraphSupportedOn (ordinaryInnerVertices A B) (markedEndpointSpokeGraph a x u) := by
  intro z w hzw
  cases z with
  | inl v=>cases w with
    | inl v'=>exact False.elim hzw
    | inr b=>
      obtain ⟨y,hy,hav|hxv⟩:=hzw
      · exact ⟨(ordinaryInnerVertices_left A B v).mpr (hav ▸ ha y),(ordinaryInnerVertices_right A B b).mpr (hy ▸ hu y)⟩
      · exact ⟨(ordinaryInnerVertices_left A B v).mpr (hxv ▸ hx y),(ordinaryInnerVertices_right A B b).mpr (hy ▸ hu y)⟩
  | inr b=>cases w with
    | inr b'=>exact False.elim hzw
    | inl v=>
      obtain ⟨y,hy,hav|hxv⟩:=hzw
      · exact ⟨(ordinaryInnerVertices_right A B b).mpr (hy ▸ hu y),(ordinaryInnerVertices_left A B v).mpr (hav ▸ ha y)⟩
      · exact ⟨(ordinaryInnerVertices_right A B b).mpr (hy ▸ hu y),(ordinaryInnerVertices_left A B v).mpr (hxv ▸ hx y)⟩

theorem marked_endpoint_spoke_subgraph (a x : Y→V) (u : Y↪U) (H : V→U→Prop)
    (ha : ∀ y,H (a y) (u y)) (hx : ∀ y,H (x y) (u y)) :
    markedEndpointSpokeGraph a x u≤ordinaryPhysicalGraph ⊥ H := by
  intro z w hzw
  cases z <;> cases w
  · exact False.elim hzw
  · obtain ⟨y,rfl,h|h⟩:=hzw
    · exact h ▸ ha y
    · exact h ▸ hx y
  · obtain ⟨y,rfl,h|h⟩:=hzw
    · exact h ▸ ha y
    · exact h ▸ hx y
  · exact hzw

end Oberwolfach
