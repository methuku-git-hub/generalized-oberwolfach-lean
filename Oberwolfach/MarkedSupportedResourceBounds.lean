module

public import Oberwolfach.MarkedSupportedResourceFamilies

@[expose] public section

/-! Finite size and validity bounds for the actual physical resources of
a supported marked graph. Both ordinary and twisted rim representations
are counted explicitly. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [DecidableEq V] [DecidableEq U]
    {tail head:E→V} {ktail khead:K→V} {π:Equiv.Perm V}

def markedSupportedResources (π:Equiv.Perm V) (X:Finset V) (B:Finset U):Finset (Finset V⊕(V×U)):=
  (X.product X).image (fun a=>Sum.inl ({a.1,a.2}:Finset V))∪
  (X.product X).image (fun a=>Sum.inl ({a.1,π a.2}:Finset V))∪
  (X.product B).image Sum.inr

theorem marked_supported_resources_subset
    (C:MarkedSupportedEdgeSet tail head ktail khead π U):
    C.edges⊆markedSupportedResources π C.rows C.hubs := by
  intro e he
  have hs:=C.supported e he
  cases e with
  | inl e=>
    obtain ⟨a,ha,ht,hh⟩:=hs
    cases a with
    | inl a=>
      apply Finset.mem_union_left
      apply Finset.mem_union_left
      apply Finset.mem_image.mpr
      exact ⟨(tail a,head a),Finset.mem_product.mpr ⟨ht,hh⟩,congrArg Sum.inl ha⟩
    | inr a=>
      apply Finset.mem_union_left
      apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      exact ⟨(ktail a,khead a),Finset.mem_product.mpr ⟨ht,hh⟩,congrArg Sum.inl ha⟩
  | inr a=>
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨a,Finset.mem_product.mpr hs,rfl⟩)

theorem marked_supported_resources_card (π:Equiv.Perm V) (X:Finset V) (B:Finset U):
    (markedSupportedResources π X B).card≤2*X.card^2+X.card*B.card := by
  have h1:((X.product X).image (fun a=>Sum.inl ({a.1,a.2}:Finset V)):Finset (Finset V⊕(V×U))).card≤X.card*X.card:=
    (Finset.card_image_le).trans_eq (Finset.card_product _ _)
  have h2:((X.product X).image (fun a=>Sum.inl ({a.1,π a.2}:Finset V)):Finset (Finset V⊕(V×U))).card≤X.card*X.card:=
    (Finset.card_image_le).trans_eq (Finset.card_product _ _)
  have h3:((X.product B).image (Sum.inr:V×U→Finset V⊕(V×U))).card≤X.card*B.card:=
    (Finset.card_image_le).trans_eq (Finset.card_product _ _)
  have hh:=Finset.card_union_le
    ((X.product X).image (fun a=>Sum.inl ({a.1,a.2}:Finset V))∪
      (X.product X).image (fun a=>Sum.inl ({a.1,π a.2}:Finset V)))
    ((X.product B).image (Sum.inr:V×U→Finset V⊕(V×U)))
  have hh':=Finset.card_union_le
    ((X.product X).image (fun a=>Sum.inl ({a.1,a.2}:Finset V)):Finset (Finset V⊕(V×U)))
    ((X.product X).image (fun a=>Sum.inl ({a.1,π a.2}:Finset V)))
  have ht:=hh.trans (Nat.add_le_add_right hh' _)
  have hf:=ht.trans (Nat.add_le_add (Nat.add_le_add h1 h2) h3)
  calc
    _ ≤ X.card*X.card+X.card*X.card+X.card*B.card:=by
      convert hf using 1 <;> congr!
    _ = _:=by ring

theorem marked_supported_edges_card
    (C:MarkedSupportedEdgeSet tail head ktail khead π U) (a₀ b₀:ℕ)
    (ha:C.rows.card≤a₀) (hb:C.hubs.card≤b₀):C.edges.card≤2*a₀^2+a₀*b₀ := by
  apply ((Finset.card_le_card (marked_supported_resources_subset C)).trans
    (marked_supported_resources_card π C.rows C.hubs)).trans
  have hsq:=Nat.mul_self_le_mul_self ha
  have hprod:=Nat.mul_le_mul ha hb
  nlinarith only [hsq,hprod]

theorem marked_supported_rim_pair
    (C:MarkedSupportedEdgeSet tail head ktail khead π U) (e:Finset V)
    (he:Sum.inl e∈C.edges):e.card≤2 := by
  obtain ⟨a,ha,_,_⟩:=C.supported _ he
  rw [←ha]
  cases a <;> dsimp [markedPhysicalEdge] <;> apply (Finset.card_insert_le _ _).trans <;> simp

end Oberwolfach
