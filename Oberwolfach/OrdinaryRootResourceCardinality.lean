module

public import Oberwolfach.OrdinaryRootResources

@[expose] public section
/-! A terminal row/hub pair determines only a bounded number of resources,
independently of the size of the ambient host. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_root_resources_card_le (W:Finset V) (B:Finset U):
    (ordinaryRootResources W B).card≤W.card*W.card+W.card*B.card:=by
  let Rim:Finset (Sym2 V⊕(V×U)):=(W.product W).image (fun p=>Sum.inl s(p.1,p.2))
  let Spoke:Finset (Sym2 V⊕(V×U)):=(W.product B).image (fun p=>Sum.inr p)
  have hsub:ordinaryRootResources W B⊆Rim∪Spoke:=by
    intro e he
    cases e with
    | inl e =>
      induction e using Sym2.inductionOn with
      | _ v w =>
        have hvw: v∈W ∧ w∈W:=(ordinaryRootResources_rim_iff W B v w).mp he
        apply Finset.mem_union_left
        exact Finset.mem_image.mpr ⟨(v,w),Finset.mem_product.mpr hvw,rfl⟩
    | inr p =>
      rcases p with ⟨v,u⟩
      have hvu:v∈W ∧ u∈B:=(ordinaryRootResources_spoke_iff W B v u).mp he
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨(v,u),Finset.mem_product.mpr hvu,rfl⟩
  calc
    _ ≤ (Rim∪Spoke).card:=Finset.card_le_card hsub
    _ ≤ Rim.card+Spoke.card:=Finset.card_union_le _ _
    _ ≤ (W.product W).card+(W.product B).card:=Nat.add_le_add Finset.card_image_le Finset.card_image_le
    _ = W.card*W.card+W.card*B.card:=by
      have h₁:=Finset.card_product W W
      have h₂:=Finset.card_product W B
      exact congrArg₂ (· + ·) h₁ h₂
end Oberwolfach
