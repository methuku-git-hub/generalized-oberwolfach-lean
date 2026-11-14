module

public import Oberwolfach.ComponentFamilyGluing

@[expose] public section
/-! Count the union of distinct connected components by their actual sizes. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n:ℕ} {A:Type} [Fintype A]

theorem component_family_domain_card
    (F:SimpleGraph (Fin n)) (C:A→F.ConnectedComponent)
    (hC:Function.Injective C):
    Fintype.card {v:Fin n // ∃a,v∈(C a).supp} = ∑a:A,Fintype.card (C a) := by
  let f:(Σa:A,C a)→{v:Fin n // ∃a,v∈(C a).supp}:=fun z=>⟨z.2.val,⟨z.1,z.2.property⟩⟩
  have hinj:Function.Injective f:=by
    rintro ⟨a,x⟩ ⟨b,y⟩ heq
    have hv:x.val=y.val:=congrArg Subtype.val heq
    have hy:x.val∈(C b).supp:=by rw [hv];exact y.property
    have hc:C a=C b:=SimpleGraph.ConnectedComponent.eq_of_common_vertex x.property hy
    have hab:a=b:=hC hc
    subst b
    have hxy:x=y:=Subtype.ext hv
    subst y
    rfl
  have hsurj:Function.Surjective f:=by
    intro v
    obtain ⟨a,ha⟩:=v.property
    exact ⟨⟨a,⟨v.val,ha⟩⟩,Subtype.ext rfl⟩
  calc
    Fintype.card {v:Fin n // ∃a,v∈(C a).supp} = Fintype.card (Σa:A,C a):=
      (Fintype.card_congr (Equiv.ofBijective f ⟨hinj,hsurj⟩)).symm
    _ = ∑a:A,Fintype.card (C a):=Fintype.card_sigma
end Oberwolfach
