module

public import Oberwolfach.RegularCycleIsomorphism

@[expose] public section
/-! Glue maps on distinct factor components when their vertex images are
pairwise disjoint. The source domain is the disjoint union of those actual
components. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n:ℕ} {A:Type}

theorem component_family_embeddings_glue
    (F:SimpleGraph (Fin n)) (C:A→F.ConnectedComponent)
    (hC:Function.Injective C) (f:∀a,C a↪Fin n)
    (hdis:∀a b,a≠b→Disjoint (Finset.univ.image (f a)) (Finset.univ.image (f b))):
    ∃src dst:(Σa,C a)↪Fin n,
      (∀z,src z=z.2.val) ∧ (∀z,dst z=f z.1 z.2) :=by
  let src:(Σa,C a)↪Fin n:=⟨fun z=>z.2.val,by
    rintro ⟨a,x⟩ ⟨b,y⟩ heq
    change x.val=y.val at heq
    have hy:x.val∈(C b).supp:=by rw [heq];exact y.property
    have hc:C a=C b:=SimpleGraph.ConnectedComponent.eq_of_common_vertex x.property hy
    have hab:a=b:=hC hc
    subst b
    have hxy:x=y:=Subtype.ext heq
    subst y
    rfl⟩
  let dst:(Σa,C a)↪Fin n:=⟨fun z=>f z.1 z.2,by
    rintro ⟨a,x⟩ ⟨b,y⟩ heq
    by_cases hab:a=b
    · subst b
      have hxy:x=y:=(f a).injective heq
      subst y
      rfl
    · have ha:f a x∈Finset.univ.image (f a):=Finset.mem_image.mpr ⟨x,Finset.mem_univ _,rfl⟩
      have hb:f a x∈Finset.univ.image (f b):=Finset.mem_image.mpr ⟨y,Finset.mem_univ _,heq.symm⟩
      exact ((Finset.disjoint_left.mp (hdis a b hab)) ha hb).elim⟩
  exact ⟨src,dst,fun _=>rfl,fun _=>rfl⟩
end Oberwolfach
