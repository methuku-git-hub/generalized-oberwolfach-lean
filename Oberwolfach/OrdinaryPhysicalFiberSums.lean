module

public import Oberwolfach.OrdinaryMixedPhysicalResourceFiber

@[expose] public section
/-! Exact typed fibers over a physical rim edge or spoke pair. These sums
keep the two possible orientations and the shifted closing representation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]

abbrev OrdinaryTypedResource (V U:Type):Type:=((V×V)⊕(V×V))⊕(Bool×V×U)

theorem ordinary_physical_spoke_fiber
    (π:Equiv.Perm V) (x:V) (u:U):
    Finset.univ.filter (fun a:OrdinaryTypedResource V U=>ordinaryMixedPhysicalResource π a=Sum.inr (x,u))=
      {Sum.inr (false,x,u),Sum.inr (true,x,u)} :=by
  ext a
  cases a with
  | inl a=>simp [ordinaryMixedPhysicalResource]
  | inr a=>
    obtain ⟨j,v,w⟩:=a
    cases j <;> simp [ordinaryMixedPhysicalResource,Prod.ext_iff]

theorem ordinary_physical_rim_fiber
    (π:Equiv.Perm V) (x y:V):
    Finset.univ.filter (fun a:OrdinaryTypedResource V U=>ordinaryMixedPhysicalResource π a=Sum.inl s(x,y))=
      {Sum.inl (Sum.inl (x,y)),Sum.inl (Sum.inl (y,x)),
       Sum.inl (Sum.inr (x,π.symm y)),Sum.inl (Sum.inr (y,π.symm x))} :=by
  ext a
  cases a with
  | inr a=>simp [ordinaryMixedPhysicalResource]
  | inl a=>
    cases a with
    | inl a=>
      rcases a with ⟨v,w⟩
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,ordinaryMixedPhysicalResource,
        Sum.elim_inl,Sum.inl.injEq,markedPairPhysical,Finset.mem_insert,Finset.mem_singleton,
        Sum.inl.injEq,Sum.inl_ne_inr,or_false,Prod.mk.injEq]
      exact Sym2.eq_iff
    | inr a=>
      rcases a with ⟨v,w⟩
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,ordinaryMixedPhysicalResource,
        Sum.elim_inl,Sum.inl.injEq,markedPairPhysical,Sum.elim_inr,Finset.mem_insert,
        Finset.mem_singleton,Sum.inr.injEq,Sum.inr_ne_inl,false_or,Prod.mk.injEq]
      rw [Sym2.eq_iff]
      constructor
      · rintro (⟨rfl,h⟩|⟨rfl,h⟩)
        · exact Or.inl ⟨rfl,(Equiv.eq_symm_apply π).mpr h⟩
        · exact Or.inr ⟨rfl,(Equiv.eq_symm_apply π).mpr h⟩
      · rintro (⟨rfl,rfl⟩|⟨rfl,rfl⟩)
        · exact Or.inl ⟨rfl,Equiv.apply_symm_apply π y⟩
        · exact Or.inr ⟨rfl,Equiv.apply_symm_apply π x⟩

theorem ordinary_physical_spoke_fiber_sum
    (π:Equiv.Perm V) (x:V) (u:U) (f:OrdinaryTypedResource V U→ℝ):
    (∑a∈Finset.univ.filter (fun a=>ordinaryMixedPhysicalResource π a=Sum.inr (x,u)),f a)=
      f (Sum.inr (false,x,u))+f (Sum.inr (true,x,u)) :=by
  rw [ordinary_physical_spoke_fiber]
  simp

theorem ordinary_physical_rim_fiber_sum
    (π:Equiv.Perm V) (x y:V) (hxy:x≠y) (f:OrdinaryTypedResource V U→ℝ):
    (∑a∈Finset.univ.filter (fun a=>ordinaryMixedPhysicalResource π a=Sum.inl s(x,y)),f a)=
      f (Sum.inl (Sum.inl (x,y)))+f (Sum.inl (Sum.inl (y,x)))+
      f (Sum.inl (Sum.inr (x,π.symm y)))+f (Sum.inl (Sum.inr (y,π.symm x))) :=by
  rw [ordinary_physical_rim_fiber]
  simp [hxy,Ne.symm hxy,add_assoc]
end Oberwolfach
