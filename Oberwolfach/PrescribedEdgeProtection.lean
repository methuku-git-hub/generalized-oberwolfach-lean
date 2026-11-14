module

public import Oberwolfach.OrdinaryWheelFamilies
public import Oberwolfach.InducedFractionalCycles

@[expose] public section

/-! Exact intersections of the prescribed-edge wheels with an inner
vertex pair. These identities exclude every other prescribed inner edge. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type*} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
  {Q F:SimpleGraph V} {H:V→U→Prop} {r:ℕ}

theorem prescribed_rim_wheel_inner_intersection (C:OrdinaryWheel Q F H r)
    (I X:Finset V) (J:Finset U) (hIX:Disjoint I X) (x y:V) (hx:x∈I) (hy:y∈I)
    (hxy:(ordinaryWheelRim C).Adj x y) (hu:ordinaryWheelHub C∉J)
    (hs:∀ a∈(ordinaryWheelRim C).support,a=x∨a=y∨a∈X) :
    ordinaryWheelResources C∩ordinaryHostResources (spanningRestriction Q I)
      (fun a u=>H a u∧a∈I∧u∈J)={Sum.inl s(x,y)}:=by
  have hroot (a:V) (ha:a∈(ordinaryWheelRim C).support) (hai:a∈I):a=x∨a=y:=by
    rcases hs a ha with h|h|h
    · exact Or.inl h
    · exact Or.inr h
    · exact (Finset.disjoint_left.mp hIX hai h).elim
  ext e
  constructor
  · intro he
    obtain ⟨heC,heI⟩:=Finset.mem_inter.mp he
    cases e with
    | inl e =>
      rw [ordinaryWheelResources_rim] at heC
      rw [ordinaryHostResources_rim] at heI
      induction e using Sym2.inductionOn with
      | _ a b =>
        have hi:=(spanningRestriction_adj Q I a b).mp heI
        rcases hroot a heC.mem_support_left hi.2.1 with ha|ha <;>
          rcases hroot b heC.mem_support_right hi.2.2 with hb|hb
        · exact (heC.ne (ha.trans hb.symm)).elim
        · simp [ha,hb]
        · simp [ha,hb,Sym2.eq_swap]
        · exact (heC.ne (ha.trans hb.symm)).elim
    | inr au =>
      rw [ordinaryWheelResources_spoke] at heC
      rw [ordinaryHostResources_spoke] at heI
      exact (hu (heC.1.symm ▸ heI.2.2)).elim
  · intro he
    have he':e=Sum.inl s(x,y):=Finset.mem_singleton.mp he
    subst e
    refine Finset.mem_inter.mpr ⟨(ordinaryWheelResources_rim C _).mpr hxy,?_⟩
    rw [ordinaryHostResources_rim]
    exact (spanningRestriction_adj Q I x y).mpr ⟨C.val.1.property hxy,hx,hy⟩

theorem prescribed_spoke_wheel_inner_intersection (C:OrdinaryWheel Q F H r)
    (I X:Finset V) (J:Finset U) (hIX:Disjoint I X) (x:V) (u:U)
    (hx:x∈I) (hu:u∈J) (hCu:ordinaryWheelHub C=u) (hCx:x∈(ordinaryWheelRim C).support)
    (hs:∀ a∈(ordinaryWheelRim C).support,a=x∨a∈X) :
    ordinaryWheelResources C∩ordinaryHostResources (spanningRestriction Q I)
      (fun a u=>H a u∧a∈I∧u∈J)={Sum.inr (x,u)}:=by
  have hroot (a:V) (ha:a∈(ordinaryWheelRim C).support) (hai:a∈I):a=x:=by
    rcases hs a ha with h|h
    · exact h
    · exact (Finset.disjoint_left.mp hIX hai h).elim
  ext e
  constructor
  · intro he
    obtain ⟨heC,heI⟩:=Finset.mem_inter.mp he
    cases e with
    | inl e =>
      rw [ordinaryWheelResources_rim] at heC
      rw [ordinaryHostResources_rim] at heI
      induction e using Sym2.inductionOn with
      | _ a b =>
        have hi:=(spanningRestriction_adj Q I a b).mp heI
        exact (heC.ne ((hroot a heC.mem_support_left hi.2.1).trans (hroot b heC.mem_support_right hi.2.2).symm)).elim
    | inr au =>
      rw [ordinaryWheelResources_spoke] at heC
      rw [ordinaryHostResources_spoke] at heI
      have ha:=hroot au.1 heC.2 heI.2.1
      have hb:au.2=u:=heC.1.symm.trans hCu
      exact Finset.mem_singleton.mpr (congrArg Sum.inr (Prod.ext ha hb))
  · intro he
    have he':e=Sum.inr (x,u):=Finset.mem_singleton.mp he
    subst e
    refine Finset.mem_inter.mpr ⟨(ordinaryWheelResources_spoke C x u).mpr ⟨hCu,hCx⟩,?_⟩
    rw [ordinaryHostResources_spoke]
    exact ⟨hCu ▸ C.property.1 x hCx,hx,hu⟩

end Oberwolfach
