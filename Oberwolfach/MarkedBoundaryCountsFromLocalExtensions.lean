module

public import Oberwolfach.MarkedBoundaryExtensionCounts
public import Oberwolfach.MarkedLocalExtensions

@[expose] public section

/-! The manuscript's already proved local extension sets supply exactly
the inner-set counts used to complete marked boundary paths. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]

theorem marked_boundary_counts_from_local_extensions
    (R:(V×V)⊕(V×V)→Prop) (H:Bool→V→U→Prop) (X:Finset V) (c:ℝ)
    (hstep:∀ j x u,c≤((markedOneExtensionSet R H X j x u).card:ℝ))
    (hjoin:∀ x y u,x≠y→c≤((markedTwoExtensionSet R H X false x y u).card:ℝ)):
    MarkedBoundaryExtensionCounts
      (fun e:{e:V×V // R (Sum.inl e)}=>e.val.1) (fun e=>e.val.2)
      (fun e:{e:V×V // R (Sum.inr e)}=>e.val.1) (fun e=>e.val.2)
      (H false) (H true) X c:=by
  have harc (j:Bool) (x y:V):
      markedArcPresent (fun e:{e:V×V // R (Sum.inl e)}=>e.val.1) (fun e=>e.val.2)
        (fun e:{e:V×V // R (Sum.inr e)}=>e.val.1) (fun e=>e.val.2) j x y↔
      R (if j then Sum.inr (x,y) else Sum.inl (x,y)):=by
    cases j <;> simp only [markedArcPresent,Bool.false_eq_true,ite_false,ite_true]
    all_goals
      constructor
      · rintro ⟨⟨⟨a,b⟩,hab⟩,rfl,rfl⟩;exact hab
      · intro h;exact ⟨⟨(x,y),h⟩,rfl,rfl⟩
  constructor
  · intro j x u
    have he:X.filter (fun y=>markedArcPresent (fun e:{e:V×V // R (Sum.inl e)}=>e.val.1) (fun e=>e.val.2)
        (fun e:{e:V×V // R (Sum.inr e)}=>e.val.1) (fun e=>e.val.2) j x y∧
        (if j then H true y u else H false y u))=markedOneExtensionSet R H X j x u:=by
      ext y;simp only [Finset.mem_filter,markedOneExtensionSet,harc]
      cases j <;> rfl
    rw [he];exact hstep j x u
  · intro x y u hxy
    have he:X.filter (fun z=>markedArcPresent (fun e:{e:V×V // R (Sum.inl e)}=>e.val.1) (fun e=>e.val.2)
        (fun e:{e:V×V // R (Sum.inr e)}=>e.val.1) (fun e=>e.val.2) false x z∧
        markedArcPresent (fun e:{e:V×V // R (Sum.inl e)}=>e.val.1) (fun e=>e.val.2)
        (fun e:{e:V×V // R (Sum.inr e)}=>e.val.1) (fun e=>e.val.2) false z y∧H false z u)=
        markedTwoExtensionSet R H X false x y u:=by
      ext z;simp only [Finset.mem_filter,markedTwoExtensionSet,harc,Bool.false_eq_true,ite_false]
    rw [he];exact hjoin x y u hxy

end Oberwolfach
