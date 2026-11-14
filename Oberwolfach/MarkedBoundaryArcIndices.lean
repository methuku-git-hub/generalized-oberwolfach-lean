module

public import Oberwolfach.MarkedEndpointAssignmentIncidences
public import Oberwolfach.MarkedBoundaryRootArcs

@[expose] public section

/-! The boundary arc indices are globally injective after the selected
endpoint bijections, because their outside endpoints recover the root. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem dependent_assigned_edges_injective {J V E:Type} {A B:J→Type}
    (x:J↪V) (f:∀ j,A j↪E) (e:∀ j,B j≃A j) (root:E→V)
    (hroot:∀ j a,root (f j a)=x j):
    Function.Injective (fun i:Σ j,B j=>f i.1 (e i.1 i.2)):=by
  rintro ⟨j,a⟩ ⟨k,b⟩ he
  have hx:x j=x k:=by simpa only [hroot] using congrArg root he
  have hj:=x.injective hx
  subst k
  exact congrArg (Sigma.mk j) ((e j).injective ((f j).injective he))

theorem filter_card_reindex_equiv {A B:Type} [Fintype A] [Fintype B]
    (e:A≃B) (P:B→Prop):
    (Finset.univ.filter (fun a=>P (e a))).card=(Finset.univ.filter P).card:=by
  apply Finset.card_bij (fun a _=>e a)
  · intro a ha;exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp ha).2⟩
  · intro a ha b hb he;exact e.injective he
  · intro b hb
    refine ⟨e.symm b,?_,e.apply_symm_apply b⟩
    simpa only [Finset.mem_filter,Finset.mem_univ,true_and,e.apply_symm_apply] using hb

end Oberwolfach
