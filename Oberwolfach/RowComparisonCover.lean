module

public import Oberwolfach.RowCoverPackings

@[expose] public section

/-! The row-root construction in the comparison host is a new packing
in the actual host, disjoint from every previously chosen wheel. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U I:Type} [Fintype V] [Fintype U] [Fintype I] [DecidableEq V] [DecidableEq U]
  {Q F:SimpleGraph V} {H:V→U→Prop} {r:ℕ}

theorem row_comparison_cover_image (M:Finset (OrdinaryWheel Q F H r)) (A:Finset V) (x:V) (K:ℕ)
    (hM:∀ W∈M,x∉(ordinaryWheelRim W).support)
    (C:I→OrdinaryWheel (Q\spanningRestriction (ordinaryWheelRimGraph M) A) F
      (fun a u=>H a u∧¬(a∈A∧ordinaryPackingSpokes M a u)) r)
    (hsupport:∀ i,∀ a∈(ordinaryWheelRim (C i)).support,a=x∨a∈A)
    (hdis:∀ i j,i≠j → Disjoint (ordinaryWheelResources (C i)) (ordinaryWheelResources (C j)))
    (hrim:∀ a,(wheelFamilyRim C).Adj x a ↔ Q.Adj x a)
    (hspoke:∀ u,wheelFamilySpokes C x u ↔ H x u)
    (hdeg:∀ a,a≠x → (wheelFamilyRim C).degree a≤2*(K+1))
    (hrow:∀ a,a≠x → (Finset.univ.filter (fun u=>wheelFamilySpokes C a u)).card≤K+1)
    (hcol:∀ u,(Finset.univ.filter (fun a=>wheelFamilySpokes C a u)).card≤r) :
    ∃ N:Finset (OrdinaryWheel Q F H r),OrdinaryRowCover N x A K ∧
      Disjoint (N.biUnion ordinaryWheelResources) (M.biUnion ordinaryWheelResources) := by
  let C':I→OrdinaryWheel Q F H r:=fun i=>ordinaryWheelToLarger sdiff_le (fun _ _ h=>h.1) (C i)
  have hr:wheelFamilyRim C'=wheelFamilyRim C:=rfl
  have hs:wheelFamilySpokes C'=wheelFamilySpokes C:=rfl
  refine ⟨Finset.univ.image C',ordinaryRowCover_of_family C' x A K hsupport hdis hrim hspoke ?_ hrow hcol,?_⟩
  · convert hdeg using 1 <;> congr!
  · apply Finset.disjoint_left.mpr
    intro e he heM
    obtain ⟨W,hW,heW⟩:=Finset.mem_biUnion.mp he
    obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hW
    exact Finset.disjoint_left.mp (ordinary_wheel_comparison_disjoint M A x hM (C i) (hsupport i)) heW heM

end Oberwolfach
