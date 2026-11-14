module

public import Oberwolfach.OrdinaryWheelFamilies

@[expose] public section

/-! If distinct wheels have distinct hubs, the spoke degree at each hub
is at most the rim length. This does not require an upper bound on the
degree at a common rim root. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U I : Type*} [Fintype V] [Fintype U] [Fintype I] [DecidableEq V] [DecidableEq U]
  {Q F : SimpleGraph V} {H : V→U→Prop} {r : ℕ}

theorem wheelFamily_injective_hub_degree (W : I→OrdinaryWheel Q F H r)
    (h : Function.Injective (fun i=>ordinaryWheelHub (W i))) (u : U) :
    (Finset.univ.filter (fun v=>wheelFamilySpokes W v u)).card≤r := by
  let J:=Finset.univ.filter (fun i=>ordinaryWheelHub (W i)=u)
  have he : Finset.univ.filter (fun v=>wheelFamilySpokes W v u)=
      J.biUnion (fun i=>(ordinaryWheelRim (W i)).support.toFinset) := by
    ext v
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,wheelFamilySpokes,
      Finset.mem_biUnion,J,Set.mem_toFinset]
  have hJ : J.card≤1 := by
    apply Finset.card_le_one.mpr
    intro i hi j hj
    exact h ((Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm)
  rw [he]
  calc
    _ ≤ ∑ i∈J,(ordinaryWheelRim (W i)).support.toFinset.card:=Finset.card_biUnion_le
    _ = J.card*r := by
      have hc (i : I) : (ordinaryWheelRim (W i)).support.toFinset.card=r:=(W i).val.1.val.property.support_card
      simp only [hc,Finset.sum_const,smul_eq_mul]
    _ ≤ r := by nlinarith only [Nat.mul_le_mul_right r hJ]

theorem wheelFamily_rim_degree_spoke_degree (W : I→OrdinaryWheel Q F H r)
    (hW : ∀ i j,i≠j → Disjoint (ordinaryWheelResources (W i)) (ordinaryWheelResources (W j))) :
    ∀ v,(wheelFamilyRim W).degree v=2*(Finset.univ.filter (fun u=>wheelFamilySpokes W v u)).card :=
  (ordinary_wheel_decomposition_balance (wheelFamilyRim W) (wheelFamilySpokes W) r
    (wheelFamily_decomposition W hW)).1

end Oberwolfach
