module

public import Oberwolfach.WheelLoadBounds

@[expose] public section

/-! Free-vertex counts for wheels with different prescribed row roots.
The counts exclude each wheel's own three prescribed row vertices. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U I:Type} [Fintype V] [Fintype U] [Fintype I] [DecidableEq V] [DecidableEq U]
  {Q F:SimpleGraph V} {H:V→U→Prop} {r:ℕ}

def boundaryWheelFreeLoad (C:I→OrdinaryWheel Q F H r) (x v w:I→V) (a:V):ℕ:=
  (Finset.univ.filter (fun i=>a∈rootWheelInternal (C i) (x i) (v i) (w i))).card

theorem boundaryWheelFreeLoad_total (C:I→OrdinaryWheel Q F H r) (x v w:I→V):
    ∑ a,boundaryWheelFreeLoad C x v w a≤Fintype.card I*r:=by
  have he:∑ a,boundaryWheelFreeLoad C x v w a=
      ∑ i,(rootWheelInternal (C i) (x i) (v i) (w i)).card:=by
    simp only [boundaryWheelFreeLoad,Finset.card_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    simp
  rw [he]
  calc
    _≤∑ _i:I,r:=Finset.sum_le_sum (fun i _=>rootWheelInternal_card (C i) (x i) (v i) (w i))
    _=_:=by simp

theorem boundaryWheelFreeLoad_saturated (C:I→OrdinaryWheel Q F H r) (x v w:I→V) (K:ℕ):
    K*(Finset.univ.filter (fun a=>K≤boundaryWheelFreeLoad C x v w a)).card≤Fintype.card I*r:=by
  calc
    _=∑ a∈Finset.univ.filter (fun a=>K≤boundaryWheelFreeLoad C x v w a),K:=by simp [Nat.mul_comm]
    _≤∑ a∈Finset.univ.filter (fun a=>K≤boundaryWheelFreeLoad C x v w a),boundaryWheelFreeLoad C x v w a:=
      Finset.sum_le_sum (fun a ha=>(Finset.mem_filter.mp ha).2)
    _≤∑ a,boundaryWheelFreeLoad C x v w a:=Finset.sum_le_univ_sum_of_nonneg (fun _=>Nat.zero_le _)
    _≤_:=boundaryWheelFreeLoad_total C x v w

theorem boundaryWheel_load_bound (C:I→OrdinaryWheel Q F H r) (x v w:I→V) (K D:ℕ)
    (hcap:∀ a,boundaryWheelFreeLoad C x v w a≤K)
    (hroot:∀ a,(Finset.univ.filter (fun i=>a∈({x i,v i,w i}:Finset V))).card≤D):
    ∀ a,wheelRimLoad C a≤K+D:=by
  intro a
  have hs:Finset.univ.filter (fun i=>a∈(ordinaryWheelRim (C i)).support)⊆
      (Finset.univ.filter (fun i=>a∈rootWheelInternal (C i) (x i) (v i) (w i)))∪
      (Finset.univ.filter (fun i=>a∈({x i,v i,w i}:Finset V))):=by
    intro i hi
    have ha:=(Finset.mem_filter.mp hi).2
    by_cases hr:a∈({x i,v i,w i}:Finset V)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hr⟩)
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr
        ⟨Finset.mem_univ _,Finset.mem_sdiff.mpr ⟨Set.mem_toFinset.mpr ha,hr⟩⟩)
  exact ((Finset.card_le_card hs).trans (Finset.card_union_le _ _)).trans
    (Nat.add_le_add (hcap a) (hroot a))

theorem boundaryWheelFreeLoad_snoc {k:ℕ} (C:Fin k→OrdinaryWheel Q F H r)
    (D:OrdinaryWheel Q F H r) (x v w:Fin k→V) (a b c z:V):
    boundaryWheelFreeLoad (Fin.snoc C D) (Fin.snoc x a) (Fin.snoc v b) (Fin.snoc w c) z=
      boundaryWheelFreeLoad C x v w z+(if z∈rootWheelInternal D a b c then 1 else 0):=by
  simp only [boundaryWheelFreeLoad,Finset.card_filter,Fin.sum_univ_castSucc,Fin.snoc_castSucc,Fin.snoc_last]

end Oberwolfach
