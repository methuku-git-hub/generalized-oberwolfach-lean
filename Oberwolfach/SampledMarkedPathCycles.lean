module

public import Oberwolfach.MarkedPathRealization
public import Oberwolfach.RootFirstCommonPaths

@[expose] public section

/-! The survived physical requests are the two root-first marked cycles
used by the correction lemmas. Only free-label spokes are needed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V) (π : Equiv.Perm V) (b m : ℕ) (j : Bool) (v v' : V)
    (σ : Sym2 V→Option (Bool×Bool))

theorem markedSampleArc_exists (a : Bool) (x y : V)
    (h : markedPhysicalRim P π b σ a x y=1) :
    if a then ∃ e : MarkedSampleArc P π b σ true,e.val.1=x ∧ e.val.2=y
      else ∃ e : MarkedSampleArc P π b σ false,e.val.1=x ∧ e.val.2=y := by
  cases a <;> exact ⟨⟨(x,y),h⟩,rfl,rfl⟩

theorem markedPathRims_rootCycle (hm : 2≤m) (z : Fin (m+1)→V) (side : Bool)
    (hsep : PermutationSeparated π b (Fin.cons (if side then v' else v) z))
    (hR : MarkedPathRims P π b m j v v' σ z) :
    IsRootFirstMarkedCycle
      (fun e : MarkedSampleArc P π b σ false=>e.val.1) (fun e=>e.val.2)
      (fun e : MarkedSampleArc P π b σ true=>e.val.1) (fun e=>e.val.2)
      (m+1) π b (if j then Fin.last (m+1) else 2) (Fin.cons (if side then v' else v) z) := by
  refine ⟨hsep,?_⟩
  intro t
  refine Fin.cases ?_ (fun l=>?_) t
  · have hs : (0:Fin (m+2))≠(if j then Fin.last (m+1) else 2) := by
      cases j <;> simp [Fin.ext_iff,Fin.val_natCast,Nat.mod_eq_of_lt (show 2<m+2 by omega)]
    rw [if_neg hs]
    have hrot : finRotate (m+2) (0:Fin (m+2))=(0:Fin (m+1)).succ :=
      finRotate_castSucc_eq_succ (m+1) 0
    rw [hrot]
    exact ⟨⟨(if side then v' else v,z 0),hR (Sum.inr (false,side))⟩,rfl,rfl⟩
  · refine Fin.lastCases ?_ (fun i=>?_) l
    · have hrot : finRotate (m+2) (Fin.last m).succ=0 := finRotate_last
      rw [hrot]
      have h := hR (Sum.inr (true,side))
      cases j
      · have hs : (Fin.last m).succ≠(2:Fin (m+2)) := by
          intro he
          have hh := congrArg Fin.val he
          change m+1=2%(m+2) at hh
          rw [Nat.mod_eq_of_lt (by omega)] at hh
          omega
        simp only [Bool.false_eq_true,ite_false,hs]
        exact ⟨⟨(z (Fin.last m),if side then v' else v),h⟩,rfl,rfl⟩
      · simp only [ite_true,show (Fin.last m).succ=Fin.last (m+1) from rfl]
        exact ⟨⟨(z (Fin.last m),if side then v' else v),h⟩,rfl,rfl⟩
    · have hrot : finRotate (m+2) i.castSucc.succ=i.succ.succ :=
        finRotate_castSucc_eq_succ (m+1) i.succ
      have hmark : i.castSucc.succ=(if j then Fin.last (m+1) else (2:Fin (m+2))) ↔ j=false ∧ i.val=1 := by
        cases j
        · change (i.castSucc.succ=(2:Fin (m+2))) ↔ (false=false ∧ i.val=1)
          simp only [true_and]
          constructor
          · intro he
            have hh := congrArg Fin.val he
            change i.val+1=2%(m+2) at hh
            rw [Nat.mod_eq_of_lt (by omega)] at hh
            omega
          · intro he
            apply Fin.ext
            change i.val+1=2%(m+2)
            rw [Nat.mod_eq_of_lt (by omega)]
            omega
        · change (i.castSucc.succ=Fin.last (m+1)) ↔ (true=false ∧ i.val=1)
          simp only [Bool.true_eq_false,false_and,iff_false]
          intro he
          have hh := congrArg Fin.val he
          simp only [Fin.val_succ,Fin.val_castSucc,Fin.val_last] at hh
          omega
      simp only [hrot,hmark]
      have h := markedSampleArc_exists P π b σ (pathInternalType j i) (z i.castSucc) (z i.succ) (hR (Sum.inl i))
      simpa only [pathInternalType,decide_eq_true_eq,Fin.cons_succ] using h

end Oberwolfach
