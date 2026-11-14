module

public import Oberwolfach.RootFirstCommonPaths

@[expose] public section

/-! Close a typed directed path at an actual row root. Only the spoke at
that root and its own hub is required; no opposite root--hub incidence is
silently imposed. Internal marked arcs are at path position one. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

 theorem root_first_marked_cycle_from_path {V E K:Type*}
    (tail head:E→V) (ktail khead:K→V) (n:ℕ) (hn:2≤n)
    (π:Equiv.Perm V) (b:ℕ) (j:Bool) (v:V) (p:Fin (n+1)→V)
    (hsep:PermutationSeparated π b (Fin.cons v p))
    (hopen:∃ e,tail e=v∧head e=p 0)
    (hclose:if j then ∃ e,ktail e=p (Fin.last n)∧khead e=v
      else ∃ e,tail e=p (Fin.last n)∧head e=v)
    (hpath:∀ i:Fin n,if j=false∧i.val=1 then
      ∃ e,ktail e=p i.castSucc∧khead e=p i.succ
      else ∃ e,tail e=p i.castSucc∧head e=p i.succ):
    IsRootFirstMarkedCycle tail head ktail khead (n+1) π b
      (if j then Fin.last (n+1) else 2) (Fin.cons v p):=by
  have h2:((2:Fin (n+2)):ℕ)=2:=by change 2 % (n+2)=2;exact Nat.mod_eq_of_lt (by omega)
  refine ⟨hsep,?_⟩
  intro t
  refine Fin.cases ?_ (fun i=>?_) t
  · have hne:(0:Fin (n+2))≠(if j then Fin.last (n+1) else 2):=by
      cases j <;> simp only [Bool.false_eq_true,ite_false,ite_true,ne_eq,Fin.ext_iff,Fin.val_zero,Fin.val_last,h2]
      all_goals omega
    rw [ite_eq_right hne]
    have hrot:finRotate (n+2) (0:Fin (n+2))=(0:Fin (n+1)).succ:=by
      exact finRotate_castSucc_eq_succ (n+1) 0
    simpa only [hrot,Fin.cons_zero,Fin.cons_succ] using hopen
  · refine Fin.lastCases ?_ (fun k=>?_) i
    · have hlast:(Fin.last n).succ=Fin.last (n+1):=rfl
      rw [hlast,finRotate_last]
      have hne:(Fin.last (n+1):Fin (n+2))≠2:=by
        intro h
        have hh:=congrArg Fin.val h
        simp only [Fin.val_last,h2] at hh
        omega
      cases j
      · simp only [Bool.false_eq_true,ite_false,ite_eq_right hne] at hclose ⊢
        exact hclose
      · simp only [ite_true,ite_eq_left rfl] at hclose ⊢
        exact hclose
    · have hsucc:k.castSucc.succ=k.succ.castSucc:=rfl
      rw [hsucc,finRotate_castSucc_eq_succ]
      have hne:k.succ.castSucc≠Fin.last (n+1):=Fin.castSucc_ne_last _
      have he:k.succ.castSucc=(2:Fin (n+2))↔k.val=1:=by
        simp only [Fin.ext_iff,Fin.val_castSucc,Fin.val_succ,h2]
        omega
      have hval:Fin.cons (α:=fun _=>V) v p k.succ.castSucc=p k.castSucc:=by rw [← hsucc,Fin.cons_succ]
      cases j
      · simpa only [Bool.false_eq_true,ite_false,he,hval,Fin.cons_succ,true_and] using hpath k
      · simpa only [ite_true,ite_eq_right hne,hval,Fin.cons_succ,Bool.true_eq_false,false_and,ite_false] using hpath k

 theorem marked_wheel_from_rooted_path {V U E K:Type*}
    (tail head:E→V) (ktail khead:K→V) (n:ℕ) (hn:2≤n)
    (π:Equiv.Perm V) (b:ℕ) (H₀ Hₖ:V→U→Prop)
    (j:Bool) (v:V) (u:U) (p:Fin (n+1)→V)
    (hsep:PermutationSeparated π b (Fin.cons v p))
    (hopen:∃ e,tail e=v∧head e=p 0)
    (hclose:if j then ∃ e,ktail e=p (Fin.last n)∧khead e=v
      else ∃ e,tail e=p (Fin.last n)∧head e=v)
    (hpath:∀ i:Fin n,if j=false∧i.val=1 then
      ∃ e,ktail e=p i.castSucc∧khead e=p i.succ
      else ∃ e,tail e=p i.castSucc∧head e=p i.succ)
    (hroot:if j then Hₖ v u else H₀ v u)
    (hfree:∀ i,if j=false∧i.val=2 then Hₖ (p i) u else H₀ (p i) u):
    ∃ W:MarkedWheel tail head ktail khead (n+1) π b H₀ Hₖ,
      W.2.val=u∧∀ i,W.1.val i=rootedCycleOrder (markedRootOrder (n+1) j) v p i:=by
  have hcyc:=root_first_marked_cycle_from_path tail head ktail khead n hn π b j v p hsep hopen hclose hpath
  have hcanonical: IsMarkedCycleTuple tail head ktail khead (n+1) π b
      (rootedCycleOrder (markedRootOrder (n+1) j) v p):=
    (rootedCycleOrder_marked_iff j v p).mpr hcyc
  let C:MarkedCycleTuple tail head ktail khead (n+1) π b:=⟨_,hcanonical⟩
  have h3:((3:Fin (n+2)):ℕ)=3:=by change 3 % (n+2)=3;exact Nat.mod_eq_of_lt (by omega)
  have hrootsp:∀ t:Fin (n+2),
      if rootFirstSpokeType (n+1) j t then Hₖ (Fin.cons (α:=fun _=>V) v p t) u else H₀ (Fin.cons (α:=fun _=>V) v p t) u:=by
    intro t
    refine Fin.cases ?_ (fun i=>?_) t
    · have hzero:rootFirstSpokeType (n+1) j 0=j:=by
        cases j
        · have hne:(0:Fin (n+2))≠3:=by intro h;have hh:=congrArg Fin.val h;simp only [Fin.val_zero,h3] at hh;omega
          simp [rootFirstSpokeType,hne]
        · simp [rootFirstSpokeType]
      simpa only [hzero,Fin.cons_zero] using hroot
    · have he:rootFirstSpokeType (n+1) j i.succ=decide (j=false∧i.val=2):=by
        cases j
        · have heq:i.succ=(3:Fin (n+2))↔i.val=2:=by
            simp only [Fin.ext_iff,Fin.val_succ,h3]
            omega
          simp only [rootFirstSpokeType,Bool.false_eq_true,ite_false,true_and,heq]
        · simp [rootFirstSpokeType]
      simpa only [he,decide_eq_true_eq,Fin.cons_succ] using hfree i
  have hhub:MarkedHubCompatible H₀ Hₖ C.val u:=by
    apply (markedHubCompatible_iff_positions _ _ _ _).mpr
    intro i
    have hh:=hrootsp (markedRootOrder (n+1) j i)
    rw [← markedRootOrder_position_type,Equiv.symm_apply_apply] at hh
    exact hh
  exact ⟨⟨C,⟨u,hhub⟩⟩,rfl,fun _=>rfl⟩

end Oberwolfach
