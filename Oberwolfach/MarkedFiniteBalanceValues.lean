module

public import Oberwolfach.MarkedFiniteDivisibilityOperations
public import Oberwolfach.MarkedBalanceReservationErrors

@[expose] public section

/-! Real-valued balance differences of finite typed arc and spoke sets.
The first two row differences compare all outgoing/incoming arcs with all
spokes, the third compares marked incoming arcs with marked spokes, and
the hub difference retains the coefficient m. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem real_filter_sdiff_card {A:Type} [DecidableEq A] (S T:Finset A)
    (h:T⊆S) (p:A→Prop):
    (((S\T).filter p).card:ℝ)=(S.filter p).card-(T.filter p).card:=by
  rw [finite_filter_sdiff_card S T h,Nat.cast_sub (Finset.card_le_card (Finset.filter_subset_filter p h))]

variable {V U E K:Type} [DecidableEq V] [DecidableEq U] [DecidableEq E] [DecidableEq K]

def markedFiniteBalance (tail head:E→V) (ktail khead:K→V) (HK:V→U→Prop)
    (A:Finset (E⊕K)) (S:Finset (V×U)) (m:ℕ):V⊕U→Fin 4→ℝ
  | Sum.inl v=>![((A.filter (fun a=>Sum.elim tail ktail a=v)).card:ℝ)-(S.filter (fun s=>s.1=v)).card,
      ((A.filter (fun a=>Sum.elim head khead a=v)).card:ℝ)-(S.filter (fun s=>s.1=v)).card,
      ((A.filter (fun a=>Sum.elim head khead a=v∧markedArcType a=true)).card:ℝ)-
        (S.filter (fun s=>s.1=v∧HK s.1 s.2)).card,0]
  | Sum.inr u=>![0,0,0,((S.filter (fun s=>s.2=u∧¬HK s.1 s.2)).card:ℝ)-
      m*(S.filter (fun s=>s.2=u∧HK s.1 s.2)).card]

theorem markedFiniteBalance_sdiff
    (tail head:E→V) (ktail khead:K→V) (HK:V→U→Prop)
    (A B:Finset (E⊕K)) (S R:Finset (V×U)) (m:ℕ)
    (hA:B⊆A) (hS:R⊆S) (z:V⊕U) (i:Fin 4):
    markedFiniteBalance tail head ktail khead HK (A\B) (S\R) m z i=
      markedFiniteBalance tail head ktail khead HK A S m z i-
      markedFiniteBalance tail head ktail khead HK B R m z i:=by
  have ha:=real_filter_sdiff_card A B hA
  have hs:=real_filter_sdiff_card S R hS
  simp only [←Set.ncard_coe_finset,Finset.coe_filter,Finset.mem_sdiff] at ha hs
  cases z <;> fin_cases i <;>
    simp only [markedFiniteBalance,Matrix.cons_val_zero',Matrix.cons_val_succ'] <;>
    (try simp only [←Set.ncard_coe_finset,Finset.coe_filter,Finset.mem_sdiff]) <;>
    (try simp only [ha,hs]) <;> ring

theorem markedFiniteBalance_eq_zero_iff
    (tail head:E→V) (ktail khead:K→V) (HK:V→U→Prop)
    (A:Finset (E⊕K)) (S:Finset (V×U)) (m:ℕ):
    (∀ z i,markedFiniteBalance tail head ktail khead HK A S m z i=0)↔
      MarkedRemainderDivisible tail head ktail khead HK A S m:=by
  constructor
  · intro h
    have ho (v:V):((A.filter (fun a=>Sum.elim tail ktail a=v)).card:ℝ)=
        (S.filter (fun s=>s.1=v)).card:=sub_eq_zero.mp (h (Sum.inl v) 0)
    have hi (v:V):((A.filter (fun a=>Sum.elim head khead a=v)).card:ℝ)=
        (S.filter (fun s=>s.1=v)).card:=sub_eq_zero.mp (h (Sum.inl v) 1)
    constructor
    · intro v
      exact_mod_cast (hi v).trans (ho v).symm
    · intro v
      exact_mod_cast hi v
    · intro v
      have hh:=sub_eq_zero.mp (h (Sum.inl v) 2)
      exact_mod_cast hh
    · intro u
      have hh:=sub_eq_zero.mp (h (Sum.inr u) 3)
      exact_mod_cast hh
  · intro h z i
    cases z with
    | inl v=>
      have ho:=h.directed v
      have hi:=h.row v
      have hk:=h.marked v
      fin_cases i <;> simp only [markedFiniteBalance,Matrix.cons_val_zero',Matrix.cons_val_succ'] <;>
        simp only [←Set.ncard_coe_finset,Finset.coe_filter] at ho hi hk ⊢
      · rw [←ho,hi,sub_self]
      · rw [hi,sub_self]
      · rw [hk,sub_self]
    | inr u=>
      have hh:=h.hub u
      fin_cases i <;> simp only [markedFiniteBalance,Matrix.cons_val_zero',Matrix.cons_val_succ'] <;>
        simp only [←Set.ncard_coe_finset,Finset.coe_filter] at hh ⊢
      rw [hh,Nat.cast_mul,sub_self]

theorem markedFiniteBalance_subtract_divisible
    (tail head:E→V) (ktail khead:K→V) (HK:V→U→Prop)
    (A B:Finset (E⊕K)) (S R:Finset (V×U)) (m:ℕ)
    (hA:B⊆A) (hS:R⊆S) (hB:MarkedRemainderDivisible tail head ktail khead HK B R m)
    (z:V⊕U) (i:Fin 4):
    markedFiniteBalance tail head ktail khead HK (A\B) (S\R) m z i=
      markedFiniteBalance tail head ktail khead HK A S m z i:=by
  rw [markedFiniteBalance_sdiff _ _ _ _ _ _ _ _ _ _ hA hS,
    (markedFiniteBalance_eq_zero_iff _ _ _ _ _ _ _ _).mpr hB z i,sub_zero]

end Oberwolfach
