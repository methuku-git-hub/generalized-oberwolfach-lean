module

public import Oberwolfach.MarkedFiniteBalanceValues
public import Oberwolfach.MarkedReservedHostBalances

@[expose] public section

/-! Identify the finite-set balance differences with the actual six
incidence terms used by approximate marked wheel packing. Spoke types
are disjoint; they are not counted twice. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finite_spoke_relation_row_count {V U:Type} [Fintype V] [Fintype U] [DecidableEq V]
    (H:V→U→Prop) (v:V):
    (((Finset.univ.filter (fun s:V×U=>H s.1 s.2)).filter (fun s=>s.1=v)).card:ℝ)=
      ∑ u,if H v u then (1:ℝ) else 0:=by
  rw [Finset.filter_filter,←Finset.sum_boole,Fintype.sum_prod_type]
  rw [Finset.sum_eq_single v]
  · simp only [and_true]
  · intro x _ hx
    apply Finset.sum_eq_zero
    intro u _
    simp only [hx,and_false,ite_false]
  · intro h;exact (h (Finset.mem_univ _)).elim

theorem finite_spoke_relation_col_count {V U:Type} [Fintype V] [Fintype U] [DecidableEq U]
    (H:V→U→Prop) (u:U):
    (((Finset.univ.filter (fun s:V×U=>H s.1 s.2)).filter (fun s=>s.2=u)).card:ℝ)=
      ∑ v,if H v u then (1:ℝ) else 0:=by
  rw [Finset.filter_filter,←Finset.sum_boole,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro v _
  rw [Finset.sum_eq_single u]
  · simp only [and_true]
  · intro y _ hy;simp only [hy,and_false,ite_false]
  · intro h;exact (h (Finset.mem_univ _)).elim

variable {V U E K:Type} [Fintype V] [Fintype U] [Fintype E] [Fintype K]
  [DecidableEq V] [DecidableEq U] [DecidableEq E] [DecidableEq K]

theorem markedFiniteBalance_full_row
    (tail head:E→V) (ktail khead:K→V) (H₀ HK:V→U→Prop)
    (hd:∀ v u,¬(H₀ v u∧HK v u)) (m:ℕ) (v:V) (i:Fin 3):
    markedFiniteBalance tail head ktail khead HK Finset.univ
      (Finset.univ.filter (fun s:V×U=>H₀ s.1 s.2∨HK s.1 s.2)) m (Sum.inl v) i.castSucc=
    markedSixDegreeBalance m
      (fun j=>((markedBalanceTermSet tail head ktail khead H₀ HK (Sum.inl v) j).card:ℝ)) i.castSucc:=by
  have hSraw:=finite_spoke_relation_row_count (fun v u=>H₀ v u∨HK v u) v
  have hsplit:(∑ u,if H₀ v u∨HK v u then (1:ℝ) else 0)=
      (∑ u,if H₀ v u then (1:ℝ) else 0)+(∑ u,if HK v u then (1:ℝ) else 0):=by
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro u _
    have h:=hd v u
    by_cases h0:H₀ v u <;> by_cases hk:HK v u <;> simp_all
  have hS:(((Finset.univ.filter (fun s:V×U=>H₀ s.1 s.2∨HK s.1 s.2)).filter (fun s=>s.1=v)).card:ℝ)=
      (∑ u,if H₀ v u then (1:ℝ) else 0)+(∑ u,if HK v u then (1:ℝ) else 0):=by
    calc
      _ = ∑ u,if H₀ v u∨HK v u then (1:ℝ) else 0:=by convert hSraw using 1 <;> congr!
      _ = _:=hsplit
  have hKS:((Finset.univ.filter (fun s:V×U=>H₀ s.1 s.2∨HK s.1 s.2)).filter
      (fun s=>s.1=v∧HK s.1 s.2))=(Finset.univ.filter (fun s:V×U=>HK s.1 s.2)).filter (fun s=>s.1=v):=by
    ext s;simp only [Finset.mem_filter,Finset.mem_univ,true_and];tauto
  have hKScard:=finite_spoke_relation_row_count HK v
  have ho:((Finset.univ.filter (fun a:E⊕K=>Sum.elim tail ktail a=v)).card:ℝ)=
      occurrenceDegree (Sum.elim tail ktail) v:=by rw [←Finset.sum_boole];unfold occurrenceDegree;congr!
  have hi:((Finset.univ.filter (fun a:E⊕K=>Sum.elim head khead a=v)).card:ℝ)=
      occurrenceDegree (Sum.elim head khead) v:=by rw [←Finset.sum_boole];unfold occurrenceDegree;congr!
  have hk:((Finset.univ.filter (fun a:E⊕K=>Sum.elim head khead a=v∧markedArcType a=true)).card:ℝ)=
      occurrenceDegree khead v:=by
    rw [←Finset.sum_boole,Fintype.sum_sum_type]
    simp only [Sum.elim_inl,Sum.elim_inr,markedArcType,Bool.false_eq_true,and_false,
      ite_false,Finset.sum_const_zero,zero_add,and_true,occurrenceDegree]
    congr!
  obtain ⟨h0,h1,h2⟩:=markedSixDegreeBalance_row tail head ktail khead H₀ HK m v
  fin_cases i
  · change _=markedSixDegreeBalance m _ 0
    rw [h0]
    change _-_=_
    rw [ho,hS];ring
  · change _=markedSixDegreeBalance m _ 1
    rw [h1]
    change _-_=_
    rw [hi,hS];ring
  · change _=markedSixDegreeBalance m _ 2
    rw [h2]
    change _-_=_
    rw [hk,hKS,hKScard]

theorem markedFiniteBalance_full_hub
    (tail head:E→V) (ktail khead:K→V) (H₀ HK:V→U→Prop)
    (hd:∀ v u,¬(H₀ v u∧HK v u)) (m:ℕ) (u:U):
    markedFiniteBalance tail head ktail khead HK Finset.univ
      (Finset.univ.filter (fun s:V×U=>H₀ s.1 s.2∨HK s.1 s.2)) m (Sum.inr u) 3=
    markedSixDegreeBalance m
      (fun j=>((markedBalanceTermSet tail head ktail khead H₀ HK (Sum.inr u) j).card:ℝ)) 3:=by
  have h0:((Finset.univ.filter (fun s:V×U=>H₀ s.1 s.2∨HK s.1 s.2)).filter
      (fun s=>s.2=u∧¬HK s.1 s.2))=(Finset.univ.filter (fun s:V×U=>H₀ s.1 s.2)).filter (fun s=>s.2=u):=by
    ext s
    have hh:=hd s.1 s.2
    simp only [Finset.mem_filter,Finset.mem_univ,true_and];tauto
  have h1:((Finset.univ.filter (fun s:V×U=>H₀ s.1 s.2∨HK s.1 s.2)).filter
      (fun s=>s.2=u∧HK s.1 s.2))=(Finset.univ.filter (fun s:V×U=>HK s.1 s.2)).filter (fun s=>s.2=u):=by
    ext s;simp only [Finset.mem_filter,Finset.mem_univ,true_and];tauto
  rw [markedSixDegreeBalance_hub]
  change _-(m:ℝ)*_=_
  rw [h0,h1,finite_spoke_relation_col_count,finite_spoke_relation_col_count]

end Oberwolfach
