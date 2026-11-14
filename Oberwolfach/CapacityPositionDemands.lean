module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic

@[expose] public section

/-! The position degrees for splitting ordinary capacities. Their totals and
boundary values follow from the original marked balance identities. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach

def capacityPositionDemands (k : ℕ) (p q O : ℝ) : Fin (k+2) → ℝ :=
  Fin.cons p (Fin.snoc (fun _ : Fin k => (O-p)/k) q)

@[simp] theorem capacityPositionDemands_first (k : ℕ) (p q O : ℝ) :
    capacityPositionDemands k p q O 0=p := by simp [capacityPositionDemands]

@[simp] theorem capacityPositionDemands_last (k : ℕ) (p q O : ℝ) :
    capacityPositionDemands k p q O (Fin.last (k+1))=q := by
  change Fin.cons (α := fun _ => ℝ) p (Fin.snoc (α := fun _ => ℝ) (fun _ : Fin k => (O-p)/k) q) (Fin.last k).succ=q
  simp

theorem capacityPositionDemands_outgoing (k : ℕ) (hk : 0<k) (p q O : ℝ) :
    (∑ j : Fin (k+1),capacityPositionDemands k p q O j.castSucc)=O := by
  rw [Fin.sum_univ_succ]
  simp only [capacityPositionDemands,Fin.castSucc_zero,Fin.cons_zero,Fin.castSucc_succ,Fin.cons_succ,Fin.snoc_castSucc,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  field_simp [show (k:ℝ)≠0 from Nat.cast_ne_zero.mpr hk.ne']
  <;> ring

theorem capacityPositionDemands_incoming (k : ℕ) (hk : 0<k) (p q O I : ℝ)
    (hbalance : O-I=p-q) :
    (∑ j : Fin (k+1),capacityPositionDemands k p q O j.succ)=I := by
  simp only [capacityPositionDemands,Fin.cons_succ]
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc,Fin.snoc_last,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  have hn : (k:ℝ)≠0 := Nat.cast_ne_zero.mpr hk.ne'
  field_simp [hn]
  nlinarith

theorem capacityPositionDemands_total {V : Type*} [Fintype V]
    (k : ℕ) (hk : 0<k) (p q O : V → ℝ) (M : ℝ)
    (hp : ∑ v,p v=M) (hq : ∑ v,q v=M) (hO : ∑ v,O v=(k+1)*M)
    (j : Fin (k+2)) : (∑ v,capacityPositionDemands k (p v) (q v) (O v) j)=M := by
  refine Fin.cases ?_ (fun j => ?_) j
  · simpa only [capacityPositionDemands_first] using hp
  · refine Fin.lastCases ?_ (fun j => ?_) j
    · simpa only [capacityPositionDemands,Fin.cons_succ,Fin.snoc_last] using hq
    · simp only [capacityPositionDemands,Fin.cons_succ,Fin.snoc_castSucc]
      rw [← Finset.sum_div,Finset.sum_sub_distrib,hO,hp]
      field_simp [show (k:ℝ)≠0 from Nat.cast_ne_zero.mpr hk.ne']
      <;> ring

theorem capacityPositionDemands_error (k : ℕ) (hk : 0<k) (p q O z E : ℝ)
    (hE : 0≤E) (hp : |p-z|≤E) (hq : |q-z|≤E) (hO : |O-(k+1)*z|≤E)
    (j : Fin (k+2)) : |capacityPositionDemands k p q O j-z|≤2*E := by
  refine Fin.cases ?_ (fun j => ?_) j
  · simpa only [capacityPositionDemands_first] using hp.trans (by linarith)
  · refine Fin.lastCases ?_ (fun j => ?_) j
    · simpa only [capacityPositionDemands,Fin.cons_succ,Fin.snoc_last] using hq.trans (by linarith)
    · simp only [capacityPositionDemands,Fin.cons_succ,Fin.snoc_castSucc]
      have hkr : (1:ℝ)≤k := by exact_mod_cast hk
      have hkp : (0:ℝ)<k := by linarith
      rw [show (O-p)/(k:ℝ)-z=((O-(k+1)*z)-(p-z))/k by field_simp;ring,
        abs_div,abs_of_pos hkp]
      apply (div_le_iff₀ hkp).mpr
      have hb := (abs_sub _ _).trans (add_le_add hO hp)
      nlinarith

end Oberwolfach
