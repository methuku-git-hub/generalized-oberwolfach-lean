module

public import Oberwolfach.MarkedRestrictedSampleDegrees
public import Oberwolfach.MarkedFiniteDomainBalanceBridge
public import Oberwolfach.MarkedBalanceSpokeChanges

@[expose] public section

/-! Convert the original-law restricted-balance event to the exact finite
arc and spoke balance values used by the marked cover-down induction.
Every root remains ambient, including roots outside the fixed domains. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 18000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [LinearOrder V] [DecidableEq U]

theorem restricted_spoke_sum_row (H : V→U→Prop) (B : Finset U) (v : V) :
    (∑ u,if H v u∧u∈B then (1:ℝ) else 0)=∑ u∈B,bipAdj H v u := by
  simp only [bipAdj,ite_and,←Finset.sum_filter,Finset.filter_univ_mem]
  congr 1
  ext x
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  tauto

theorem restricted_spoke_sum_col (H : V→U→Prop) (A : Finset V) (u : U) :
    (∑ v,if H v u∧v∈A then (1:ℝ) else 0)=∑ v∈A,bipAdj H v u := by
  simp only [bipAdj,ite_and,←Finset.sum_filter,Finset.filter_univ_mem]
  congr 1
  ext x
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  tauto

theorem marked_restricted_sample_balance
    (P : SimpleGraph V) (π : Equiv.Perm V) (d m : ℕ)
    (σ : RawMarkedOutcome V U Γ Color) (H : Bool→V→U→Prop)
    (hH : ∀ v u,¬(H false v u∧H true v u)) (A : Finset V) (B : Finset U)
    (η : ℝ) (hη : 0≤η) (hbal : MarkedRestrictedBalanceWithSpokes P π d m A B η σ H) :
    let E := MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K := MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let S := Finset.univ.filter (fun s:V×U=>H false s.1 s.2∨H true s.1 s.2);
    ∀ z i,|markedFiniteDomainBalance (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) (H true) Finset.univ S m A B z i|≤η := by
  intro E K S z i
  cases z with
  | inl v=>
    let PE : E→Prop := fun e=>(if e.val.1=v then e.val.2 else e.val.1)∈A
    let PK : K→Prop := fun e=>(if e.val.1=v then e.val.2 else e.val.1)∈A
    let t := fun e:{e:E // PE e}=>e.val.val.1
    let h := fun e:{e:E // PE e}=>e.val.val.2
    let kt := fun e:{e:K // PK e}=>e.val.val.1
    let kh := fun e:{e:K // PK e}=>e.val.val.2
    let H0 := fun x u=>H false x u∧u∈B
    let HK := fun x u=>H true x u∧u∈B
    have hd : ∀ x u,¬(H0 x u∧HK x u) := fun x u hh=>hH x u ⟨hh.1.1,hh.2.1⟩
    have hf (j:Fin 4) : markedFiniteDomainBalance (fun e:E=>e.val.1) (fun e=>e.val.2)
        (fun e:K=>e.val.1) (fun e=>e.val.2) (H true) Finset.univ S m A B (Sum.inl v) j=
      markedFiniteBalance t h kt kh HK Finset.univ
        (Finset.univ.filter (fun s:V×U=>H0 s.1 s.2∨HK s.1 s.2)) m (Sum.inl v) j := by
      have hh := markedFiniteBalance_subtype_restriction (fun e:E=>e.val.1) (fun e=>e.val.2)
        (fun e:K=>e.val.1) (fun e=>e.val.2) (H false) (H true) PE PK (fun _ u=>u∈B) m (Sum.inl v) j
      dsimp only [markedFiniteDomainBalance]
      convert hh.symm using 1 <;> congr!
      rename_i e he
      cases e <;> rfl
    have hE : occurrenceDegree t v=(markedRestrictedDegree P π (3*d) (fun e=>σ (Sum.inl e)) false false v A:ℝ) ∧
        occurrenceDegree h v=(markedRestrictedDegree P π (3*d) (fun e=>σ (Sum.inl e)) false true v A:ℝ) := by
      convert markedSampleArc_opposite_domain_degrees P π (3*d) (fun e=>σ (Sum.inl e)) false v A using 1 <;> congr!
    have hK : occurrenceDegree kt v=(markedRestrictedDegree P π (3*d) (fun e=>σ (Sum.inl e)) true false v A:ℝ) ∧
        occurrenceDegree kh v=(markedRestrictedDegree P π (3*d) (fun e=>σ (Sum.inl e)) true true v A:ℝ) := by
      convert markedSampleArc_opposite_domain_degrees P π (3*d) (fun e=>σ (Sum.inl e)) true v A using 1 <;> congr!
    have hr0 : (∑ u,if H0 v u then (1:ℝ) else 0)=∑ u∈B,bipAdj (H false) v u := restricted_spoke_sum_row (H false) B v
    have hrK : (∑ u,if HK v u then (1:ℝ) else 0)=∑ u∈B,bipAdj (H true) v u := restricted_spoke_sum_row (H true) B v
    obtain ⟨h0,h1,h2⟩ := markedSixDegreeBalance_row t h kt kh H0 HK m v
    rw [hf]
    fin_cases i
    · have hh := markedFiniteBalance_full_row t h kt kh H0 HK hd m v (0:Fin 3)
      change markedFiniteBalance t h kt kh HK Finset.univ _ m (Sum.inl v) 0=_ at hh
      have heq : markedFiniteBalance t h kt kh HK Finset.univ
          (Finset.univ.filter (fun s:V×U=>H0 s.1 s.2∨HK s.1 s.2)) m (Sum.inl v) (0:Fin 4)=
        markedSixDegreeBalance m
          (fun j=>((markedBalanceTermSet t h kt kh H0 HK (Sum.inl v) j).card:ℝ)) (0:Fin 4) := by
        convert hh using 1 <;> congr!
      change |markedFiniteBalance t h kt kh HK Finset.univ
        (Finset.univ.filter (fun s:V×U=>H0 s.1 s.2∨HK s.1 s.2)) m (Sum.inl v) (0:Fin 4)|≤η
      rw [heq,h0,occurrenceDegree_sum,hE.1,hK.1]
      dsimp only [H0,HK]
      have hb := (hbal.1 v).1 false
      dsimp only at hb
      rw [←restricted_spoke_sum_row (H false) B v,←restricted_spoke_sum_row (H true) B v] at hb
      convert hb using 1 <;> congr 1 <;> ring
    · have hh := markedFiniteBalance_full_row t h kt kh H0 HK hd m v (1:Fin 3)
      change markedFiniteBalance t h kt kh HK Finset.univ _ m (Sum.inl v) 1=_ at hh
      have heq : markedFiniteBalance t h kt kh HK Finset.univ
          (Finset.univ.filter (fun s:V×U=>H0 s.1 s.2∨HK s.1 s.2)) m (Sum.inl v) (1:Fin 4)=
        markedSixDegreeBalance m
          (fun j=>((markedBalanceTermSet t h kt kh H0 HK (Sum.inl v) j).card:ℝ)) (1:Fin 4) := by
        convert hh using 1 <;> congr!
      change |markedFiniteBalance t h kt kh HK Finset.univ
        (Finset.univ.filter (fun s:V×U=>H0 s.1 s.2∨HK s.1 s.2)) m (Sum.inl v) (1:Fin 4)|≤η
      rw [heq,h1,occurrenceDegree_sum,hE.2,hK.2]
      dsimp only [H0,HK]
      have hb := (hbal.1 v).1 true
      dsimp only at hb
      rw [←restricted_spoke_sum_row (H false) B v,←restricted_spoke_sum_row (H true) B v] at hb
      convert hb using 1 <;> congr 1 <;> ring
    · have hh := markedFiniteBalance_full_row t h kt kh H0 HK hd m v (2:Fin 3)
      change markedFiniteBalance t h kt kh HK Finset.univ _ m (Sum.inl v) 2=_ at hh
      have heq : markedFiniteBalance t h kt kh HK Finset.univ
          (Finset.univ.filter (fun s:V×U=>H0 s.1 s.2∨HK s.1 s.2)) m (Sum.inl v) (2:Fin 4)=
        markedSixDegreeBalance m
          (fun j=>((markedBalanceTermSet t h kt kh H0 HK (Sum.inl v) j).card:ℝ)) (2:Fin 4) := by
        convert hh using 1 <;> congr!
      change |markedFiniteBalance t h kt kh HK Finset.univ
        (Finset.univ.filter (fun s:V×U=>H0 s.1 s.2∨HK s.1 s.2)) m (Sum.inl v) (2:Fin 4)|≤η
      rw [heq,h2,hK.2]
      dsimp only [H0,HK]
      have hb := (hbal.1 v).2
      dsimp only at hb
      rw [←restricted_spoke_sum_row (H true) B v] at hb
      convert hb using 1 <;> congr!
    · simpa only [markedFiniteBalance,Matrix.cons_val_succ',Matrix.cons_val_zero',abs_zero] using hη
  | inr u=>
    let H0 := fun x u=>H false x u∧x∈A
    let HK := fun x u=>H true x u∧x∈A
    have hd : ∀ x u,¬(H0 x u∧HK x u) := fun x u hh=>hH x u ⟨hh.1.1,hh.2.1⟩
    have hf (j:Fin 4) : markedFiniteDomainBalance (fun e:E=>e.val.1) (fun e=>e.val.2)
        (fun e:K=>e.val.1) (fun e=>e.val.2) (H true) Finset.univ S m A B (Sum.inr u) j=
      markedFiniteBalance (fun e:E=>e.val.1) (fun e=>e.val.2) (fun e:K=>e.val.1) (fun e=>e.val.2)
        HK Finset.univ (Finset.univ.filter (fun s:V×U=>H0 s.1 s.2∨HK s.1 s.2)) m (Sum.inr u) j := by
      fin_cases j <;> simp only [markedFiniteDomainBalance,markedFiniteBalance,Matrix.cons_val_succ',Matrix.cons_val_zero']
      congr 2 <;> norm_cast <;> congr 1 <;> ext s <;>
        simp only [S,H0,HK,Finset.mem_filter,Finset.mem_univ,true_and] <;> tauto
    rw [hf]
    fin_cases i
    · simpa only [markedFiniteBalance,Matrix.cons_val_zero',abs_zero] using hη
    · simpa only [markedFiniteBalance,Matrix.cons_val_succ',Matrix.cons_val_zero',abs_zero] using hη
    · simpa only [markedFiniteBalance,Matrix.cons_val_succ',Matrix.cons_val_zero',abs_zero] using hη
    · have heq : markedFiniteBalance (fun e:E=>e.val.1) (fun e=>e.val.2)
          (fun e:K=>e.val.1) (fun e=>e.val.2) HK Finset.univ
          (Finset.univ.filter (fun s:V×U=>H0 s.1 s.2∨HK s.1 s.2)) m (Sum.inr u) 3=
        (∑ v,if H0 v u then (1:ℝ) else 0)-(m:ℝ)*(∑ v,if HK v u then (1:ℝ) else 0) := by
        have hh := markedFiniteBalance_full_hub (fun e:E=>e.val.1) (fun e=>e.val.2)
          (fun e:K=>e.val.1) (fun e=>e.val.2) H0 HK hd m u
        rw [markedSixDegreeBalance_hub] at hh
        convert hh using 1 <;> congr!
      change |markedFiniteBalance (fun e:E=>e.val.1) (fun e=>e.val.2)
        (fun e:K=>e.val.1) (fun e=>e.val.2) HK Finset.univ
        (Finset.univ.filter (fun s:V×U=>H0 s.1 s.2∨HK s.1 s.2)) m (Sum.inr u) 3|≤η
      rw [heq]
      change |(∑ v,if H false v u∧v∈A then (1:ℝ) else 0)-
        (m:ℝ)*(∑ v,if H true v u∧v∈A then (1:ℝ) else 0)|≤η
      rw [restricted_spoke_sum_col,restricted_spoke_sum_col]
      exact hbal.2 u

end Oberwolfach
