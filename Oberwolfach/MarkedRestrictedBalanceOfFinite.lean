module

public import Oberwolfach.MarkedRestrictedSampleBalance

@[expose] public section
/-! Recover the restricted balance inequalities from the exact finite
balance values on the same domains and for all ambient roots. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_restricted_balance_of_finite_balance
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (hH:∀ v u,¬(H false v u∧H true v u)) (A:Finset V) (B:Finset U) (η:ℝ):
    let E:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let S:=Finset.univ.filter (fun s:V×U=>H false s.1 s.2∨H true s.1 s.2);
    (∀ z i,|markedFiniteDomainBalance (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) (H true) Finset.univ S m A B z i|≤η) →
    MarkedRestrictedBalanceWithSpokes P π d m A B η σ H := by
  intro E K S hfin
  constructor
  · intro v
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
    have hh0 := markedFiniteBalance_full_row t h kt kh H0 HK hd m v (0:Fin 3)
    have hh1 := markedFiniteBalance_full_row t h kt kh H0 HK hd m v (1:Fin 3)
    have hh2 := markedFiniteBalance_full_row t h kt kh H0 HK hd m v (2:Fin 3)
    change markedFiniteBalance t h kt kh HK Finset.univ _ m (Sum.inl v) 0=_ at hh0
    change markedFiniteBalance t h kt kh HK Finset.univ _ m (Sum.inl v) 1=_ at hh1
    change markedFiniteBalance t h kt kh HK Finset.univ _ m (Sum.inl v) 2=_ at hh2
    have heq0 : markedFiniteBalance t h kt kh HK Finset.univ
        (Finset.univ.filter (fun s:V×U=>H0 s.1 s.2∨HK s.1 s.2)) m (Sum.inl v) (0:Fin 4)=
      markedSixDegreeBalance m (fun j=>((markedBalanceTermSet t h kt kh H0 HK (Sum.inl v) j).card:ℝ)) 0 := by convert hh0 using 1 <;> congr!
    have heq1 : markedFiniteBalance t h kt kh HK Finset.univ
        (Finset.univ.filter (fun s:V×U=>H0 s.1 s.2∨HK s.1 s.2)) m (Sum.inl v) (1:Fin 4)=
      markedSixDegreeBalance m (fun j=>((markedBalanceTermSet t h kt kh H0 HK (Sum.inl v) j).card:ℝ)) 1 := by convert hh1 using 1 <;> congr!
    have heq2 : markedFiniteBalance t h kt kh HK Finset.univ
        (Finset.univ.filter (fun s:V×U=>H0 s.1 s.2∨HK s.1 s.2)) m (Sum.inl v) (2:Fin 4)=
      markedSixDegreeBalance m (fun j=>((markedBalanceTermSet t h kt kh H0 HK (Sum.inl v) j).card:ℝ)) 2 := by convert hh2 using 1 <;> congr!
    have hb0:=hfin (Sum.inl v) 0
    have hb1:=hfin (Sum.inl v) 1
    have hb2:=hfin (Sum.inl v) 2
    rw [hf,heq0,h0,occurrenceDegree_sum,hE.1,hK.1] at hb0
    rw [hf,heq1,h1,occurrenceDegree_sum,hE.2,hK.2] at hb1
    rw [hf,heq2,h2,hK.2] at hb2
    dsimp only [H0,HK] at hb0 hb1 hb2
    constructor
    · intro incoming
      cases incoming
      · dsimp only
        rw [←restricted_spoke_sum_row (H false) B v,←restricted_spoke_sum_row (H true) B v]
        convert hb0 using 1 <;> congr 1 <;> ring
      · dsimp only
        rw [←restricted_spoke_sum_row (H false) B v,←restricted_spoke_sum_row (H true) B v]
        convert hb1 using 1 <;> congr 1 <;> ring
    · dsimp only
      rw [←restricted_spoke_sum_row (H true) B v]
      convert hb2 using 1 <;> congr!
  · intro u
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
    have heq : markedFiniteBalance (fun e:E=>e.val.1) (fun e=>e.val.2)
          (fun e:K=>e.val.1) (fun e=>e.val.2) HK Finset.univ
          (Finset.univ.filter (fun s:V×U=>H0 s.1 s.2∨HK s.1 s.2)) m (Sum.inr u) 3=
        (∑ v,if H0 v u then (1:ℝ) else 0)-(m:ℝ)*(∑ v,if HK v u then (1:ℝ) else 0) := by
      have hh := markedFiniteBalance_full_hub (fun e:E=>e.val.1) (fun e=>e.val.2)
          (fun e:K=>e.val.1) (fun e=>e.val.2) H0 HK hd m u
      rw [markedSixDegreeBalance_hub] at hh
      convert hh using 1 <;> congr!
    have hb:=hfin (Sum.inr u) 3
    rw [hf,heq] at hb
    dsimp only [H0,HK] at hb
    dsimp only
    rw [←restricted_spoke_sum_col (H false) A u,←restricted_spoke_sum_col (H true) A u]
    exact hb
end Oberwolfach
