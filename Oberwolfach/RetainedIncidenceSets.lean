module

public import Oberwolfach.SupportedIndicatorScale
public import Oberwolfach.InterfaceFamilyRegularization
public import Oberwolfach.FiniteCoordinateEvents
public import Oberwolfach.EdgeRetention

@[expose] public section

/-! A retained incidence is witnessed by one of its actual physical coins.
Different outside indices will have disjoint coordinate sets; a single
coordinate may still place several labels in the same support. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V J E:Type*} [Fintype V] [Fintype J] [Fintype E]
  [DecidableEq V] [DecidableEq J] [DecidableEq E]

def retainedIncidenceSet (C:J→V→Finset E) (σ:E→Bool) (j:J):Finset V :=
  Finset.univ.filter (fun v=>∃ e∈C j v,σ e=true)

@[simp] theorem mem_retainedIncidenceSet (C:J→V→Finset E) (σ:E→Bool) (j:J) (v:V):
    v∈retainedIncidenceSet C σ j ↔ ∃ e∈C j v,σ e=true := by
  simp [retainedIncidenceSet]

theorem retainedIncidenceSet_local (C:J→V→Finset E) (j:J) (v:V) (σ τ:E→Bool)
    (h:∀ e∈C j v,σ e=τ e):
    (v∈retainedIncidenceSet C σ j ↔ v∈retainedIncidenceSet C τ j) := by
  simp only [mem_retainedIncidenceSet]
  constructor
  · rintro ⟨e,he,hσ⟩;exact ⟨e,he,(h e he).symm.trans hσ⟩
  · rintro ⟨e,he,hτ⟩;exact ⟨e,he,(h e he).trans hτ⟩

theorem retainedIncidenceSet_probability (C:J→V→Finset E) (j:J) (v:V)
    (p:ℝ) (hp:0≤p) (hp1:p≤1):
    (FiniteLaw.pi (fun _:E=>FiniteLaw.retentionCoin p hp hp1)).probability
      (fun σ=>v∈retainedIncidenceSet C σ j) ≤ p*(C j v).card := by
  have hh:=finiteLaw_union_bound (FiniteLaw.pi (fun _:E=>FiniteLaw.retentionCoin p hp hp1))
    (C j v) (fun e σ=>σ e=true)
  have he (e:E):
      (FiniteLaw.pi (fun _:E=>FiniteLaw.retentionCoin p hp hp1)).probability (fun σ=>σ e=true)=p := by
    have hx:=finiteLaw_pi_coordinate_event (fun _:E=>FiniteLaw.retentionCoin p hp hp1) e (fun a=>a=true)
    rw [finiteLaw_probability_point] at hx
    exact hx
  simpa only [mem_retainedIncidenceSet,he,Finset.sum_const,nsmul_eq_mul,mul_comm] using hh

theorem retainedIncidenceSet_pair_probability (C:J→V→Finset E) (i j:J) (v:V)
    (hd:Disjoint (C i v) (C j v)) (p:ℝ) (hp:0≤p) (hp1:p≤1):
    (FiniteLaw.pi (fun _:E=>FiniteLaw.retentionCoin p hp hp1)).probability
      (fun σ=>v∈retainedIncidenceSet C σ i ∧ v∈retainedIncidenceSet C σ j) ≤
        p^2*((C i v).card:ℝ)*(C j v).card := by
  rw [finiteLaw_disjoint_supported_events _ (C i v) (C j v) hd _ _
    (retainedIncidenceSet_local C i v) (retainedIncidenceSet_local C j v)]
  calc
    _ ≤ (p*(C i v).card)*(p*(C j v).card) := mul_le_mul
      (retainedIncidenceSet_probability C i v p hp hp1)
      (retainedIncidenceSet_probability C j v p hp hp1)
      (finiteLaw_probability_nonneg _ _) (by positivity)
    _ = _ := by ring

theorem retainedIncidenceSet_row_mean (C:J→V→Finset E) (j:J)
    (p:ℝ) (hp:0≤p) (hp1:p≤1) (M:ℝ) (hC:∀ v,((C j v).card:ℝ)≤M):
    (FiniteLaw.pi (fun _:E=>FiniteLaw.retentionCoin p hp hp1)).expectation
      (fun σ=>((retainedIncidenceSet C σ j).card:ℝ)) ≤ p*M*Fintype.card V := by
  have he:(FiniteLaw.pi (fun _:E=>FiniteLaw.retentionCoin p hp hp1)).expectation
      (fun σ=>((retainedIncidenceSet C σ j).card:ℝ))=
      ∑ v:V,(FiniteLaw.pi (fun _:E=>FiniteLaw.retentionCoin p hp hp1)).probability
        (fun σ=>v∈retainedIncidenceSet C σ j) := by
    convert finiteLaw_expectation_count (FiniteLaw.pi (fun _:E=>FiniteLaw.retentionCoin p hp hp1))
      (Finset.univ:Finset V) (fun v σ=>v∈retainedIncidenceSet C σ j) using 1
    congr 1;funext σ;congr 1;congr 1;ext v;simp
  rw [he]
  calc
    _ ≤ ∑ v:V,p*M := Finset.sum_le_sum (fun v _=>
      (retainedIncidenceSet_probability C j v p hp hp1).trans (mul_le_mul_of_nonneg_left (hC v) hp))
    _ = _ := by simp;ring

theorem retainedIncidenceSet_pair_mean (C:J→V→Finset E) (i j:J)
    (hd:∀ v,Disjoint (C i v) (C j v))
    (p:ℝ) (hp:0≤p) (hp1:p≤1) (M:ℝ) (hM:0≤M)
    (hCi:∀ v,((C i v).card:ℝ)≤M) (hCj:∀ v,((C j v).card:ℝ)≤M):
    (FiniteLaw.pi (fun _:E=>FiniteLaw.retentionCoin p hp hp1)).expectation
      (fun σ=>((retainedIncidenceSet C σ i∩retainedIncidenceSet C σ j).card:ℝ)) ≤
        p^2*M^2*Fintype.card V := by
  have he (σ:E→Bool):retainedIncidenceSet C σ i∩retainedIncidenceSet C σ j=
      Finset.univ.filter (fun v=>v∈retainedIncidenceSet C σ i∧v∈retainedIncidenceSet C σ j) := by ext;simp
  simp_rw [he]
  have hx:=finiteLaw_expectation_count (FiniteLaw.pi (fun _:E=>FiniteLaw.retentionCoin p hp hp1))
    (Finset.univ:Finset V) (fun v σ=>v∈retainedIncidenceSet C σ i∧v∈retainedIncidenceSet C σ j)
  have hx':(FiniteLaw.pi (fun _:E=>FiniteLaw.retentionCoin p hp hp1)).expectation
      (fun σ=>((Finset.univ.filter (fun v=>v∈retainedIncidenceSet C σ i∧v∈retainedIncidenceSet C σ j)).card:ℝ))=
      ∑ v:V,(FiniteLaw.pi (fun _:E=>FiniteLaw.retentionCoin p hp hp1)).probability
        (fun σ=>v∈retainedIncidenceSet C σ i∧v∈retainedIncidenceSet C σ j) := by
    convert hx using 1 <;> congr!
  rw [hx']
  calc
    _ ≤ ∑ v:V,p^2*M^2 := by
      apply Finset.sum_le_sum
      intro v _
      apply (retainedIncidenceSet_pair_probability C i j v (hd v) p hp hp1).trans
      have hh:=mul_le_mul (hCi v) (hCj v) (Nat.cast_nonneg _) hM
      nlinarith only [mul_le_mul_of_nonneg_left hh (sq_nonneg p)]
    _ = _ := by simp;ring

end Oberwolfach
