module

public import Oberwolfach.BoundedGraphFractionalMatching
public import Oberwolfach.FractionalCycleIncidence

@[expose] public section

/-! The deterministic matching-weight losses at an endpoint. All weights
are kept fixed; deleting conflict neighbours is charged at the original
row-domain scale. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

def endpointEligibleRowWeight (F : SimpleGraph V) (P : Finset V) (x v : V)
    (weight : V→V→ℝ) : ℝ :=
  ∑ w∈P,if ¬F.Adj x w ∧ ¬F.Adj v w then weight v w else 0

theorem endpoint_matching_row_target (F : SimpleGraph V) (P : Finset V) (x v : V)
    (weight : V→V→ℝ) (a C L : ℝ) (ha : 0<a) (hC : 0≤C)
    (hF : ∀ u,(F.degree u:ℝ)≤L)
    (hweight : ∀ w∈P,0≤weight v w ∧ weight v w≤C/a)
    (hsum : ∑ w∈P,weight v w=1) :
    |endpointEligibleRowWeight F P x v weight-1|≤2*C*L/a := by
  let Bad:=P.filter (fun w=>F.Adj x w ∨ F.Adj v w)
  have hBad : Bad⊆F.neighborFinset x∪F.neighborFinset v := by
    intro w hw
    rcases (Finset.mem_filter.mp hw).2 with h|h
    · exact Finset.mem_union_left _ (by simpa using h)
    · exact Finset.mem_union_right _ (by simpa using h)
  have hcard:=(Finset.card_le_card hBad).trans (Finset.card_union_le _ _)
  rw [SimpleGraph.card_neighborFinset_eq_degree,SimpleGraph.card_neighborFinset_eq_degree] at hcard
  have hcardR : (Bad.card:ℝ)≤2*L := by
    have hh : (Bad.card:ℝ)≤(F.degree x:ℝ)+(F.degree v:ℝ) := by exact_mod_cast hcard
    linarith only [hh,hF x,hF v]
  have hsplit : endpointEligibleRowWeight F P x v weight+(∑ w∈Bad,weight v w)=1 := by
    rw [←hsum,Finset.sum_filter]
    unfold endpointEligibleRowWeight
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro w hw
    by_cases hx:F.Adj x w <;> by_cases hv:F.Adj v w <;> simp [hx,hv]
  have hnonneg : 0≤∑ w∈Bad,weight v w := Finset.sum_nonneg
    (fun w hw=>(hweight w (Finset.mem_filter.mp hw).1).1)
  have hupper : (∑ w∈Bad,weight v w)≤2*C*L/a := by
    calc
      _ ≤ ∑ _w∈Bad,C/a := Finset.sum_le_sum (fun w hw=>(hweight w (Finset.mem_filter.mp hw).1).2)
      _ = (Bad.card:ℝ)*(C/a) := by simp
      _ ≤ (2*L)*(C/a) := mul_le_mul_of_nonneg_right hcardR (div_nonneg hC ha.le)
      _ = _ := by ring
  have he : endpointEligibleRowWeight F P x v weight-1=-(∑ w∈Bad,weight v w) := by linarith only [hsplit]
  rw [he,abs_neg,abs_of_nonneg hnonneg]
  exact hupper

def endpointEligibleOrderedMass (F : SimpleGraph V) (P : Finset V) (x : V)
    (weight : V→V→ℝ) : ℝ :=
  ∑ v∈P,if ¬F.Adj x v then endpointEligibleRowWeight F P x v weight else 0

theorem endpoint_matching_total_target (F : SimpleGraph V) (P : Finset V) (x : V)
    (weight : V→V→ℝ) (a C L : ℝ) (ha : 0<a) (hC : 0≤C)
    (hPa : (P.card:ℝ)≤a) (hF : ∀ u,(F.degree u:ℝ)≤L)
    (hweight : ∀ v∈P,∀ w∈P,0≤weight v w ∧ weight v w≤C/a)
    (hsum : ∀ v∈P,∑ w∈P,weight v w=1) :
    |endpointEligibleOrderedMass F P x weight/2-(P.card:ℝ)/2|≤(1+2*C)*L/2 := by
  have hL : 0≤L := (Nat.cast_nonneg (F.degree x)).trans (hF x)
  let Good:=P.filter (fun v=>¬F.Adj x v)
  let Bad:=P.filter (fun v=>F.Adj x v)
  have hcount : Good.card+Bad.card=P.card := by
    dsimp [Good,Bad]
    rw [Finset.card_filter,Finset.card_filter,←Finset.sum_add_distrib]
    calc
      _ = ∑ _v∈P,(1:ℕ) := by
        apply Finset.sum_congr rfl
        intro v hv
        by_cases h:F.Adj x v <;> simp [h]
      _ = _ := by simp
  have hBad : (Bad.card:ℝ)≤L := by
    have hh : Bad⊆F.neighborFinset x := by intro v hv;simpa using (Finset.mem_filter.mp hv).2
    exact (by exact_mod_cast Finset.card_le_card hh : (Bad.card:ℝ)≤(F.degree x:ℝ)).trans (hF x)
  have hGood : (Good.card:ℝ)≤a := (by exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _) :
    (Good.card:ℝ)≤P.card).trans hPa
  have hrow (v : V) (hv:v∈Good) :
      |endpointEligibleRowWeight F P x v weight-1|≤2*C*L/a :=
    endpoint_matching_row_target F P x v weight a C L ha hC hF
      (hweight v (Finset.mem_filter.mp hv).1) (hsum v (Finset.mem_filter.mp hv).1)
  have he : endpointEligibleOrderedMass F P x weight=∑ v∈Good,endpointEligibleRowWeight F P x v weight := by
    dsimp [endpointEligibleOrderedMass,Good];rw [Finset.sum_filter]
  have htotal : |endpointEligibleOrderedMass F P x weight-(Good.card:ℝ)|≤2*C*L := by
    rw [he]
    have hh : (∑ v∈Good,endpointEligibleRowWeight F P x v weight)-(Good.card:ℝ)=
        ∑ v∈Good,(endpointEligibleRowWeight F P x v weight-1) := by rw [Finset.sum_sub_distrib];simp
    rw [hh]
    calc
      _ ≤ ∑ v∈Good,|endpointEligibleRowWeight F P x v weight-1| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _v∈Good,2*C*L/a := Finset.sum_le_sum hrow
      _ = (Good.card:ℝ)*(2*C*L/a) := by simp
      _ ≤ a*(2*C*L/a) := mul_le_mul_of_nonneg_right hGood (by positivity)
      _ = 2*C*L := by field_simp
  have hcountR : (P.card:ℝ)=Good.card+(Bad.card:ℝ) := by exact_mod_cast hcount.symm
  have hd : |endpointEligibleOrderedMass F P x weight-(P.card:ℝ)|≤(1+2*C)*L := by
    rw [hcountR]
    have hh:=abs_sub_le (endpointEligibleOrderedMass F P x weight) (Good.card:ℝ)
      ((Good.card:ℝ)+Bad.card)
    have he' : |(Good.card:ℝ)-((Good.card:ℝ)+Bad.card)|=Bad.card := by
      rw [show (Good.card:ℝ)-((Good.card:ℝ)+Bad.card)=-(Bad.card:ℝ) by ring,abs_neg,abs_of_nonneg (Nat.cast_nonneg _)]
    rw [he'] at hh
    nlinarith only [hh,htotal,hBad]
  rw [←sub_div,abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
  exact div_le_div_of_nonneg_right hd (by norm_num)

end Oberwolfach
