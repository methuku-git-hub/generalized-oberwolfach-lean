module

public import Oberwolfach.UniformIncomingRounded

@[expose] public section
/-! The rounding keeps the tail load small when most heads have a smaller demand. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {X Y E : Type} [Fintype X] [Fintype Y] [Fintype E]

theorem uniform_incoming_rounding_inner_sum
    (tail:E→X) (head:E→Y) (eligible:E→Prop) (t:Y→ℕ) (I:Finset Y)
    (ht:∀y,t y≤(eligibleIncoming head eligible y).card)
    (global loc rho:ℝ) (hglobal:0≤global) (hlocal:0≤loc) (hrho:0<rho)
    (hglobalBound:(∑y∈I,(t y:ℝ))≤global) (hlocalBound:∀y,y∉I→(t y:ℝ)≤loc)
    (hsize:∀y,rho≤((eligibleIncoming head eligible y).card:ℝ))
    (hpair:Function.Injective (fun e:E=>(tail e,head e))):
    ∃D:E→Bool,
      (∀e,D e=true→eligible e) ∧
      (∀y,(∑e,if head e=y ∧ D e=true then (1:ℕ) else 0)=t y) ∧
      (∀x,(∑e,if tail e=x ∧ D e=true then (1:ℕ) else 0)≤
        ⌈global/rho+(Fintype.card Y:ℝ)*(loc/rho)⌉₊):=by
  obtain ⟨D,hD,hhead,htail⟩:=uniform_incoming_rounding tail head eligible t ht
  refine ⟨D,hD,hhead,?_⟩
  intro x
  apply (htail x).trans
  apply Nat.ceil_mono
  let S:=Finset.univ.filter (fun e=>tail e=x)
  let Sin:=S.filter (fun e=>head e∈I)
  let Sout:=S.filter (fun e=>head e∉I)
  have hin:Sin.card≤I.card:=by
    apply Finset.card_le_card_of_injOn head
    · intro e he;exact (Finset.mem_filter.mp he).2
    · intro e he f hf hef
      apply hpair
      apply Prod.ext
      · exact ((Finset.mem_filter.mp (Finset.mem_filter.mp he).1).2).trans
          ((Finset.mem_filter.mp (Finset.mem_filter.mp hf).1).2).symm
      · exact hef
  have hout:Sout.card≤Fintype.card Y:=by
    apply (Finset.card_le_card_of_injOn head (t:=Finset.univ) ?_ ?_)
    · intro e he;exact Finset.mem_univ _
    · intro e he f hf hef
      apply hpair
      apply Prod.ext
      · exact ((Finset.mem_filter.mp (Finset.mem_filter.mp he).1).2).trans
          ((Finset.mem_filter.mp (Finset.mem_filter.mp hf).1).2).symm
      · exact hef
  have hweightin:∀e,uniformIncomingWeight head eligible t e≤(t (head e):ℝ)/rho:=by
    intro e
    unfold uniformIncomingWeight
    split_ifs with h
    · exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hrho (hsize (head e))
    · exact div_nonneg (Nat.cast_nonneg _) hrho.le
  have hweightout:∀e,head e∉I→uniformIncomingWeight head eligible t e≤loc/rho:=by
    intro e he
    unfold uniformIncomingWeight
    split_ifs with h
    · exact div_le_div₀ hlocal (hlocalBound (head e) he) hrho (hsize (head e))
    · exact div_nonneg hlocal hrho.le
  have hsum: (∑e∈S,uniformIncomingWeight head eligible t e)=
      (∑e∈Sin,uniformIncomingWeight head eligible t e)+(∑e∈Sout,uniformIncomingWeight head eligible t e):=by
    rw [← Finset.sum_filter_add_sum_filter_not S (fun e=>head e∈I)]
  have hinj: Set.InjOn head (↑Sin:Set E):=by
    intro e he f hf hef
    apply hpair
    apply Prod.ext
    · exact ((Finset.mem_filter.mp (Finset.mem_filter.mp he).1).2).trans
        ((Finset.mem_filter.mp (Finset.mem_filter.mp hf).1).2).symm
    · exact hef
  have hsubset:Sin.image head⊆I:=by
    intro y hy
    obtain ⟨e,he,rfl⟩:=Finset.mem_image.mp hy
    exact (Finset.mem_filter.mp he).2
  have h₁:(∑e∈Sin,uniformIncomingWeight head eligible t e)≤global/rho:=by
    calc
      _ ≤ ∑e∈Sin,(t (head e):ℝ)/rho :=by
        apply Finset.sum_le_sum
        intro e he
        exact hweightin e
      _ = ∑y∈Sin.image head,(t y:ℝ)/rho :=by
        symm
        apply Finset.sum_image
        intro e he f hf hef
        exact hinj he hf hef
      _ ≤ ∑y∈I,(t y:ℝ)/rho :=by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
        intro y hy hnot
        exact div_nonneg (Nat.cast_nonneg _) hrho.le
      _ = (∑y∈I,(t y:ℝ))/rho :=by rw [Finset.sum_div]
      _ ≤ global/rho:=div_le_div_of_nonneg_right hglobalBound hrho.le
  have h₂:(∑e∈Sout,uniformIncomingWeight head eligible t e)≤(Fintype.card Y:ℝ)*(loc/rho):=by
    calc
      _ ≤ ∑_e∈Sout,loc/rho :=by
        apply Finset.sum_le_sum;intro e he
        exact hweightout e (Finset.mem_filter.mp he).2
      _ = (Sout.card:ℝ)*(loc/rho):=by simp
      _ ≤ _:=mul_le_mul_of_nonneg_right (by exact_mod_cast hout) (div_nonneg hlocal hrho.le)
  have htotal:(∑e∈S,uniformIncomingWeight head eligible t e)≤global/rho+(Fintype.card Y:ℝ)*(loc/rho):=by
    rw [hsum];exact add_le_add h₁ h₂
  simpa only [S,Finset.sum_filter] using htotal
end Oberwolfach
