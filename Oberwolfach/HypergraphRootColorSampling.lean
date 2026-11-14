module

public import Oberwolfach.HypergraphColorSampling

@[expose] public section

/-! Degrees after vertex colouring. The root is omitted from the random
product, and estimates are simultaneous over the prescribed root colour. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V E C : Type*} [Fintype V] [Fintype E] [Fintype C]
    [DecidableEq V] [Nonempty C]

abbrev HypergraphEdgesAt (R : E → Finset V) (v : V) := {e : E // v∈R e}

def hypergraphRootRemainder (R : E → Finset V) (v : V) (e : HypergraphEdgesAt R v) : Finset V :=
  (R e.val).erase v

theorem hypergraphRootRemainder_card (R : E → Finset V) (k : ℕ)
    (hR : ∀ e,(R e).card=k) (v : V) (e : HypergraphEdgesAt R v) :
    (hypergraphRootRemainder R v e).card=k-1 := by
  rw [hypergraphRootRemainder,Finset.card_erase_of_mem e.property,hR]

theorem hypergraphRootRemainder_degree (R : E → Finset V) (v u : V) :
    hypergraphWeightedDegree (hypergraphRootRemainder R v) (fun _=>1) u=
      if u=v then 0 else ((Finset.univ.filter (fun e=>v∈R e ∧ u∈R e)).card:ℝ) := by
  unfold hypergraphWeightedDegree hypergraphRootRemainder
  have he := Finset.sum_subtype (p:=fun e=>v∈R e) (F:=inferInstance) (Finset.univ.filter (fun e=>v∈R e))
    (fun e=>by simp) (fun e : E=>if u∈(R e).erase v then (1:ℝ) else 0)
  rw [← he,Finset.sum_filter]
  by_cases huv : u=v
  · subst u;simp only [Finset.notMem_erase,ite_false,ite_self,Finset.sum_const_zero,ite_true]
  rw [if_neg huv,← Finset.sum_boole]
  apply Finset.sum_congr rfl
  intro e _
  simp only [Finset.mem_erase,ne_eq,huv,not_false_eq_true,true_and,ite_and]

theorem hypergraphRootColor_tail (R : E → Finset V) (k : ℕ) (hk : 2≤k)
    (hR : ∀ e,(R e).card=k) (v : V) (hv : 0<Fintype.card (HypergraphEdgesAt R v))
    (D : ℝ) (hD : 0≤D)
    (hcodegree : ∀ u,u≠v → ((Finset.univ.filter (fun e=>v∈R e ∧ u∈R e)).card:ℝ)≤D)
    (c : C) (t : ℝ) (ht : 0≤t) :
    (FiniteLaw.pi (fun _ : V=>FiniteLaw.uniform C)).probability
      (fun σ=>t≤|monochromaticWeightedSum (hypergraphRootRemainder R v) (fun _=>1) c σ-
        (Fintype.card (HypergraphEdgesAt R v):ℝ)/(Fintype.card C:ℝ)^(k-1)|)≤
      2*Real.exp (-2*t^2/(D*(k-1)*Fintype.card (HypergraphEdgesAt R v))) := by
  have hload (u : V) : hypergraphWeightedDegree (hypergraphRootRemainder R v) (fun _=>1) u≤D := by
    rw [hypergraphRootRemainder_degree]
    by_cases huv : u=v
    · simpa only [if_pos huv] using hD
    · simpa only [if_neg huv] using hcodegree u huv
  have hh := monochromaticWeightedSum_tail (hypergraphRootRemainder R v) (fun _=>1)
    (by intro e;norm_num) (k-1) (by omega) (hypergraphRootRemainder_card R k hR v)
    (by simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] using Nat.cast_pos.mpr hv)
    D hload c t ht
  have hkcast : ((k-1:ℕ):ℝ)=(k:ℝ)-1 := by rw [Nat.cast_sub (by omega),Nat.cast_one]
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,hkcast] using hh

theorem hypergraphRootColor_present (R : E → Finset V) (v : V) (c : C) (σ : V → C)
    (hv : σ v=c) :
    monochromaticWeightedSum (hypergraphRootRemainder R v) (fun _=>1) c σ=
      ∑ e,if v∈R e ∧ (∀ u∈R e,σ u=c) then (1:ℝ) else 0 := by
  unfold monochromaticWeightedSum hypergraphRootRemainder
  simp only [one_mul,patternValue_indicator]
  have he := Finset.sum_subtype (p:=fun e=>v∈R e) (F:=inferInstance) (Finset.univ.filter (fun e=>v∈R e))
    (fun e=>by simp) (fun e : E=>if ∀ u∈(R e).erase v,σ u=c then (1:ℝ) else 0)
  trans (∑ e∈Finset.univ.filter (fun e=>v∈R e),if ∀ u∈(R e).erase v,σ u=c then (1:ℝ) else 0)
  · convert he.symm using 1
    all_goals
      apply Finset.sum_congr
      · ext e;simp
      · intro e _;split_ifs <;> rfl
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e _
  have hp : (∀ u∈(R e).erase v,σ u=c) ↔ (∀ u∈R e,σ u=c) := by
    constructor
    · intro h u hu
      by_cases huv : u=v
      · simpa only [huv] using hv
      · exact h u (Finset.mem_erase.mpr ⟨huv,hu⟩)
    · intro h u hu;exact h u (Finset.mem_erase.mp hu).2
  simp only [hp,ite_and]

end Oberwolfach
