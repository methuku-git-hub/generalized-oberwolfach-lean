module

public import Oberwolfach.RawIntervalFamily
public import Oberwolfach.SupportedPatternSums

@[expose] public section

/-! Counts in fixed label domains and common neighbourhoods of fixed hub
sets, under the original locally dependent interval experiment. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [DecidableEq V] [DecidableEq U]

def rawIntervalNeighbourCount (π : Equiv.Perm V) (d : ℕ)
    (σ : RawIntervalFamilyOutcome V U Γ Color) (j : Color) (A : Finset V) (J : Finset U) : ℝ :=
  ∑ v∈A,if ∀ u∈J,rawIntervalFamilyState π d σ (v,u)=some (Sum.inr j) then 1 else 0

theorem rawIntervalNeighbourCount_pattern (π : Equiv.Perm V) (d : ℕ)
    (σ : RawIntervalFamilyOutcome V U Γ Color) (j : Color) (A : Finset V) (J : Finset U) :
    rawIntervalNeighbourCount π d σ j A J=
      supportedPatternSum (fun v=>{v}×ˢJ) (fun v=>if v∈A then 1 else 0)
        (fun _ _=>some (Sum.inr j)) (rawIntervalFamilyState π d) σ := by
  unfold supportedPatternSum
  simp_rw [patternValue_indicator,ite_mul,one_mul,zero_mul]
  simp only [Finset.sum_ite_mem,Finset.univ_inter]
  unfold rawIntervalNeighbourCount
  apply Finset.sum_congr rfl
  intro v _
  congr 1
  simp only [Finset.mem_product,Finset.mem_singleton]
  apply propext
  constructor
  · intro h a ha
    rcases a with ⟨x,u⟩
    rcases ha with ⟨rfl,hu⟩
    exact h u hu
  · intro h u hu
    exact h (v,u) ⟨rfl,hu⟩

theorem neighbour_pattern_resource_weight (A : Finset V) (J : Finset U) (a : V×U) :
    (∑ v,if a∈{v}×ˢJ then (if v∈A then (1:ℝ) else 0) else 0)=
      if a.1∈A ∧ a.2∈J then 1 else 0 := by
  simp only [Finset.mem_product,Finset.mem_singleton]
  by_cases hu : a.2∈J
  · simp [hu]
  · simp [hu]

theorem neighbour_pattern_square_sum (A : Finset V) (J : Finset U) :
    (∑ a : V×U,(∑ v,if a∈{v}×ˢJ then (if v∈A then (1:ℝ) else 0) else 0)^2)≤
      (J.card:ℝ)*Fintype.card V := by
  simp_rw [neighbour_pattern_resource_weight]
  rw [Fintype.sum_prod_type]
  simp only [ite_and,ite_pow,one_pow,zero_pow (by decide : 2≠0)]
  simp only [Finset.sum_ite_mem,Finset.sum_const_zero,Finset.univ_inter,
    Finset.sum_ite_irrel,Finset.sum_const,nsmul_eq_mul,mul_one]
  have hA : (A.card:ℝ)≤Fintype.card V := by exact_mod_cast Finset.card_le_univ A
  nlinarith only [mul_le_mul_of_nonneg_left hA (Nat.cast_nonneg (α:=ℝ) J.card)]

variable (π : Equiv.Perm V) (d : ℕ) (hd : 2≤d)
    (q : U → Γ → ℝ) (hq : ∀ u g,0≤q u g) (hQ : ∀ u,∑ g,q u g≤1/8)
    (s : U → Color → ℝ) (hs : ∀ u j,0≤s u j)
    (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
local notation "μfamily" => rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS

theorem rawIntervalNeighbourCount_expectation
    (hnoshort : ∀ x k,0<k → k<2*d+1 → (π^k) x≠x)
    (j : Color) (A : Finset V) (J : Finset U) :
    (FiniteLaw.pi μfamily).expectation (fun σ=>rawIntervalNeighbourCount π d σ j A J)=
      (A.card:ℝ)*∏ u∈J,s u j := by
  unfold FiniteLaw.expectation rawIntervalNeighbourCount
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  have he (v : V) :
      (FiniteLaw.pi μfamily).probability (fun σ=>∀ u∈J,rawIntervalFamilyState π d σ (v,u)=some (Sum.inr j))=
        ∏ u∈J,s u j := by
    have hh := rawIntervalFamily_labels_probability π d hd q hq hQ s hs hS hnoshort
      ({v}×ˢJ) (fun _=>j) (by
        intro a ha b hb hab
        left
        have ha' := Finset.mem_product.mp ha
        have hb' := Finset.mem_product.mp hb
        intro he
        exact hab (Prod.ext ((Finset.mem_singleton.mp ha'.1).trans (Finset.mem_singleton.mp hb'.1).symm) he))
    have hforall (σ : RawIntervalFamilyOutcome V U Γ Color) :
        (∀ a∈{v}×ˢJ,rawIntervalFamilyState π d σ a=some (Sum.inr j)) ↔
          (∀ u∈J,rawIntervalFamilyState π d σ (v,u)=some (Sum.inr j)) := by
      constructor
      · intro h u hu
        exact h (v,u) (by simp only [Finset.mem_product,Finset.mem_singleton,true_and];exact hu)
      · intro h a ha
        rcases a with ⟨x,u⟩
        obtain ⟨hx,hu⟩ := Finset.mem_product.mp ha
        have hx' : x=v := Finset.mem_singleton.mp hx
        subst x
        exact h u hu
    simpa only [hforall,Finset.prod_product,Finset.prod_singleton] using hh

  calc
    _ = ∑ v∈A,(FiniteLaw.pi μfamily).probability (fun σ=>∀ u∈J,rawIntervalFamilyState π d σ (v,u)=some (Sum.inr j)) := by
      apply Finset.sum_congr rfl
      intro v _
      unfold FiniteLaw.probability
      apply Finset.sum_congr rfl
      intro σ _
      split_ifs <;> simp
    _ = _ := by simp_rw [he];simp

theorem rawIntervalNeighbourCount_tail
    (hn : 0<Fintype.card V) (j : Color) (A : Finset V) (J : Finset U) (hJ : J.Nonempty)
    (t : ℝ) (ht : 0<t) :
    (FiniteLaw.pi μfamily).probability (fun σ=>t≤
      |rawIntervalNeighbourCount π d σ j A J-
        (FiniteLaw.pi μfamily).expectation (fun τ=>rawIntervalNeighbourCount π d τ j A J)|)≤
      2*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*((J.card:ℝ)*Fintype.card V))) := by
  have hn0 : (0:ℝ)<Fintype.card V := by exact_mod_cast hn
  have hJ0 : (0:ℝ)<J.card := by exact_mod_cast hJ.card_pos
  simp_rw [rawIntervalNeighbourCount_pattern]
  apply supportedPatternSum_tail μfamily (fun v=>{v}×ˢJ) (fun v=>if v∈A then 1 else 0)
    (by intro v;split_ifs <;> norm_num) (fun _ _=>some (Sum.inr j))
    (rawIntervalFamilyCoordinates π d) (rawIntervalFamilyState π d)
    (fun a σ τ ha=>rawIntervalFamilyState_supported π d σ τ a ha)
    (4*(d:ℝ)+3) ((J.card:ℝ)*Fintype.card V) (by positivity) (by positivity)
    (by intro a;exact_mod_cast rawIntervalFamilyCoordinates_card π d a)
    (by intro e;exact_mod_cast rawIntervalFamilyCoordinates_reverse_card π d e)
    (neighbour_pattern_square_sum A J) t ht


theorem rawIntervalNeighbourCount_common_event
    (hnoshort : ∀ x k,0<k → k<2*d+1 → (π^k) x≠x)
    (hn : 0<Fintype.card V) (j : Color)
    {I : Type} [Fintype I] (A : I → Finset V) (J : I → Finset U)
    (hJ : ∀ i,(J i).Nonempty) (k : ℕ) (hk : 0<k) (hsize : ∀ i,(J i).card≤k)
    (t : ℝ) (ht : 0<t) :
    1-(Fintype.card I:ℝ)*(2*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*((k:ℝ)*Fintype.card V))))≤
      (FiniteLaw.pi μfamily).probability (fun σ=>∀ i,
        |rawIntervalNeighbourCount π d σ j (A i) (J i)-(A i).card*∏ u∈J i,s u j|<t) := by
  have hn0 : (0:ℝ)<Fintype.card V := by exact_mod_cast hn
  have hk0 : (0:ℝ)<k := by exact_mod_cast hk
  have htail (i : I) :
      (FiniteLaw.pi μfamily).probability (fun σ=>t≤
        |rawIntervalNeighbourCount π d σ j (A i) (J i)-(A i).card*∏ u∈J i,s u j|)≤
        2*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*((k:ℝ)*Fintype.card V))) := by
    have hh := rawIntervalNeighbourCount_tail π d hd q hq hQ s hs hS hn j (A i) (J i) (hJ i) t ht
    rw [rawIntervalNeighbourCount_expectation π d hd q hq hQ s hs hS hnoshort] at hh
    apply hh.trans
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Real.exp_le_exp.mpr
    have hJi : (0:ℝ)<(J i).card := by exact_mod_cast (hJ i).card_pos
    have hle : (4*(d:ℝ)+3)^2*((J i).card*Fintype.card V)≤
        (4*(d:ℝ)+3)^2*((k:ℝ)*Fintype.card V) := by
      gcongr
      exact_mod_cast hsize i
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    exact mul_le_mul_of_nonpos_left hle (by nlinarith only [sq_nonneg t])
  have hh := finiteLaw_common_event_lower (FiniteLaw.pi μfamily) Finset.univ
    (fun i σ=>t≤|rawIntervalNeighbourCount π d σ j (A i) (J i)-(A i).card*∏ u∈J i,s u j|)
    (fun _=>2*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*((k:ℝ)*Fintype.card V))))
    (fun i _=>htail i)
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Finset.mem_univ,true_implies,not_le] using hh

end Oberwolfach
