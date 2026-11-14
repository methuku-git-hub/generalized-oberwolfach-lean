module

public import Oberwolfach.RawIntervalNeighbourCounts
public import Oberwolfach.AsymptoticMargins

@[expose] public section

/-! Cut counts in the original interval experiment. A quadratic deviation
allows a simultaneous estimate for every pair of vertex subsets; the local
coordinate dependencies are retained throughout. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [DecidableEq V] [DecidableEq U]

def rawIntervalCutCount (π : Equiv.Perm V) (d : ℕ)
    (σ : RawIntervalFamilyOutcome V U Γ Color) (j : Color) (X : Finset V) (Y : Finset U) : ℝ :=
  ∑ v∈X,∑ u∈Y,if rawIntervalFamilyState π d σ (v,u)=some (Sum.inr j) then 1 else 0

theorem rawIntervalCutCount_pattern (π : Equiv.Perm V) (d : ℕ)
    (σ : RawIntervalFamilyOutcome V U Γ Color) (j : Color) (X : Finset V) (Y : Finset U) :
    rawIntervalCutCount π d σ j X Y=
      supportedPatternSum (fun a : V×U=>{a}) (fun a=>if a∈X×ˢY then 1 else 0)
        (fun _ _=>some (Sum.inr j)) (rawIntervalFamilyState π d) σ := by
  unfold supportedPatternSum rawIntervalCutCount
  simp_rw [patternValue_indicator]
  simp only [Finset.mem_singleton,forall_eq,ite_mul,one_mul,zero_mul,Finset.sum_ite_mem,Finset.univ_inter,
    Finset.sum_product]

theorem singleton_pattern_square_sum (X : Finset V) (Y : Finset U) :
    (∑ a : V×U,(∑ b : V×U,if a∈({b}:Finset (V×U)) then (if b∈X×ˢY then (1:ℝ) else 0) else 0)^2)≤
      (Fintype.card V:ℝ)*Fintype.card U := by
  have he (a : V×U) :
      (∑ b : V×U,if a∈({b}:Finset (V×U)) then (if b∈X×ˢY then (1:ℝ) else 0) else 0)=
        if a∈X×ˢY then 1 else 0 := by simp
  simp_rw [he]
  calc
    _ ≤ ∑ _a : V×U,(1:ℝ) := by apply Finset.sum_le_sum;intro a _;split_ifs <;> norm_num
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,Fintype.card_prod,Nat.cast_mul]

variable (π : Equiv.Perm V) (d : ℕ) (hd : 2≤d)
    (q : U → Γ → ℝ) (hq : ∀ u g,0≤q u g) (hQ : ∀ u,∑ g,q u g≤1/8)
    (s : U → Color → ℝ) (hs : ∀ u j,0≤s u j)
    (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
local notation "μfamily" => rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS

theorem rawIntervalCutCount_expectation
    (hnoshort : ∀ x k,0<k → k<2*d+1 → (π^k) x≠x)
    (j : Color) (X : Finset V) (Y : Finset U) :
    (FiniteLaw.pi μfamily).expectation (fun σ=>rawIntervalCutCount π d σ j X Y)=
      (X.card:ℝ)*∑ u∈Y,s u j := by
  simp_rw [rawIntervalCutCount_pattern]
  rw [supportedPatternSum_expectation μfamily _ _ _ (rawIntervalFamilyCoordinates π d)
    (rawIntervalFamilyState π d) (fun a σ τ ha=>rawIntervalFamilyState_supported π d σ τ a ha)
    (by intro i a ha b hb hab;simp only [Finset.mem_singleton] at ha hb;exact (hab (ha.trans hb.symm)).elim)]
  simp only [Finset.prod_singleton,rawIntervalFamily_label_probability π d hd q hq hQ s hs hS hnoshort,
    ite_mul,one_mul,zero_mul,Finset.sum_ite_mem,Finset.univ_inter,Finset.sum_product,
    Finset.sum_const,nsmul_eq_mul]

theorem rawIntervalCutCount_tail
    (hn : 0<Fintype.card V) (hm : 0<Fintype.card U) (j : Color) (X : Finset V) (Y : Finset U)
    (t : ℝ) (ht : 0<t) :
    (FiniteLaw.pi μfamily).probability (fun σ=>t≤
      |rawIntervalCutCount π d σ j X Y-
        (FiniteLaw.pi μfamily).expectation (fun τ=>rawIntervalCutCount π d τ j X Y)|)≤
      2*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*((Fintype.card V:ℝ)*Fintype.card U))) := by
  have hn0 : (0:ℝ)<Fintype.card V := by exact_mod_cast hn
  have hm0 : (0:ℝ)<Fintype.card U := by exact_mod_cast hm
  simp_rw [rawIntervalCutCount_pattern]
  apply supportedPatternSum_tail μfamily (fun a : V×U=>{a}) (fun a=>if a∈X×ˢY then 1 else 0)
    (by intro a;split_ifs <;> norm_num) (fun _ _=>some (Sum.inr j))
    (rawIntervalFamilyCoordinates π d) (rawIntervalFamilyState π d)
    (fun a σ τ ha=>rawIntervalFamilyState_supported π d σ τ a ha)
    (4*(d:ℝ)+3) ((Fintype.card V:ℝ)*Fintype.card U) (by positivity) (by positivity)
    (by intro a;exact_mod_cast rawIntervalFamilyCoordinates_card π d a)
    (by intro e;exact_mod_cast rawIntervalFamilyCoordinates_reverse_card π d e)
    (singleton_pattern_square_sum X Y) t ht

theorem rawIntervalCutCount_uniform_tail
    (hnoshort : ∀ x k,0<k → k<2*d+1 → (π^k) x≠x)
    (hn : 0<Fintype.card V) (hm : 0<Fintype.card U) (hmhi : Fintype.card U≤Fintype.card V)
    (j : Color) (pH : ℝ) (hj : ∀ u,s u j=pH) (X : Finset V) (Y : Finset U)
    (t : ℝ) (ht : 0<t) :
    (FiniteLaw.pi μfamily).probability (fun σ=>t≤
      |rawIntervalCutCount π d σ j X Y-pH*X.card*Y.card|)≤
      2*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*(Fintype.card V:ℝ)^2)) := by
  have hn0 : (0:ℝ)<Fintype.card V := by exact_mod_cast hn
  have hm0 : (0:ℝ)<Fintype.card U := by exact_mod_cast hm
  have hh := rawIntervalCutCount_tail π d hd q hq hQ s hs hS hn hm j X Y t ht
  rw [rawIntervalCutCount_expectation π d hd q hq hQ s hs hS hnoshort] at hh
  simp only [hj,Finset.sum_const,nsmul_eq_mul] at hh
  have hmean : (X.card:ℝ)*((Y.card:ℝ)*pH)=pH*X.card*Y.card := by ring
  rw [hmean] at hh
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.exp_le_exp.mpr
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have hsize : (Fintype.card U:ℝ)≤Fintype.card V := by exact_mod_cast hmhi
  have hden : (4*(d:ℝ)+3)^2*((Fintype.card V:ℝ)*Fintype.card U)≤
      (4*(d:ℝ)+3)^2*(Fintype.card V:ℝ)^2 := by
    have hh := mul_le_mul_of_nonneg_left hsize (by positivity : (0:ℝ)≤(4*(d:ℝ)+3)^2*Fintype.card V)
    nlinarith only [hh]
  exact mul_le_mul_of_nonpos_left hden (by nlinarith only [sq_nonneg t])

theorem bipartite_cut_domain_card (hmhi : Fintype.card U≤Fintype.card V) :
    Fintype.card (Finset V×Finset U)≤4^Fintype.card V := by
  simp only [Fintype.card_prod,Fintype.card_finset]
  calc
    _ ≤ 2^Fintype.card V*2^Fintype.card V := Nat.mul_le_mul_left _ (pow_le_pow_right₀ (by norm_num : (1:ℕ)≤2) hmhi)
    _ = _ := by rw [← mul_pow];norm_num

theorem rawIntervalCutCount_all_cuts
    (hnoshort : ∀ x k,0<k → k<2*d+1 → (π^k) x≠x)
    (hn : 0<Fintype.card V) (hm : 0<Fintype.card U) (hmhi : Fintype.card U≤Fintype.card V)
    (j : Color) (pH : ℝ) (hj : ∀ u,s u j=pH) (t : ℝ) (ht : 0<t) :
    1-(4:ℝ)^Fintype.card V*(2*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*(Fintype.card V:ℝ)^2)))≤
      (FiniteLaw.pi μfamily).probability (fun σ=>∀ X Y,
        |rawIntervalCutCount π d σ j X Y-pH*X.card*Y.card|<t) := by
  let b := 2*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*(Fintype.card V:ℝ)^2))
  have hh := finiteLaw_common_event_lower (FiniteLaw.pi μfamily) (Finset.univ : Finset (Finset V×Finset U))
    (fun a σ=>t≤|rawIntervalCutCount π d σ j a.1 a.2-pH*a.1.card*a.2.card|) (fun _=>b)
    (fun a _=>rawIntervalCutCount_uniform_tail π d hd q hq hQ s hs hS hnoshort hn hm hmhi j pH hj a.1 a.2 t ht)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Finset.mem_univ,true_implies,Prod.forall,not_le] at hh
  have hcard : (Fintype.card (Finset V×Finset U):ℝ)≤(4:ℝ)^Fintype.card V := by
    exact_mod_cast bipartite_cut_domain_card (V:=V) (U:=U) hmhi
  exact (sub_le_sub_left (mul_le_mul_of_nonneg_right hcard (by positivity)) 1).trans hh

theorem rawIntervalCutCount_quadratic_event (d : ℕ) (hd : 2≤d)
    (ε : ℝ) (hε : 0<ε) (q₀ : ℕ) :
    ∃ N : ℕ,∀ (V U Γ Color : Type)
      [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [DecidableEq V] [DecidableEq U],
      N≤Fintype.card V → 0<Fintype.card U → Fintype.card U≤Fintype.card V →
    ∀ (π : Equiv.Perm V)
      (q : U → Γ → ℝ) (hq : ∀ u g,0≤q u g) (hQ : ∀ u,∑ g,q u g≤1/8)
      (s : U → Color → ℝ) (hs : ∀ u j,0≤s u j)
      (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
      (j : Color),(∀ x k,0<k → k<2*d+1 → (π^k) x≠x) →
    ∀ pH : ℝ,(∀ u,s u j=pH) →
    1-1/(Fintype.card V:ℝ)^q₀≤
      (FiniteLaw.pi (rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS)).probability
        (fun σ=>∀ X Y,|rawIntervalCutCount π d σ j X Y-pH*X.card*Y.card|<ε*(Fintype.card V:ℝ)^2) := by
  obtain ⟨N,hN⟩ := eventually_allCuts_failure_small (C:=2) (c:=2*ε^2/(4*(d:ℝ)+3)^2)
    (by norm_num) (by positivity) q₀
  refine ⟨max N 1,?_⟩
  intro V U Γ Color _ _ _ _ _ _ hnN hm hmhi π q hq hQ s hs hS j hnoshort pH hj
  let n := Fintype.card V
  have hn : 0<n := by dsimp [n];omega
  have hn0 : (0:ℝ)<n := by exact_mod_cast hn
  have hh := rawIntervalCutCount_all_cuts π d hd q hq hQ s hs hS hnoshort hn hm hmhi
    j pH hj (ε*(n:ℝ)^2) (by positivity)
  have hex : -2*(ε*(n:ℝ)^2)^2/((4*(d:ℝ)+3)^2*(n:ℝ)^2)=
      -(2*ε^2/(4*(d:ℝ)+3)^2)*(n:ℝ)^2 := by field_simp <;> ring
  change 1-(4:ℝ)^n*(2*Real.exp (-2*(ε*(n:ℝ)^2)^2/((4*(d:ℝ)+3)^2*(n:ℝ)^2)))≤_ at hh
  rw [hex] at hh
  have htail := hN n (by dsimp [n] at *;omega)
  have heq : (4:ℝ)^n*(2*Real.exp (-(2*ε^2/(4*(d:ℝ)+3)^2)*(n:ℝ)^2))=
      2*(4:ℝ)^n*Real.exp (-(2*ε^2/(4*(d:ℝ)+3)^2)*(n:ℝ)^2) := by ring
  rw [heq] at hh
  exact (sub_le_sub_left htail 1).trans hh

end Oberwolfach
