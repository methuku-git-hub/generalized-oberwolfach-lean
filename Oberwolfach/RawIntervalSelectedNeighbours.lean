module

public import Oberwolfach.RawIntervalSelectedPatterns
public import Oberwolfach.RawIntervalNeighbourCounts

@[expose] public section

/-! Common neighbourhoods of fixed distinct hub sets, allowing each hub
to request an ordinary or interval colour. The label domain is fixed before
sampling; a vertex used to define it may be outside that domain. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [DecidableEq V] [DecidableEq U]

def rawIntervalSelectedNeighbourCount (π : Equiv.Perm V) (d : ℕ)
    (σ : RawIntervalFamilyOutcome V U Γ Color) (j : U→Γ⊕Color) (A : Finset V) (J : Finset U) : ℝ :=
  ∑ v∈A,if ∀ u∈J,rawIntervalFamilyState π d σ (v,u)=some (j u) then 1 else 0

theorem rawIntervalSelectedNeighbourCount_pattern (π : Equiv.Perm V) (d : ℕ)
    (σ : RawIntervalFamilyOutcome V U Γ Color) (j : U→Γ⊕Color) (A : Finset V) (J : Finset U) :
    rawIntervalSelectedNeighbourCount π d σ j A J=
      supportedPatternSum (fun v=>{v}×ˢJ) (fun v=>if v∈A then 1 else 0)
        (fun _ a=>some (j a.2)) (rawIntervalFamilyState π d) σ := by
  unfold supportedPatternSum
  simp_rw [patternValue_indicator,ite_mul,one_mul,zero_mul]
  simp only [Finset.sum_ite_mem,Finset.univ_inter]
  unfold rawIntervalSelectedNeighbourCount
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

variable (π : Equiv.Perm V) (d : ℕ) (hd : 2≤d)
    (q : U→Γ→ℝ) (hq : ∀ u g,0≤q u g) (hQ : ∀ u,∑ g,q u g≤1/8)
    (s : U→Color→ℝ) (hs : ∀ u j,0≤s u j)
    (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
local notation "μfamily" => rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS

theorem rawIntervalSelectedNeighbourCount_expectation
    (hnoshort : ∀ x k,0<k → k<2*d+1 → (π^k) x≠x)
    (j : U→Γ⊕Color) (A : Finset V) (J : Finset U) :
    (FiniteLaw.pi μfamily).expectation (fun σ=>rawIntervalSelectedNeighbourCount π d σ j A J)=
      (A.card:ℝ)*∏ u∈J,Sum.elim (q u) (s u) (j u) := by
  simp_rw [rawIntervalSelectedNeighbourCount_pattern]
  rw [rawIntervalFamily_selected_sum_expectation π d hd q hq hQ s hs hS hnoshort
    (fun v=>{v}×ˢJ) (fun v=>if v∈A then 1 else 0) (fun _ a=>j a.2) (by
      intro v a ha b hb hab
      left
      have ha' := Finset.mem_product.mp ha
      have hb' := Finset.mem_product.mp hb
      intro he
      exact hab (Prod.ext ((Finset.mem_singleton.mp ha'.1).trans (Finset.mem_singleton.mp hb'.1).symm) he))]
  simp only [Finset.prod_product,Finset.prod_singleton,ite_mul,one_mul,zero_mul,
    Finset.sum_ite_mem,Finset.univ_inter,Finset.sum_const,nsmul_eq_mul]

theorem rawIntervalSelectedNeighbourCount_tail
    (hn : 0<Fintype.card V) (j : U→Γ⊕Color) (A : Finset V) (J : Finset U) (hJ : J.Nonempty)
    (t : ℝ) (ht : 0<t) :
    (FiniteLaw.pi μfamily).probability (fun σ=>t≤
      |rawIntervalSelectedNeighbourCount π d σ j A J-
        (FiniteLaw.pi μfamily).expectation (fun τ=>rawIntervalSelectedNeighbourCount π d τ j A J)|)≤
      2*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*((J.card:ℝ)*Fintype.card V))) := by
  have hn0 : (0:ℝ)<Fintype.card V := by exact_mod_cast hn
  have hJ0 : (0:ℝ)<J.card := by exact_mod_cast hJ.card_pos
  simp_rw [rawIntervalSelectedNeighbourCount_pattern]
  apply supportedPatternSum_tail μfamily (fun v=>{v}×ˢJ) (fun v=>if v∈A then 1 else 0)
    (by intro v;split_ifs <;> norm_num) (fun _ a=>some (j a.2))
    (rawIntervalFamilyCoordinates π d) (rawIntervalFamilyState π d)
    (fun a σ τ ha=>rawIntervalFamilyState_supported π d σ τ a ha)
    (4*(d:ℝ)+3) ((J.card:ℝ)*Fintype.card V) (by positivity) (by positivity)
    (by intro a;exact_mod_cast rawIntervalFamilyCoordinates_card π d a)
    (by intro e;exact_mod_cast rawIntervalFamilyCoordinates_reverse_card π d e)
    (neighbour_pattern_square_sum A J) t ht

theorem rawIntervalSelectedNeighbourCount_common_event
    (hnoshort : ∀ x k,0<k → k<2*d+1 → (π^k) x≠x)
    (hn : 0<Fintype.card V) {I : Type} [Fintype I]
    (j : I→U→Γ⊕Color) (A : I→Finset V) (J : I→Finset U)
    (hJ : ∀ i,(J i).Nonempty) (k : ℕ) (hk : 0<k) (hsize : ∀ i,(J i).card≤k)
    (t : ℝ) (ht : 0<t) :
    1-(Fintype.card I:ℝ)*(2*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*((k:ℝ)*Fintype.card V))))≤
      (FiniteLaw.pi μfamily).probability (fun σ=>∀ i,
        |rawIntervalSelectedNeighbourCount π d σ (j i) (A i) (J i)-
          (A i).card*∏ u∈J i,Sum.elim (q u) (s u) (j i u)|<t) := by
  have hn0 : (0:ℝ)<Fintype.card V := by exact_mod_cast hn
  have hk0 : (0:ℝ)<k := by exact_mod_cast hk
  have htail (i : I) :
      (FiniteLaw.pi μfamily).probability (fun σ=>t≤
        |rawIntervalSelectedNeighbourCount π d σ (j i) (A i) (J i)-
          (A i).card*∏ u∈J i,Sum.elim (q u) (s u) (j i u)|)≤
        2*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*((k:ℝ)*Fintype.card V))) := by
    have hh := rawIntervalSelectedNeighbourCount_tail π d hd q hq hQ s hs hS hn (j i) (A i) (J i) (hJ i) t ht
    rw [rawIntervalSelectedNeighbourCount_expectation π d hd q hq hQ s hs hS hnoshort] at hh
    apply hh.trans
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Real.exp_le_exp.mpr
    have hJi : (0:ℝ)<(J i).card := by exact_mod_cast (hJ i).card_pos
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    apply mul_le_mul_of_nonpos_left _ (by nlinarith only [sq_nonneg t])
    gcongr
    exact_mod_cast hsize i
  have hh := finiteLaw_common_event_lower (FiniteLaw.pi μfamily) Finset.univ
    (fun i σ=>t≤|rawIntervalSelectedNeighbourCount π d σ (j i) (A i) (J i)-
      (A i).card*∏ u∈J i,Sum.elim (q u) (s u) (j i u)|)
    (fun _=>2*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*((k:ℝ)*Fintype.card V))))
    (fun i _=>htail i)
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Finset.mem_univ,true_implies,not_le] using hh

end Oberwolfach
