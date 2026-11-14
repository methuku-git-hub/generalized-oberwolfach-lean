module

public import Oberwolfach.RawIntervalSelectedPatterns
public import Oberwolfach.RawIntervalLabelCounts

@[expose] public section

/-! Compatible hubs for a fixed separated label set with mixed ordinary
and interval-colour requests. The same raw variables and exact marginals
are used for every request; the labelled pattern is fixed before sampling. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [DecidableEq V] [DecidableEq U]

def rawIntervalSelectedLabelCount (π : Equiv.Perm V) (d : ℕ)
    (σ : RawIntervalFamilyOutcome V U Γ Color) (j : V→Γ⊕Color) (T : Finset V) : ℝ :=
  ∑ u : U,if ∀ v∈T,rawIntervalFamilyState π d σ (v,u)=some (j v) then 1 else 0

theorem rawIntervalSelectedLabelCount_pattern (π : Equiv.Perm V) (d : ℕ)
    (σ : RawIntervalFamilyOutcome V U Γ Color) (j : V→Γ⊕Color) (T : Finset V) :
    rawIntervalSelectedLabelCount π d σ j T=
      supportedPatternSum (fun u : U=>T×ˢ{u}) (fun _=>1)
        (fun _ a=>some (j a.1)) (rawIntervalFamilyState π d) σ := by
  unfold supportedPatternSum rawIntervalSelectedLabelCount
  simp_rw [patternValue_indicator,one_mul]
  apply Finset.sum_congr rfl
  intro u _
  congr 1
  apply propext
  constructor
  · intro h a ha
    obtain ⟨hv,hu⟩ := Finset.mem_product.mp ha
    have heu := Finset.mem_singleton.mp hu
    simpa only [← heu] using h a.1 hv
  · intro h v hv
    exact h (v,u) (Finset.mem_product.mpr ⟨hv,Finset.mem_singleton_self u⟩)


variable (π : Equiv.Perm V) (d : ℕ) (hd : 2≤d)
    (q : U → Γ → ℝ) (hq : ∀ u g,0≤q u g) (hQ : ∀ u,∑ g,q u g≤1/8)
    (s : U → Color → ℝ) (hs : ∀ u j,0≤s u j)
    (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
local notation "μfamily" => rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS

theorem rawIntervalSelectedLabelCount_expectation
    (hnoshort : ∀ x k,0<k → k<2*d+1 → (π^k) x≠x)
    (j : V→Γ⊕Color) (T : Finset V)
    (hsep : ∀ x∈T,∀ y∈T,x≠y → ¬PermutationClose π (3*d) x y) :
    (FiniteLaw.pi μfamily).expectation (fun σ=>rawIntervalSelectedLabelCount π d σ j T)=
      ∑ u : U,∏ v∈T,Sum.elim (q u) (s u) (j v) := by
  unfold FiniteLaw.expectation rawIntervalSelectedLabelCount
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  have hh := rawIntervalFamily_selected_patterns_probability π d hd q hq hQ s hs hS hnoshort
    (T×ˢ{u}) (fun a=>j a.1) (by
      intro a ha b hb hab
      right
      obtain ⟨ha,hu⟩ := Finset.mem_product.mp ha
      obtain ⟨hb,hv⟩ := Finset.mem_product.mp hb
      exact hsep a.1 ha b.1 hb (fun he=>hab (Prod.ext he ((Finset.mem_singleton.mp hu).trans (Finset.mem_singleton.mp hv).symm))))
  have he (σ : RawIntervalFamilyOutcome V U Γ Color) :
      (∀ a∈T×ˢ{u},rawIntervalFamilyState π d σ a=some (j a.1)) ↔
        (∀ v∈T,rawIntervalFamilyState π d σ (v,u)=some (j v)) := by
    constructor
    · intro h v hv;exact h (v,u) (Finset.mem_product.mpr ⟨hv,Finset.mem_singleton_self u⟩)
    · intro h a ha
      obtain ⟨hv,hu⟩ := Finset.mem_product.mp ha
      have heu := Finset.mem_singleton.mp hu
      simpa only [← heu] using h a.1 hv
  simp only [he,Finset.prod_product,Finset.prod_singleton,Finset.prod_const] at hh
  convert hh using 1
  unfold FiniteLaw.probability
  apply Finset.sum_congr rfl
  intro σ _
  split_ifs <;> simp


theorem rawIntervalSelectedLabelCount_tail
    (hm : 0<Fintype.card U) (j : V→Γ⊕Color) (T : Finset V) (hT : T.Nonempty)
    (t : ℝ) (ht : 0<t) :
    (FiniteLaw.pi μfamily).probability (fun σ=>t≤
      |rawIntervalSelectedLabelCount π d σ j T-
        (FiniteLaw.pi μfamily).expectation (fun τ=>rawIntervalSelectedLabelCount π d τ j T)|)≤
      2*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*((T.card:ℝ)*Fintype.card U))) := by
  have hm0 : (0:ℝ)<Fintype.card U := by exact_mod_cast hm
  have hT0 : (0:ℝ)<T.card := by exact_mod_cast hT.card_pos
  simp_rw [rawIntervalSelectedLabelCount_pattern]
  apply supportedPatternSum_tail μfamily (fun u : U=>T×ˢ{u}) (fun _=>1)
    (by intro u;norm_num) (fun _ a=>some (j a.1))
    (rawIntervalFamilyCoordinates π d) (rawIntervalFamilyState π d)
    (fun a σ τ ha=>rawIntervalFamilyState_supported π d σ τ a ha)
    (4*(d:ℝ)+3) ((T.card:ℝ)*Fintype.card U) (by positivity) (by positivity)
    (by intro a;exact_mod_cast rawIntervalFamilyCoordinates_card π d a)
    (by intro e;exact_mod_cast rawIntervalFamilyCoordinates_reverse_card π d e)
    (label_pattern_square_sum T).le t ht


theorem rawIntervalSelectedLabelCount_common_event
    (hnoshort : ∀ x k,0<k → k<2*d+1 → (π^k) x≠x)
    (hm : 0<Fintype.card U)
    {I : Type} [Fintype I] (j : I→V→Γ⊕Color) (T : I → Finset V)
    (hsep : ∀ i,∀ x∈T i,∀ y∈T i,x≠y → ¬PermutationClose π (3*d) x y)
    (hT : ∀ i,(T i).Nonempty) (k : ℕ) (hk : 0<k) (hsize : ∀ i,(T i).card≤k)
    (t : ℝ) (ht : 0<t) :
    1-(Fintype.card I:ℝ)*(2*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*((k:ℝ)*Fintype.card U))))≤
      (FiniteLaw.pi μfamily).probability (fun σ=>∀ i,
        |rawIntervalSelectedLabelCount π d σ (j i) (T i)-∑ u : U,∏ v∈T i,Sum.elim (q u) (s u) (j i v)|<t) := by
  have hm0 : (0:ℝ)<Fintype.card U := by exact_mod_cast hm
  have hk0 : (0:ℝ)<k := by exact_mod_cast hk
  have htail (i : I) :
      (FiniteLaw.pi μfamily).probability (fun σ=>t≤
        |rawIntervalSelectedLabelCount π d σ (j i) (T i)-∑ u : U,∏ v∈T i,Sum.elim (q u) (s u) (j i v)|)≤
        2*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*((k:ℝ)*Fintype.card U))) := by
    have hh := rawIntervalSelectedLabelCount_tail π d hd q hq hQ s hs hS hm (j i) (T i) (hT i) t ht
    rw [rawIntervalSelectedLabelCount_expectation π d hd q hq hQ s hs hS hnoshort (j i) (T i) (hsep i)] at hh
    apply hh.trans
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Real.exp_le_exp.mpr
    have hTi : (0:ℝ)<(T i).card := by exact_mod_cast (hT i).card_pos
    have hle : (4*(d:ℝ)+3)^2*((T i).card*Fintype.card U)≤
        (4*(d:ℝ)+3)^2*((k:ℝ)*Fintype.card U) := by
      gcongr
      exact_mod_cast hsize i
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    exact mul_le_mul_of_nonpos_left hle (by nlinarith only [sq_nonneg t])
  have hh := finiteLaw_common_event_lower (FiniteLaw.pi μfamily) Finset.univ
    (fun i σ=>t≤|rawIntervalSelectedLabelCount π d σ (j i) (T i)-∑ u : U,∏ v∈T i,Sum.elim (q u) (s u) (j i v)|)
    (fun _=>2*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*((k:ℝ)*Fintype.card U))))
    (fun i _=>htail i)
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Finset.mem_univ,true_implies,not_le] using hh

end Oberwolfach
