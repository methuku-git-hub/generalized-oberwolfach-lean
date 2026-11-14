module

public import Oberwolfach.RawIntervalFamily
public import Oberwolfach.SupportedPatternSums

@[expose] public section

/-! Selected ordinary and interval colours in the original common law.
The separation hypotheses refer to actual coordinate supports, including
mixed selections; no independent-pair replacement is made. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [DecidableEq V] [DecidableEq U]

variable (π : Equiv.Perm V) (d : ℕ) (hd : 2≤d)
    (q : U→Γ→ℝ) (hq : ∀ u g,0≤q u g) (hQ : ∀ u,∑ g,q u g≤1/8)
    (s : U→Color→ℝ) (hs : ∀ u j,0≤s u j)
    (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
local notation "μfamily" => rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS

theorem rawIntervalFamily_selected_probability
    (hnoshort : ∀ x k,0<k → k<2*d+1 → (π^k) x≠x) (a : V×U) (j : Γ⊕Color) :
    (FiniteLaw.pi μfamily).probability (fun σ=>rawIntervalFamilyState π d σ a=some j)=
      Sum.elim (q a.2) (s a.2) j := by
  cases j with
  | inl g=>exact rawIntervalFamily_interval_probability π d hd q hq hQ s hs hS hnoshort a g
  | inr j=>exact rawIntervalFamily_label_probability π d hd q hq hQ s hs hS hnoshort a j

theorem rawIntervalFamily_selected_patterns_probability
    (hnoshort : ∀ x k,0<k → k<2*d+1 → (π^k) x≠x)
    (T : Finset (V×U)) (j : V×U→Γ⊕Color)
    (hsep : ∀ a∈T,∀ b∈T,a≠b → a.2≠b.2 ∨ ¬PermutationClose π (3*d) a.1 b.1) :
    (FiniteLaw.pi μfamily).probability (fun σ=>∀ a∈T,rawIntervalFamilyState π d σ a=some (j a))=
      ∏ a∈T,Sum.elim (q a.2) (s a.2) (j a) := by
  have hh := finiteLaw_disjoint_supported_family μfamily (rawIntervalFamilyCoordinates π d)
    (fun a σ=>rawIntervalFamilyState π d σ a=some (j a))
    (by intro a σ τ ha;rw [rawIntervalFamilyState_supported π d σ τ a ha]) T
    (fun a ha b hb hab=>rawIntervalFamilyCoordinates_disjoint π d a b (hsep a ha b hb hab))
  rw [hh]
  exact Finset.prod_congr rfl (fun a _=>rawIntervalFamily_selected_probability π d hd q hq hQ s hs hS hnoshort a (j a))

theorem rawIntervalFamily_selected_sum_expectation
    (hnoshort : ∀ x k,0<k → k<2*d+1 → (π^k) x≠x)
    {I : Type} [Fintype I] (T : I→Finset (V×U)) (w : I→ℝ) (j : I→V×U→Γ⊕Color)
    (hsep : ∀ i,∀ a∈T i,∀ b∈T i,a≠b → a.2≠b.2 ∨ ¬PermutationClose π (3*d) a.1 b.1) :
    (FiniteLaw.pi μfamily).expectation
      (supportedPatternSum T w (fun i a=>some (j i a)) (rawIntervalFamilyState π d))=
      ∑ i,w i*∏ a∈T i,Sum.elim (q a.2) (s a.2) (j i a) := by
  unfold FiniteLaw.expectation supportedPatternSum
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  have hh := rawIntervalFamily_selected_patterns_probability π d hd q hq hQ s hs hS hnoshort
    (T i) (j i) (hsep i)
  rw [← hh]
  unfold FiniteLaw.probability
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  rw [patternValue_indicator]
  split_ifs <;> ring

theorem rawIntervalFamily_selected_sum_tail
    (hnoshort : ∀ x k,0<k → k<2*d+1 → (π^k) x≠x)
    {I : Type} [Fintype I] (T : I→Finset (V×U)) (w : I→ℝ) (hw : ∀ i,0≤w i)
    (j : I→V×U→Γ⊕Color)
    (hsep : ∀ i,∀ a∈T i,∀ b∈T i,a≠b → a.2≠b.2 ∨ ¬PermutationClose π (3*d) a.1 b.1)
    (Q : ℝ) (hQpos : 0<Q)
    (henergy : (∑ a : V×U,(∑ i,if a∈T i then w i else 0)^2)≤Q)
    (t : ℝ) (ht : 0<t) :
    (FiniteLaw.pi μfamily).probability (fun σ=>t≤
      |supportedPatternSum T w (fun i a=>some (j i a)) (rawIntervalFamilyState π d) σ-
        ∑ i,w i*∏ a∈T i,Sum.elim (q a.2) (s a.2) (j i a)|)≤
      2*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*Q)) := by
  rw [← rawIntervalFamily_selected_sum_expectation π d hd q hq hQ s hs hS hnoshort T w j hsep]
  exact supportedPatternSum_tail μfamily T w hw (fun i a=>some (j i a))
    (rawIntervalFamilyCoordinates π d) (rawIntervalFamilyState π d)
    (fun a σ τ ha=>rawIntervalFamilyState_supported π d σ τ a ha)
    (4*(d:ℝ)+3) Q (by positivity) hQpos
    (by intro a;exact_mod_cast rawIntervalFamilyCoordinates_card π d a)
    (by intro e;exact_mod_cast rawIntervalFamilyCoordinates_reverse_card π d e)
    henergy t ht

end Oberwolfach
