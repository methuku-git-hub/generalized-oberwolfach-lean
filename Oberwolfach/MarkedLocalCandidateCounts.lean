module

public import Oberwolfach.MarkedBaseCycleCounts
public import Oberwolfach.MarkedPathParentCounts

@[expose] public section

/-! Uniform greedy counts at an explicitly supplied local scale. All ambient roots
retain their neighbourhood hypotheses, even outside the two supplied classes. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem denseMarkedBase_local_density
    (m b : ℕ) (hm : 0<m) (α θ : ℝ) (hα : 0<α) (hα1 : α≤1) (hθ : 0<θ) :
    ∃ N : ℕ,∀ (V : Type) [Fintype V] [DecidableEq V],∀ a : ℕ,N≤a →
    ∀ (P : SimpleGraph V) (π : Equiv.Perm V) (T₀ TK : Finset V),
      θ*a≤(T₀.card:ℝ) → θ*a≤(TK.card:ℝ) →
      (∀ x : V,(1/2+α/2)*T₀.card≤((P.neighborFinset x∩T₀).card:ℝ)) →
      (∀ x : V,(1/2+α/2)*TK.card≤((P.neighborFinset x∩TK).card:ℝ)) →
    (α*θ/4)^(m+1)*(a:ℝ)^(m+1)≤
      (Fintype.card {f : Fin (m+1)→V // DenseMarkedBase P π b T₀ TK f}:ℝ) := by
  obtain ⟨N,hN⟩ := exists_nat_ge ((((m:ℝ)+1)*(2*(b:ℝ)+1))/(α*θ/4))
  refine ⟨N,?_⟩
  intro V _ _ a hn P π T₀ TK h₀ hK hd₀ hdK
  have hnR : (N:ℝ)≤a := by exact_mod_cast hn
  have hmargin := (div_le_iff₀ (show 0<α*θ/4 by positivity)).mp (hN.trans hnR)
  have hsize := mul_le_mul_of_nonneg_left (le_min h₀ hK) hα.le
  have hbudget : (α*θ/4)*a≤α*min (T₀.card:ℝ) TK.card-
      ((m:ℝ)+1)*(2*(b:ℝ)+1) := by
    have hn0 : (0:ℝ)≤a := Nat.cast_nonneg _
    have hpos : 0≤α*θ*a := by positivity
    nlinarith only [hsize,hmargin,hpos]
  have hh := dense_marked_base_cycle_count P π b m hm T₀ TK α
    ((α*θ/4)*a) hα.le hα1 (by positivity) hbudget hd₀ hdK
  simpa only [mul_pow] using hh

theorem denseRootMarkedPath_local_density
    (r b : ℕ) (hr : 1≤r) (α θ : ℝ) (hα : 0<α) (hα1 : α≤1) (hθ : 0<θ) :
    ∃ N : ℕ,∀ (V : Type) [Fintype V] [DecidableEq V],∀ a : ℕ,N≤a →
    ∀ (P : SimpleGraph V) (π : Equiv.Perm V) (T₀ TK : Finset V),
      θ*a≤(T₀.card:ℝ) → θ*a≤(TK.card:ℝ) →
      (∀ x : V,(1/2+α/2)*T₀.card≤((P.neighborFinset x∩T₀).card:ℝ)) →
      (∀ x : V,(1/2+α/2)*TK.card≤((P.neighborFinset x∩TK.image π).card:ℝ)) →
    ∀ (j : Bool) (v v' : V),
    (α*θ/4)^(r+4)*(a:ℝ)^(r+4)≤
      (Fintype.card {z : Fin (r+4)→V // DenseRootMarkedPath P π b j T₀ TK v v' z}:ℝ) := by
  obtain ⟨N,hN⟩ := exists_nat_ge ((((r:ℝ)+6)*(2*(b:ℝ)+1))/(α*θ/4))
  refine ⟨N,?_⟩
  intro V _ _ a hn P π T₀ TK h₀ hK hd₀ hdK j v v'
  have hnR : (N:ℝ)≤a := by exact_mod_cast hn
  have hmargin := (div_le_iff₀ (show 0<α*θ/4 by positivity)).mp (hN.trans hnR)
  have hsize := mul_le_mul_of_nonneg_left (le_min h₀ hK) hα.le
  have hbudget : (α*θ/4)*a≤α*min (T₀.card:ℝ) TK.card-
      ((r:ℝ)+6)*(2*(b:ℝ)+1) := by
    have hpos : 0≤α*θ*a := by positivity
    nlinarith only [hsize,hmargin,hpos]
  have hh := denseRootMarkedPath_count P π b r hr j T₀ TK v v' α ((α*θ/4)*a)
    hα.le hα1 (by positivity) hbudget hd₀ hdK
  simpa only [mul_pow] using hh


end Oberwolfach
