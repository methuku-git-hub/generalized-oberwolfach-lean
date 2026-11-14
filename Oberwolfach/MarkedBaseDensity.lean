module

public import Oberwolfach.MarkedBaseCycleCounts

@[expose] public section

/-! A uniform deterministic order threshold for the actual greedy base
cycle count. The two classes are supplied by the spoke exposure. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem denseMarkedBase_uniform_density
    (m b : ℕ) (hm : 0<m) (α θ : ℝ) (hα : 0<α) (hα1 : α≤1) (hθ : 0<θ) :
    ∃ N : ℕ,∀ (V : Type) [Fintype V] [DecidableEq V],N≤Fintype.card V →
    ∀ (P : SimpleGraph V) (π : Equiv.Perm V) (T₀ TK : Finset V),
      θ*Fintype.card V≤(T₀.card:ℝ) → θ*Fintype.card V≤(TK.card:ℝ) →
      (∀ x : V,(1/2+α/2)*T₀.card≤((P.neighborFinset x∩T₀).card:ℝ)) →
      (∀ x : V,(1/2+α/2)*TK.card≤((P.neighborFinset x∩TK).card:ℝ)) →
    (α*θ/4)^(m+1)*(Fintype.card V:ℝ)^(m+1)≤
      (Fintype.card {f : Fin (m+1)→V // DenseMarkedBase P π b T₀ TK f}:ℝ) := by
  obtain ⟨N,hN⟩ := exists_nat_ge ((((m:ℝ)+1)*(2*(b:ℝ)+1))/(α*θ/4))
  refine ⟨N,?_⟩
  intro V _ _ hn P π T₀ TK h₀ hK hd₀ hdK
  have hnR : (N:ℝ)≤Fintype.card V := by exact_mod_cast hn
  have hmargin := (div_le_iff₀ (show 0<α*θ/4 by positivity)).mp (hN.trans hnR)
  have hsize := mul_le_mul_of_nonneg_left (le_min h₀ hK) hα.le
  have hbudget : (α*θ/4)*Fintype.card V≤α*min (T₀.card:ℝ) TK.card-
      ((m:ℝ)+1)*(2*(b:ℝ)+1) := by
    have hn0 : (0:ℝ)≤Fintype.card V := Nat.cast_nonneg _
    have hpos : 0≤α*θ*Fintype.card V := by positivity
    nlinarith only [hsize,hmargin,hpos]
  have hh := dense_marked_base_cycle_count P π b m hm T₀ TK α
    ((α*θ/4)*Fintype.card V) hα.le hα1 (by positivity) hbudget hd₀ hdK
  simpa only [mul_pow] using hh

end Oberwolfach
