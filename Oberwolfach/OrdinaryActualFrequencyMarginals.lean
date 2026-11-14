module

public import Oberwolfach.OrdinaryDiscardedFrequencies
public import Oberwolfach.OrdinaryFrequencyMarginals

@[expose] public section
/-! Derive the ordinary-class probability bounds from the actual finite
short-length frequencies and the long-component frequency. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
open scoped BigOperators

theorem ordinary_actual_frequency_marginals
    (K:ℕ) (hK:0<K) (s θ c long:ℝ) (f:Fin K→ℝ)
    (hs0:0≤s) (hs1:s≤1/100) (hθ0:0≤θ) (hθ1:θ≤1/100) (hc:8≤c)
    (hlong:0≤long) (hf:∀ i,0≤f i)
    (hfreq:(∑ i,f i)+long=1-s):
    let cutoff:=θ/(100*(K:ℝ))
    let longKept:=if long<θ/100 then 0 else long
    let shortKept:=∑ i:Fin K,(if f i<cutoff then 0 else f i)
    let omitted:=(∑ i:Fin K,(if f i<cutoff then f i else 0))+
      (if long<θ/100 then long else 0)
    let a:=(1-θ)*longKept/c
    let b:=(c-1)*a+(1-θ)*shortKept
    let u:=1-s-a-b;
    0≤omitted ∧ omitted≤θ/50 ∧
    u=θ*(1-s)+(1-θ)*omitted ∧ θ/2≤u ∧ u≤2*θ ∧
    0≤a ∧ a≤1/c ∧ 1/2≤b ∧ s+a+b+u=1 := by
  intro cutoff longKept shortKept omitted a b u
  have hshort:=ordinary_discarded_short_frequency K hK θ hθ0 f hf
  have hlong0:0≤(if long<θ/100 then long else 0):=by split_ifs <;> positivity
  have hlongmax:(if long<θ/100 then long else 0)≤θ/100:=by
    split_ifs with h
    · exact h.le
    · positivity
  have homit0:0≤omitted:=by dsimp [omitted,cutoff];linarith [hshort.1]
  have homitmax:omitted≤θ/50:=by dsimp [omitted,cutoff];linarith [hshort.2]
  have hL:0≤longKept:=by dsimp [longKept];split_ifs <;> positivity
  have hS:0≤shortKept:=by
    dsimp [shortKept]
    apply Finset.sum_nonneg
    intro i _
    split_ifs <;> simp [hf]
  have hsplit:(∑ i:Fin K,(if f i<cutoff then 0 else f i))+
      (∑ i:Fin K,(if f i<cutoff then f i else 0))=∑ i:Fin K,f i:=by
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> ring
  have hlongsplit:longKept+(if long<θ/100 then long else 0)=long:=by dsimp [longKept];split_ifs <;> ring
  have htotal:longKept+shortKept+omitted=1-s:=by dsimp [shortKept,omitted];linarith
  have hh:=ordinary_frequency_marginal_bounds s θ c longKept shortKept omitted
    hs0 hs1 hθ0 hθ1 hc hL hS homit0 homitmax htotal
  exact ⟨homit0,homitmax,hh⟩
end Oberwolfach
