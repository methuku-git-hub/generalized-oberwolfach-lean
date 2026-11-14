module

public import Oberwolfach.RawUniformRetention

@[expose] public section

/-! Real polynomial exponents in the manuscript's restriction interface.
Rounding exponents upward changes only uniform thresholds, not the law. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
namespace Oberwolfach

theorem raw_uniform_retention_restrictions_real (d : ℕ) (hd : 2≤d)
    (C Q p ζ : ℝ) (hp : 0<p) (hζ : 0<ζ) :
    ∃ m N : ℕ,1≤m ∧ 1≤N ∧ ∀ (V U Γ Color I : Type)
      [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [Fintype I] [Nonempty V]
      [DecidableEq V] [DecidableEq U],
    N≤Fintype.card V → Fintype.card U≤Fintype.card V →
      (Fintype.card I:ℝ)≤(Fintype.card V:ℝ)^C →
    ∀ (π : Equiv.Perm V), (∀ x l,0<l → l<2*d+1 → (π^l) x≠x) →
    ∀ (q : U→Γ→ℝ) (hq : ∀ u a,0≤q u a) (hQ : ∀ u,∑ a,q u a≤1/8)
      (s : U→Color→ℝ) (hs : ∀ u j,0≤s u j)
      (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ a,q u a))
      (g : Γ) (t₀ : ℝ),(∀ u,q u g=t₀) → p*Fintype.card V≤t₀*Fintype.card U →
    ∀ (S : I→Finset V) (T : I→Finset U),
      (∀ i x,π x∈S i ↔ x∈S i) → (∀ i,m≤(S i).card) → (∀ i,m≤(T i).card) →
    1-(Fintype.card V:ℝ)^(-Q)≤(rawUniformRetentionLaw π d hd g q hq hQ s hs hS).probability
      (fun z=>(∀ a,|((rawStartHubSet π d z.1 g a).card:ℝ)-t₀*Fintype.card U/d|≤(Fintype.card V:ℝ)^(3/5:ℝ)) ∧
        RetainedRestrictionGood π d z.1 g (startRetentionMinimum (rawStartHubSet π d z.1 g)) S T ζ z.2) := by
  obtain ⟨m,N,hm,hN1,hN⟩ := raw_uniform_retention_restrictions d (Nat.ceil C) (Nat.ceil Q) hd p ζ hp hζ
  refine ⟨m,N,hm,hN1,?_⟩
  intro V U Γ Color I _ _ _ _ _ _ _ _ hn hu hI π hπ q hq hQ s hs hS g t₀ hg hmass S T hInv hSc hTc
  have hn1 : (1:ℝ)≤Fintype.card V := by exact_mod_cast hN1.trans hn
  have hi : Fintype.card I≤(Fintype.card V)^(Nat.ceil C) := by
    have hh := hI.trans (Real.rpow_le_rpow_of_exponent_le hn1 (Nat.le_ceil C))
    rw [Real.rpow_natCast] at hh
    exact_mod_cast hh
  have he : 1/(Fintype.card V:ℝ)^(Nat.ceil Q)≤(Fintype.card V:ℝ)^(-Q) := by
    have hh := Real.rpow_le_rpow_of_exponent_le hn1 (neg_le_neg (Nat.le_ceil Q))
    simpa only [Real.rpow_neg (by linarith : (0:ℝ)≤Fintype.card V),Real.rpow_natCast,one_div] using hh
  exact (sub_le_sub_left he 1).trans
    (hN V U Γ Color I hn hu hi π hπ q hq hQ s hs hS g t₀ hg hmass S T hInv hSc hTc)

end Oberwolfach
