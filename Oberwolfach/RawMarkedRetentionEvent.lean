module

public import Oberwolfach.RawMarkedRetention

@[expose] public section

/-! A single event combines all already proved raw marked estimates with
uniform one-colour retention on every fixed row and index restriction.
The raw event may involve physical edges as well as interval variables. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem raw_marked_retention_common_event (d : ℕ) (hd : 2≤d)
    (C Q pstar ζ : ℝ) (hpstar : 0<pstar) (hζ : 0<ζ) :
    ∃ m N : ℕ,1≤m ∧ 1≤N ∧ ∀ (V U Γ Color I : Type)
      [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [Fintype I]
      [LinearOrder V] [Nonempty V] [DecidableEq U],
    N≤Fintype.card V → Fintype.card U≤Fintype.card V →
      (Fintype.card I:ℝ)≤(Fintype.card V:ℝ)^C →
    ∀ (π : Equiv.Perm V), (∀ x l,0<l → l<2*d+1 → (π^l) x≠x) →
    ∀ (p k : ℝ) (hp : 0≤p) (hk : 0≤k) (hphys : 2*p+2*k≤1)
      (q : U→Γ→ℝ) (hq : ∀ u a,0≤q u a) (hQ : ∀ u,∑ a,q u a≤1/8)
      (s : U→Color→ℝ) (hs : ∀ u j,0≤s u j)
      (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ a,q u a))
      (g : Γ) (t₀ : ℝ),(∀ u,q u g=t₀) → pstar*Fintype.card V≤t₀*Fintype.card U →
    ∀ (S : I→Finset V) (T : I→Finset U),
      (∀ i x,π x∈S i ↔ x∈S i) → (∀ i,m≤(S i).card) → (∀ i,m≤(T i).card) →
    ∀ (E : RawMarkedOutcome V U Γ Color→Prop) (a : ℝ),
      1-a≤(FiniteLaw.pi (rawMarkedWheelLaw p k hp hk hphys d hd q hq hQ s hs hS)).probability E →
    1-a-(Fintype.card V:ℝ)^(-Q)≤
      (rawMarkedRetentionLaw π d hd g p k hp hk hphys q hq hQ s hs hS).probability
        (fun z=>E z.1 ∧
          (∀ v,|((rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) g v).card:ℝ)-
            t₀*Fintype.card U/d|≤(Fintype.card V:ℝ)^(3/5:ℝ)) ∧
          RetainedRestrictionGood π d (fun e=>z.1 (Sum.inr e)) g
            (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) g)) S T ζ z.2) := by
  obtain ⟨m,N,hm,hN1,hN⟩ := raw_uniform_retention_restrictions_real d hd C Q pstar ζ hpstar hζ
  refine ⟨m,N,hm,hN1,?_⟩
  intro V U Γ Color I _ _ _ _ _ _ _ _ hn hu hI π hπ p k hp hk hphys q hq hQ s hs hS g t₀ hg hmass S T hInv hSc hTc E a hE
  have hG := hN V U Γ Color I hn hu hI π hπ q hq hQ s hs hS g t₀ hg hmass S T hInv hSc hTc
  exact rawMarkedRetentionLaw_common_event π d hd g p k hp hk hphys q hq hQ s hs hS E _ a _ hE hG

end Oberwolfach
