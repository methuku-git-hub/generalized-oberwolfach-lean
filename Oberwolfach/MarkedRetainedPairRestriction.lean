module

public import Oberwolfach.MarkedRetainedPairConditional

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W U Z Γ Color : Type} [Fintype V] [Fintype W] [Fintype U] [Fintype Z]
  [Fintype Γ] [Fintype Color] [Nonempty V] [Nonempty W]
  [LinearOrder V] [LinearOrder W] [DecidableEq U] [DecidableEq Z]

theorem marked_retained_pair_restriction_probability
    (f : W ≃ V) (g : Z ≃ U) (π : Equiv.Perm V) (ρ : Equiv.Perm W)
    (hc : ∀ x, f (ρ x) = π (f x)) (d : ℕ) (hd : 2 ≤ d) (a : Γ)
    (p k : ℝ) (hp : 0 ≤ p) (hk : 0 ≤ k) (hphys : 2*p+2*k ≤ 1)
    (q : U → Γ → ℝ) (hq : ∀ u c, 0 ≤ q u c) (hQ : ∀ u, ∑ c, q u c ≤ 1/8)
    (s : U → Color → ℝ) (hs : ∀ u c, 0 ≤ s u c)
    (hS : ∀ u, ∑ c, s u c ≤ intervalUncoveredProbability d (∑ c, q u c))
    (E : RawMarkedRetainedOutcome (U:=Z) (Color:=Color) ρ d a → Prop) :
    (rawMarkedRetentionLaw π d hd a p k hp hk hphys q hq hQ s hs hS).probability
      (fun z => E (markedRetainedPairRestriction f g π ρ hc d a z)) =
    (rawMarkedRetentionLaw ρ d hd a p k hp hk hphys (fun z => q (g z))
      (fun z => hq (g z)) (fun z => hQ (g z)) (fun z => s (g z))
      (fun z => hs (g z)) (fun z => hS (g z))).probability E := by
  let μ := FiniteLaw.pi (rawMarkedWheelLaw (V:=V) p k hp hk hphys d hd q hq hQ s hs hS)
  let ν := FiniteLaw.pi (rawMarkedWheelLaw (V:=W) p k hp hk hphys d hd
    (fun z => q (g z)) (fun z => hq (g z)) (fun z => hQ (g z))
    (fun z => s (g z)) (fun z => hs (g z)) (fun z => hS (g z)))
  have hraw : μ.map (rawMarkedRestrictPair f g) = ν := by
    apply finiteLaw_ext
    intro x
    have hm := finiteLaw_map_probability μ (rawMarkedRestrictPair f g) (fun y => y = x)
    have hr := rawMarked_pair_restriction_probability f f.injective g g.injective
      p k hp hk hphys d hd q hq hQ s hs hS (fun y => y = x)
    have hh := hm.trans hr
    have hone (L : FiniteLaw (RawMarkedOutcome W Z Γ Color)) :
        L.probability (fun y => y = x) = L.mass x := by
      unfold FiniteLaw.probability
      rw [Finset.sum_eq_single x]
      · simp
      · intro y hy hne; simp [hne]
      · simp
    rw [hone, hone] at hh
    exact hh
  unfold rawMarkedRetentionLaw
  change (μ.sigma _).probability _ = (ν.sigma _).probability E
  rw [← hraw]
  have hh := finiteLaw_sigma_dependent_transport μ
    (fun σ => startRetentionLaw (rawStartHubSet π d (fun e => σ (Sum.inr e)) a)
      (startRetentionMinimum (rawStartHubSet π d (fun e => σ (Sum.inr e)) a)) (startRetentionMinimum_le _))
    (rawMarkedRestrictPair f g)
    (fun σ => startRetentionLaw (rawStartHubSet ρ d (fun e => σ (Sum.inr e)) a)
      (startRetentionMinimum (rawStartHubSet ρ d (fun e => σ (Sum.inr e)) a)) (startRetentionMinimum_le _))
    (markedRetainedPairSecond f g π ρ hc d a)
    (fun σ => marked_retained_pair_conditional_map f g π ρ hc d a σ) E
  have he : (fun z => E ⟨rawMarkedRestrictPair f g z.1,
      (markedRetainedPairSecond f g π ρ hc d a z.1 z.2)⟩) =
      (fun z => E (markedRetainedPairRestriction f g π ρ hc d a z)) := by
    funext z
    cases z
    rfl
  rw [he] at hh
  exact hh
end Oberwolfach
