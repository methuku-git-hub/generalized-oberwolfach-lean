module

public import Oberwolfach.RawMarkedSeedExpectations
public import Oberwolfach.MarkedSeedMeanBounds

@[expose] public section

/-! Unconditional means of the marked seed on the original independent
coordinates. No root indicator is conditioned on, including for external hubs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]
  (P : SimpleGraph V) (π : Equiv.Perm V)
  (p k : ℝ) (hp : 0<p) (hk : 0<k) (hsum : 2*p+2*k≤1)
  (d : ℕ) (hd : 2≤d)
  (q : U→Γ→ℝ) (hq : ∀ u g,0≤q u g) (hQ : ∀ u,∑ g,q u g≤1/8)
  (s : U→Color→ℝ) (hs : ∀ u j,0≤s u j)
  (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
  (hnoshort : ∀ x l,0<l → l<2*d+1 → (π^l) x≠x)
  (m : ℕ) (hm : 2≤m) (g : Γ) (j : Color)
  (s₀ t₀ D τ A B : ℝ) (hs₀ : 0<s₀) (hD : 0<D) (ht : t₀=s₀/m)
  (hq₀ : ∀ u,q u g=t₀) (hs₀' : ∀ u,s u j=s₀)
  (weight : (Fin (m+1)→V)→ℝ)
  (hw : SuccessorSequenceWeightConditions P π (3*d) D τ A B weight)

local notation "μmark" => rawMarkedWheelLaw p k hp.le hk.le hsum d hd q hq hQ s hs hS
local notation "Parent" => MarkedWheel (Prod.fst : V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d)
  (fun (_ : V) (_ : U)=>True) (fun _ _=>True)
set_option quotPrecheck false
local notation "seed" => (fun W : Parent=>weight W.1.val/(D*p^m*k*s₀^m))

include hnoshort hm hs₀ hD ht hq₀ hs₀' hw

theorem rawMarkedSeed_spoke_mean (a : Bool) (v : V) (u : U) :
    |(FiniteLaw.pi μmark).expectation
      (fun σ=>typedMarkedPotentialLoad seed (rawMarkedPairRims P π d σ)
        (rawMarkedPairSpokes π d σ g j) (Sum.inr (a,v,u)))-1|≤τ := by
  have ht' : 0<t₀ := by rw [ht];positivity
  have hroot : rawMarkedWheelMarginal P π d p k q s g j (Sum.inr (a,v,u))≠0 := by
    cases a <;> simp [rawMarkedWheelMarginal,hq₀,hs₀',ne_of_gt hs₀,ne_of_gt ht']
  rw [rawMarkedSeed_expectation P π p k hp hk hsum d hd q hq hQ s hs hS hnoshort m hm
    (fun _ _=>True) (fun _ _=>True) g j s₀ t₀ D hs₀ hD hq₀ hs₀' (fun W : Parent=>weight W.1.val)
    (fun W hW=>successor_weight_parent_edges hw W.1.val hW) (Sum.inr (a,v,u)) hroot]
  simpa only [rawMarkedWheelMarginal,hq₀,hs₀'] using
    markedParent_spoke_normalized hw (by omega) hD s₀ t₀ hs₀ ht a v u

theorem rawMarkedSeed_rim_mean
    (hmarked : (Fintype.card U:ℝ)*t₀=D*k)
    (hordinary : (Fintype.card U:ℝ)*t₀*m=D*p)
    (e : (V×V)⊕(V×V))
    (he : rawMarkedWheelMarginal P π d p k q s g j (Sum.inl e)≠0) :
    |(FiniteLaw.pi μmark).expectation
      (fun σ=>typedMarkedPotentialLoad seed (rawMarkedPairRims P π d σ)
        (rawMarkedPairSpokes π d σ g j) (Sum.inl e))-1|≤τ := by
  have ht' : 0<t₀ := by rw [ht];positivity
  rw [rawMarkedSeed_expectation P π p k hp hk hsum d hd q hq hQ s hs hS hnoshort m hm
    (fun _ _=>True) (fun _ _=>True) g j s₀ t₀ D hs₀ hD hq₀ hs₀' (fun W : Parent=>weight W.1.val)
    (fun W hW=>successor_weight_parent_edges hw W.1.val hW) (Sum.inl e) he]
  cases e with
  | inl xy=>
    have he' : ¬PermutationClose π (3*d) xy.1 xy.2 ∧ P.Adj xy.1 xy.2 := by
      by_contra h;exact he (by simp [rawMarkedWheelMarginal,h])
    simp only [rawMarkedWheelMarginal,he',ite_true]
    exact markedParent_ordinary_rim_normalized hw (by omega) hD p t₀ hp ht'.le hordinary xy.1 xy.2 he'.1 he'.2
  | inr xy=>
    have he' : ¬PermutationClose π (3*d) xy.1 xy.2 ∧ P.Adj xy.1 (π xy.2) := by
      by_contra h;exact he (by simp [rawMarkedWheelMarginal,h])
    simp only [rawMarkedWheelMarginal,he',ite_true]
    exact markedParent_marked_rim_normalized hw hD k t₀ hk ht'.le hmarked xy.1 xy.2 he'.1 he'.2

end Oberwolfach
