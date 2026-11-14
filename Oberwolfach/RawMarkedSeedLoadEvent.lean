module

public import Oberwolfach.RawMarkedSeedMeans
public import Oberwolfach.RawMarkedLoadConcentration
public import Oberwolfach.SuccessorSeedBounds

@[expose] public section

/-! One common event for every fixed potential root of the marked seed.
Coefficients and their degree normalization are fixed before exposure. -/
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
  (m : ℕ) (hm : 3≤m) (g : Γ) (j : Color)
  (s₀ t₀ D τ A B : ℝ) (hs₀ : 0<s₀) (hD : 0<D) (ht : t₀=s₀/m)
  (hq₀ : ∀ u,q u g=t₀) (hs₀' : ∀ u,s u j=s₀)
  (weight : (Fin (m+1)→V)→ℝ)
  (hw : SuccessorSequenceWeightConditions P π (3*d) D τ A B weight)

local notation "μmark" => rawMarkedWheelLaw p k hp.le hk.le hsum d hd q hq hQ s hs hS
local notation "Parent" => MarkedWheel (Prod.fst : V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d)
  (fun (_ : V) (_ : U)=>True) (fun _ _=>True)
set_option quotPrecheck false
local notation "seed" => (fun W : Parent=>weight W.1.val/(D*p^m*k*s₀^m))


variable (hn : 0<Fintype.card V)
  (hDlo : (Fintype.card V:ℝ)/2≤D) (hDhi : D≤2*Fintype.card V)
  (pstar : ℝ) (hpstar : 0<pstar) (hpstar' : pstar≤p) (hkstar : pstar≤k) (hsstar : pstar≤s₀)
  (hp1 : p≤1) (hk1 : k≤1) (hs1 : s₀≤1) (hB : 0<B)
local notation "Bplus" => (2*B/pstar^(2*m+1))
include hnoshort hm hs₀ hD ht hq₀ hs₀' hw hn hDlo hDhi hpstar hpstar' hkstar hsstar hp1 hk1 hs1 hB

theorem rawMarkedSeed_load_event
    (hu : Fintype.card U≤Fintype.card V)
    (hmarked : (Fintype.card U:ℝ)*t₀=D*k)
    (hordinary : (Fintype.card U:ℝ)*t₀*m=D*p)
    (ε : ℝ) (hε : 0<ε) :
    1-(Fintype.card (((V×V)⊕(V×V))⊕(Bool×V×U)):ℝ)*
      (2*Real.exp (-2*ε^2/((8*(d:ℝ)+6)^2*(((m:ℝ)+1)^4*Bplus/Fintype.card V)*(2*((m:ℝ)+1))*(((m:ℝ)+1)^2*Bplus))))≤
    (FiniteLaw.pi μmark).probability (fun σ=>∀ root,
      rawMarkedWheelMarginal P π d p k q s g j root≠0 →
      |typedMarkedPotentialLoad seed (rawMarkedPairRims P π d σ) (rawMarkedPairSpokes π d σ g j) root-1|≤τ+ε) := by
  have hseed (W : Parent) := successor_seed_nonneg_upper hw (by omega) hn hDlo hDhi
    p k s₀ pstar hpstar hpstar' hkstar hsstar hp1 hk1 hs1 hB.le W.1.val
  have hh := rawMarkedPotentialLoad_mean_event P π p k hp.le hk.le hsum d hd q hq hQ s hs hS
    m hm (fun _ _=>True) (fun _ _=>True) hn hu seed Bplus (by positivity) hseed g j ε hε
  apply hh.trans
  apply finiteLaw_probability_mono
  intro σ hσ root hroot
  have hmean : |(FiniteLaw.pi μmark).expectation
      (fun ω=>typedMarkedPotentialLoad seed (rawMarkedPairRims P π d ω) (rawMarkedPairSpokes π d ω g j) root)-1|≤τ := by
    cases root with
    | inl e=>
      exact rawMarkedSeed_rim_mean P π p k hp hk hsum d hd q hq hQ s hs hS hnoshort
        m (by omega) g j s₀ t₀ D τ A B hs₀ hD ht hq₀ hs₀' weight hw hmarked hordinary e hroot
    | inr a=>
      exact rawMarkedSeed_spoke_mean P π p k hp hk hsum d hd q hq hQ s hs hS hnoshort
        m (by omega) g j s₀ t₀ D τ A B hs₀ hD ht hq₀ hs₀' weight hw a.1 a.2.1 a.2.2
  calc
    _ ≤ |typedMarkedPotentialLoad seed (rawMarkedPairRims P π d σ) (rawMarkedPairSpokes π d σ g j) root-
      (FiniteLaw.pi μmark).expectation (fun ω=>typedMarkedPotentialLoad seed
        (rawMarkedPairRims P π d ω) (rawMarkedPairSpokes π d ω g j) root)|+
      |(FiniteLaw.pi μmark).expectation (fun ω=>typedMarkedPotentialLoad seed
        (rawMarkedPairRims P π d ω) (rawMarkedPairSpokes π d ω g j) root)-1| := abs_sub_le _ _ _
    _ ≤ ε+τ := add_le_add (hσ root).le hmean
    _ = _ := by ring

theorem rawMarkedSeed_external_spoke_event (ε : ℝ) (hε : 0<ε) :
    1-(Fintype.card (Bool×V×U):ℝ)*
      (2*Real.exp (-2*ε^2/((8*(d:ℝ)+6)^2*(((m:ℝ)+1)^4*Bplus/Fintype.card V)*(2*((m:ℝ)+1))*(((m:ℝ)+1)^2*Bplus))))≤
    (FiniteLaw.pi μmark).probability (fun σ=>∀ a : Bool×V×U,
      |typedMarkedPotentialLoad seed (rawMarkedPairRims P π d σ) (rawMarkedPairSpokes π d σ g j) (Sum.inr a)-1|≤τ+ε) := by
  have hseed (W : Parent) := successor_seed_nonneg_upper hw (by omega) hn hDlo hDhi
    p k s₀ pstar hpstar hpstar' hkstar hsstar hp1 hk1 hs1 hB.le W.1.val
  have hh := rawMarkedSpokeLoad_mean_event P π p k hp.le hk.le hsum d hd q hq hQ s hs hS
    m hm (fun _ _=>True) (fun _ _=>True) hn seed Bplus (by positivity) hseed g j ε hε
  apply hh.trans
  apply finiteLaw_probability_mono
  intro σ hσ a
  have hmean := rawMarkedSeed_spoke_mean P π p k hp hk hsum d hd q hq hQ s hs hS hnoshort
    m (by omega) g j s₀ t₀ D τ A B hs₀ hD ht hq₀ hs₀' weight hw a.1 a.2.1 a.2.2
  calc
    _ ≤ |typedMarkedPotentialLoad seed (rawMarkedPairRims P π d σ) (rawMarkedPairSpokes π d σ g j) (Sum.inr a)-
      (FiniteLaw.pi μmark).expectation (fun ω=>typedMarkedPotentialLoad seed
        (rawMarkedPairRims P π d ω) (rawMarkedPairSpokes π d ω g j) (Sum.inr a))|+
      |(FiniteLaw.pi μmark).expectation (fun ω=>typedMarkedPotentialLoad seed
        (rawMarkedPairRims P π d ω) (rawMarkedPairSpokes π d ω g j) (Sum.inr a))-1| := abs_sub_le _ _ _
    _ ≤ ε+τ := add_le_add (hσ a).le hmean
    _ = _ := by ring

end Oberwolfach
