module

public import Oberwolfach.RawMarkedSeedLoadEvent
public import Oberwolfach.RawMarkedHubRestriction
public import Oberwolfach.MarkedLoadFailureBounds
public import Oberwolfach.GoodPlacementEvents

@[expose] public section

/-! Inner rim/spoke loads and external spoke loads on one ambient raw sample.
The denominator uses the inner hub order; outer hubs are a fixed larger domain. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V U Z Γ Color : Type} [Fintype V] [Fintype U] [Fintype Z] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U] [DecidableEq Z]
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


local notation "InnerParent" => MarkedWheel (Prod.fst : V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d)
  (fun (_ : V) (_ : Z)=>True) (fun _ _=>True)
local notation "innerSeed" => (fun W : InnerParent=>weight W.1.val/(D*p^m*k*s₀^m))

theorem rawMarkedSeed_nested_hubs_event
    (f : Z→U) (hf : Function.Injective f) (hz : Fintype.card Z≤Fintype.card V)
    (hmarked : (Fintype.card Z:ℝ)*t₀=D*k)
    (hordinary : (Fintype.card Z:ℝ)*t₀*m=D*p)
    (Kout : ℝ) (hu : (Fintype.card U:ℝ)≤Kout*Fintype.card V)
    (ε : ℝ) (hε : 0<ε) :
    1-(8+4*Kout)*(Fintype.card V:ℝ)^2*
      Real.exp (-markedLoadExponent m d Bplus ε*Fintype.card V)≤
    (FiniteLaw.pi μmark).probability (fun σ=>
      (∀ a : Bool×V×U,|typedMarkedPotentialLoad seed (rawMarkedPairRims P π d σ)
        (rawMarkedPairSpokes π d σ g j) (Sum.inr a)-1|≤τ+ε) ∧
      (∀ root : ((V×V)⊕(V×V))⊕(Bool×V×Z),
        rawMarkedWheelMarginal P π d p k (fun z=>q (f z)) (fun z=>s (f z)) g j root≠0 →
        |typedMarkedPotentialLoad innerSeed (rawMarkedPairRims P π d (rawMarkedRestrictHubs f σ))
          (rawMarkedPairSpokes π d (rawMarkedRestrictHubs f σ) g j) root-1|≤τ+ε)) := by
  have hext := rawMarkedSeed_external_spoke_event P π p k hp hk hsum d hd q hq hQ s hs hS hnoshort
    m hm g j s₀ t₀ D τ A B hs₀ hD ht hq₀ hs₀' weight hw hn hDlo hDhi
    pstar hpstar hpstar' hkstar hsstar hp1 hk1 hs1 hB ε hε
  have hint := rawMarkedSeed_load_event P π p k hp hk hsum d hd
    (fun z=>q (f z)) (fun z=>hq (f z)) (fun z=>hQ (f z))
    (fun z=>s (f z)) (fun z=>hs (f z)) (fun z=>hS (f z)) hnoshort
    m hm g j s₀ t₀ D τ A B hs₀ hD ht (fun z=>hq₀ (f z)) (fun z=>hs₀' (f z))
    weight hw hn hDlo hDhi pstar hpstar hpstar' hkstar hsstar hp1 hk1 hs1 hB hz hmarked hordinary ε hε
  rw [← rawMarked_hub_restriction_probability f hf p k hp.le hk.le hsum d hd q hq hQ s hs hS] at hint
  have hn' : (0:ℝ)<Fintype.card V := by exact_mod_cast hn
  have htail₁ := marked_load_failure_bound m d Bplus ε (Fintype.card V)
    (Fintype.card (Bool×V×U)) (2*Kout) hn' (marked_external_spoke_domain_card Kout hu)
  have htail₂ := marked_load_failure_bound m d Bplus ε (Fintype.card V)
    (Fintype.card (((V×V)⊕(V×V))⊕(Bool×V×Z))) 4 hn' (by exact_mod_cast marked_root_domain_card hz)
  have hgood : 1-8*(Fintype.card V:ℝ)^2*Real.exp (-markedLoadExponent m d Bplus ε*Fintype.card V)≤
      (FiniteLaw.pi μmark).probability (fun σ=>∀ root,
        rawMarkedWheelMarginal P π d p k (fun z=>q (f z)) (fun z=>s (f z)) g j root≠0 →
        |typedMarkedPotentialLoad innerSeed (rawMarkedPairRims P π d (rawMarkedRestrictHubs f σ))
          (rawMarkedPairSpokes π d (rawMarkedRestrictHubs f σ) g j) root-1|≤τ+ε) := by
    linarith only [hint,htail₂]
  have hh := finiteLaw_good_intersection (FiniteLaw.pi μmark)
    (fun σ=>∀ a : Bool×V×U,|typedMarkedPotentialLoad seed (rawMarkedPairRims P π d σ)
      (rawMarkedPairSpokes π d σ g j) (Sum.inr a)-1|≤τ+ε) _ _ hgood
  nlinarith only [hh,hext,htail₁]

end Oberwolfach
