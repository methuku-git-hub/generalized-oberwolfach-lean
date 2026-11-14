module

public import Oberwolfach.RawMarkedNestedLoadEvent
public import Oberwolfach.MarkedSeedDensities

@[expose] public section

/-! Marked reference loads with the manuscript's actual density formulas.
The lower coefficient bound and the exponential failure exponent depend
only on the supplied fixed parameters. The graph and weighting are fixed
before the raw sampling coordinates are exposed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option quotPrecheck false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V U Z Γ Color : Type} [Fintype V] [Fintype U] [Fintype Z] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U] [DecidableEq Z]

theorem marked_reference_loads
    (m : ℕ) (hm : 3≤m) (ρstar sstar A B : ℝ)
    (hρstar : 0<ρstar) (hsstar : 0<sstar) (hA : 0<A) (hB : 0<B)
    (P : SimpleGraph V) (π : Equiv.Perm V) (hn : 0<Fintype.card V)
    (f : Z→U) (hf : Function.Injective f) (hz : Fintype.card Z≤Fintype.card V)
    (Kout : ℝ) (hu : (Fintype.card U:ℝ)≤Kout*Fintype.card V)
    (ρ s₀ : ℝ) (hρlo : ρstar≤ρ) (hρhi : ρ≤1) (hslo : sstar≤s₀) (hshi : s₀≤1/100)
    (hDlo : (Fintype.card V:ℝ)/2≤2*Fintype.card Z/ρ)
    (hDhi : 2*Fintype.card Z/ρ≤2*Fintype.card V)
    (d : ℕ) (hd : 2≤d) (hnoshort : ∀ x l,0<l → l<2*d+1 → (π^l) x≠x)
    (q : U→Γ→ℝ) (hq : ∀ u g,0≤q u g) (hQ : ∀ u,∑ g,q u g≤1/8)
    (s : U→Color→ℝ) (hs : ∀ u j,0≤s u j)
    (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
    (g : Γ) (j : Color) (hq₀ : ∀ u,q u g=s₀/m) (hs₀' : ∀ u,s u j=s₀)
    (τ ε : ℝ) (hε : 0<ε) (weight : (Fin (m+1)→V)→ℝ)
    (hw : SuccessorSequenceWeightConditions P π (3*d) (2*Fintype.card Z/ρ) τ A B weight) :
    let p := ρ*s₀/2
    let k := p/m
    let D := 2*(Fintype.card Z:ℝ)/ρ
    let pstar := ρstar*sstar/(2*m)
    let Bplus := 2*B/pstar^(2*m+1)
    let densities := marked_seed_density_bounds m (by omega) ρ s₀ ρstar sstar hρstar hsstar hρlo hρhi hslo hshi
    let μ := rawMarkedWheelLaw p k
      ((densities.1.trans_le densities.2.1).le)
      ((densities.1.trans_le densities.2.2.1).le)
      densities.2.2.2.2.2.2.2.2 d hd q hq hQ s hs hS
    let seed := fun W : MarkedWheel (Prod.fst : V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun (_ : V) (_ : U)=>True) (fun _ _=>True)=>weight W.1.val/(D*p^m*k*s₀^m)
    let innerSeed := fun W : MarkedWheel (Prod.fst : V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun (_ : V) (_ : Z)=>True) (fun _ _=>True)=>weight W.1.val/(D*p^m*k*s₀^m)
    0<markedLoadExponent m d Bplus ε ∧
    (∀ C,SuccessorSequenceValid P π C → PermutationSeparated π (3*d) C →
      (A/2)/(Fintype.card V:ℝ)^m≤weight C/(D*p^m*k*s₀^m) ∧
      weight C/(D*p^m*k*s₀^m)≤Bplus/(Fintype.card V:ℝ)^m) ∧
    1-(8+4*Kout)*(Fintype.card V:ℝ)^2*
      Real.exp (-markedLoadExponent m d Bplus ε*Fintype.card V)≤
    (FiniteLaw.pi μ).probability (fun σ=>
      (∀ a : Bool×V×U,|typedMarkedPotentialLoad seed (rawMarkedPairRims P π d σ)
        (rawMarkedPairSpokes π d σ g j) (Sum.inr a)-1|≤τ+ε) ∧
      (∀ root : ((V×V)⊕(V×V))⊕(Bool×V×Z),
        rawMarkedWheelMarginal P π d p k (fun z=>q (f z)) (fun z=>s (f z)) g j root≠0 →
        |typedMarkedPotentialLoad innerSeed (rawMarkedPairRims P π d (rawMarkedRestrictHubs f σ))
          (rawMarkedPairSpokes π d (rawMarkedRestrictHubs f σ) g j) root-1|≤τ+ε)) := by
  intro p k D pstar Bplus densities μ seed innerSeed
  obtain ⟨hps,hpp,hpk,hps₀,hp1,hk1,hs1,ht,hsum⟩ := densities
  have hρ : 0<ρ := hρstar.trans_le hρlo
  have hs₀ : 0<s₀ := hsstar.trans_le hslo
  have hp : 0<p := hps.trans_le hpp
  have hk : 0<k := hps.trans_le hpk
  have hn' : (0:ℝ)<Fintype.card V := by exact_mod_cast hn
  have hD : 0<D := (half_pos hn').trans_le hDlo
  have hBp : 0<Bplus := by dsimp [Bplus];positivity
  refine ⟨markedLoadExponent_pos m d Bplus ε hBp hε,?_,?_⟩
  · intro C hvalid hsep
    exact ⟨successor_seed_positive_lower hw (by omega) hn hDlo hDhi p k s₀ pstar hps hpp hpk hps₀
      hp1 hk1 hs1 hA.le hB.le C hvalid hsep,
      (successor_seed_nonneg_upper hw (by omega) hn hDlo hDhi p k s₀ pstar hps hpp hpk hps₀
        hp1 hk1 hs1 hB.le C).2⟩
  · have hbal := marked_seed_density_balance m (by omega) ρ s₀ (Fintype.card Z) hρ.ne'
    exact rawMarkedSeed_nested_hubs_event P π p k hp hk hsum d hd q hq hQ s hs hS hnoshort
      m hm g j s₀ (s₀/m) D τ A B hs₀ hD rfl hq₀ hs₀' weight hw hn hDlo hDhi
      pstar hps hpp hpk hps₀ hp1 hk1 hs1 hB f hf hz hbal.1 hbal.2 Kout hu ε hε

end Oberwolfach
