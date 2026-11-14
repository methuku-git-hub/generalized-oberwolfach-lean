module

public import Oberwolfach.OrdinaryExpandedInducedRimPriorFromHalfDensity
public import Oberwolfach.OrdinaryShiftedMatchingCoreEvent

@[expose] public section
/-! The induced rim event and an earlier matching-core event use the same
expanded state and the same physical orientation coins. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 12000000
set_option synthInstance.maxSize 65536
set_option maxRecDepth 32768
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance (priority := high) rimMatchingPriorFin (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

theorem ordinary_induced_rim_with_matching_core_prior
    (α pstar : ℝ) (hα : 0<α) (hα1 : α≤1/2) (hpstar : 0<pstar) (q₀ : ℕ) :
    ∃ N : ℕ, ∀ (n K : ℕ) (U : Type) [Fintype U] [DecidableEq U],
    ∀ (P Pmatch : SimpleGraph (Fin n)) (I : Finset (Fin n)), N≤I.card →
    ∀ density : ℝ, (1/2:ℝ)+α≤density →
      (∀v∈I,density*I.card≤((I∩P.neighborFinset v).card:ℝ)) →
    ∀ (p k p₂ k₂ u : ℝ) (hp : 0≤p) (hk : 0≤k) (hp₂ : 0≤p₂) (hk₂ : 0≤k₂) (hu : 0≤u)
      (hsum : 2*p+2*k+2*p₂+2*k₂+u≤1), pstar≤2*p →
    ∀ (d : ℕ) (hd : 2≤d)
      (q : U→Bool→ℝ) (hq : ∀v g,0≤q v g) (hQ : ∀v,∑g,q v g≤1/8)
      (s : U→Bool→ℝ) (hs : ∀v j,0≤s v j)
      (hS : ∀v,∑j,s v j ≤ intervalUncoveredProbability d (∑g,q v g)),
    ∀ (π : Equiv.Perm (Fin n)) (m : ℕ) (pm km : ℝ)
      (wM : MarkedWheel (Prod.fst : Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d)
        (fun _ (_ : U)=>True) (fun _ (_ : U)=>True)→ℝ)
      (wO : ∀i : Fin K, OrderedOrdinaryWheel (U:=U) π (3*d) (longPaddedSeedExponent i+2)→ℝ)
      (t ξ : ℝ)
      {R : (∀e : RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)→Type}
      [∀σ,Fintype (R σ)] (ρ : ∀σ,FiniteLaw (R σ))
      (E : (Σσ,R σ)×(Sym2 (Fin n)→Bool)→Prop) (a : ℝ),
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=Fin n) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS);
    let ν:=FiniteLaw.pi (fun _ : Sym2 (Fin n)=>FiniteLaw.fairCoin);
    1-a≤((μ.sigma ρ).prod ν).probability (fun z=>E z ∧
      OrdinaryShiftedMatchingCoreEvent Pmatch π d m pm km q s wM wO t ξ z.1.1) →
    1-a-1/(I.card:ℝ)^q₀≤((μ.sigma ρ).prod ν).probability (fun z=>
      (E z ∧ OrdinaryShiftedMatchingCoreEvent Pmatch π d m pm km q s wM wO t ξ z.1.1) ∧
      OrdinaryInducedRimCutEvent I
        (sampledOrientation (rawWheelGraph P (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e))) z.2) α pstar) := by
  obtain ⟨N,hN⟩:=ordinary_expanded_induced_rim_cut_with_prior_from_half_density α pstar hα hα1 hpstar q₀
  refine ⟨N,?_⟩
  intro n K U _ _ P Pmatch I hI density hdensity hmin p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum hpstarR
    d hd q hq hQ s hs hS π m pm km wM wO t ξ R _ ρ E a μ ν hE
  exact hN (Fin n) U Bool Bool P I hI density hdensity hmin p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum hpstarR
    d hd q hq hQ s hs hS ρ (fun z=>E z ∧ OrdinaryShiftedMatchingCoreEvent Pmatch π d m pm km q s wM wO t ξ z.1.1) a hE
end Oberwolfach
