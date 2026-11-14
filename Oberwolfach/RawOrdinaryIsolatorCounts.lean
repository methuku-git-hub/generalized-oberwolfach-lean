module

public import Oberwolfach.RawOrdinaryHubCounts
public import Oberwolfach.OrdinaryIsolatorPotential
public import Oberwolfach.GoodPlacementEvents

@[expose] public section

/-! Combining the two common events gives both potential isolator bounds
at absent root edges and actual configuration counts at retained edges. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [DecidableEq V] [DecidableEq U]

theorem raw_ordinary_isolator_count_event
    (P F : SimpleGraph V) (π : Equiv.Perm V)
    (ρ : Sym2 V → ℝ) (hρ : ∀ e,0≤ρ e) (hρ1 : ∀ e,ρ e≤1)
    (d : ℕ) (hd : 2≤d)
    (q : U → Γ → ℝ) (hq : ∀ u g,0≤q u g) (hQ : ∀ u,∑ g,q u g≤1/8)
    (s : U → Color → ℝ) (hs : ∀ u j,0≤s u j)
    (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
    (hnoshort : ∀ x l,0<l → l<2*d+1 → (π^l) x≠x)
    (hF : permutationConflictGraph π (3*d)≤F)
    (hn : 0<Fintype.card V) (hm : 0<Fintype.card U)
    (j : Color) (pH : ℝ) (hj : ∀ u,s u j=pH)
    (k : ℕ) (hk : 2≤k) (θ α c ω b t : ℝ) (hc : 0≤c) (ht : 0<t)
    (hsize : ω*Fintype.card V≤(Fintype.card U:ℝ))
    (htsmall : t≤pH^2*ω*Fintype.card V/2)
    (hpotential : 1-b≤
      (FiniteLaw.pi (rawWheelLaw ρ hρ hρ1 d hd q hq hQ s hs hS)).probability
        (fun σ=>∀ x y : V,x≠y → ¬F.Adj x y → ∀ u : U,
          c≤rootedInducedSurvivalSum P
            (fun S : OrdinaryIsolatorCandidate P F (rawWheelSpokes π d σ j)
              k θ α x y u=>S.val) s(x,y) (fun e=>σ (Sum.inl e)))) :
    1-b-(Fintype.card {a : V×V // a.1≠a.2 ∧ ¬F.Adj a.1 a.2}:ℝ)*
      (2*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*(2*Fintype.card U))))≤
      (FiniteLaw.pi (rawWheelLaw ρ hρ hρ1 d hd q hq hQ s hs hS)).probability
        (fun σ=>∀ x y : V,x≠y → ¬F.Adj x y →
          c*(pH^2*ω/2)≤ordinaryIsolatorPotential P F (rawWheelSpokes π d σ j)
            k θ α x y (fun e=>σ (Sum.inl e)) ∧
          ((rawWheelGraph P σ).Adj x y →
            c*(pH^2*ω/2)*(Fintype.card V:ℝ)^(k-1)≤
              Fintype.card (OrdinaryIsolatorConfiguration P (rawWheelGraph P σ\F) F
                (rawWheelSpokes π d σ j) k θ α x y))) := by
  let μ := FiniteLaw.pi (rawWheelLaw ρ hρ hρ1 d hd q hq hQ s hs hS)
  let E (σ : RawWheelOutcome V U Γ Color) := ∀ x y : V,x≠y → ¬F.Adj x y → ∀ u : U,
    c≤rootedInducedSurvivalSum P
      (fun S : OrdinaryIsolatorCandidate P F (rawWheelSpokes π d σ j) k θ α x y u=>S.val)
      s(x,y) (fun e=>σ (Sum.inl e))
  have hh := rawWheelCommonHubs_event π F ρ hρ hρ1 d hd q hq hQ s hs hS
    hnoshort hF hm j pH hj t ht
  have hi := finiteLaw_good_intersection μ E _ _ hh
  have hbound := (sub_le_sub_right hpotential _).trans hi
  apply hbound.trans
  apply finiteLaw_probability_mono
  intro σ hσ x y hxy hfxy
  have hhub : (pH^2*ω/2)*Fintype.card V≤
      (Fintype.card {u : U // rawWheelSpokes π d σ j x u ∧ rawWheelSpokes π d σ j y u}:ℝ) := by
    have hhlo := (abs_lt.mp (hσ.2 x y hxy hfxy)).1
    have hsz := mul_le_mul_of_nonneg_left hsize (sq_nonneg pH)
    nlinarith only [hhlo,hsz,htsmall]
  constructor
  · exact ordinary_isolator_potential_lower P F (rawWheelSpokes π d σ j) k θ α x y
      (fun e=>σ (Sum.inl e)) hn c (pH^2*ω/2) hc hhub (fun u _ _=>hσ.1 x y hxy hfxy u)
  · intro hroot
    exact ordinary_isolator_total_count_lower P F (rawWheelSpokes π d σ j) k hk θ α x y
      (fun e=>σ (Sum.inl e)) hn hroot c (pH^2*ω/2) hc hhub (fun u _ _=>hσ.1 x y hxy hfxy u)

end Oberwolfach
