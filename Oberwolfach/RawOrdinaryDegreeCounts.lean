module

public import Oberwolfach.RawOrdinaryHubCounts

@[expose] public section

/-! Ordinary spoke degrees under the original interval law, on a single event
for every ambient vertex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [DecidableEq V] [DecidableEq U]

theorem rawWheelSpokeDegrees_event
    (π : Equiv.Perm V)
    (ρ : Sym2 V → ℝ) (hρ : ∀ e,0≤ρ e) (hρ1 : ∀ e,ρ e≤1)
    (d : ℕ) (hd : 2≤d)
    (q : U → Γ → ℝ) (hq : ∀ u g,0≤q u g) (hQ : ∀ u,∑ g,q u g≤1/8)
    (s : U → Color → ℝ) (hs : ∀ u j,0≤s u j)
    (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
    (hnoshort : ∀ x k,0<k → k<2*d+1 → (π^k) x≠x)
    (hm : 0<Fintype.card U) (j : Color) (pH : ℝ) (hj : ∀ u,s u j=pH)
    (t : ℝ) (ht : 0<t) :
    1-(Fintype.card V:ℝ)*
      (2*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*Fintype.card U)))≤
      (FiniteLaw.pi (rawWheelLaw ρ hρ hρ1 d hd q hq hQ s hs hS)).probability
        (fun σ=>∀ v : V,
          |(Fintype.card {u : U // rawWheelSpokes π d σ j v u}:ℝ)-pH*Fintype.card U|<t) := by
  have hh := rawIntervalCommonHubs_common_event π d hd q hq hQ s hs hS hnoshort hm j pH hj
    (fun v : V=>({v}:Finset V))
    (by intro v x hx y hy hxy; simp only [Finset.mem_singleton] at hx hy; exact (hxy (hx.trans hy.symm)).elim)
    (fun v=>Finset.singleton_nonempty v) 1 (by omega) (by intro v;simp) t ht
  have hproj := finiteLaw_pi_injective_projection_event
    (rawWheelLaw ρ hρ hρ1 d hd q hq hQ s hs hS) Sum.inr Sum.inr_injective
    (fun ω=>∀ v : V,|(Fintype.card {u : U // ∀ z∈({v}:Finset V),rawIntervalFamilyState π d ω (z,u)=some (Sum.inr j)}:ℝ)-
      pH^({v}:Finset V).card*Fintype.card U|<t)
  erw [← hproj] at hh
  simp only [Finset.card_singleton,pow_one,Nat.cast_one,one_mul] at hh
  apply hh.trans
  apply finiteLaw_probability_mono
  intro σ hσ v
  convert hσ v using 1
  congr 3
  exact Fintype.card_congr (Equiv.subtypeEquivRight (fun u=>by
    simp only [Finset.mem_singleton,forall_eq,rawWheelSpokes]))

end Oberwolfach
