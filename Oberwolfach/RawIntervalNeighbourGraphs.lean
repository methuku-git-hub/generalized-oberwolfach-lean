module

public import Oberwolfach.RawIntervalNeighbourCounts
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum

@[expose] public section

/-! The fixed-domain count event expressed as sizes and degrees into the
actual random common neighbourhoods. All ambient roots are included. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [DecidableEq V] [DecidableEq U]

def rawIntervalHubNeighbourhood (π : Equiv.Perm V) (d : ℕ)
    (σ : RawIntervalFamilyOutcome V U Γ Color) (j : Color) (J : Finset U) : Finset V :=
  Finset.univ.filter (fun v=>∀ u∈J,rawIntervalFamilyState π d σ (v,u)=some (Sum.inr j))

theorem rawIntervalNeighbourCount_card (π : Equiv.Perm V) (d : ℕ)
    (σ : RawIntervalFamilyOutcome V U Γ Color) (j : Color) (A : Finset V) (J : Finset U) :
    rawIntervalNeighbourCount π d σ j A J=((A∩rawIntervalHubNeighbourhood π d σ j J).card:ℝ) := by
  unfold rawIntervalNeighbourCount rawIntervalHubNeighbourhood
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const,nsmul_eq_mul,mul_one]
  congr 2
  ext v
  simp

variable (π : Equiv.Perm V) (d : ℕ) (hd : 2≤d)
    (q : U → Γ → ℝ) (hq : ∀ u g,0≤q u g) (hQ : ∀ u,∑ g,q u g≤1/8)
    (s : U → Color → ℝ) (hs : ∀ u j,0≤s u j)
    (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
local notation "μfamily" => rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS

theorem rawIntervalHubNeighbourhood_common_event
    (hnoshort : ∀ x k,0<k → k<2*d+1 → (π^k) x≠x)
    (hn : 0<Fintype.card V) (P : SimpleGraph V) (j : Color) (pH : ℝ) (hj : ∀ u,s u j=pH)
    {I : Type} [Fintype I] (J : I → Finset U)
    (hJ : ∀ i,(J i).Nonempty) (k : ℕ) (hk : 0<k) (hsize : ∀ i,(J i).card≤k)
    (t : ℝ) (ht : 0<t) :
    1-((Fintype.card I:ℝ)*(Fintype.card V+1))*
      (2*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*((k:ℝ)*Fintype.card V))))≤
      (FiniteLaw.pi μfamily).probability (fun σ=>∀ i,
        let T := rawIntervalHubNeighbourhood π d σ j (J i)
        (|(T.card:ℝ)-pH^(J i).card*Fintype.card V|<t) ∧
        (∀ v,|((P.neighborFinset v∩T).card:ℝ)-pH^(J i).card*P.degree v|<t)) := by
  let A : I×Option V → Finset V := fun a=>match a.2 with
    | none=>Finset.univ
    | some v=>P.neighborFinset v
  let JJ : I×Option V → Finset U := fun a=>J a.1
  have hh := rawIntervalNeighbourCount_common_event π d hd q hq hQ s hs hS hnoshort hn j A JJ
    (fun a=>hJ a.1) k hk (fun a=>hsize a.1) t ht
  have hcard : (Fintype.card (I×Option V):ℝ)=(Fintype.card I:ℝ)*(Fintype.card V+1) := by
    simp only [Fintype.card_prod,Fintype.card_option,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
  rw [hcard] at hh
  apply hh.trans
  apply finiteLaw_probability_mono
  intro σ hσ i
  have hprod : (∏ u∈J i,s u j)=pH^(J i).card := by simp only [hj,Finset.prod_const]
  constructor
  · have hi := hσ (i,none)
    simpa only [A,JJ,rawIntervalNeighbourCount_card,Finset.univ_inter,Finset.card_univ,hprod,mul_comm] using hi
  · intro v
    have hi := hσ (i,some v)
    simpa only [A,JJ,rawIntervalNeighbourCount_card,SimpleGraph.card_neighborFinset_eq_degree,hprod,mul_comm] using hi

end Oberwolfach
