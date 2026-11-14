module

public import Oberwolfach.ExpandedUnassignedRimInvCardSq
public import Oberwolfach.FiniteHighEventsCommon

@[expose] public section
/-! A common sample controls any fixed family of at most |V| physical rows. -/
set_option autoImplicit false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem raw_expanded_unassigned_rim_degrees_family_highProbability :
    ∃ N:ℕ,∀ (V:Type) [Fintype V] [LinearOrder V],N≤Fintype.card V→
    ∀ (U Γ Color:Type) [Fintype U] [Fintype Γ] [Fintype Color] [DecidableEq U],
    ∀ (G:SimpleGraph V) (I:Type) (T:Finset I) (A:I→Finset V) (hT:T.card≤Fintype.card V)
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (d:ℕ) (hd:2≤d) (q:U→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀ u j,0≤s u j) (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
    (F:RawMarkedOutcome V U Γ Color→Type) [∀ a,Fintype (F a)] (ν:∀ a,FiniteLaw (F a)),
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)
    let f:=fun (ω:∀ e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e) e=>rawExpandedMarkedCollapse e (ω e)
    1-1/(Fintype.card V:ℝ)≤(μ.sigma (fun ω=>ν (f ω))).probability (fun z=>∀ i∈T,∀ x,
      |(((G.neighborFinset x∩A i).filter (fun y=>(z.1 (Sum.inl s(x,y))).1=4)).card:ℝ)-
        u*(G.neighborFinset x∩A i).card|<(Fintype.card V:ℝ)^(3/4:ℝ)) :=by
  obtain ⟨N,hN⟩:=raw_expanded_unassigned_rim_degree_highProbability_invCardSq
  refine ⟨max N 1,?_⟩
  intro V _ _ hn U Γ Color _ _ _ _ G I T A hT p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS F _ ν μ f
  have hnN:N≤Fintype.card V:=le_trans (le_max_left _ _) hn
  have hnpos:(0:ℝ)<Fintype.card V:=by exact_mod_cast (show 0<Fintype.card V by omega)
  let E:=fun i (z:Σω:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e,F (f ω))=>
    ∀x,|(((G.neighborFinset x∩A i).filter (fun y=>(z.1 (Sum.inl s(x,y))).1=4)).card:ℝ)-
      u*(G.neighborFinset x∩A i).card|<(Fintype.card V:ℝ)^(3/4:ℝ)
  have hEach:∀i∈T,1-1/(Fintype.card V:ℝ)^2≤(μ.sigma (fun ω=>ν (f ω))).probability (E i):=by
    intro i hi
    exact hN V hnN U Γ Color G (A i) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS F ν
  have hh:=finiteLaw_high_events_common (μ.sigma (fun ω=>ν (f ω))) T E
    (fun _=>1/(Fintype.card V:ℝ)^2) hEach
  have hbound : (T.card:ℝ)/(Fintype.card V:ℝ)^2≤1/(Fintype.card V:ℝ):=by
    have ht:(T.card:ℝ)≤Fintype.card V:=by exact_mod_cast hT
    rw [div_le_div_iff₀ (sq_pos_of_pos hnpos) hnpos]
    nlinarith
  simp only [Finset.sum_const,nsmul_eq_mul] at hh
  dsimp [E] at hh
  simp only [mul_one_div] at hh
  linarith
end Oberwolfach
