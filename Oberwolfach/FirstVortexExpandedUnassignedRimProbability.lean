module

public import Oberwolfach.FiniteCoordinateEvents
public import Oberwolfach.VortexExpandedUnassignedRimLocalEvent

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem raw_expanded_first_vortex_unassigned_rim_high_probability
    (ε failure:ℝ) (hε:0<ε) (hεq:ε≤1/4) (hfailure:0<failure):
    ∃m₀:ℕ,1≤m₀ ∧ ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [DecidableEq U], ∀(G:SimpleGraph V) (D m:ℕ) (β:ℝ)
      (Q:Vortex U G D β ε m),
    (m₀:ℝ)≤ε*m/2 →
    ∀ (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (d:ℕ) (hd:2≤d) (q:U→Γ→ℝ) (hq:∀w g,0≤q w g) (hQ:∀w,∑g,q w g≤1/8)
    (s:U→Color→ℝ) (hs:∀w j,0≤s w j) (hS:∀w,∑j,s w j≤ intervalUncoveredProbability d (∑g,q w g))
    (F:RawMarkedOutcome V U Γ Color→Type) [∀a,Fintype (F a)] (ν:∀a,FiniteLaw (F a)),
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)
    let f:=fun (ω:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e) e=>rawExpandedMarkedCollapse e (ω e)
    1-failure≤(μ.sigma (fun ω=>ν (f ω))).probability (fun z=>∀v,
      |(((G.neighborFinset v∩Q.extendedVertices 1).filter (fun x=>(z.1 (Sum.inl s(v,x))).1=4)).card:ℝ)-
        u*(G.neighborFinset v∩Q.extendedVertices 1).card|<(Fintype.card V:ℝ)^(3/4:ℝ)) :=by
  obtain ⟨m₀,hm₀,hRim⟩:=vortex_expanded_unassigned_rim_local_common_event ε failure hε hεq hfailure
  refine ⟨m₀,hm₀,?_⟩
  intro V U Γ Color _ _ _ _ _ _ G D m β Q hsize p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS F _ ν μ f
  have ht:∀i∈({1}:Finset ℕ),1 ≤ i ∧ i ≤ Q.length:=by
    intro i hi
    have hieq:i=1:=by simpa using hi
    subst i
    exact ⟨le_rfl,Q.length_pos⟩
  have hh:=hRim V U Γ Color G D m β Q {1} hsize ht p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS F ν (fun _=>True) 0 (by simp [finiteLaw_probability_true])
  have hcard:((Q.extendedVertices 1).card:ℝ)≤Fintype.card V:=by exact_mod_cast Finset.card_le_univ (Q.extendedVertices 1)
  have hpow:((Q.extendedVertices 1).card:ℝ)^(3/4:ℝ)≤(Fintype.card V:ℝ)^(3/4:ℝ):=
    Real.rpow_le_rpow (by positivity) hcard (by norm_num)
  have hzero:Q.extendedVertices 0=Finset.univ:=by rw [Q.extendedVertices_eq (Nat.zero_le _),Q.initial]
  simp only [sub_zero] at hh
  apply le_trans hh
  apply finiteLaw_probability_mono
  intro z hz v
  have hx:=hz.2 1 (by simp) v (by rw [show 1-1=0 by omega,hzero];simp)
  exact lt_of_lt_of_le hx hpow
end Oberwolfach
