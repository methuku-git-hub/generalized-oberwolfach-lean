module

public import Oberwolfach.ExpandedUnassignedRimDegree

@[expose] public section
/-! High probability of all restricted unassigned physical degrees. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem raw_expanded_unassigned_rim_degree_highProbability :
    ∃ N:ℕ,∀ (V:Type) [Fintype V] [LinearOrder V],N≤Fintype.card V→
    ∀ (U Γ Color:Type) [Fintype U] [Fintype Γ] [Fintype Color] [DecidableEq U],
    ∀ (G:SimpleGraph V) (A:Finset V)
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (d:ℕ) (hd:2≤d) (q:U→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀ u j,0≤s u j) (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
    (F:RawMarkedOutcome V U Γ Color→Type) [∀ a,Fintype (F a)] (ν:∀ a,FiniteLaw (F a)),
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)
    let f:=fun (ω:∀ e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e) e=>rawExpandedMarkedCollapse e (ω e)
    (999:ℝ)/1000≤(μ.sigma (fun ω=>ν (f ω))).probability (fun z=>∀ x,
      |(((G.neighborFinset x∩A).filter (fun y=>(z.1 (Sum.inl s(x,y))).1=4)).card:ℝ)-
        u*(G.neighborFinset x∩A).card|<(Fintype.card V:ℝ)^(3/4:ℝ)):=by
  obtain ⟨N,hN⟩:=eventually_stretchedExp_le_inv_pow (2:ℝ) 1 (c:=2) (p:=1/2) (by norm_num) (by norm_num) 1
  refine ⟨max N 1000,?_⟩
  intro V _ _ hn U Γ Color _ _ _ _ G A p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS F _ ν
  have hn1000:1000≤Fintype.card V:=le_trans (le_max_right _ _) hn
  have hnpos:(0:ℝ)<Fintype.card V:=by exact_mod_cast (show 0<Fintype.card V by omega)
  have hb:=hN (Fintype.card V) (le_trans (le_max_left _ _) hn)
  simp only [Real.rpow_one,pow_one] at hb
  have ht:0<(Fintype.card V:ℝ)^(3/4:ℝ):=by positivity
  have hh:=raw_expanded_unassigned_rim_degree_event G A p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS F ν _ ht
  have heq:((Fintype.card V:ℝ)^(3/4:ℝ))^2=(Fintype.card V:ℝ)^(1/2:ℝ)*(Fintype.card V:ℝ):=by
    calc
      _ = (Fintype.card V:ℝ)^(3/2:ℝ) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hnpos.le];norm_num
      _ = (Fintype.card V:ℝ)^(1/2:ℝ)*(Fintype.card V:ℝ)^(1:ℝ) := by rw [← Real.rpow_add hnpos];norm_num
      _ = _ := by rw [Real.rpow_one]
  have harg: -2*((Fintype.card V:ℝ)^(3/4:ℝ))^2/(Fintype.card V:ℝ) = -2*(Fintype.card V:ℝ)^(1/2:ℝ):=by rw [heq];field_simp
  rw [harg] at hh
  have hsmall:(1:ℝ)/(Fintype.card V:ℝ)≤1/1000:=by
    apply (div_le_iff₀ hnpos).2
    have : (1000:ℝ)≤Fintype.card V:=by exact_mod_cast hn1000
    linarith
  have hnum:(999:ℝ)/1000≤1-2*(Fintype.card V:ℝ)*Real.exp (-2*(Fintype.card V:ℝ)^(1/2:ℝ)):=by
    convert sub_le_sub_left (hb.trans hsmall) 1 using 1 <;> norm_num
  exact hnum.trans hh
end Oberwolfach
