module

public import Oberwolfach.MarkedExpandedDegreeEvent

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem raw_expanded_marked_colour_degrees_999 :
    ∃ N:ℕ,∀ (V:Type) [Fintype V] [LinearOrder V],
    N≤Fintype.card V→∀ (U Γ Color:Type) [Fintype U] [Fintype Γ] [Fintype Color] [DecidableEq U]
    (G Z:SimpleGraph V)
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (d:ℕ) (hd:2≤d) (q:U→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀ u j,0≤s u j) (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
    (F:RawMarkedOutcome V U Γ Color→Type) [∀ a,Fintype (F a)] (ν:∀ a,FiniteLaw (F a)),
    let ρ:=markedExpandedPhysicalProbability p k p₂ k₂ u
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)
    let f:=fun (ω:∀ e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e) e=>rawExpandedMarkedCollapse e (ω e)
    (999:ℝ)/1000≤(μ.sigma (fun ω=>ν (f ω))).probability (fun z=>∀ a x,
      |((∑ y,sampledColourOrientation G (fun e=>z.1 (Sum.inl e)) a x y:ℕ):ℝ)-ρ a/2*G.degree x|<(Fintype.card V:ℝ)^(3/5:ℝ) ∧
      |((∑ y,sampledColourOrientation G (fun e=>z.1 (Sum.inl e)) a y x:ℕ):ℝ)-ρ a/2*G.degree x|<(Fintype.card V:ℝ)^(3/5:ℝ) ∧
      |(sampledColourDegree Z (fun e=>(z.1 (Sum.inl e)).1) a x:ℝ)-ρ a*Z.degree x|<(Fintype.card V:ℝ)^(3/5:ℝ)) := by
  obtain ⟨N,hN⟩:=eventually_stretchedExp_le_inv_pow (36:ℝ) 1
    (c:=2) (p:=1/5) (by norm_num) (by norm_num) 1
  refine ⟨max N 1000,?_⟩
  intro V _ _ hn U Γ Color _ _ _ _ G Z p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS F _ ν
  have hn1000:1000≤Fintype.card V:=le_trans (le_max_right _ _) hn
  have hnpos:(0:ℝ)<Fintype.card V:=by exact_mod_cast (show 0<Fintype.card V by omega)
  have hb:=hN (Fintype.card V) (le_trans (le_max_left _ _) hn)
  simp only [Real.rpow_one, pow_one] at hb
  have hh:=raw_expanded_marked_all_colour_degrees G Z p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS F ν
    (t:=(Fintype.card V:ℝ)^(3/5:ℝ)) (by positivity)
  rw [threeFifths_tail_exponent hnpos] at hh
  have hsmall:(1:ℝ)/(Fintype.card V:ℝ)≤1/1000:=by
    apply (div_le_iff₀ hnpos).2
    have : (1000:ℝ)≤Fintype.card V:=by exact_mod_cast hn1000
    linarith
  linarith only [hh,hb,hsmall]
end Oberwolfach
