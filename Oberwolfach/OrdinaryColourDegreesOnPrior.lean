module

public import Oberwolfach.OrdinaryExpandedAllColourDegreeBundle
public import Oberwolfach.MarkedExpandedDegreeArbitraryFailure

@[expose] public section
/-! The physical colour-degree tests can be added to any earlier event on
the same expanded sample, with an arbitrarily small fixed failure budget. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 15000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_colour_degrees_on_prior_arbitrary_failure (δ:ℝ) (hδ:0<δ):
    ∃N:ℕ,1≤N ∧ ∀(V:Type) [Fintype V] [LinearOrder V],N≤Fintype.card V→
    ∀(U Γ Color:Type) [Fintype U] [Fintype Γ] [Fintype Color] [DecidableEq U]
    (P:SimpleGraph V)
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1) (d:ℕ) (hd:2≤d)
    (q:U→Γ→ℝ) (hq:∀w g,0≤q w g) (hQ:∀w,∑g,q w g≤1/8)
    (s:U→Color→ℝ) (hs:∀w j,0≤s w j) (hS:∀w,∑j,s w j≤ intervalUncoveredProbability d (∑g,q w g))
    {R:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)→Type}
    [∀σ,Fintype (R σ)] (ν:∀σ,FiniteLaw (R σ)) (E:(Σσ,R σ)→Prop) (εE:ℝ),
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS);
    1-εE≤(μ.sigma ν).probability E→
    1-(εE+δ)≤(μ.sigma ν).probability (fun z=>E z ∧ ∀a x,
      |(sampledColourDegree P (fun e=>(z.1 (Sum.inl e)).1) a x:ℝ)-
        markedExpandedPhysicalProbability p k p₂ k₂ u a*P.degree x|<(Fintype.card V:ℝ)^(3/5:ℝ)) :=by
  obtain ⟨N,hN⟩:=eventually_stretchedExp_le_inv_pow (36:ℝ) 1
    (c:=2) (p:=1/5) (by norm_num) (by norm_num) 1
  obtain ⟨Nsmall,hNsmallPos,hsmall⟩:=joint_event_polynomial_margin (1-δ) 1 0 1 1 (by linarith) (by norm_num) (by norm_num)
  refine ⟨max N Nsmall,by omega,?_⟩
  intro V _ _ hn U Γ Color _ _ _ _ P p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS R _ ν E εE μ hE
  have hnpos:(0:ℝ)<Fintype.card V:=by exact_mod_cast (show 0<Fintype.card V by omega)
  have hb:=hN (Fintype.card V) (by omega)
  simp only [Real.rpow_one,pow_one] at hb
  have hsm:=hsmall (Fintype.card V) (by omega)
  have hpow:(Fintype.card V:ℝ)^(-(1:ℝ))=1/(Fintype.card V:ℝ):=by
    rw [Real.rpow_neg (Nat.cast_nonneg _),Real.rpow_one,one_div]
  rw [hpow] at hsm
  have hh:=ordinary_expanded_all_colour_degrees_and_prior P p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS
    ((Fintype.card V:ℝ)^(3/5:ℝ)) (by positivity) ν E εE hE
  rw [threeFifths_tail_exponent hnpos] at hh
  have hproj: (μ.sigma ν).probability (fun z=>E z ∧ (∀a x,
      |((∑y,sampledColourOrientation P (fun e=>z.1 (Sum.inl e)) a x y:ℕ):ℝ)-markedExpandedPhysicalProbability p k p₂ k₂ u a/2*P.degree x|<(Fintype.card V:ℝ)^(3/5:ℝ) ∧
      |((∑y,sampledColourOrientation P (fun e=>z.1 (Sum.inl e)) a y x:ℕ):ℝ)-markedExpandedPhysicalProbability p k p₂ k₂ u a/2*P.degree x|<(Fintype.card V:ℝ)^(3/5:ℝ) ∧
      |(sampledColourDegree P (fun e=>(z.1 (Sum.inl e)).1) a x:ℝ)-markedExpandedPhysicalProbability p k p₂ k₂ u a*P.degree x|<(Fintype.card V:ℝ)^(3/5:ℝ))) ≤
    (μ.sigma ν).probability (fun z=>E z ∧ ∀a x,
      |(sampledColourDegree P (fun e=>(z.1 (Sum.inl e)).1) a x:ℝ)-markedExpandedPhysicalProbability p k p₂ k₂ u a*P.degree x|<(Fintype.card V:ℝ)^(3/5:ℝ)):=by
    apply finiteLaw_probability_mono
    intro z hz
    exact ⟨hz.1,fun a x=>(hz.2 a x).2.2⟩
  linarith only [hh,hb,hsm,hproj]
end Oberwolfach
