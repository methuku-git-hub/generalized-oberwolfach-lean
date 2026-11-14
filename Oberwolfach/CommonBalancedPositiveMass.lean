module

public import Oberwolfach.CommonBalancedOrientationEvent
public import Oberwolfach.JointEventPolynomialMargins

@[expose] public section
/-! The additional balanced-orientation event fits into the same fixed
failure budget at a later order threshold, with one positive-mass outcome. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem common_balanced_positive_mass
    (a A B:ℝ) (ha:a<1) (q:ℕ) (hq:0<q) (r:ℝ) (hr:0<r)
    (α:ℝ) (hα:0<α):
    ∃N:ℕ,1≤N ∧ ∀(V:Type) [Fintype V] [LinearOrder V],N≤Fintype.card V→
      ∀(G:SimpleGraph V),(∀v,Even (G.degree v))→
      (∀v,(1/2+α)*(Fintype.card V:ℝ)≤G.degree v)→
      ∀{Ω:Type} [Fintype Ω] (μ:FiniteLaw Ω) (bits:Ω→Sym2 V→Bool),
      (∀E:(Sym2 V→Bool)→Prop,μ.probability (fun z=>E (bits z))=
        (FiniteLaw.pi (fun _:Sym2 V=>FiniteLaw.fairCoin)).probability E)→
      ∀Good:Ω→Prop,
      1-a-A*(Fintype.card V:ℝ)^(-(q:ℝ))-B*(Fintype.card V:ℝ)^(-r)≤μ.probability Good→
      ∃z,Good z ∧ BalancedSampleOrientationEvent G α (bits z) ∧ 0<μ.mass z:=by
  have hqR:0<(q:ℝ):=by exact_mod_cast hq
  obtain ⟨N,hN,hMass⟩:=joint_event_positive_mass_witness a (A+1) B q r ha hqR hr
  let Nbal:=Classical.choose (balancedOrientation_highProbability_pow.{0} hα q)
  refine ⟨max N Nbal,le_trans hN (le_max_left _ _),?_⟩
  intro V _ _ hn G heven hmin Ω _ μ bits hbits Good hGood
  have hN':N≤Fintype.card V:=le_trans (le_max_left _ _) hn
  have hbal:Nbal≤Fintype.card V:=le_trans (le_max_right _ _) hn
  have hevent:=finiteLaw_common_balanced_orientation μ bits hbits α hα q G hbal heven hmin Good
    (a+A*(Fintype.card V:ℝ)^(-(q:ℝ))+B*(Fintype.card V:ℝ)^(-r)) (by linarith)
  have hpow:(Fintype.card V:ℝ)^(-(q:ℝ))=1/(Fintype.card V:ℝ)^q:=by
    rw [Real.rpow_neg (Nat.cast_nonneg _),Real.rpow_natCast,one_div]
  have hsmall:1-a-(A+1)*(Fintype.card V:ℝ)^(-(q:ℝ))-B*(Fintype.card V:ℝ)^(-r)≤
      μ.probability (fun z=>Good z ∧ BalancedSampleOrientationEvent G α (bits z)):=by
    rw [←hpow] at hevent
    nlinarith
  obtain ⟨z,hz,hmass⟩:=hMass (Fintype.card V) hN' μ
    (fun z=>Good z ∧ BalancedSampleOrientationEvent G α (bits z)) hsmall
  exact ⟨z,hz.1,hz.2,hmass⟩
end Oberwolfach
