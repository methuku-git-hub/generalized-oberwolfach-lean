module

public import Oberwolfach.OrdinaryTriangleFiniteCoverSeparateLoadFineEvent
public import Oberwolfach.OrdinaryTrianglePrescribedJointProbability

@[expose] public section
/-! High probability for finite prescribed-edge and root coverage by triangle
wheels, under the original parent host and sampling hypotheses. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
set_option synthInstance.maxSize 32768
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_triangle_finite_cover_separate_load_fine_capped_high_probability (α p ω cap:ℝ)
    (hα:0<α) (hp:0<p) (hp1:p≤1) (hω:0<ω) (hcap:0<cap):
    ∃κ:ℝ,0<κ ∧ κ≤1 ∧ κ≤cap ∧ ∀aLoad:ℝ,0<aLoad→aLoad≤κ→∀Dmax d q₀:ℕ,∀hd:2≤d,∃N:ℕ,
    ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [LinearOrder V] [LinearOrder U],
    ∀(P F:SimpleGraph V) (π:Equiv.Perm V) (J:Finset U),N≤Fintype.card V →
      (J.card:ℝ)≤κ*Fintype.card V → ω*Fintype.card V≤((Finset.univ\J).card:ℝ) → Fintype.card U≤Fintype.card V →
      (∀v,(cycleThreshold 3+α)*Fintype.card V≤(P.degree v:ℝ)) →
      (∀v,F.degree v≤Dmax) → permutationConflictGraph π (3*d)≤F →
      (∀v k,0<k→k<2*d+1→(π^k) v≠v) →
    ∀(pR pH D ε:ℝ) (hpR:p≤pR) (hpR1:pR≤1),p≤pH → pH≤1 →
      (Fintype.card V:ℝ)/2≤D → 0≤ε → ε≤κ →
      (∀v,|(P.degree v:ℝ)-D|≤ε*Fintype.card V) → pR*D=2*Fintype.card U*pH →
    ∀(q:U→Γ→ℝ) (hq:∀u g,0≤q u g) (hQ:∀u,∑g,q u g≤1/8)
      (s:U→Color→ℝ) (hs:∀u j,0≤s u j)
      (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑g,q u g))
      (j:Color),(∀u,s u j=pH) →
    1-1/(Fintype.card V:ℝ)^q₀≤
      (FiniteLaw.pi (rawWheelLaw (fun _=>pR) (fun _=>hp.le.trans hpR) (fun _=>hpR1) d hd q hq hQ s hs hS)).probability
        (OrdinaryTriangleFiniteCoverSeparateLoadFineEvent κ aLoad P F J π d j):=by
  obtain ⟨a₀,ε₀,ρhub,η,θ,ρ,ha₀,hε₀,hρhub,hη,hθ,hρ,hjoint⟩:=
    ordinary_triangle_prescribed_joint_probability α p ω hα hp hp1 hω
  let γ:=min α 1
  have hγ:0<γ:=lt_min hα zero_lt_one
  obtain ⟨κ₀,hκ₀,hκa₀,hκε₀,hκθ₀,hκhub₀,hκρ₀,hκbal₀,hκscale₀⟩:=
    ordinary_triangle_parameter_selection a₀ ε₀ θ ρhub ρ ω p η γ ha₀ hε₀ hθ hρhub hρ hω hp hη hγ
  let κ:=min κ₀ cap
  have hκ:0<κ:=lt_min hκ₀ hcap
  have hκ₀le:κ≤κ₀:=min_le_left _ _
  have hκcap:κ≤cap:=min_le_right _ _
  have hκa:κ≤a₀:=hκ₀le.trans hκa₀
  have hκε:κ≤ε₀:=hκ₀le.trans hκε₀
  have hκθ:κ≤θ:=hκ₀le.trans hκθ₀
  have hκhub:13*κ≤ρhub:=by linarith
  have hκρ:54*κ≤ρ:=by linarith
  have hκbal:3*κ≤2*ω*p*η:=by linarith
  have hκscale:48*κ≤p^6*γ*min 1 ω:=by linarith
  have hγ1:γ≤1:=min_le_right _ _
  have hω1:min (1:ℝ) ω≤1:=min_le_left _ _
  have hω0:0≤min (1:ℝ) ω:=by positivity
  have hp6:p^6≤1:=pow_le_one₀ hp.le hp1
  have hproduct:p^6*γ*min (1:ℝ) ω≤1:=by
    calc
      _≤(1:ℝ)*1*1:=by gcongr
      _=1:=by ring
  have hκ1:κ≤1:=by nlinarith only [hκscale,hproduct]
  refine ⟨κ,hκ,hκ1,hκcap,?_⟩
  intro aLoad haLoad haLoadκ Dmax d q₀ hd
  obtain ⟨Nj,hj⟩:=hjoint aLoad haLoad (haLoadκ.trans hκa) Dmax d q₀ hd
  obtain ⟨Ns,hNs⟩:=exists_nat_gt (2*((Dmax:ℝ)+2*(3*d:ℕ))/ρ)
  refine ⟨max 1 (max Nj Ns),?_⟩
  intro V U Γ Color _ _ _ _ _ _ P F π J hn hJ hB hU hP hF hclose hnoshort
    pR pH D ε hpR hpR1 hpH hpH1 hD hε hεsmall hreg hidentity q hq hQ s hs hS j hjp
  have hnpos:0<Fintype.card V:=by omega
  have hnsize:(Ns:ℝ)≤Fintype.card V:=by exact_mod_cast (show Ns≤Fintype.card V by omega)
  have hconst:((Dmax:ℝ)+2*(3*d:ℕ))≤ρ*Fintype.card V/2:=by
    have hh:= (div_lt_iff₀ hρ).mp hNs
    have ht:=mul_le_mul_of_nonneg_left hnsize hρ.le
    linarith only [hh,ht]
  have hprob:=hj V U Γ Color P F π (Finset.univ\J) (by omega) hB hU hP hF hclose hnoshort
    pR pH D ε hpR hpR1 hpH hpH1 hD hε (hεsmall.trans hκε) hreg hidentity q hq hQ s hs hS j hjp
  apply hprob.trans
  apply finiteLaw_probability_mono
  intro σ hσ
  exact ordinary_triangle_joint_implies_finite_cover_separate_load_fine P F π d Dmax κ aLoad p γ ω η θ ρ ρhub pR pH D ε
    hκ haLoad haLoadκ hp hγ hω hη.le hκscale hκhub hκρ hκθ hκbal hε hεsmall (hp.le.trans hpR) hpR1 hpH hpH1
    hnpos hreg hidentity hconst J hJ hB j σ hσ.1 hσ.2.1 hσ.2.2
end Oberwolfach
