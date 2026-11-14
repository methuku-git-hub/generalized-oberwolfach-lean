module

public import Oberwolfach.OrdinaryWheelAbsorberHighProbabilityBeforeSpacing
public import Oberwolfach.OrdinaryUniformProtectedReservoirEvent

@[expose] public section
/-! The uniform terminal reservoir exists with high probability on the
actual sampled host for every ordinary wheel length r≥3. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
set_option synthInstance.maxSize 32768
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_uniform_protected_reservoir_high_probability_before_spacing
    (r:ℕ) (hr:3≤r) (α pmin smin ω:ℝ)
    (hα:0<α) (hpmin:0<pmin) (hsmin:0<smin) (hsmin1:smin≤1) (hω:0<ω):
    ∃ εabs εtrans:ℝ,0<εabs ∧ 0<εtrans ∧ ∀(d:ℕ) (hd:2≤d),∀L:ℝ,0≤L→∃εsample:ℝ,0<εsample ∧ ∀ m:ℕ,∃ a₀ b₀ t:ℕ,1≤t ∧ ∀ tterm f:ℕ,∃ N:ℕ,
    ∀ (V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [DecidableEq V] [DecidableEq U],
    N≤Fintype.card V → Fintype.card U≤Fintype.card V → ω*Fintype.card V≤(Fintype.card U:ℝ) →
    ∀ (P F:SimpleGraph V) (π:Equiv.Perm V),
    permutationConflictGraph π (3*d)≤F →
    (∀ x k,0<k→k<2*d+1→(π^k) x≠x) →
    (∀ v,(F.degree v:ℝ)≤L) →
    (∀ v,(cycleThreshold r+α)*Fintype.card V≤(P.degree v:ℝ)) →
    ∀ D:ℝ,(Fintype.card V:ℝ)/2≤D → D≤2*Fintype.card V →
    (∀ v,|(P.degree v:ℝ)-D|≤εsample*Fintype.card V) →
    ∀ (p:ℝ) (hp:pmin≤p) (hp1:p≤1),
    ∀ (q:U→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
      (s:U→Color→ℝ) (hs:∀ u j,0≤s u j)
      (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g)) (j:Color),
    (∀ u,smin≤s u j) → (∀ u,s u j≤1) →
    ∀ pH:ℝ,smin≤pH → (∀ u,s u j=pH) →
    let μ:=FiniteLaw.pi (rawWheelLaw (fun _ : Sym2 V=>p) (fun _=>le_trans (le_of_lt hpmin) hp) (fun _=>hp1) d hd q hq hQ s hs hS);
    1-(1/(Fintype.card V:ℝ)+2/(Fintype.card V:ℝ)^2)≤μ.probability
      (fun σ:RawWheelOutcome V U Γ Color=>
        OrdinaryUniformProtectedReservoirEvent r m tterm f a₀ b₀ εabs
          (rawWheelGraph P σ\F) F (rawWheelSpokes π d σ j)) := by
  obtain ⟨εabs,εtrans,hεabs,hεtrans,hMain⟩:=
    ordinary_uniform_wheel_absorber_high_probability_before_spacing
      r hr α pmin smin ω hα hpmin hsmin hsmin1 hω
  refine ⟨εabs,εtrans,hεabs,hεtrans,?_⟩
  intro d hd L hL
  obtain ⟨εsample,hεsample,hMain⟩:=hMain d hd L hL
  refine ⟨εsample,hεsample,?_⟩
  intro m
  obtain ⟨a₀,b₀,t,ht,hMain⟩:=hMain m
  refine ⟨a₀,b₀,t,ht,?_⟩
  intro tterm f
  let f₀:=f+2^(tterm*tterm)*a₀+2^(tterm*tterm)*b₀
  obtain ⟨N,hMain⟩:=hMain f₀
  refine ⟨N,?_⟩
  intro V U Γ Color _ _ _ _ _ _ hn hu hlo P F π hF hnoshort hdeg hP D hD hDhi hnear p hp hp1 q hq hQ s hs hS j hslo hshi pH hpH hj μ
  have hh:=hMain V U Γ Color hn hu hlo P F π hF hnoshort hdeg hP D hD hDhi hnear p hp hp1 q hq hQ s hs hS j hslo hshi pH hpH hj
  apply hh.trans
  apply finiteLaw_probability_mono
  intro σ hσ
  apply ordinary_uniform_absorbers_imply_protected_reservoir_event r m tterm f a₀ b₀ εabs
    (rawWheelGraph P σ\F) F (rawWheelSpokes π d σ j)
  exact hσ.1
end Oberwolfach
