module

public import Oberwolfach.OrdinaryExpandedGeneralReferenceEvent
public import Oberwolfach.OrdinaryDomainNeighbourhoodEvent

@[expose] public section
/-! Add the two fixed-domain neighborhood events to an arbitrary previous
event on the same expanded raw sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

theorem ordinary_expanded_add_domain_profiles
    (P F:SimpleGraph V) (π:Equiv.Perm V) (I:Finset V) (J:Finset U) (d:ℕ) (hd:2≤d)
    (pH tR tH:ℝ) (j:Color)
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (q:U→Γ→ℝ) (hq:∀w g,0≤q w g) (hQ:∀w,∑g,q w g≤1/8)
    (s:U→Color→ℝ) (hs:∀w j,0≤s w j) (hS:∀w,∑j,s w j≤ intervalUncoveredProbability d (∑g,q w g))
    {R:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)→Type}
    [∀σ,Fintype (R σ)] (ν:∀σ,FiniteLaw (R σ))
    (E:(Σσ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e,R σ)→Prop)
    (εE εProfile:ℝ)
    (hProfile:1-εProfile≤(FiniteLaw.pi (rawWheelLaw (V:=V) (fun _=>2*p)
      (fun _=>by linarith) (fun _=>by linarith) d hd q hq hQ s hs hS)).probability
      (fun σ=>RawOrdinaryRows P π d 2 I (2*p) s j tR σ ∧ RawOrdinaryDomainIndices F π d 3 J pH j tH σ))
    (hE:let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS);
      1-εE≤(μ.sigma ν).probability E):
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS);
    1-(εE+εProfile)≤(μ.sigma ν).probability (fun z=>E z ∧
      RawOrdinaryRows P π d 2 I (2*p) s j tR (fun e=>expandedOrdinarySelectedCollapse e (z.1 e)) ∧
      RawOrdinaryDomainIndices F π d 3 J pH j tH (fun e=>expandedOrdinarySelectedCollapse e (z.1 e))):=by
  exact ordinary_expanded_add_general_reference_event p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS ν
    (fun σ=>RawOrdinaryRows P π d 2 I (2*p) s j tR σ ∧ RawOrdinaryDomainIndices F π d 3 J pH j tH σ)
    E εProfile εE hProfile hE
end Oberwolfach
