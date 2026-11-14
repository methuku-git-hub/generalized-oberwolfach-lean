module

public import Oberwolfach.FiniteSigmaReferenceExtension
public import Oberwolfach.MarkedExpandedRawLaw

@[expose] public section
/-! The retained reference theorem's arbitrary high-probability extra event
can carry the richer approximate sample without assuming independent layers. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem raw_expanded_reference_positive_extension
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (d:ℕ) (hd:2≤d) (q:U→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀ u j,0≤s u j) (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
    (F:RawMarkedOutcome V U Γ Color→Type) [∀ a,Fintype (F a)] (ν:∀ a,FiniteLaw (F a))
    (Ref:(Σ a,F a)→Prop)
    (Good:(Σ ω:(∀ e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e),
        F (fun e=>rawExpandedMarkedCollapse e (ω e)))→Prop):
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)
    let f:=fun (ω:∀ e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e) e=>rawExpandedMarkedCollapse e (ω e)
    let law:=μ.sigma (fun ω=>ν (f ω));
    (99:ℝ)/100≤law.probability Good→
    (∀ E:(Σ a,F a)→Prop,(99:ℝ)/100≤((FiniteLaw.pi (rawMarkedWheelLaw (V:=V) p k hp hk (by linarith) d hd q hq hQ s hs hS)).sigma ν).probability E→
      ∃ y,Ref y ∧ E y)→
    ∃ z,Ref ⟨f z.1,z.2⟩ ∧ Good z ∧ 0<law.mass z:=by
  intro μ f law hGood hRef
  have hmap:μ.map f=FiniteLaw.pi (rawMarkedWheelLaw (V:=V) p k hp hk (by linarith) d hd q hq hQ s hs hS):=
    raw_expanded_marked_wheel_law_projection p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS
  have href':∀ E:(Σ a,F a)→Prop,(99:ℝ)/100≤((μ.map f).sigma ν).probability E→∃ y,Ref y ∧ E y:=by
    intro E hE
    apply hRef E
    simpa only [hmap] using hE
  exact finiteLaw_sigma_reference_extension μ f ν Good Ref (99/100) hGood href'
end Oberwolfach
