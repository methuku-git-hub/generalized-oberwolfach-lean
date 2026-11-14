module

public import Oberwolfach.MarkedExpandedDegreeEvent
public import Oberwolfach.MarkedExpandedRawCommonEvent

@[expose] public section
/-! The colour-degree event is available simultaneously with any selected
retained event of probability at least 7/10, without assuming the former. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

def expandedPhysicalDegreeGood (G Z:SimpleGraph V) (ρ:Fin 6→ℝ)
    (σ:Sym2 V→Fin 6×Bool):Prop:=∀ a x,
      |((∑ y,sampledColourOrientation G σ a x y:ℕ):ℝ)-ρ a/2*G.degree x|<(Fintype.card V:ℝ)^(3/5:ℝ) ∧
      |((∑ y,sampledColourOrientation G σ a y x:ℕ):ℝ)-ρ a/2*G.degree x|<(Fintype.card V:ℝ)^(3/5:ℝ) ∧
      |(sampledColourDegree Z (fun e=>(σ e).1) a x:ℝ)-ρ a*Z.degree x|<(Fintype.card V:ℝ)^(3/5:ℝ)

theorem raw_expanded_marked_selected_and_degrees :
    ∃ N:ℕ,∀ (V:Type) [Fintype V] [LinearOrder V],
    N≤Fintype.card V→∀ (U Γ Color:Type) [Fintype U] [Fintype Γ] [Fintype Color] [DecidableEq U]
    (G Z:SimpleGraph V)
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (d:ℕ) (hd:2≤d) (q:U→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀ u j,0≤s u j) (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
    (F:RawMarkedOutcome V U Γ Color→Type) [∀ a,Fintype (F a)] (ν:∀ a,FiniteLaw (F a)) (E:(Σ a,F a)→Prop),
    (7:ℝ)/10≤((FiniteLaw.pi (rawMarkedWheelLaw (V:=V) p k hp hk (by linarith) d hd q hq hQ s hs hS)).sigma ν).probability E→
    let ρ:=markedExpandedPhysicalProbability p k p₂ k₂ u
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)
    let f:=fun (ω:∀ e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e) e=>rawExpandedMarkedCollapse e (ω e)
    ∃ z,0<(μ.sigma (fun ω=>ν (f ω))).mass z ∧ E ⟨f z.1,z.2⟩ ∧
      expandedPhysicalDegreeGood G Z ρ (fun e=>z.1 (Sum.inl e)) := by
  obtain ⟨N,hN⟩:=raw_expanded_marked_colour_degrees_highProbability
  refine ⟨N,?_⟩
  intro V _ _ hn U Γ Color _ _ _ _ G Z p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS F _ ν E hE ρ μ f
  let Extra:=fun z:(Σ ω:(∀ e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e),F (f ω))=>
    expandedPhysicalDegreeGood G Z ρ (fun e=>z.1 (Sum.inl e))
  have hExtra:(99:ℝ)/100≤(μ.sigma (fun ω=>ν (f ω))).probability Extra:=by
    exact hN V hn U Γ Color G Z p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS F ν
  exact raw_expanded_marked_retained_common_event p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS F ν E Extra hE hExtra
end Oberwolfach
