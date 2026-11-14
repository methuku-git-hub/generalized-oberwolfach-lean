module

public import Oberwolfach.OrdinaryReferenceSpokeColumns
public import Oberwolfach.OrdinaryExpandedGeneralReferenceEvent

@[expose] public section
/-! Add all reference spoke-column counts to an arbitrary event of the same
    expanded sample, without an independence hypothesis. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

theorem ordinary_expanded_reference_spoke_columns_and_prior
    (π:Equiv.Perm V) (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1) (d:ℕ) (hd:2≤d)
    (q:U→Γ→ℝ) (hq:∀w g,0≤q w g) (hQ:∀w,∑g,q w g≤1/8)
    (s:U→Color→ℝ) (hs:∀w j,0≤s w j) (hS:∀w,∑j,s w j≤ intervalUncoveredProbability d (∑g,q w g))
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x) (hn:0<Fintype.card V)
    (g:Γ) (j:Color) (t:ℝ) (ht:0<t)
    {R:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)→Type}
    [∀σ,Fintype (R σ)] (ν:∀σ,FiniteLaw (R σ))
    (E:(Σσ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e,R σ)→Prop) (εE:ℝ)
    (hE:let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS);
      1-εE≤(μ.sigma ν).probability E):
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)
    let loss:=4*(Fintype.card U:ℝ)*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*Fintype.card V));
    1-(εE+loss)≤(μ.sigma ν).probability (fun z=>E z ∧
      ∀w,|((Finset.univ.filter (fun v=>rawWheelSpokes π d (fun e=>expandedOrdinarySelectedCollapse e (z.1 e)) j v w)).card:ℝ)-s w j*Fintype.card V|<t):=by
  intro μ loss
  have hpR:0≤2*p:=by positivity
  have hpR1:2*p≤1:=by linarith
  have hCol:=ordinary_reference_spoke_columns_high_probability π (2*p) hpR hpR1 d hd q hq hQ s hs hS hnoshort hn g j t ht
  exact ordinary_expanded_add_general_reference_event p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS ν
    (fun σ=>∀w,|((Finset.univ.filter (fun v=>rawWheelSpokes π d σ j v w)).card:ℝ)-s w j*Fintype.card V|<t)
    E loss εE hCol hE
end Oberwolfach
