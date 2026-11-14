module

public import Oberwolfach.RawUnassignedFixedFamilyEvent
public import Oberwolfach.FiniteLawUniformConditionalEvent
public import Oberwolfach.FiniteSumProduct
public import Oberwolfach.FiniteSigmaFirstMap
public import Oberwolfach.MarkedExpandedRawLaw

@[expose] public section
/-! The test family may depend on the physical-edge sample: condition on that
independent coordinate block, then use the fixed-family interval estimate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem raw_unassigned_physical_adaptive_family_event
    {V U Γ Color I:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U]
    [Fintype Γ] [Fintype Color] [Fintype I]
    (π:Equiv.Perm V) (d:ℕ) (hd:2≤d)
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (q:U→Γ→ℝ) (hq:∀w g,0≤q w g) (hQ:∀w,∑g,q w g≤1/8)
    (s:U→Color→ℝ) (hs:∀w j,0≤s w j) (hS:∀w,∑j,s w j≤ intervalUncoveredProbability d (∑g,q w g))
    (hn:0<Fintype.card V) (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (A:(Sym2 V→Fin 6×Bool)→I→Finset V) (t:ℝ) (ht:0<t)
    (F:RawMarkedOutcome V U Γ Color→Type) [∀a,Fintype (F a)] (ν:∀a,FiniteLaw (F a)):
    let law:=rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS
    let μ:=FiniteLaw.pi law
    let f:=fun (ω:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e) e=>rawExpandedMarkedCollapse e (ω e)
    1-2*(Fintype.card U:ℝ)*(Fintype.card I:ℝ)*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*(Fintype.card V:ℝ)))≤
    (μ.sigma (fun ω=>ν (f ω))).probability (fun z=>
      ∀w i,|rawIntervalUnassignedHubCountOn π d (fun e=>z.1 (Sum.inr e)) w (A (fun e=>z.1 (Sum.inl e)) i)-
        (A (fun e=>z.1 (Sum.inl e)) i).card*(1-(∑g,q w g)-(∑j,s w j))|<t):=by
  intro law μ f
  let E:=fun (τ:RawIntervalFamilyOutcome V U Γ Color) (ω:Sym2 V→Fin 6×Bool)=>
    ∀w i,|rawIntervalUnassignedHubCountOn π d τ w (A ω i)-(A ω i).card*(1-(∑g,q w g)-(∑j,s w j))|<t
  let μint:=FiniteLaw.pi (rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS)
  let μphys:=FiniteLaw.pi (fun e:Sym2 V=>law (Sum.inl e))
  let δ:=2*(Fintype.card U:ℝ)*(Fintype.card I:ℝ)*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*(Fintype.card V:ℝ)))
  have hb:∀ω,1-δ≤μint.probability (fun τ=>E τ ω):=by
    intro ω
    exact raw_interval_unassigned_fixed_family_event π d hd q hq hQ s hs hS hn hnoshort (A ω) t ht
  have hp:=finiteLaw_product_uniform_conditional_event μint μphys (fun ω τ=>E τ ω) δ hb
  have hsplit:=finiteLaw_pi_sum_probability law E
  have hprob:1-δ≤μ.probability (fun ω=>E (fun e=>ω (Sum.inr e)) (fun e=>ω (Sum.inl e))):=by
    rw [hsplit]
    exact hp
  have hproj:=finiteLaw_sigma_first_probability μ (fun ω=>ν (f ω))
    (fun ω=>E (fun e=>ω (Sum.inr e)) (fun e=>ω (Sum.inl e)))
  rw [hproj]
  exact hprob
end Oberwolfach
