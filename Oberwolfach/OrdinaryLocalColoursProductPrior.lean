module

public import Oberwolfach.PhysicalRestrictedLocalScale
public import Oberwolfach.FiniteLawManyGoodEvents
public import Oberwolfach.FiniteProductProjection
public import Oberwolfach.FiniteProductRegrouping
public import Oberwolfach.FiniteLawSigmaProjection
public import Oberwolfach.MarkedExpandedRawLaw

@[expose] public section
/-! Every physical colour has its local degree estimate on the same expanded
sample, while retaining any prior event and reference coin. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
open scoped BigOperators

theorem ordinary_local_colours_product_prior
    {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [LinearOrder V] [DecidableEq U]
    (P:SimpleGraph V) (A B:Finset V)
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (d:ℕ) (hd:2≤d) (q:U→Γ→ℝ) (hq:∀w g,0≤q w g) (hQ:∀w,∑g,q w g≤1/8)
    (s:U→Color→ℝ) (hs:∀w j,0≤s w j) (hS:∀w,∑j,s w j≤ intervalUncoveredProbability d (∑g,q w g))
    {R:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)→Type}
    [∀σ,Fintype (R σ)] (ν:∀σ,FiniteLaw (R σ)) (κ:FiniteLaw (Sym2 V→Bool))
    (E:(Σσ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e,R σ)×(Sym2 V→Bool)→Prop)
    (loss t:ℝ) (ht:0<t):
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)
    let err:ℝ:=12*(B.card:ℝ)*Real.exp (-2*t^2/(A.card:ℝ));
    1-loss≤((μ.sigma ν).prod κ).probability E→
    1-err-loss≤((μ.sigma ν).prod κ).probability (fun z=>
      (∀a:Fin 6,∀x∈B,
        |(((P.neighborFinset x∩A).filter (fun y=>(z.1.1 (Sum.inl s(x,y))).1=a)).card:ℝ)-
          markedExpandedPhysicalProbability p k p₂ k₂ u a*(P.neighborFinset x∩A).card|<t) ∧ E z) :=by
  intro μ err hE
  let ρ:=markedExpandedPhysicalProbability p k p₂ k₂ u
  let law:=FiniteLaw.pi (fun _:Sym2 V=>FiniteLaw.categoricalDirection ρ
    (markedExpandedPhysicalProbability_nonneg p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum)
    (markedExpandedPhysicalProbability_sum p k p₂ k₂ u))
  let Good:=fun (a:Fin 6) (z:(Σσ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e,R σ)×(Sym2 V→Bool))=>
    ∀x∈B,|(((P.neighborFinset x∩A).filter (fun y=>(z.1.1 (Sum.inl s(x,y))).1=a)).card:ℝ)-
      ρ a*(P.neighborFinset x∩A).card|<t
  let failure:ℝ:=2*(B.card:ℝ)*Real.exp (-2*t^2/(A.card:ℝ))
  have hGood:∀a∈(Finset.univ:Finset (Fin 6)),1-failure≤((μ.sigma ν).prod κ).probability (Good a):=by
    intro a _
    have hpure:=physicalRestrictedColourDegree_local_event P A B ρ
      (markedExpandedPhysicalProbability_nonneg p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum)
      (markedExpandedPhysicalProbability_sum p k p₂ k₂ u) a t ht
    let H:=fun ω:Sym2 V→Fin 6×Bool=>∀x∈B,
      |(((P.neighborFinset x∩A).filter (fun y=>(ω s(x,y)).1=a)).card:ℝ)-ρ a*(P.neighborFinset x∩A).card|<t
    have heq:((μ.sigma ν).prod κ).probability (Good a)=law.probability H:=by
      change ((μ.sigma ν).prod κ).probability (fun z=>H (fun e=>z.1.1 (Sum.inl e)))=law.probability H
      calc
        _ = (μ.sigma ν).probability (fun z=>H (fun e=>z.1 (Sum.inl e))) :=
          finiteLaw_prod_first_probability (μ.sigma ν) κ (fun z=>H (fun e=>z.1 (Sum.inl e)))
        _ = μ.probability (fun ω=>H (fun e=>ω (Sum.inl e))) :=
          finiteLaw_sigma_first_probability μ ν (fun ω=>H (fun e=>ω (Sum.inl e)))
        _ = law.probability H := by
          simpa only [μ,law,ρ,rawExpandedMarkedWheelLaw] using
            (finiteLaw_pi_injective_projection_event
              (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)
              Sum.inl Sum.inl_injective H)
    rw [heq]
    exact hpure
  have hh:=finiteLaw_many_good_events_with_prior ((μ.sigma ν).prod κ) (Finset.univ:Finset (Fin 6)) Good (fun _=>failure) E loss hGood hE
  have hsum':(∑a∈(Finset.univ:Finset (Fin 6)),failure)=err:=by simp only [Finset.sum_const,Finset.card_fin,nsmul_eq_mul];dsimp [err,failure];ring
  rw [hsum'] at hh
  simpa only [Finset.mem_univ,true_implies,Good,ρ] using hh
end Oberwolfach
