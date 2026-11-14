module

public import Oberwolfach.RawStartEndColumnLocalSmallFailure
public import Oberwolfach.RawIntervalBoundaryHubsUpper
public import Oberwolfach.MarkedExpandedRawLaw
public import Oberwolfach.FiniteProductProjection
public import Oberwolfach.FiniteLawSigmaProjection

@[expose] public section
/-! The global boundary-start test has arbitrarily small failure on the same
expanded experiment, even after dependent retention. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem expanded_global_boundary_arbitrary_failure (d:ℕ) (hd:2≤d) (δ:ℝ) (hδ:0<δ):
    ∃N:ℕ,∀ (V:Type) [Fintype V] [LinearOrder V],N≤Fintype.card V→
    ∀(U Color:Type) [Fintype U] [DecidableEq U] [Fintype Color],
    0<Fintype.card U→Fintype.card U≤Fintype.card V→
    ∀(π:Equiv.Perm V) (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (q:U→Bool→ℝ) (hq:∀w g,0≤q w g) (hQ:∀w,∑g,q w g≤1/8)
    (s:U→Color→ℝ) (hs:∀w j,0≤s w j) (hS:∀w,∑j,s w j≤ intervalUncoveredProbability d (∑g,q w g))
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (F:RawMarkedOutcome V U Bool Color→Type) [∀a,Fintype (F a)] (ν:∀a,FiniteLaw (F a)),
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)
    let f:=fun (ω:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Bool Color e) e=>rawExpandedMarkedCollapse e (ω e)
    1-δ≤(μ.sigma (fun ω=>ν (f ω))).probability (fun z=>∀v,
      ((rawIntervalBoundaryHubSet π d (fun e=>z.1 (Sum.inr e)) Finset.univ v).card:ℝ)≤
        4*(Fintype.card U:ℝ)/d+4*(Fintype.card V:ℝ)^(3/4:ℝ)):=by
  obtain ⟨N,hNpos,hN⟩:=raw_interval_start_end_column_local_family_small_failure d hd δ hδ
  refine ⟨N,?_⟩
  intro V _ _ hn U Color _ _ _ hU hUV π p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum q hq hQ s hs hS hnoshort F _ ν μ f
  have hlocal:=hN V U Color Unit (Finset.univ:Finset Unit) (fun _=>Finset.univ) (fun _=>Finset.univ)
    (by intro i hi;simpa using hn) (by intro i hi j hj hij;cases i;cases j;rfl)
    (by intro i hi;simpa using hU) (by intro i hi;simpa using hUV)
    π q hq hQ s hs hS hnoshort
  let E:=fun σ:RawIntervalFamilyOutcome V U Bool Color=>∀v,
    ((rawIntervalBoundaryHubSet π d σ Finset.univ v).card:ℝ)≤
      4*(Fintype.card U:ℝ)/d+4*(Fintype.card V:ℝ)^(3/4:ℝ)
  have hq1:∀w g,q w g≤1:=by
    intro w g
    have hh:=Finset.single_le_sum (fun j _=>hq w j) (Finset.mem_univ g)
    linarith [hQ w]
  have hlower:1-δ≤(FiniteLaw.pi (rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS)).probability E:=by
    apply hlocal.trans
    apply finiteLaw_probability_mono
    intro σ hσ
    have hstart:∀v∈(Finset.univ:Finset V),∀g,
        |rawIntervalStartColumnCount π d σ v g Finset.univ-∑w,q w g/(d:ℝ)|<(Fintype.card V:ℝ)^(3/4:ℝ) ∧
        |rawIntervalStartColumnCount π d σ ((π^d).symm v) g Finset.univ-∑w,q w g/(d:ℝ)|<(Fintype.card V:ℝ)^(3/4:ℝ):=by
      intro v hv g
      simpa using hσ () (Finset.mem_univ ()) v (Finset.mem_univ v) g
    intro v
    have hh:=raw_interval_boundary_hubs_upper π d (by omega) σ q Finset.univ Finset.univ
      ((Fintype.card V:ℝ)^(3/4:ℝ)) hq1 hstart v (Finset.mem_univ v)
    simpa [E] using hh
  have heq:(μ.sigma (fun ω=>ν (f ω))).probability (fun z=>E (fun e=>z.1 (Sum.inr e)))=
      (FiniteLaw.pi (rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS)).probability E:=by
    calc
      _ = μ.probability (fun ω=>E (fun e=>ω (Sum.inr e))) := finiteLaw_sigma_first_probability μ (fun ω=>ν (f ω)) _
      _ = _ := by
        simpa only [μ,rawExpandedMarkedWheelLaw] using
          (finiteLaw_pi_injective_projection_event
            (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)
            Sum.inr Sum.inr_injective E)
  change 1-δ≤(μ.sigma (fun ω=>ν (f ω))).probability (fun z=>E (fun e=>z.1 (Sum.inr e)))
  rw [heq]
  exact hlower
end Oberwolfach
