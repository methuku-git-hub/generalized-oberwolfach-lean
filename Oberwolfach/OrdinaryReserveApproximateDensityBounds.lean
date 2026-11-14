module

public import Oberwolfach.OrdinaryAssignedReserveBasic
public import Oberwolfach.OrdinaryReserveSamplingParameters

@[expose] public section
/-! Uniform lower bounds for the actual ordinary-preparation approximate
spokes and physical rim probability, before sampling. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_assigned_approximate_density_bounds_of_reserve
    {n:ℕ} (hn:0<n) {U:Type} [Fintype U]
    (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (K:ℕ) (hK:0<K) (i₀:Fin K) (rsv θ c ρ D:ℝ) (d:ℕ) (hd:2≤d)
    (hs0:0≤rsv) (hs1:rsv≤1/100) (hθ:0<θ) (hθ1:θ≤1/100) (hc:8≤c)
    (hda:1/θ≤d) (hρ:0<ρ) (hρ1:ρ≤1) (hD:0<D) (hsize:ρ*D=2*(Fintype.card U:ℝ))
    (S:Set ℕ) (hS:∀w,AllowedCycleLengths (F w) S)
    (hreserve:∀w,rsv≤((Finset.univ.filter (fun v=>longPreparationCycleClass (F w) (hF w) K v=some i₀)).card:ℝ)/n):
    let a:=ordinaryAssignedLongWeight F hF K θ c
    let b:=ordinaryAssignedShortWeight F hF K i₀ rsv θ c
    let p:=(∑w,(a w+b w))/D
    let η:=fun i w=>ordinaryAssignedFrequencyCoefficient F hF K i₀ rsv θ c w i
    let pstar:=min (1/2:ℝ) (ρ/4);
    0<pstar ∧ pstar≤p ∧ p≤1 ∧
    (∀w,pstar≤b w ∧ b w≤1) ∧
    (∀i w,0≤η i w ∧ η i w≤1/b w) := by
  intro a b p η pstar
  have h:=ordinary_reserve_assigned_sampling_parameters hn F hF K hK i₀ rsv θ c ρ D d hd
    hs0 hs1 hθ hθ1 hc hda hρ hρ1 hD hsize S hS hreserve
  rcases h with ⟨hubs,hq,hqsum,hs,hssum,hp0,hp20,hu0,htotal,hcap,hpD,hplow,huid⟩
  have hcoef:=ordinary_assigned_frequency_coefficient_of_reserve hn F hF S hS K hK i₀ rsv θ c
    hs0 hs1 hθ hθ1 hc hreserve
  have hlocal (w:U):0≤a w ∧ 1/2≤b w ∧ θ/2≤1-rsv-a w-b w := by
    have hh:=hubs w
    have ha:0≤a w:=by simpa only [a,ordinaryAssignedLongWeight,ordinaryAssignedFraction] using hh.1
    have hb:1/2≤b w:=by simpa only [b,ordinaryAssignedShortWeight,ordinaryAssignedLongWeight,ordinaryAssignedFraction] using hh.2.2.1
    have hu:θ/2≤1-rsv-a w-b w:=by simpa only [a,b,ordinaryAssignedShortWeight,ordinaryAssignedLongWeight,ordinaryAssignedFraction] using hh.2.2.2.1
    exact ⟨ha,hb,hu⟩
  have hpBound:ρ/4≤p:=by
    convert hplow using 1 <;>
      simp only [p,a,b,ordinaryAssignedShortWeight,ordinaryAssignedLongWeight,ordinaryAssignedFraction]
  have hpUpper:p≤1:=by
    have hcap':2*(ρ*rsv/2)+2*p+2*(∑ w : U, (1 - rsv - a w - b w))/D≤1:=by
      convert hcap using 1 <;>
        simp only [p,a,b,ordinaryAssignedShortWeight,ordinaryAssignedLongWeight,ordinaryAssignedFraction]
    have hu':0≤2*(∑ w : U, (1 - rsv - a w - b w))/D:=by
      convert hu0 using 1 <;>
        simp only [a,b,ordinaryAssignedShortWeight,ordinaryAssignedLongWeight,ordinaryAssignedFraction]
    nlinarith [hcap',hp0,hu']
  refine ⟨lt_min (by norm_num) (by positivity),?_,hpUpper,?_,?_⟩
  · exact (min_le_right _ _).trans hpBound
  · intro w
    constructor
    · exact (min_le_left _ _).trans (hlocal w).2.1
    · have hh:=hlocal w
      nlinarith [hθ,hs0,hh.1,hh.2.2]
  · intro i w
    exact (hcoef w).2.1 i
end Oberwolfach
