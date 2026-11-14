module

public import Oberwolfach.OrdinaryFactorFamilySamplingParameters
public import Oberwolfach.OrdinaryAbundanceReservation

@[expose] public section
/-! The class assignment supplies the reserve hypothesis of the concrete
ordinary-family sampling construction. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
open scoped BigOperators
theorem ordinary_reserve_assigned_sampling_parameters {n:ℕ} (hn:0<n)
    {U:Type} [Fintype U] (F:U→SimpleGraph (Fin n)) (hF:∀ w,(F w).IsRegularOfDegree 2)
    (K:ℕ) (hK:0<K) (i₀:Fin K) (s θ c ρ D:ℝ) (d:ℕ) (hd:2≤d)
    (hs0:0≤s) (hs1:s≤1/100) (hθ:0<θ) (hθ1:θ≤1/100) (hc:8≤c)
    (hda:1/θ≤d) (hρ:0<ρ) (hρ1:ρ≤1) (hD:0<D) (hsize:ρ*D=2*(Fintype.card U:ℝ))
    (S:Set ℕ) (hS:∀ w,AllowedCycleLengths (F w) S)
    (hreserve:∀w,s≤((Finset.univ.filter (fun v=>longPreparationCycleClass (F w) (hF w) K v=some i₀)).card:ℝ)/n):
    let fraction:=fun w (j:Option (Fin K))=>
      ((Finset.univ.filter (fun v=>longPreparationCycleClass (F w) (hF w) K v=j)).card:ℝ)/n
    let f:=fun w (i:Fin K)=>fraction w (some i)-(if i=i₀ then s else 0)
    let long:=fun w=>fraction w none
    let cutoff:=θ/(100*(K:ℝ))
    let longKept:=fun w=>if long w<θ/100 then 0 else long w
    let shortKept:=fun w=>∑ i:Fin K,(if f w i<cutoff then 0 else f w i)
    let a:=fun w=>(1-θ)*longKept w/c
    let b:=fun w=>(c-1)*a w+(1-θ)*shortKept w
    let u:=fun w=>1-s-a w-b w
    let q:=fun w (j:Bool)=>if j then a w else 0
    let sco:=fun w (j:Bool)=>if j then b w else s
    let p:=ρ*s/2
    let p₂:=(∑ w,(a w+b w))/D
    let unassigned:=2*(∑ w,u w)/D;
    (∀ w,0≤a w ∧ a w≤1/8 ∧ 1/2≤b w ∧ θ/2≤u w ∧ u w≤2*θ ∧ s+a w+b w+u w=1) ∧
    (∀ w j,0≤q w j) ∧ (∀ w,∑ j,q w j≤1/8) ∧
    (∀ w j,0≤sco w j) ∧ (∀ w,∑ j,sco w j ≤ intervalUncoveredProbability d (∑ j,q w j)) ∧
    0≤p ∧ 0≤p₂ ∧ 0≤unassigned ∧ 2*p+2*p₂+unassigned=ρ ∧
    2*p+2*p₂+unassigned≤1 ∧ (2*p)*D=2*(Fintype.card U:ℝ)*s ∧ ρ/4≤p₂ ∧
    unassigned=ρ*((∑ w,u w)/(Fintype.card U:ℝ)) := by
  exact ordinary_factor_family_sampling_parameters hn F hF K hK i₀ s θ c ρ D d hd
    hs0 hs1 hθ hθ1 hc hda hρ hρ1 hD hsize hreserve
end Oberwolfach
