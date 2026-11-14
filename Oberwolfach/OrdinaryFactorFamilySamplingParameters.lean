module

public import Oberwolfach.OrdinaryFactorActualMarginals
public import Oberwolfach.OrdinaryIntervalMarginals
public import Oberwolfach.OrdinaryClassPhysicalParameters

@[expose] public section
/-! Construct the ordinary class's physical and interval probabilities from
the cycle frequencies of every prescribed factor, keeping their original
frequency cutoffs and common reserved fraction. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
open scoped BigOperators

theorem ordinary_factor_family_sampling_parameters {n:ℕ} (hn:0<n)
    {U:Type} [Fintype U] (F:U→SimpleGraph (Fin n)) (hF:∀ w,(F w).IsRegularOfDegree 2)
    (K:ℕ) (hK:0<K) (i₀:Fin K) (s θ c ρ D:ℝ) (d:ℕ) (hd:2≤d)
    (hs0:0≤s) (hs1:s≤1/100) (hθ:0<θ) (hθ1:θ≤1/100) (hc:8≤c)
    (hda:1/θ≤d) (hρ:0<ρ) (hρ1:ρ≤1) (hD:0<D) (hsize:ρ*D=2*(Fintype.card U:ℝ))
    (hreserve:∀ w,s≤((Finset.univ.filter (fun v=>longPreparationCycleClass (F w) (hF w) K v=some i₀)).card:ℝ)/n):
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
  intro fraction f long cutoff longKept shortKept a b u q sco p p₂ unassigned
  have hc0:0<c:=by linarith
  have hcinv:1/c≤(1/8:ℝ):=by apply (div_le_div_iff₀ hc0 (by norm_num)).2;nlinarith
  have hw:∀ w,0≤a w ∧ a w≤1/8 ∧ 1/2≤b w ∧ θ/2≤u w ∧ u w≤2*θ ∧ s+a w+b w+u w=1:=by
    intro w
    have hh:=ordinary_factor_actual_marginals hn (F w) (hF w) K hK i₀ s θ c hs0 hs1 hθ.le hθ1 hc (hreserve w)
    obtain ⟨_,_,_,hulo,huhi,ha,ha1,hb,hrow⟩:=hh
    exact ⟨ha,ha1.trans hcinv,hb,hulo,huhi,hrow⟩
  have hinterval:∀ w,(∀ j,0≤q w j) ∧ (∑ j,q w j)≤1/8 ∧ (∀ j,0≤sco w j) ∧
      (∑ j,sco w j) ≤ intervalUncoveredProbability d (∑ j,q w j):=by
    intro w
    have hh:=ordinary_interval_marginals_feasible s (a w) (b w) (u w) θ d hd hθ hda hs0
      (hw w).1 (hw w).2.1 (by linarith [(hw w).2.2.1]) (hw w).2.2.2.1 (hw w).2.2.2.2.2
    exact hh
  have hphys:=ordinary_class_physical_parameters ρ D s (1/2) hρ hρ1 hD hs0 (by norm_num)
    a b u (fun w=>(hw w).1) (fun w=>(hw w).2.2.1) (fun w=>by linarith [(hw w).2.2.2.1])
    (fun w=>(hw w).2.2.2.2.2) hsize
  refine ⟨hw,fun w=>(hinterval w).1,fun w=>(hinterval w).2.1,
    fun w=>(hinterval w).2.2.1,fun w=>(hinterval w).2.2.2,?_⟩
  have hbound:ρ/4≤p₂:=by nlinarith [hphys.2.2.2.2.2.2.1]
  exact ⟨hphys.1,hphys.2.1,hphys.2.2.1,hphys.2.2.2.1,hphys.2.2.2.2.1,hphys.2.2.2.2.2.1,
    hbound,hphys.2.2.2.2.2.2.2⟩
end Oberwolfach
