module

public import Oberwolfach.OrdinaryClassReserveBound
public import Oberwolfach.CandidateOrdinaryAssignedSamplingWitness
public import Oberwolfach.CandidateOrdinaryAssignedClassRecipeValidDirectReserve

@[expose] public section
/-! The actual ordinary-class recipe supplies its four class probability
weights and the interval law used by the shared categorical exposure. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_assigned_class_sampling_witness_candidate_direct_reserve {n:ℕ} (hn:0<n)
    {U:Type} [Fintype U] (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (Allowed:Set ℕ) (hAllowed:∀w,AllowedCycleLengths (F w) Allowed)
    (K:ℕ) (hK:0<K) (i₀:Fin K) (s θ c ρ D:ℝ) (d:ℕ) (hd:2≤d)
    (hs0:0≤s) (hs1:s≤1/100) (hθ:0<θ) (hθ1:θ≤1/100) (hc:8≤c)
    (hda:1/θ≤d) (hρ:0<ρ) (hρ1:ρ≤1) (hD:0<D) (hsize:ρ*D=2*(Fintype.card U:ℝ))
    (hClassReserve:OrdinaryClassReserveBound F hF i₀ s):
    ∃ (p p₂ udens:ℝ),0≤p ∧ 0≤p₂ ∧ 0≤udens ∧ 2*p+2*p₂+udens=ρ ∧
      2*p=ρ*s ∧ ρ/4≤p₂ ∧
      p₂*D=∑w,(ordinaryAssignedLongWeight F hF K θ c w+ordinaryAssignedShortWeight F hF K i₀ s θ c w) ∧
      udens*D=2*∑w,(1-s-ordinaryAssignedLongWeight F hF K θ c w-ordinaryAssignedShortWeight F hF K i₀ s θ c w) ∧
    let q:=ordinaryAssignedMarkedProbability F hF K θ c
    let sco:=ordinaryAssignedSpokeProbability F hF K i₀ s θ c;
      (∀w j,0≤q w j) ∧ (∀w,∑j,q w j≤1/8) ∧
      (∀w j,0≤sco w j) ∧ (∀w,∑j,sco w j≤ intervalUncoveredProbability d (∑j,q w j)) ∧
      (∀w,q w false=0 ∧ sco w false=s) :=by
  let av:=ordinaryAssignedLongWeight F hF K θ c
  let bv:=ordinaryAssignedShortWeight F hF K i₀ s θ c
  let p:=ρ*s/2
  let p₂:=(∑ w:U, (av w+bv w))/D
  let udens:=2*(∑ w:U, (1-s-av w-bv w))/D
  have hh:=ordinary_class_assigned_sampling_parameters_candidate_direct_reserve hn F hF K hK i₀ s θ c ρ D d hd
    hs0 hs1 hθ hθ1 hc hda hρ hρ1 hD hsize Allowed hAllowed hClassReserve
  have hh':0≤p ∧ 0≤p₂ ∧ 0≤udens ∧ 2*p+2*p₂+udens=ρ ∧ ρ/4≤p₂:=by
    dsimp only [p,p₂,udens,av,bv,ordinaryAssignedLongWeight,ordinaryAssignedShortWeight,ordinaryAssignedFraction]
    exact ⟨hh.2.2.2.2.2.1,hh.2.2.2.2.2.2.1,hh.2.2.2.2.2.2.2.1,
      hh.2.2.2.2.2.2.2.2.1,hh.2.2.2.2.2.2.2.2.2.2.2.1⟩
  have hp₂eq:p₂*D=∑w,(av w+bv w):=by dsimp [p₂];field_simp
  have hueq:udens*D=2*∑w,(1-s-av w-bv w):=by dsimp [udens];field_simp
  have hrecipe:=ordinary_assigned_class_recipe_valid_candidate_direct_reserve hn F hF K hK i₀ s θ c ρ D d hd
    hs0 hs1 hθ hθ1 hc hda hρ hρ1 hD hsize Allowed hAllowed hClassReserve
  refine ⟨p,p₂,udens,hh'.1,hh'.2.1,hh'.2.2.1,hh'.2.2.2.1,?_,hh'.2.2.2.2,hp₂eq,hueq,
    hrecipe.1,hrecipe.2.1,hrecipe.2.2.1,hrecipe.2.2.2.1,?_⟩
  · dsimp [p];ring
  · intro w
    exact ⟨by simp [ordinaryAssignedMarkedProbability],hrecipe.2.2.2.2 w⟩
end Oberwolfach
