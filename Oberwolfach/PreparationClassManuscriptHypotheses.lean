module

public import Oberwolfach.FactorClassAssignment
public import Oberwolfach.PreparationWeightsFromAllowedThreshold

@[expose] public section
/-! The actual factor classification supplies the threshold and abundance
hypotheses of the ordinary and long preparation propositions. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem preparation_class_manuscript_hypotheses {n K:ℕ} (hn:0<n) (hK:3≤K)
    (F:SimpleGraph (Fin n)) (hF:F.IsRegularOfDegree 2) (Allowed:Set ℕ)
    (hAllowed:AllowedCycleLengths F Allowed):
    (∀v,cycleThreshold (Fintype.card (F.connectedComponentMk v))≤allowedThreshold Allowed) ∧
    (factorPreparationClass F K=none→
      (n:ℝ)/2≤((Finset.univ.filter (fun v=>K<Fintype.card (F.connectedComponentMk v))).card:ℝ)) ∧
    (∀i:Fin K,factorPreparationClass F K=some i→
      3≤ i.val+1 ∧ (1/(2*(K:ℝ)))*n≤
        ((Finset.univ.filter (fun v=>Fintype.card (F.connectedComponentMk v)=i.val+1)).card:ℝ)) :=by
  have hbdd:BddAbove (cycleThreshold '' Allowed):=by
    refine ⟨1,?_⟩
    rintro x ⟨r,hr,rfl⟩
    exact cycleThreshold_le_one r
  have hclass:=factor_preparation_class hn F hF Allowed hAllowed K (by omega)
  have hnR:0<(n:ℝ):=by exact_mod_cast hn
  refine ⟨?_,?_,?_⟩
  · intro v
    exact le_csSup hbdd ⟨_,(AllowedCycleLengths_iff_component_orders F Allowed).1 hAllowed _,rfl⟩
  · intro hnone
    have hfrac:=hclass.1.1 hnone
    have hmul:((1/2:ℝ)*(n:ℝ))≤
        ((Finset.univ.filter (fun v=>K<Fintype.card (F.connectedComponentMk v))).card:ℝ):=
      (le_div_iff₀ hnR).1 hfrac
    linarith
  · intro i hi
    obtain ⟨hthree,_,hcand,_⟩:=hclass.2 i hi
    refine ⟨hthree,?_⟩
    exact (le_div_iff₀ hnR).1 (Finset.mem_filter.mp hcand).2
end Oberwolfach
