module

public import Oberwolfach.FirstVortexOriginalMarginLongRepeatedPositiveCutoff
public import Oberwolfach.FactorClassAssignment

@[expose] public section
/-! Enlarging the long-class cutoff preserves the proved repeated-factor
result. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem first_vortex_long_arbitrary_cutoff_monotone (α:ℝ) (hα:0<α) (KExtra:ℕ):
    ∃K N:ℕ,KExtra≤K ∧ 3≤K ∧ ∀n≥N,∀(G:SimpleGraph (Fin n)) (D:ℕ),G.IsRegularOfDegree D→Even D→
      ∀F₀:SimpleGraph (Fin n),F₀.IsRegularOfDegree 2→∀Allowed:Set ℕ,
      Allowed.Nonempty→(∀s∈Allowed,3≤s)→AllowedCycleLengths F₀ Allowed→factorPreparationClass F₀ K=none→
      (allowedThreshold Allowed+α/2)*n≤(D:ℝ)→
      HasFactorDecomposition G (fun _:Fin (D/2)=>F₀) :=by
  obtain ⟨K₀,N₀,hK₀,hbase⟩:=first_vortex_original_margin_long_repeated_factor_positive_cutoff α hα
  refine ⟨max KExtra K₀,max N₀ 1,le_max_left _ _,le_trans hK₀ (le_max_right _ _),?_⟩
  intro n hn G D hG hEven F hF Allowed hAllowed hValid hFAllowed hLong hdegree
  have hn0:0<n:=by omega
  have hLongFrac:=((factor_preparation_class hn0 F hF Allowed hFAllowed (max KExtra K₀) (by omega)).1).1 hLong
  have hsubset:(Finset.univ.filter (fun v=>max KExtra K₀<Fintype.card (F.connectedComponentMk v)))⊆
      (Finset.univ.filter (fun v=>K₀<Fintype.card (F.connectedComponentMk v))):=by
    intro v hv
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _,lt_of_le_of_lt (le_max_right _ _) (Finset.mem_filter.mp hv).2⟩
  have hcard:((Finset.univ.filter (fun v=>max KExtra K₀<Fintype.card (F.connectedComponentMk v))).card:ℝ)≤
      ((Finset.univ.filter (fun v=>K₀<Fintype.card (F.connectedComponentMk v))).card:ℝ):=by
    exact_mod_cast Finset.card_le_card hsubset
  have hOld:factorPreparationClass F K₀=none:=
    ((factor_preparation_class hn0 F hF Allowed hFAllowed K₀ (by omega)).1).2
      (hLongFrac.trans (div_le_div_of_nonneg_right hcard (Nat.cast_nonneg n)))
  exact hbase n (by omega) G D hG hEven F hF Allowed hAllowed hValid hFAllowed hOld hdegree
end Oberwolfach
