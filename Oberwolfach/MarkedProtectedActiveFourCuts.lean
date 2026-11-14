module

public import Oberwolfach.MarkedPhysicalCutTransfer
public import Oberwolfach.MarkedReferenceFixedCuts
public import Oberwolfach.MarkedActiveConfigurationMargins
public import Oberwolfach.OccurrenceRestrictionCuts

@[expose] public section

/-! All four correction cuts on the actual active host, derived from the
original cut family, the earlier spoke changes and the later deletions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W U Z Γ Color:Type} [Fintype V] [Fintype W] [Fintype U] [Fintype Z]
  [Fintype Γ] [Fintype Color] [LinearOrder V] [LinearOrder W] [DecidableEq U] [DecidableEq Z]

theorem marked_reference_four_bipartite_cuts
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (a:Γ) (c:Color)
    (α kstar tstar p k:ℝ) (hα:0<α) (hkstar:0<kstar) (htstar:0<tstar)
    (hpmin:kstar≤p) (hkmin:kstar≤k) (hn:0<Fintype.card V) (hm:0<Fintype.card U)
    (σ:RawMarkedOutcome V U Γ Color) (hcuts:MarkedReferenceCutFamilies P π d a c α p k tstar σ):
    let δ:=min (min α kstar) tstar/256
    let h:=min (α*kstar) tstar/128;
    (∀ mark,BipartiteLargeCut (markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) mark) δ (16*h))∧
    (∀ mark,BipartiteLargeCut (relationMultiplicity (rawMarkedPairSpokes π d σ a c mark)) δ (16*h)):=by
  intro δ h
  obtain ⟨hs,hr⟩:=markedReferenceCutFamilies_fixed_cuts P π d a c α kstar tstar p k
    hα hkstar htstar hpmin hkmin hn σ hcuts
  constructor
  · intro mark S T hST
    rw [bipartiteLargeCut_sum_restrict,bipartite_normalized_cut_scale hn hn]
    exact hr mark S T hST
  · intro mark S T hST
    rw [bipartiteLargeCut_sum_restrict,bipartite_normalized_cut_scale hn hm]
    exact hs mark S T hST

theorem marked_protected_active_four_cuts
    (f:W↪oV) (g:Z↪U) (π:Equiv.Perm V) (ρ:Equiv.Perm W)
    (hf:∀ x,f (ρ x)=π (f x)) (P:SimpleGraph V) (d:ℕ)
    (hW:0<Fintype.card W) (hZ:0<Fintype.card Z)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop) (a:Γ) (c:Color)
    (α kstar tstar p k ζold ζ:ℝ) (hα:0<α) (hkstar:0<kstar) (htstar:0<tstar)
    (hpmin:kstar≤p) (hkmin:kstar≤k) (htstar1:tstar≤1) (hζold:0≤ζold) (hζ:0≤ζ)
    (hcuts:MarkedReferenceCutFamilies P π d a c α p k tstar σ)
    (hrowOld:∀ mark x,(∑ u,if ¬(rawMarkedPairSpokes π d σ a c mark x u↔H mark x u) then (1:ℝ) else 0)≤ζold*Fintype.card U)
    (hcolOld:∀ mark u,(∑ x,if ¬(rawMarkedPairSpokes π d σ a c mark x u↔H mark x u) then (1:ℝ) else 0)≤ζold*Fintype.card V)
    (DR:SimpleGraph V) (DS:SimpleGraph (V⊕U))
    (hrim:∀ x,((DR.comap f).degree x:ℝ)≤ζ*Fintype.card W)
    (hrow:∀ x,((DS.comap (Sum.map f g)).degree (Sum.inl x):ℝ)≤ζ*Fintype.card Z)
    (hcol:∀ u,((DS.comap (Sum.map f g)).degree (Sum.inr u):ℝ)≤ζ*Fintype.card W):
    let δ:=min (min α kstar) tstar/256
    let h:=min (α*kstar) tstar/128;
    (1-δ/2)*Fintype.card V≤(Fintype.card W:ℝ)→
    (1-δ/2)*Fintype.card U≤(Fintype.card Z:ℝ)→ζold+ζ≤14*h→
    let σA:=rawMarkedRestrictPair f g (rawMarkedDeleteRims σ DR.edgeFinset)
    let HA:=fun b x u=>markedDeletePhysicalSpokes H DS b (f x) (g u);
    (∀ mark,BipartiteLargeCut
      (occurrenceMultiplicity (fun e:MarkedSampleArc (P.comap f) ρ (3*d) (fun e=>σA (Sum.inl e)) mark=>e.val.1)
        (fun e=>e.val.2)) (δ/2) (2*h))∧
    (∀ mark,BipartiteLargeCut (relationMultiplicity (HA mark)) (δ/2) (2*h)):=by
  intro δ h hWsize hZsize hbudget σA HA
  have hV:0<Fintype.card V:=lt_of_lt_of_le hW (Fintype.card_le_of_injective f f.injective)
  have hU:0<Fintype.card U:=lt_of_lt_of_le hZ (Fintype.card_le_of_injective g g.injective)
  have hd:0<δ:=by dsimp [δ];positivity
  have hd1:δ<1:=by have hh:=min_le_right (min α kstar) tstar;dsimp [δ];linarith
  have hh:0<h:=by dsimp [h];positivity
  obtain ⟨hcR,hcS⟩:=marked_reference_four_bipartite_cuts P π d a c α kstar tstar p k
    hα hkstar htstar hpmin hkmin hV hU σ hcuts
  have hcR':∀ mark,BipartiteLargeCut (markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) mark) δ (16*h-ζold):=by
    intro mark
    exact bipartiteLargeCut_coefficient_mono _ δ (16*h) (16*h-ζold) (by linarith) (hcR mark)
  have hcS':∀ mark,BipartiteLargeCut (relationMultiplicity (H mark)) δ (16*h-ζold):=by
    intro mark
    exact bipartiteLargeCut_after_relation_changes hV hU _ _ δ (16*h) ζold hζold (hrowOld mark) (hcolOld mark) (hcS mark)
  obtain ⟨hκ,hδA,hcutoff⟩:=marked_active_cut_parameters δ hd hd1
  obtain ⟨hR,hS⟩:=marked_protected_active_cuts f g π ρ hf P d hW hZ (1-δ/2) δ (δ/2) (16*h-ζold) ζ
    hκ (by linarith) hζ hWsize hZsize hcutoff σ H hcR' hcS' DR DS hrim hrow hcol
  constructor
  · intro mark
    rw [markedSampleArc_multiplicity]
    exact bipartiteLargeCut_coefficient_mono _ _ _ _ (by linarith) (hR mark)
  · intro mark
    exact bipartiteLargeCut_coefficient_mono _ _ _ _ (by linarith) (hS mark)

end Oberwolfach
