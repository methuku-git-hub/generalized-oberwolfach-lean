module

public import Oberwolfach.BipartiteLargeCutEmbedding
public import Oberwolfach.MarkedSampleOccurrenceMatrix
public import Oberwolfach.MarkedPhysicalDeletionRestriction

@[expose] public section

/-! Actual marked rim and spoke cuts on embedded domains after deletion.
All coefficient losses use realized physical degrees. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W U Z Γ Color:Type} [Fintype V] [Fintype W] [Fintype U] [Fintype Z]
  [Fintype Γ] [Fintype Color] [LinearOrder V] [LinearOrder W] [DecidableEq U] [DecidableEq Z]

theorem markedPhysicalRim_restrictPair_eq
    (f:W↪oV) (g:Z↪U) (π:Equiv.Perm V) (ρ:Equiv.Perm W)
    (hf:∀ x,f (ρ x)=π (f x)) (P:SimpleGraph V) (d:ℕ)
    (σ:RawMarkedOutcome V U Γ Color) (mark:Bool) (x y:W):
    markedPhysicalRim (P.comap f) ρ (3*d) (fun e=>rawMarkedRestrictPair f g σ (Sum.inl e)) mark x y=
      markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) mark (f x) (f y):=by
  rw [←markedPhysicalRim_indicator (P.comap f) ρ (3*d),←markedPhysicalRim_indicator P π (3*d)]
  congr 1
  have hh:=rawMarkedRestrictPair_rims f g π ρ hf P d σ (if mark then Sum.inr (x,y) else Sum.inl (x,y))
  cases mark <;> simpa only [rawMarkedPairRims,Bool.false_eq_true,ite_false,ite_true,
    Sum.map_inl,Sum.map_inr,Prod.map_apply,Sum.elim_inl,Sum.elim_inr] using propext hh

theorem marked_rim_largeCut_after_physical_deletion
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (hn:0<Fintype.card V)
    (σ:RawMarkedOutcome V U Γ Color) (mark:Bool) (DR:SimpleGraph V) (δ h ζ:ℝ) (hζ:0≤ζ)
    (hDR:∀ x,(DR.degree x:ℝ)≤ζ*Fintype.card V)
    (hcut:BipartiteLargeCut (markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) mark) δ h):
    BipartiteLargeCut (markedPhysicalRim P π (3*d) (fun e=>rawMarkedDeleteRims σ DR.edgeFinset (Sum.inl e)) mark) δ (h-ζ):=by
  let R:=fun x y=>markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) mark x y=1
  let Q:=fun x y=>markedPhysicalRim P π (3*d) (fun e=>rawMarkedDeleteRims σ DR.edgeFinset (Sum.inl e)) mark x y=1
  have heR:relationMultiplicity R=markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) mark:=by
    funext x y
    unfold relationMultiplicity R markedPhysicalRim permutationSeparatedMatrix markedPhysicalOrientation
    split_ifs <;> simp_all
  have heQ:relationMultiplicity Q=markedPhysicalRim P π (3*d) (fun e=>rawMarkedDeleteRims σ DR.edgeFinset (Sum.inl e)) mark:=by
    funext x y
    unfold relationMultiplicity Q markedPhysicalRim permutationSeparatedMatrix markedPhysicalOrientation
    split_ifs <;> simp_all
  rw [←heR] at hcut
  rw [←heQ]
  apply bipartiteLargeCut_after_relation_changes hn hn R Q δ h ζ hζ _ _ hcut
  · intro x
    have hh:=(marked_row_rim_physical_deletion_change P π d σ DR Finset.univ (mark,false,x)).trans (hDR _)
    convert hh using 1
    apply Finset.sum_congr rfl
    intro y _
    cases mark <;> rfl
  · intro y
    have hh:=(marked_row_rim_physical_deletion_change P π d σ DR Finset.univ (mark,true,y)).trans (hDR _)
    convert hh using 1
    apply Finset.sum_congr rfl
    intro x _
    cases mark <;> rfl

theorem marked_protected_active_cuts
    (f:W↪oV) (g:Z↪U) (π:Equiv.Perm V) (ρ:Equiv.Perm W)
    (hf:∀ x,f (ρ x)=π (f x)) (P:SimpleGraph V) (d:ℕ)
    (hW:0<Fintype.card W) (hZ:0<Fintype.card Z)
    (κ δ δA h ζ:ℝ) (hκ:0<κ) (hh:0≤h) (hζ:0≤ζ)
    (hWsize:κ*Fintype.card V≤(Fintype.card W:ℝ))
    (hZsize:κ*Fintype.card U≤(Fintype.card Z:ℝ)) (hcutoff:1-2*δ≤κ*(1-2*δA))
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (hR:∀ mark,BipartiteLargeCut (markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) mark) δ h)
    (hS:∀ mark,BipartiteLargeCut (relationMultiplicity (H mark)) δ h)
    (DR:SimpleGraph V) (DS:SimpleGraph (V⊕U))
    (hrim:∀ x,((DR.comap f).degree x:ℝ)≤ζ*Fintype.card W)
    (hrow:∀ x,((DS.comap (Sum.map f g)).degree (Sum.inl x):ℝ)≤ζ*Fintype.card Z)
    (hcol:∀ u,((DS.comap (Sum.map f g)).degree (Sum.inr u):ℝ)≤ζ*Fintype.card W):
    let σA:=rawMarkedRestrictPair f g (rawMarkedDeleteRims σ DR.edgeFinset)
    let HA:=fun b x u=>markedDeletePhysicalSpokes H DS b (f x) (g u);
    (∀ mark,BipartiteLargeCut (markedPhysicalRim (P.comap f) ρ (3*d) (fun e=>σA (Sum.inl e)) mark) δA (h-ζ))∧
    (∀ mark,BipartiteLargeCut (relationMultiplicity (HA mark)) δA (h-ζ)):=by
  intro σA HA
  have hσ:σA=rawMarkedDeleteRims (rawMarkedRestrictPair f g σ) (DR.comap f).edgeFinset:=
    rawMarkedRestrictPair_deleteRims f g σ DR
  constructor
  · intro mark
    rw [hσ]
    apply marked_rim_largeCut_after_physical_deletion (P.comap f) ρ d hW
      (rawMarkedRestrictPair f g σ) mark (DR.comap f) δA h ζ hζ hrim
    have hc:=bipartiteLargeCut_embedding f.toEmbedding f.toEmbedding _ hW hW κ δ δA h
      hκ hh hWsize hWsize hcutoff (hR mark)
    have he:(fun x y=>markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) mark (f x) (f y))=
        markedPhysicalRim (P.comap f) ρ (3*d) (fun e=>rawMarkedRestrictPair f g σ (Sum.inl e)) mark:=by
      funext x y;exact (markedPhysicalRim_restrictPair_eq f g π ρ hf P d σ mark x y).symm
    change BipartiteLargeCut (fun x y=>markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) mark (f x) (f y)) δA h at hc
    rw [he] at hc
    exact hc
  · intro mark
    have hc:=bipartiteLargeCut_embedding f.toEmbedding g _ hW hZ κ δ δA h
      hκ hh hWsize hZsize hcutoff (hS mark)
    let H₀:=fun b x u=>H b (f x) (g u)
    apply bipartiteLargeCut_after_relation_changes hW hZ (H₀ mark) (HA mark) δA h ζ hζ _ _ hc
    · intro x
      convert (marked_spoke_physical_deletion_row_change H₀ (DS.comap (Sum.map f g)) Finset.univ mark x).trans (hrow x) using 1 <;> congr!
    · intro u
      convert (marked_spoke_physical_deletion_column_change H₀ (DS.comap (Sum.map f g)) Finset.univ mark u).trans (hcol u) using 1 <;> congr!

end Oberwolfach
