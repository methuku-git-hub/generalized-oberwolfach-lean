module

public import Oberwolfach.MarkedConfigurationPathDeletion
public import Oberwolfach.MarkedNeighbourhoodPhysicalDeletion

@[expose] public section

/-! The deep-stage cycle and path estimates after arbitrary later physical
deletions. The domain is the whole current ambient vertex type. No root
spokes are added to the common-path requirements. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
set_option maxRecDepth 4096
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_local_configurations_after_physical_rim_deletion
    (r:ℕ) (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (βC βP zeta:ℝ)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (hc:MarkedLocalConfigurationsWithSpokes r P π d Finset.univ βC βP σ H)
    (D:SimpleGraph V) (hD:∀ x,(D.degree x:ℝ)≤zeta*Fintype.card V):
    MarkedLocalConfigurationsWithSpokes r P π d Finset.univ
      (βC-(r+5:ℕ)*zeta) (βP-(r+7:ℕ)*zeta) (rawMarkedDeleteRims σ D.edgeFinset) H:=by
  constructor
  · intro u
    have hl:=marked_base_physical_rim_deletion_loss P π d (r+4) (by omega)
      (Finset.univ.filter (H false · u)) (Finset.univ.filter (H true · u)) σ D (zeta*Fintype.card V) hD
    have he:(((r+4:ℕ):ℝ)+1)*(zeta*Fintype.card V)*(Fintype.card V:ℝ)^(r+4)=
      (r+5:ℕ)*zeta*(Fintype.card V:ℝ)^(r+5):=by
      simp only [show r+5=(r+4)+1 by omega,Nat.cast_add,Nat.cast_one,pow_succ];ring
    rw [he] at hl
    have hh:=hc.1 u
    simp only [Finset.card_univ] at hh ⊢
    nlinarith only [hh,hl]
  · intro u j v v' hv
    have hl:=marked_path_physical_rim_deletion_loss P π d (r+3) j v v'
      (Finset.univ.filter (H false · u)) (Finset.univ.filter (H true · u)) σ D (zeta*Fintype.card V) hD
    have he:(((r+3:ℕ):ℝ)+4)*(zeta*Fintype.card V)*(Fintype.card V:ℝ)^(r+3)=
      (r+7:ℕ)*zeta*(Fintype.card V:ℝ)^(r+4):=by
      simp only [show r+4=(r+3)+1 by omega,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,pow_succ];ring
    rw [he] at hl
    have hh:=hc.2 u j v v' hv
    simp only [Finset.card_univ] at hh ⊢
    nlinarith only [hh,hl]

theorem marked_local_configurations_after_physical_deletion
    (r:ℕ) (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (βC βP zetaR zetaS:ℝ)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (hc:MarkedLocalConfigurationsWithSpokes r P π d Finset.univ βC βP σ H)
    (DR:SimpleGraph V) (DS:SimpleGraph (V⊕U))
    (hrim:∀ x,(DR.degree x:ℝ)≤zetaR*Fintype.card V)
    (hcol:∀ u,(DS.degree (Sum.inr u):ℝ)≤zetaS*Fintype.card V):
    MarkedLocalConfigurationsWithSpokes r P π d Finset.univ
      (βC-(r+5:ℕ)*(zetaR+zetaS)) (βP-(r+7:ℕ)*zetaR-(r+4:ℕ)*zetaS)
      (rawMarkedDeleteRims σ DR.edgeFinset) (markedDeletePhysicalSpokes H DS):=by
  have hchange (a:Bool) (u:U):
      (((Finset.univ.filter (H a · u))\(Finset.univ.filter (markedDeletePhysicalSpokes H DS a · u))).card:ℝ)
        ≤zetaS*(Finset.univ:Finset V).card:=by
    apply (filter_sdiff_card_le_change_sum Finset.univ _ _).trans
    simpa only [Finset.card_univ] using
      (marked_spoke_physical_deletion_column_change H DS Finset.univ a u).trans (hcol u)
  have hsp:=markedLocalPhysicalCounts_class_changes r (3*d) P π Finset.univ
    (fun u=>Finset.univ.filter (H false · u)) (fun u=>Finset.univ.filter (H true · u))
    (fun u=>Finset.univ.filter (markedDeletePhysicalSpokes H DS false · u))
    (fun u=>Finset.univ.filter (markedDeletePhysicalSpokes H DS true · u))
    (fun _=>Finset.filter_subset _ _) (fun _=>Finset.filter_subset _ _)
    (fun _=>Finset.filter_subset _ _) (fun _=>Finset.filter_subset _ _)
    βC βP zetaS (hchange false) (hchange true) (fun e=>σ (Sum.inl e)) hc
  have h:=marked_local_configurations_after_physical_rim_deletion r P π d
    (βC-(r+5:ℕ)*zetaS) (βP-(r+4:ℕ)*zetaS) zetaR σ (markedDeletePhysicalSpokes H DS) hsp DR hrim
  convert h using 1 <;> ring

end Oberwolfach
