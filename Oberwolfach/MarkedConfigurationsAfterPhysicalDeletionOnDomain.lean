module

public import Oberwolfach.MarkedConfigurationRimDeletionOnDomain
public import Oberwolfach.MarkedConfigurationPathDeletionOnDomain
public import Oberwolfach.MarkedNeighbourhoodPhysicalDeletion

@[expose] public section

/-! Cycle and path estimates on a fixed invariant free-coordinate domain.
All ambient roots are retained; deleted neighbours are counted into that
domain, including for external roots. Tested root spokes remain omitted. -/
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

theorem marked_local_configurations_after_physical_rim_deletion_on_domain
    (r:ℕ) (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (A:Finset V) (hA:∀ x,π x∈A↔x∈A) (βC βP zeta:ℝ)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (hc:MarkedLocalConfigurationsWithSpokes r P π d A βC βP σ H)
    (D:SimpleGraph V) (hD:∀ x,((D.neighborFinset x∩A).card:ℝ)≤zeta*A.card):
    MarkedLocalConfigurationsWithSpokes r P π d A
      (βC-(r+5:ℕ)*zeta) (βP-(r+7:ℕ)*zeta) (rawMarkedDeleteRims σ D.edgeFinset) H:=by
  have hDs:=physical_deletion_invariant_domain_sum D π A hA (zeta*A.card) hD
  constructor
  · intro u
    have hl:=marked_base_physical_rim_deletion_loss_on_domain P π d (r+4) (by omega)
      A (A.filter (H false · u)) (A.filter (H true · u))
      (Finset.filter_subset _ _) (Finset.filter_subset _ _) σ D (zeta*A.card) hDs
    have he:(((r+4:ℕ):ℝ)+1)*(zeta*A.card)*(A.card:ℝ)^(r+4)=
      (r+5:ℕ)*zeta*(A.card:ℝ)^(r+5):=by
      simp only [show r+5=(r+4)+1 by omega,Nat.cast_add,Nat.cast_one,pow_succ];ring
    rw [he] at hl
    have hh:=hc.1 u
    nlinarith only [hh,hl]
  · intro u j v v' hv
    have hl:=marked_path_physical_rim_deletion_loss_on_domain P π d (r+3) j v v'
      A (A.filter (H false · u)) (A.filter (H true · u))
      (Finset.filter_subset _ _) (Finset.filter_subset _ _) σ D (zeta*A.card) hDs
    have he:(((r+3:ℕ):ℝ)+4)*(zeta*A.card)*(A.card:ℝ)^(r+3)=
      (r+7:ℕ)*zeta*(A.card:ℝ)^(r+4):=by
      simp only [show r+4=(r+3)+1 by omega,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,pow_succ];ring
    rw [he] at hl
    have hh:=hc.2 u j v v' hv
    nlinarith only [hh,hl]

theorem marked_local_configurations_after_physical_deletion_on_domain
    (r:ℕ) (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (A:Finset V) (hA:∀ x,π x∈A↔x∈A) (βC βP zetaR zetaS:ℝ)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (hc:MarkedLocalConfigurationsWithSpokes r P π d A βC βP σ H)
    (DR:SimpleGraph V) (DS:SimpleGraph (V⊕U))
    (hrim:∀ x,((DR.neighborFinset x∩A).card:ℝ)≤zetaR*A.card)
    (hcol:∀ u,((A.filter (fun x=>DS.Adj (Sum.inl x) (Sum.inr u))).card:ℝ)≤zetaS*A.card):
    MarkedLocalConfigurationsWithSpokes r P π d A
      (βC-(r+5:ℕ)*(zetaR+zetaS)) (βP-(r+7:ℕ)*zetaR-(r+4:ℕ)*zetaS)
      (rawMarkedDeleteRims σ DR.edgeFinset) (markedDeletePhysicalSpokes H DS):=by
  have hchange (a:Bool) (u:U):
      (((A.filter (H a · u))\(A.filter (markedDeletePhysicalSpokes H DS a · u))).card:ℝ)
        ≤zetaS*(A:Finset V).card:=by
    apply (filter_sdiff_card_le_change_sum A _ _).trans
    have he:(∑ x∈A,if ¬(H a x u↔markedDeletePhysicalSpokes H DS a x u) then (1:ℝ) else 0)≤
        ((A.filter (fun x=>DS.Adj (Sum.inl x) (Sum.inr u))).card:ℝ):=by
      calc
        _ ≤∑ x∈A,if DS.Adj (Sum.inl x) (Sum.inr u) then (1:ℝ) else 0:=by
          apply Finset.sum_le_sum
          intro x _
          unfold markedDeletePhysicalSpokes
          split_ifs <;> simp_all
        _ = _:=by simp only [←Finset.sum_filter,Finset.sum_const,nsmul_eq_mul,mul_one]
    exact he.trans (hcol u)
  have hsp:=markedLocalPhysicalCounts_class_changes r (3*d) P π A
    (fun u=>A.filter (H false · u)) (fun u=>A.filter (H true · u))
    (fun u=>A.filter (markedDeletePhysicalSpokes H DS false · u))
    (fun u=>A.filter (markedDeletePhysicalSpokes H DS true · u))
    (fun _=>Finset.filter_subset _ _) (fun _=>Finset.filter_subset _ _)
    (fun _=>Finset.filter_subset _ _) (fun _=>Finset.filter_subset _ _)
    βC βP zetaS (hchange false) (hchange true) (fun e=>σ (Sum.inl e)) hc
  have h:=marked_local_configurations_after_physical_rim_deletion_on_domain r P π d A hA
    (βC-(r+5:ℕ)*zetaS) (βP-(r+4:ℕ)*zetaS) zetaR σ (markedDeletePhysicalSpokes H DS) hsp DR hrim
  convert h using 1 <;> ring

end Oberwolfach
