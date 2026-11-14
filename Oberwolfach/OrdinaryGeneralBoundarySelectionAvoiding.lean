module

public import Oberwolfach.OrdinaryFreshPairingActualHostAvoiding
public import Oberwolfach.OrdinaryBoundarySeparateClassChanges
public import Oberwolfach.OrdinaryBoundarySupportFromSample
public import Oberwolfach.OrdinaryBoundaryClassDivisibilityGeneral
public import Oberwolfach.OrdinaryBoundaryFactorClassesAfterPacking
public import Oberwolfach.OrdinaryBoundaryClassesMonotone

@[expose] public section
/-! Actual triangle boundary factors after packing, with class overlap,
class changes, balance and divisibility discharged from the actual graph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_general_sampled_boundary_selection_avoiding
    (m:ℕ)
    (Q₀ Q Q' F:SimpleGraph V) (H₀ H H':V→U→Prop) (X:Finset V) (Z:Finset U)
    (C D K:SimpleGraph (V⊕U)) (σ:Sym2 (V⊕U)→Bool) (p ρ ζ ε L δ:ℝ)
    (hgood:MixedFreshPairingAvoidingEvent m p ρ ζ Q F (ordinaryPhysicalGraph Q H)
      (ordinaryPhysicalGraph F (fun _ _=>False)) (Function.Embedding.inl:V↪V⊕U)
      (ordinaryBoundaryHubSet H₀ Z X)
      (fun i=>(ordinaryBoundaryRimSet Q₀ X i).image Sum.inl)
      (fun i=>(ordinaryBoundaryRowSet H₀ X Z i).image Sum.inr)
      (fun j=>hubSpokeCoin j.val) (fun i=>physicalIncidentCoin (Sum.inl i.val))
      σ)
    (hτ:0≤p) (hsample:BoundaryReserveSupportGood (ordinaryBoundaryGraph Q₀ H₀ X Z) p ε σ)
    (hCR:Disjoint C (retainedGraph (ordinaryBoundaryGraph Q₀ H₀ X Z) σ))
    (hphys:ordinaryBoundaryGraph Q' H' X Z=((ordinaryBoundaryGraph Q₀ H₀ X Z\C)\D))
    (hL:∀w,((((ordinaryBoundaryGraph Q₀ H₀ X Z)\retainedGraph (ordinaryBoundaryGraph Q₀ H₀ X Z) σ)\C).degree w:ℝ)+
      (D.degree w:ℝ)≤L)
    (hK:∀w,(K.degree w:ℝ)≤δ)
    (hkeep:ordinaryPhysicalGraph Q H\K≤ordinaryPhysicalGraph Q' H')
    (hNoR:∀v∉X,∀w∉X,¬Q'.Adj v w)
    (hNoS:∀v∉X,∀u∉Z,¬H' v u)
    (hbal:∀v,Q'.degree v=2*(Finset.univ.filter (H' v)).card)
    (hdiv:∀u,(m+1)∣(Finset.univ.filter (fun v=>H' v u)).card)
    (hdeg:(p+ε)*Fintype.card (V⊕U)+L≤ρ*Fintype.card (V⊕U))
    (hpair:(p^2+ε)*Fintype.card (V⊕U)+2*L≤ρ^2*Fintype.card (V⊕U))
    (hscaleY:∀j:{u:U // u∉Z},L≤ζ*(p*(ordinaryBoundaryHubSet H₀ Z X j).card))
    (hscaleZ:L≤ζ*(p*Fintype.card (V⊕U)))
    (hbudgetY:∀j:{u:U // u∉Z},2*(ρ*Real.sqrt ρ*Fintype.card (V⊕U))+
      2*(Nat.ceil (4*(ρ*Real.sqrt ρ*Fintype.card (V⊕U))):ℝ)+δ≤ζ*(p*(ordinaryBoundaryHubSet H₀ Z X j).card))
    (hbudgetZ:2*(ρ*Real.sqrt ρ*Fintype.card (V⊕U))+
      2*(Nat.ceil (4*(ρ*Real.sqrt ρ*Fintype.card (V⊕U))):ℝ)+δ≤ζ*(p*Fintype.card (V⊕U))):
    Nonempty (OrdinaryPairingSelectedFactorsAvoiding m Q' F H' (ordinaryBoundaryRimSet Q' X) (ordinaryBoundaryRowSet H' X Z)
      (ordinaryBoundaryHubSet H₀ Z X) (ordinaryBoundaryHubSet H' Z X) (2*(ρ*Fintype.card (V⊕U))) K):=by
  let G:=ordinaryBoundaryGraph Q₀ H₀ X Z
  have hsub:ordinaryBoundaryGraph Q' H' X Z≤G:=by rw [hphys];exact sdiff_le.trans sdiff_le
  have hm:=ordinary_boundary_classes_of_subgraph Q₀ Q' H₀ H' X Z hsub
  have hA (i:{v:V // v∉X}):(ordinaryBoundaryRimSet Q' X i).image (Sum.inl:V→V⊕U)⊆
      (ordinaryBoundaryRimSet Q₀ X i).image (Sum.inl:V→V⊕U):=Finset.image_subset_image (hm.2.1 i)
  have hB (i:{v:V // v∉X}):(ordinaryBoundaryRowSet H' X Z i).image (Sum.inr:U→V⊕U)⊆
      (ordinaryBoundaryRowSet H₀ X Z i).image (Sum.inr:U→V⊕U):=Finset.image_subset_image (hm.2.2 i)
  have hd:=ordinary_boundary_local_class_divisibility_general (m+1) Q' H' X Z hNoR hNoS hbal hdiv
  have hc:=ordinary_boundary_factor_classes_after_packing Q₀ Q' H₀ H' X Z C D σ L hCR hphys hL
  have hs:=ordinary_boundary_supports_from_sample Q' H' X Z G C D σ p ε L ρ hτ hsample hCR hL
    (le_of_eq hphys) hdeg hpair
  apply ordinary_fresh_pairing_actual_host_avoiding m p ρ ζ Q Q' F H H' _ _ _ _ _ σ hgood
    (ordinaryBoundaryHubSet H' Z X) (ordinaryBoundaryRimSet Q' X) (ordinaryBoundaryRowSet H' X Z)
    hA hB K δ hK hm.1 hd.2 hd.1
  · intro j;exact (hc.1 j).trans (hscaleY j)
  · intro i
    have hsep:=ordinary_boundary_separate_class_changes (ordinaryBoundaryRimSet Q₀ X i) (ordinaryBoundaryRimSet Q' X i)
      (ordinaryBoundaryRowSet H₀ X Z i) (ordinaryBoundaryRowSet H' X Z i)
      (fun w=>σ (physicalIncidentCoin (Sum.inl i.val) w)=true)
    have hfull:((changed ((ordinaryBoundaryRimSet Q' X i).image Sum.inl∪(ordinaryBoundaryRowSet H' X Z i).image Sum.inr)
      (((ordinaryBoundaryRimSet Q₀ X i).image Sum.inl∪(ordinaryBoundaryRowSet H₀ X Z i).image Sum.inr).filter
        (fun w=>σ (physicalIncidentCoin (Sum.inl i.val) w)=true))).card:ℝ)≤L:=by
      rw [changed_card_eq_differences]
      exact hc.2 i
    calc
      _ ≤ ((changed ((ordinaryBoundaryRimSet Q' X i).image Sum.inl∪(ordinaryBoundaryRowSet H' X Z i).image Sum.inr)
        (((ordinaryBoundaryRimSet Q₀ X i).image Sum.inl∪(ordinaryBoundaryRowSet H₀ X Z i).image Sum.inr).filter
          (fun w=>σ (physicalIncidentCoin (Sum.inl i.val) w)=true))).card:ℝ) := by
        convert (Nat.cast_le (α:=ℝ)).mpr hsep.1 using 1 <;> congr! 12 <;> exact Subsingleton.elim _ _
      _ ≤ _ := hfull.trans hscaleZ
  · intro i
    have hsep:=ordinary_boundary_separate_class_changes (ordinaryBoundaryRimSet Q₀ X i) (ordinaryBoundaryRimSet Q' X i)
      (ordinaryBoundaryRowSet H₀ X Z i) (ordinaryBoundaryRowSet H' X Z i)
      (fun w=>σ (physicalIncidentCoin (Sum.inl i.val) w)=true)
    have hfull:((changed ((ordinaryBoundaryRimSet Q' X i).image Sum.inl∪(ordinaryBoundaryRowSet H' X Z i).image Sum.inr)
      (((ordinaryBoundaryRimSet Q₀ X i).image Sum.inl∪(ordinaryBoundaryRowSet H₀ X Z i).image Sum.inr).filter
        (fun w=>σ (physicalIncidentCoin (Sum.inl i.val) w)=true))).card:ℝ)≤L:=by
      rw [changed_card_eq_differences]
      exact hc.2 i
    calc
      _ ≤ ((changed ((ordinaryBoundaryRimSet Q' X i).image Sum.inl∪(ordinaryBoundaryRowSet H' X Z i).image Sum.inr)
        (((ordinaryBoundaryRimSet Q₀ X i).image Sum.inl∪(ordinaryBoundaryRowSet H₀ X Z i).image Sum.inr).filter
          (fun w=>σ (physicalIncidentCoin (Sum.inl i.val) w)=true))).card:ℝ) := by
        convert (Nat.cast_le (α:=ℝ)).mpr hsep.2 using 1 <;> congr! 12 <;> exact Subsingleton.elim _ _
      _ ≤ _ := hfull.trans hscaleZ
  · intro a b hab
    have hh:=hs.1 a b hab
    convert hh using 1 <;> simp only [ordinaryBoundaryPhysicalSupports] <;> congr! 12 <;> exact Subsingleton.elim _ _
  · intro w
    have hh:=hs.2 w
    convert hh using 1 <;> simp only [ordinaryBoundaryPhysicalSupports] <;> congr! 12 <;> exact Subsingleton.elim _ _
  · exact hbudgetY
  · exact hbudgetZ
  · exact hkeep
end Oberwolfach
