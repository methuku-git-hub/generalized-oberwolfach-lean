module

public import Oberwolfach.MarkedPotentialHubStability
public import Oberwolfach.MarkedNeighbourhoodPhysicalDeletion
public import Oberwolfach.FiniteCenteredDomainRestriction

@[expose] public section

/-! Compatible hubs on a fixed embedded hub domain. The later physical
spoke deletion is charged by its realized row degrees. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W U Z:Type} [Fintype V] [Fintype W] [Fintype U] [Fintype Z]
  [LinearOrder V] [LinearOrder W] [DecidableEq U] [DecidableEq Z]

theorem potentialMarkedHubs_embedding_loss (f:W↪V) (g:Z↪U) (H:Bool→V→U→Prop)
    {m:ℕ} (C:Fin (m+1)→W):
    ((potentialMarkedHubs H (f∘C)).card:ℝ)-
      (potentialMarkedHubs (fun b x u=>H b (f x) (g u)) C).card≤(Finset.univ\Finset.univ.image g).card:=by
  let A:=Finset.univ.image g
  let J:=fun u=>∀ i,H (decide (i=0)) (f (C i)) u
  have he:(potentialMarkedHubs (fun b x u=>H b (f x) (g u)) C).image g=
      A.filter J:=by
    ext u
    simp only [Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and,potentialMarkedHubs,common,Function.comp_apply,J,A,true_implies]
    constructor
    · rintro ⟨v,hv,rfl⟩;exact ⟨⟨v,rfl⟩,hv⟩
    · rintro ⟨⟨v,rfl⟩,hv⟩;exact ⟨v,hv,rfl⟩
  have hc:((potentialMarkedHubs (fun b x u=>H b (f x) (g u)) C).card:ℝ)=(A.filter J).card:=by
    rw [←he,Finset.card_image_of_injective _ g.injective]
  rw [hc]
  have hh:=finite_bounded_sum_restriction A Finset.univ (Finset.subset_univ _)
    (fun u=>if J u then (1:ℝ) else 0) (by intro u _;split_ifs <;> norm_num)
  have heS (B:Finset U):(∑ u∈B,if J u then (1:ℝ) else 0)=((B.filter J).card:ℝ):=by
    simp only [Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  rw [heS,heS] at hh
  have hlo:=(abs_le.mp hh).1
  have heP:potentialMarkedHubs H (f∘C)=Finset.univ.filter J:=by
    ext u;simp [potentialMarkedHubs,common,J]
  rw [heP]
  linarith only [hlo]

theorem marked_protected_active_compatible_hubs (f:W↪V) (g:Z↪U) (H:Bool→V→U→Prop)
    (DS:SimpleGraph (V⊕U)) (δ:ℝ)
    (hDS:∀ x,((DS.comap (Sum.map f g)).degree (Sum.inl x):ℝ)≤δ)
    {m:ℕ} (C:Fin (m+1)→W):
    ((potentialMarkedHubs H (f∘C)).card:ℝ)-
      (potentialMarkedHubs (fun b x u=>markedDeletePhysicalSpokes H DS b (f x) (g u)) C).card≤
      (Finset.univ\Finset.univ.image g).card+(m+1:ℕ)*δ:=by
  let H₀:=fun b x u=>H b (f x) (g u)
  let HA:=fun b x u=>markedDeletePhysicalSpokes H DS b (f x) (g u)
  have hv:=potentialMarkedHubs_embedding_loss f g H C
  have hd:=potentialMarkedHubs_change H₀ HA C δ (by
    intro b x
    convert (marked_spoke_physical_deletion_row_change H₀ (DS.comap (Sum.map f g)) Finset.univ b x).trans (hDS x) using 1
    apply Finset.sum_congr rfl
    intro u _
    unfold bipAdj
    congr! )
  have hlo:=(abs_le.mp hd).1
  push_cast at hlo ⊢
  linarith only [hv,hlo]

end Oberwolfach
