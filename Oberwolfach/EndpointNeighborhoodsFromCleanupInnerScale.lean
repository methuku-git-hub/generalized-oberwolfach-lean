module

public import Oberwolfach.EndpointNeighborhoodsFromCleanup
public import Oberwolfach.OrdinaryPhysicalInnerEndpointDomain

@[expose] public section
/-! Endpoint common-neighborhood lower bounds can be expressed in the
actual inner physical scale, without the ambient-to-inner ratio. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

theorem endpoint_neighbour_counts_mono
    {W:Type} [Fintype W] [DecidableEq W] (Q F:SimpleGraph W) (S T:Finset W) (a b:ℝ)
    (hab:a≤b) (h:EndpointNeighbourCounts Q F S T b):EndpointNeighbourCounts Q F S T a :=by
  refine ⟨hab.trans h.indices,?_,?_⟩
  · intro Y J hY hJ hYc hJc hsum
    exact hab.trans (h.rows Y J hY hJ hYc hJc hsum)
  · intro v hv w hw hne hF
    exact hab.trans (h.pairs v hv w hw hne hF)

theorem endpoint_neighborhoods_from_cleanup_inner_scale
    (P Q F:SimpleGraph V) (H:V→U→Prop) (A:Finset V) (B:Finset U)
    (π:Equiv.Perm V) (d:ℕ) (j:Color) (s:U→Color→ℝ)
    (γ κ p pR pH density tR tH L Ledit βe βh δ ε:ℝ) (σ:RawWheelOutcome V U Γ Color)
    (profile:OrdinaryCleanupParentProfiles P Q F H π d A B pR pH density tR tH Ledit βe βh s j σ)
    (deep:RawOrdinaryRows P π d 3 A pR s j tR σ)
    (geom:EndpointPhysicalEditedConditions P Q F H A B Aᶜ π d j κ p pR pH L Ledit δ σ)
    (hrowbudget:tR+4*Ledit≤ε*A.card) (hindexbudget:tH+3*Ledit≤ε*B.card)
    (hLA:L≤(A.card:ℝ)/24) (hε:ε≤min (p^4/16) (p^3/2))
    (hA:A.Nonempty) (hB:B.card≤A.card) (hγ:0≤γ) (hγcap:2*γ≤endpointCountCoefficient p κ)
    (hdeg:∀x∉A,∀v∈insert x A,(3/4:ℝ)*A.card≤((A∩P.neighborFinset v).card:ℝ)):
    ∀i:{v:V // v∉A},EndpointNeighbourCounts
      (ordinaryPhysicalGraph (spanningRestriction Q A) (fun v u=>H v u∧v∈A∧u∈B))
      (ordinaryPhysicalGraph F (fun _ _=>False))
      ((ordinaryBoundaryRimSet Q A i).image Sum.inl) ((ordinaryBoundaryRowSet H A B i).image Sum.inr)
      (γ*(ordinaryPhysicalInnerDomain A B).card) :=by
  have hV:0<Fintype.card V:=Fintype.card_pos_iff.mpr ⟨hA.choose⟩
  have hn:0<(Fintype.card (V⊕U):ℝ):=by
    have hh:Fintype.card V≤Fintype.card (V⊕U):=Fintype.card_le_of_injective Sum.inl Sum.inl_injective
    exact_mod_cast (show 0<Fintype.card (V⊕U) by omega)
  let γambient:ℝ:=endpointCountCoefficient p κ*A.card/Fintype.card (V⊕U)
  have heq:γambient*Fintype.card (V⊕U)=endpointCountCoefficient p κ*A.card:=by
    dsimp [γambient]
    exact div_mul_cancel₀ _ (ne_of_gt hn)
  have hcounts:=endpoint_neighborhoods_from_cleanup P Q F H A B π d j s γambient κ p pR pH density
    tR tH L Ledit βe βh δ ε σ profile deep geom hrowbudget hindexbudget hLA hε (le_of_eq heq) hdeg
  have hcard:(ordinaryPhysicalInnerDomain A B).card=A.card+B.card:=ordinary_physical_inner_domain_card A B
  have hscale:γ*(ordinaryPhysicalInnerDomain A B).card≤γambient*Fintype.card (V⊕U):=by
    rw [heq,hcard,Nat.cast_add]
    have hB':(B.card:ℝ)≤A.card:=by exact_mod_cast hB
    have hmul:=mul_le_mul_of_nonneg_right hγcap (show (0:ℝ)≤A.card by positivity)
    nlinarith [mul_nonneg hγ (sub_nonneg.mpr hB')]
  intro i
  exact endpoint_neighbour_counts_mono _ _ _ _ _ _ hscale (hcounts i)
end Oberwolfach
