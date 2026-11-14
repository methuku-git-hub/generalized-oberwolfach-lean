module

public import Oberwolfach.MarkedVortexNonDeeperInnerHubs
public import Oberwolfach.MarkedVortexActiveDomainEquivalences
public import Oberwolfach.MarkedFixedVortexSizes

@[expose] public section
/-! The active hubs in the nested parent type and at the next vortex level
are the same physical set, and therefore have the same cardinality. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
variable {G:SimpleGraph V} {D m:ℕ} {β ε:ℝ} (Q:Vortex U G D β ε m)

theorem marked_vortex_active_hub_cardinality (i:ℕ):
    (markedVortexInnerNonDeeperHubs Q i).card=
      ((Finset.univ\markedVortexInnerHubs Q (i+1)):
        Finset (markedVortexHubType Q (i+1))).card:=by
  let J:=markedVortexInnerHubs Q i
  let R:=markedVortexDeeperHubs Q i
  have hB:(markedVortexInnerNonDeeperHubs Q i).card=(J\R).card:=by
    have hh:=marked_vortex_inner_nondeeper_hubs_image Q i
    rw [←hh,Finset.card_image_of_injective _ (markedVortexNonDeeperHubToParent Q i).injective]
  have hnext:((Finset.univ\markedVortexInnerHubs Q (i+1)):
      Finset (markedVortexHubType Q (i+1))).card=
      (Q.extendedIndices (i+1)\Q.extendedIndices (i+2)).card:=by
    have hh:=Fintype.card_congr (markedVortexActiveHubEquiv Q (i+1))
    change Fintype.card ↥((Finset.univ\markedVortexInnerHubs Q (i+1)):
      Finset (markedVortexHubType Q (i+1)))=Fintype.card ↥(Q.extendedIndices (i+1)\Q.extendedIndices (i+1+1)) at hh
    simpa only [Fintype.card_coe,Nat.add_assoc,show 1+1=2 by omega] using hh
  obtain ⟨_,_,hJ,hR⟩:=marked_vortex_inner_cardinalities Q i
  have hsub:R⊆J:=by
    intro x hx
    have hh:x.val∈Q.extendedIndices (i+2):=(Finset.mem_filter.mp hx).2
    have hnest:=Q.extendedIndices_subset (show i+1 ≤ i+2 by omega)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hnest hh⟩
  have hsubphys:Q.extendedIndices (i+2)⊆Q.extendedIndices (i+1):=
    Q.extendedIndices_subset (by omega)
  rw [hB,hnext,Finset.card_sdiff,Finset.card_sdiff,Finset.inter_eq_left.mpr hsub,
    Finset.inter_eq_left.mpr hsubphys,hJ,hR]
end Oberwolfach

namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
variable {G:SimpleGraph V} {D m:ℕ} {β ε:ℝ} (Q:Vortex U G D β ε m)

theorem marked_vortex_active_hub_degree_target (i:ℕ) (rho:ℝ):
    2*((((Finset.univ\markedVortexInnerHubs Q (i+1)):
      Finset (markedVortexHubType Q (i+1))).card):ℝ)/rho=
      2*((markedVortexInnerNonDeeperHubs Q i).card:ℝ)/rho:=by
  rw [marked_vortex_active_hub_cardinality Q i]
end Oberwolfach
