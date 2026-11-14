module

public import Oberwolfach.OrdinaryUncoveredMarkedSpokeRow

@[expose] public section

/-! If covered physical spokes are in the old image, every unused sampled
ordinary spoke injects into the same matching's uncovered hub row. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]

theorem ordinary_unused_spokes_le_physical_row
    (π:Equiv.Perm (Fin n)) (d m:ℕ)
    (Rim:(Fin n×Fin n)⊕(Fin n×Fin n)→Prop) (H:Bool→Fin n→U→Prop):
    let RM:=fun W:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ (_:U)=>True) (fun _ (_:U)=>True)=>typedMarkedOccurrenceResources W
    let state:=typedMarkedResourceState Rim H
    let RR:=ordinaryMixedGenericResources RM (fun (i:Fin K) (W:OrderedOrdinaryWheel (U:=U) π (3*d) (longPaddedSeedExponent i+2))=>orderedOrdinaryResources W)
    let φ:=ordinaryMixedPhysicalResource (U:=U) π;
    ∀(L:Finset (PhysicalSampledCandidate (mixedCandidateResources RR) state)) (u:U) (Old:Finset (Fin n)),
    let Q:=physicalSampledCandidateSet φ (mixedCandidateResources RR) state
    let Row:=physicalSampledRow φ state (ordinaryPhysicalRow (.inr (.inr u)));
    (∀v,H false v u→∀c∈L,∀x:PhysicalSampledActive φ state,
      x.val=Sum.inr (v,u)→x∈Q c→v∈Old)→
    ((Finset.univ.filter (fun v=>H false v u))\Old).card≤(Row\L.biUnion Q).card :=by
  intro RM state RR φ L u Old Q Row hOld
  let Available:=Finset.univ.filter (fun v=>H false v u)
  let T:Finset (Sym2 (Fin n)⊕(Fin n×U)):=ordinaryPhysicalRow (.inr (.inr u))
  let Inc:=T.filter (fun x=>∃a,state a=true ∧ φ a=x)
  let Matched:Finset (Sym2 (Fin n)⊕(Fin n×U)):=(L.biUnion Q).image Subtype.val
  let f:Fin n→Sym2 (Fin n)⊕(Fin n×U):=fun v=>Sum.inr (v,u)
  have hf:Function.Injective f:=by intro x y h;exact Prod.mk.inj (Sum.inr.inj h) |>.1
  have hinc:∀v∈Available,f v∈Inc:=by
    intro v hv
    have ht:H false v u:=(Finset.mem_filter.mp hv).2
    apply Finset.mem_filter.mpr
    constructor
    · simp [T,ordinaryPhysicalRow,f]
    · refine ⟨Sum.inr (false,v,u),?_,rfl⟩
      simpa only [state,typedMarkedResourceState,Sum.elim_inr,decide_eq_true_eq] using ht
  have hcover:∀v∈Available,f v∈Matched→v∈Old:=by
    intro v hv hm
    obtain ⟨x,hx,hval⟩:=Finset.mem_image.mp hm
    obtain ⟨c,hc,hcx⟩:=Finset.mem_biUnion.mp hx
    exact hOld v (Finset.mem_filter.mp hv).2 c hc x hval hcx
  have hh:=uncovered_spoke_incidence_bound Available Old Inc Matched f hf hinc hcover
  have heq:=physical_sampled_uncovered_row_card φ (mixedCandidateResources RR) state T L
  change (Row\L.biUnion Q).card=(Inc\Matched).card at heq
  rw [heq]
  exact hh
end Oberwolfach
