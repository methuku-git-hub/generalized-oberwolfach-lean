module

public import Oberwolfach.OrdinaryPhysicalMarkedSpokeCoverage
public import Oberwolfach.OrdinaryPhysicalMatchingRows
public import Oberwolfach.UncoveredSpokeIncidenceBound

@[expose] public section
/-! Uncovered true spokes incident with a fixed vertex inject into that
vertex's uncovered physical matching row, simultaneously across all hubs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_uncovered_marked_spokes_le_vertex_matching_row
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (π:Equiv.Perm (Fin n)) (d m:ℕ)
    (Rim:(Fin n×Fin n)⊕(Fin n×Fin n)→Prop) (H:Bool→Fin n→U→Prop)
    (hexclusive:∀v u,H true v u→¬H false v u):
    let RM:=fun W:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ (_:U)=>True) (fun _ (_:U)=>True)=>typedMarkedOccurrenceResources W
    let state:=typedMarkedResourceState Rim H
    let RR:=ordinaryMixedGenericResources RM (fun (i:Fin K) (W:OrderedOrdinaryWheel (U:=U) π (3*d) (longPaddedSeedExponent i+2))=>orderedOrdinaryResources W)
    let φ:=ordinaryMixedPhysicalResource (U:=U) π;
    ∀(L:Finset (PhysicalSampledCandidate (mixedCandidateResources RR) state))
    (W:∀u,OrdinaryPhysicalMarkedHub (K:=K) π d m RM state L u→
      MarkedWheel (fun e:{e:Fin n×Fin n // Rim (Sum.inl e)}=>e.val.1) (fun e=>e.val.2)
      (fun e:{e:Fin n×Fin n // Rim (Sum.inr e)}=>e.val.1) (fun e=>e.val.2) m π (3*d) (H false) (H true))
    (hW:∀u a,(W u a).1.val=(ordinaryPhysicalMarkedPayload π d m RM state L u a).1.val ∧ (W u a).2.val=u),
    let Covered:=fun v=>Finset.univ.filter (fun u=>∃Z∈Finset.univ.image (W u),Sum.inr (v,u)∈markedWheelPhysicalResources Z)
    let Q:=physicalSampledCandidateSet φ (mixedCandidateResources RR) state
    let Row:=fun v=>physicalSampledRow φ state (ordinaryPhysicalRow (.inr (.inl v)));
    ∀v,((Finset.univ.filter (fun u=>H true v u))\Covered v).card≤(Row v\L.biUnion Q).card :=by
  intro RM state RR φ L W hW Covered Q Row v
  let Available:=Finset.univ.filter (fun u=>H true v u)
  let T:Finset (Sym2 (Fin n)⊕(Fin n×U)):=ordinaryPhysicalRow (.inr (.inl v))
  let Inc:=T.filter (fun x=>∃a,state a=true ∧ φ a=x)
  let Matched:Finset (Sym2 (Fin n)⊕(Fin n×U)):=(L.biUnion Q).image Subtype.val
  let f:U→Sym2 (Fin n)⊕(Fin n×U):=fun u=>Sum.inr (v,u)
  have hf:Function.Injective f:=by intro x y h;exact Prod.mk.inj (Sum.inr.inj h) |>.2
  have hinc:∀u∈Available,f u∈Inc:=by
    intro u hu
    have ht:H true v u:=(Finset.mem_filter.mp hu).2
    apply Finset.mem_filter.mpr
    constructor
    · simp [T,ordinaryPhysicalRow,f]
    · refine ⟨Sum.inr (true,v,u),?_,rfl⟩
      simpa only [state,typedMarkedResourceState,Sum.elim_inr,decide_eq_true_eq] using ht
  have hcover:∀u∈Available,f u∈Matched→u∈Covered v:=by
    intro u hu hm
    have ht:H true v u:=(Finset.mem_filter.mp hu).2
    obtain ⟨x,hx,hval⟩:=Finset.mem_image.mp hm
    obtain ⟨c,hc,hcx⟩:=Finset.mem_biUnion.mp hx
    have hval':x.val=Sum.inr (v,u):=hval
    obtain ⟨a,ha⟩:=ordinary_physical_marked_spoke_coverage π d m Rim H hexclusive L u (W u) (hW u) c hc x v hval' hcx ht
    simpa only [Covered,Finset.mem_filter,Finset.mem_univ,true_and] using
      (show ∃Z∈Finset.univ.image (W u),Sum.inr (v,u)∈markedWheelPhysicalResources Z from
        ⟨W u a,Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩,ha⟩)
  have h:=uncovered_spoke_incidence_bound Available (Covered v) Inc Matched f hf hinc hcover
  have heq:=physical_sampled_uncovered_row_card φ (mixedCandidateResources RR) state T L
  change (Row v\L.biUnion Q).card=(Inc\Matched).card at heq
  rw [heq]
  exact h
end Oberwolfach
