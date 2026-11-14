module

public import Oberwolfach.OrdinaryPhysicalMarkedSpokeCoverage
public import Oberwolfach.OrdinaryPhysicalMatchingRows
public import Oberwolfach.UncoveredSpokeIncidenceBound

@[expose] public section
/-! Every uncovered true spoke injects into the uncovered physical hub row of
the same matching. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]

theorem ordinary_uncovered_marked_spokes_le_matching_row
    (π:Equiv.Perm (Fin n)) (d m:ℕ)
    (Rim:(Fin n×Fin n)⊕(Fin n×Fin n)→Prop) (H:Bool→Fin n→U→Prop)
    (hexclusive:∀v u,H true v u→¬H false v u):
    let RM:=fun W:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ (_:U)=>True) (fun _ (_:U)=>True)=>typedMarkedOccurrenceResources W
    let state:=typedMarkedResourceState Rim H
    let RR:=ordinaryMixedGenericResources RM (fun (i:Fin K) (W:OrderedOrdinaryWheel (U:=U) π (3*d) (longPaddedSeedExponent i+2))=>orderedOrdinaryResources W)
    let φ:=ordinaryMixedPhysicalResource (U:=U) π;
    ∀(L:Finset (PhysicalSampledCandidate (mixedCandidateResources RR) state)) (u:U)
    (W:OrdinaryPhysicalMarkedHub (K:=K) π d m RM state L u→
      MarkedWheel (fun e:{e:Fin n×Fin n // Rim (Sum.inl e)}=>e.val.1) (fun e=>e.val.2)
      (fun e:{e:Fin n×Fin n // Rim (Sum.inr e)}=>e.val.1) (fun e=>e.val.2) m π (3*d) (H false) (H true))
    (hW:∀a,(W a).1.val=(ordinaryPhysicalMarkedPayload π d m RM state L u a).1.val ∧ (W a).2.val=u),
    let M:=Finset.univ.image W
    let Covered:=Finset.univ.filter (fun v=>∃Z∈M,Sum.inr (v,u)∈markedWheelPhysicalResources Z)
    let Q:=physicalSampledCandidateSet φ (mixedCandidateResources RR) state
    let Row:=physicalSampledRow φ state (ordinaryPhysicalRow (.inr (.inr u)));
    ((Finset.univ.filter (fun v=>H true v u))\Covered).card≤(Row\L.biUnion Q).card:=by
  intro RM state RR φ L u W hW M Covered Q Row
  let Available:=Finset.univ.filter (fun v=>H true v u)
  let T:Finset (Sym2 (Fin n)⊕(Fin n×U)):=ordinaryPhysicalRow (.inr (.inr u))
  let Inc:=T.filter (fun x=>∃a,state a=true ∧ φ a=x)
  let Matched:Finset (Sym2 (Fin n)⊕(Fin n×U)):=(L.biUnion Q).image Subtype.val
  let f:Fin n→Sym2 (Fin n)⊕(Fin n×U):=fun v=>Sum.inr (v,u)
  have hf:Function.Injective f:=by intro x y h;exact Prod.mk.inj (Sum.inr.inj h) |>.1
  have hinc:∀v∈Available,f v∈Inc:=by
    intro v hv
    have ht:H true v u:=(Finset.mem_filter.mp hv).2
    apply Finset.mem_filter.mpr
    constructor
    · simp [T,ordinaryPhysicalRow,f]
    · refine ⟨Sum.inr (true,v,u),?_,rfl⟩
      simpa only [state,typedMarkedResourceState,Sum.elim_inr,decide_eq_true_eq] using ht
  have hcover:∀v∈Available,f v∈Matched→v∈Covered:=by
    intro v hv hm
    have ht:H true v u:=(Finset.mem_filter.mp hv).2
    obtain ⟨x,hx,hval⟩:=Finset.mem_image.mp hm
    obtain ⟨c,hc,hcx⟩:=Finset.mem_biUnion.mp hx
    have hval':x.val=Sum.inr (v,u):=hval
    obtain ⟨a,ha⟩:=ordinary_physical_marked_spoke_coverage π d m Rim H hexclusive L u W hW c hc x v hval' hcx ht
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _,W a,Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩,ha⟩
  have h:=uncovered_spoke_incidence_bound Available Covered Inc Matched f hf hinc hcover
  have heq:=physical_sampled_uncovered_row_card φ (mixedCandidateResources RR) state T L
  change (Row\L.biUnion Q).card=(Inc\Matched).card at heq
  rw [heq]
  exact h
end Oberwolfach
