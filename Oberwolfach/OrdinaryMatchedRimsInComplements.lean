module

public import Oberwolfach.OrdinaryMatchingPacksCoverRims
public import Oberwolfach.OrdinaryRequiredEdgesCovered
public import Oberwolfach.PhysicalRimResourceResidual

@[expose] public section
/-! The same matching's covered physical rim graph lies in the actual
unreserved complementary factors once their old edges contain the packs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_matched_rims_embedded_in_complements {n q K:ℕ}
    (Fs:Fin q→SimpleGraph (Fin n)) (C:∀u,Finset (Fs u).ConnectedComponent)
    (f:∀u,{x:Fin n // (Fs u).connectedComponentMk x∉C u}↪Fin n)
    (Old New:Fin q→Finset (Sym2 (Fin n)))
    (hpartition:∀u,(((Fs u).induce {x | (Fs u).connectedComponentMk x∉C u}).edgeFinset).image
      (Sym2.map (f u))=Old u∪New u)
    (π:Equiv.Perm (Fin n)) (d m:ℕ)
    (Rim:(Fin n×Fin n)⊕(Fin n×Fin n)→Prop) (H:Bool→Fin n→Fin q→Prop):
    let RM:=fun W:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ (_:Fin q)=>True) (fun _ (_:Fin q)=>True)=>typedMarkedOccurrenceResources W
    let state:=typedMarkedResourceState Rim H
    let RR:=ordinaryMixedGenericResources RM (fun (i:Fin K) (W:OrderedOrdinaryWheel (U:=Fin q) π (3*d) (longPaddedSeedExponent i+2))=>orderedOrdinaryResources W)
    let φ:=ordinaryMixedPhysicalResource (U:=Fin q) π;
    ∀(L:Finset (PhysicalSampledCandidate (mixedCandidateResources RR) state))
    (W:∀u,OrdinaryPhysicalMarkedHub (K:=K) π d m RM state L u→
      MarkedWheel (fun e:{e:Fin n×Fin n // Rim (Sum.inl e)}=>e.val.1) (fun e=>e.val.2)
        (fun e:{e:Fin n×Fin n // Rim (Sum.inr e)}=>e.val.1) (fun e=>e.val.2) m π (3*d) (H false) (H true))
    (hW:∀u a,(W u a).1.val=(ordinaryPhysicalMarkedPayload π d m RM state L u a).1.val ∧ (W u a).2.val=u),
    let Pack:=fun u=>mixedWheelRimPack
      (fun a:OrdinaryPhysicalUnmarkedHub (K:=K) π d m RM state L u=>longPaddedSeedExponent (ordinaryPhysicalUnmarkedPayload π d m RM state L u a).1+2)
      (Finset.univ.image (W u)) (fun a=>(ordinaryPhysicalUnmarkedPayload π d m RM state L u a).2)
    let ι:PhysicalSampledActive φ state↪Sym2 (Fin n)⊕(Fin n×Fin q):=Function.Embedding.subtype _;
    (∀u edge,edge∈Pack u→∃e∈Old u,e.toFinset=edge)→
    physicalRimCoveredGraph ι (L.biUnion (physicalSampledCandidateSet φ (mixedCandidateResources RR) state))≤
      ordinaryEmbeddedComplements Fs C f:=by
  intro RM state RR φ L W hW Pack ι hPack
  have hmatching:=ordinary_matching_packs_cover_physical_rims (K:=K) π d m Rim H L W hW
  have hcover:∀e∈(physicalRimCoveredGraph ι (L.biUnion (physicalSampledCandidateSet φ (mixedCandidateResources RR) state))).edgeFinset,
      ∃u,e∈Old u:=by
    intro e he
    induction e using Sym2.ind with
    | _ x y =>
      have hadj:=(SimpleGraph.mem_edgeFinset.mp he)
      obtain ⟨_,z,hz,hze⟩:=hadj
      obtain ⟨c,hc,hzc⟩:=Finset.mem_biUnion.mp hz
      have heq:z.val=Sum.inl s(x,y):=hze
      obtain ⟨u,hu⟩:=hmatching c hc z hzc s(x,y) heq
      obtain ⟨e',he',hEq⟩:=hPack u (s(x,y).toFinset) hu
      have ee:e'=s(x,y):=sym2_toFinset_injective_local hEq
      exact ⟨u,ee ▸ he'⟩
  apply ordinary_required_edges_covered_by_complements _ Fs C f New Old ?_ hcover
  intro u
  rw [hpartition u,Finset.union_comm]
end Oberwolfach
