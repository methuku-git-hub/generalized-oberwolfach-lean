module

public import Oberwolfach.ResidualActualFamilyExactReservation
public import Oberwolfach.MarkedReservedResourceGraphs
public import Oberwolfach.RawMarkedRimDeletion

@[expose] public section
/-! Reserved physical rim edges remain in the host after deleting the full
images of the actual glued factor remnants. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I V:Type} [Fintype I] [DecidableEq I] [Fintype V] [LinearOrder V]
  {X:I→Type} [∀i,Fintype (X i)] [∀i,DecidableEq (X i)]

theorem actual_glued_factor_images_avoid_reserved_physical_deletion
    (F:∀i,SimpleGraph (X i)) (f:∀i,X i→V)
    (C:Finset (Finset V⊕(V×I))) (D:SimpleGraph V)
    (hD:D.edgeFinset⊆Finset.univ.biUnion (fun i=>((F i).edgeFinset).image (Sym2.map (f i))))
    (hAvoid:∀i,Disjoint (((F i).edgeFinset).image (Sym2.map (f i)))
      (physicalEdgeGraph (markedReservedRimPairs C)).edgeFinset):
    ∀e:Sym2 V,Sum.inl e.toFinset∈C→e∉D.edgeFinset :=by
  intro e hC
  induction e using Sym2.ind with
  | _ x y =>
    by_cases hxy:x=y
    · subst y
      simpa only [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet] using D.loopless.irrefl x
    · have hR:(physicalEdgeGraph (markedReservedRimPairs C)).Adj x y:=by
        apply ((marked_reserved_resource_graphs C).1 x y).mpr
        exact ⟨hxy,by simpa only [Sym2.toFinset_mk_eq] using hC⟩
      have he:s(x,y)∈(physicalEdgeGraph (markedReservedRimPairs C)).edgeFinset:=by
        simpa only [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet] using hR
      intro hd
      obtain ⟨i,_,hi⟩:=Finset.mem_biUnion.mp (hD hd)
      exact (Finset.disjoint_left.mp (hAvoid i)) hi he

theorem actual_glued_factor_images_preserve_typed_rims {Γ Color:Type} [Fintype Γ] [Fintype Color]
    (F:∀i,SimpleGraph (X i)) (f:∀i,X i→V)
    (C:Finset (Finset V⊕(V×I))) (P D:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (σ:RawMarkedOutcome V I Γ Color)
    (hD:D.edgeFinset⊆Finset.univ.biUnion (fun i=>((F i).edgeFinset).image (Sym2.map (f i))))
    (hAvoid:∀i,Disjoint (((F i).edgeFinset).image (Sym2.map (f i)))
      (physicalEdgeGraph (markedReservedRimPairs C)).edgeFinset):
    ∀e:(V×V)⊕(V×V),Sum.inl (markedPairPhysical π e).toFinset∈C→
      (rawMarkedPairRims P π d (rawMarkedDeleteRims σ D.edgeFinset) e ↔ rawMarkedPairRims P π d σ e) :=by
  intro e hC
  rw [rawMarkedDeleteRims_rims]
  have hn:=actual_glued_factor_images_avoid_reserved_physical_deletion F f C D hD hAvoid (markedPairPhysical π e) hC
  simp [hn]

theorem actual_glued_factor_images_preserve_reserved_rims
    (F:∀i,SimpleGraph (X i)) (f:∀i,X i→V)
    (C:Finset (Finset V⊕(V×I))) (P D:SimpleGraph V)
    (hD:D.edgeFinset⊆Finset.univ.biUnion (fun i=>((F i).edgeFinset).image (Sym2.map (f i))))
    (hAvoid:∀i,Disjoint (((F i).edgeFinset).image (Sym2.map (f i)))
      (physicalEdgeGraph (markedReservedRimPairs C)).edgeFinset):
    ∀x y,P.Adj x y→Sum.inl ({x,y}:Finset V)∈C→(P\D).Adj x y :=by
  intro x y hP hC
  have hR:(physicalEdgeGraph (markedReservedRimPairs C)).Adj x y:=
    ((marked_reserved_resource_graphs C).1 x y).mpr ⟨hP.ne,hC⟩
  have he:s(x,y)∈(physicalEdgeGraph (markedReservedRimPairs C)).edgeFinset:=by
    simpa only [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet] using hR
  have hnot:¬D.Adj x y:=by
    intro hd
    have hd':s(x,y)∈D.edgeFinset:=by simpa only [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet] using hd
    obtain ⟨i,_,hi⟩:=Finset.mem_biUnion.mp (hD hd')
    exact (Finset.disjoint_left.mp (hAvoid i)) hi he
  exact ⟨hP,hnot⟩
end Oberwolfach
