module

public import Oberwolfach.MarkedHubFactor
public import Oberwolfach.MarkedWheelResources
public import Oberwolfach.TwistedFactorDegrees
public import Oberwolfach.DisjointCycleLabels
public import Oberwolfach.PhysicalEdgeGraph

@[expose] public section

/-! The physical conclusions for a vertex-disjoint factor of actual
marked cycles. They use the original physical map and ambient successor. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K : Type*} [Fintype V] [DecidableEq V]
    {tail head : E → V} {ktail khead : K → V} {m : ℕ}
    {π : Equiv.Perm V} {b : ℕ} {H₀ Hₖ : V → U → Prop}

def hubCycleAsMarked (w : U) (C : HubMarkedCycle tail head ktail khead m π b H₀ Hₖ w) :
    MarkedCycleTuple tail head ktail khead m π b := ⟨C.val,C.property.1⟩

def hubCycleWheel (w : U) (C : HubMarkedCycle tail head ktail khead m π b H₀ Hₖ w) :
    MarkedWheel tail head ktail khead m π b H₀ Hₖ := ⟨hubCycleAsMarked w C,⟨w,C.property.2⟩⟩

def hubCyclePhysicalEdges (w : U) (C : HubMarkedCycle tail head ktail khead m π b H₀ Hₖ w) : Finset (Finset V) :=
  markedCyclePhysicalEdges tail head ktail khead m π b (hubCycleAsMarked w C)

theorem marked_factor_joint_labels (w : U)
    (M : Finset (HubMarkedCycle tail head ktail khead m π b H₀ Hₖ w))
    (hM : ∀ C∈M,∀ D∈M,C≠D → Disjoint (hubMarkedCycleVertices w C) (hubMarkedCycleVertices w D)) :
    Function.Injective (fun p : M×Fin (m+1) => p.1.val.val p.2) :=
  disjoint_resource_tuple_injective (hubMarkedCycleVertices w) (fun C => C.val)
    (fun C => permutationSeparated_injective π b C.val C.property.1.1)
    (fun C i => Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩) M hM

theorem marked_factor_physical_edges_disjoint (w : U)
    (hp : Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (M : Finset (HubMarkedCycle tail head ktail khead m π b H₀ Hₖ w))
    (hM : ∀ C∈M,∀ D∈M,C≠D → Disjoint (hubMarkedCycleVertices w C) (hubMarkedCycleVertices w D)) :
    ∀ C∈M,∀ D∈M,C≠D → Disjoint (hubCyclePhysicalEdges w C) (hubCyclePhysicalEdges w D) := by
  intro C hC D hD hCD
  apply Finset.disjoint_left.mpr
  intro e he hf
  obtain ⟨i,_,hi⟩ := Finset.mem_image.mp he
  obtain ⟨j,_,hj⟩ := Finset.mem_image.mp hf
  have htype := hp (hi.trans hj.symm)
  have htail := congrArg (Sum.elim tail ktail) htype
  have hci := (markedCycleTypedEdge_endpoints tail head ktail khead m π b (hubCycleAsMarked w C) i).1
  have hdj := (markedCycleTypedEdge_endpoints tail head ktail khead m π b (hubCycleAsMarked w D) j).1
  have heq : C.val i=D.val j := hci.symm.trans (htail.trans hdj)
  exact Finset.disjoint_left.mp (hM C hC D hD hCD)
    (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
    (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,heq.symm⟩)

theorem marked_factor_physical_incident_card (w : U)
    (hsep : ∀ x y,H₀ x w → Hₖ y w → x≠π y)
    (M : Finset (HubMarkedCycle tail head ktail khead m π b H₀ Hₖ w))
    (hM : ∀ C∈M,∀ D∈M,C≠D → Disjoint (hubMarkedCycleVertices w C) (hubMarkedCycleVertices w D))
    (v : V) :
    ((M.biUnion (hubCyclePhysicalEdges w)).filter (fun e => v∈e)).card≤2 := by
  let f : M → Fin (m+1) → V := fun C => C.val.val
  have hf := marked_factor_joint_labels w M hM
  have hs (C D : M) (j : Fin m) : f C j.succ≠π (f D 0) :=
    hsep _ _ (C.val.property.2.2 j) D.val.property.2.1
  have he : M.biUnion (hubCyclePhysicalEdges w)=
      Finset.univ.image (fun p : M×Fin (m+1) => ({f p.1 p.2,twistedTupleHead π (f p.1) p.2}:Finset V)) := by
    ext e
    constructor
    · intro he
      obtain ⟨C,hC,he⟩ := Finset.mem_biUnion.mp he
      obtain ⟨j,_,hj⟩ := Finset.mem_image.mp he
      refine Finset.mem_image.mpr ⟨(⟨C,hC⟩,j),Finset.mem_univ _,?_⟩
      exact (markedCycle_physical_pair tail head ktail khead π b (hubCycleAsMarked w C) j).symm.trans hj
    · intro he
      obtain ⟨⟨C,j⟩,_,hj⟩ := Finset.mem_image.mp he
      refine Finset.mem_biUnion.mpr ⟨C.val,C.property,Finset.mem_image.mpr ⟨j,Finset.mem_univ _,?_⟩⟩
      exact (markedCycle_physical_pair tail head ktail khead π b (hubCycleAsMarked w C.val) j).trans hj
  rw [he]
  exact twisted_factor_incident_card π f hf hs v

theorem marked_factor_spoke_once (w : U)
    (M : Finset (HubMarkedCycle tail head ktail khead m π b H₀ Hₖ w))
    (hM : ∀ C∈M,∀ D∈M,C≠D → Disjoint (hubMarkedCycleVertices w C) (hubMarkedCycleVertices w D))
    (v : V) (hv : v∈M.biUnion (hubMarkedCycleVertices w)) :
    ∃! C : M,v∈hubMarkedCycleVertices w C.val :=
  resource_factor_vertex_unique (hubMarkedCycleVertices w) M hM v hv

theorem marked_factor_physical_degree (w : U)
    (hsep : ∀ x y,H₀ x w → Hₖ y w → x≠π y)
    (M : Finset (HubMarkedCycle tail head ktail khead m π b H₀ Hₖ w))
    (hM : ∀ C∈M,∀ D∈M,C≠D → Disjoint (hubMarkedCycleVertices w C) (hubMarkedCycleVertices w D))
    (v : V) : (physicalEdgeGraph (M.biUnion (hubCyclePhysicalEdges w))).degree v≤2 :=
  (physicalEdgeGraph_degree_le_incident _ v).trans (marked_factor_physical_incident_card w hsep M hM v)

theorem hubCycleWheel_spoke [DecidableEq U] (w : U)
    (C : HubMarkedCycle tail head ktail khead m π b H₀ Hₖ w) (v : V) :
    Sum.inr (v,w)∈markedWheelPhysicalResources (hubCycleWheel w C) ↔ v∈hubMarkedCycleVertices w C := by
  rw [markedWheelPhysicalResources_spoke]
  change (w=w ∧ v∈hubMarkedCycleVertices w C) ↔ v∈hubMarkedCycleVertices w C
  simp

theorem marked_factor_physical_spoke_once [DecidableEq U] (w : U)
    (M : Finset (HubMarkedCycle tail head ktail khead m π b H₀ Hₖ w))
    (hM : ∀ C∈M,∀ D∈M,C≠D → Disjoint (hubMarkedCycleVertices w C) (hubMarkedCycleVertices w D))
    (v : V) (hv : v∈M.biUnion (hubMarkedCycleVertices w)) :
    ∃! C : M,Sum.inr (v,w)∈markedWheelPhysicalResources (hubCycleWheel w C.val) := by
  simpa only [hubCycleWheel_spoke] using marked_factor_spoke_once w M hM v hv

end Oberwolfach
