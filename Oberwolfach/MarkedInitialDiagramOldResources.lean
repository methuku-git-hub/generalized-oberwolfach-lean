module

public import Oberwolfach.MarkedInitialDiagramSupport
public import Oberwolfach.MarkedRootArcIsolation

@[expose] public section

/-! The initial positive packing contains no old-root resource other than
an original root-graph edge. This gives the independence needed by later
absorber and transformer callers. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K A S:Type} [Fintype V] [Fintype U] [Fintype A] [Fintype S]
    [DecidableEq V] [DecidableEq U] [DecidableEq A] [DecidableEq S]
    {tail head:E→V} {ktail khead:K→V} {H₀ HK:V→U→Prop} {π:Equiv.Perm V} {b l:ℕ}
    {src dst:A→V} {row:S→V} {φ:V→V} {u u':S→U} {jr:A→Bool} {js:S→Bool}
    {W Z:Finset V} {B:Finset U}

def MarkedOldResource (tail head:E→V) (ktail khead:K→V) (π:Equiv.Perm V)
    (Z:Finset V) (B:Finset U):Finset V⊕(V×U)→Prop
  | .inl e=>∃ a:E⊕K,markedPhysicalEdge tail head ktail khead π a=e∧
      Sum.elim tail ktail a∈Z∧Sum.elim head khead a∈Z
  | .inr vu=>vu.1∈Z∧vu.2∈B

theorem rooted_cycle_old_vertex {n:ℕ} (σ:Equiv.Perm (Fin (n+1))) (x:V) (p:Fin n→V)
    (Z:Finset V) (hp:∀ k,p k∉Z) (i:Fin (n+1))
    (hi:rootedCycleOrder σ x p i∈Z):rootedCycleOrder σ x p i=x:=by
  change Fin.cases x p (σ i)∈Z at hi
  change Fin.cases x p (σ i)=x
  generalize σ i=k at hi ⊢
  cases k using Fin.cases with
  | zero=>rfl
  | succ k=>exact (hp k hi).elim

theorem marked_diagram_plus_old_resources
    (D:MarkedInitialDiagram tail head ktail khead H₀ HK π b l src dst row φ u u' jr js W Z B)
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π)):
    ∀ e∈markedDiagramPlus D,MarkedOldResource tail head ktail khead π Z B e→
      e∈markedRootGraphResources π src dst row jr u:=by
  have rim_pull (C:MarkedWheel tail head ktail khead (l+4) π b H₀ HK) (e:Finset V)
      (he:Sum.inl e∈markedWheelPhysicalResources C)
      (hold:MarkedOldResource tail head ktail khead π Z B (Sum.inl e)):
      ∃ k,markedPhysicalEdge tail head ktail khead π (markedCycleTypedEdge tail head ktail khead (l+4) π b C.1 k)=e∧
        C.1.val k∈Z∧C.1.val (finRotate (l+5) k)∈Z:=by
    obtain ⟨a,ha,hat,hah⟩:=hold
    obtain ⟨k,_,hk⟩:=Finset.mem_image.mp ((markedWheelPhysicalResources_rim C e).mp he)
    have hka:=hp (hk.trans ha.symm)
    have ends:=markedCycleTypedEdge_endpoints tail head ktail khead (l+4) π b C.1 k
    rw [hka] at ends
    exact ⟨k,hk,ends.1 ▸ hat,ends.2 ▸ hah⟩
  intro e he hold
  obtain ⟨i,_,hi⟩:=Finset.mem_biUnion.mp he
  cases e with
  | inl e=>
    rcases i with a|(s|z)
    · obtain ⟨k,hk,ht,hh⟩:=rim_pull (D.RC a) e hi hold
      have hid:=marked_two_root_wheel_old_arc (l+2) (by omega) (D.pr a) (src a) (dst a) (jr a) Z
        (fun k=>(D.rimAvoid a k).2.1) (D.RC a) (D.rimCoordinates a) k ht hh
      exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨a,Finset.mem_univ _,congrArg Sum.inl (hid.symm.trans hk)⟩)
    · obtain ⟨k,hk,ht,hh⟩:=rim_pull (D.SC s) e hi hold
      exact (marked_one_root_wheel_no_old_arc (D.ps s) (row s) Z (fun k=>(D.spokeAvoid s k).2.1)
        (markedRootOrder (l+4) (js s)) (markedRootOrder_successor (l+4) (js s)) (D.SC s) (D.spokeCoordinates s) k ⟨ht,hh⟩).elim
    · obtain ⟨k,hk,ht,hh⟩:=rim_pull (D.VD z) e hi hold
      exact (marked_one_root_wheel_no_old_arc (D.pv z) (φ z.1) Z (fun k=>(D.vertexAvoid z k).1)
        (markedRootOrder (l+4) (markedIncidenceSpokeType jr (D.τ z.1 z.2)))
        (markedRootOrder_successor (l+4) _) (D.VD z) (D.imageVertexCoordinates z) k ⟨ht,hh⟩).elim
  | inr vu=>
    rcases vu with ⟨v,z⟩
    rcases i with a|(s|a)
    · have hz:=((markedWheelPhysicalResources_spoke (D.RC a) v z).mp hi).1
      exact (D.freshHub a (((D.rimHubs a).1.symm.trans hz).symm ▸ hold.2)).elim
    · obtain ⟨hz,hv⟩:=(markedWheelPhysicalResources_spoke (D.SC s) v z).mp hi
      obtain ⟨k,_,hk⟩:=Finset.mem_image.mp hv
      have hv':v=row s:=by
        have hmem:rootedCycleOrder (markedRootOrder (l+4) (js s)) (row s) (D.ps s) k∈Z:=by
          rw [←D.spokeCoordinates];exact hk.symm ▸ hold.1
        exact hk.symm.trans ((D.spokeCoordinates s k).trans
          (rooted_cycle_old_vertex _ _ _ Z (fun k=>(D.spokeAvoid s k).2.1) k hmem))
      have hz':u s=z:=(D.spokeHubs s).1.symm.trans hz
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨s,Finset.mem_univ _,congrArg Sum.inr (Prod.ext hv'.symm hz')⟩)
    · have hz:=((markedWheelPhysicalResources_spoke (D.VD a) v z).mp hi).1
      exact (D.freshHub (directedIncidenceEdge (D.τ a.1 a.2)) (((D.vertexHubs a).2.symm.trans hz).symm ▸ hold.2)).elim

end Oberwolfach
