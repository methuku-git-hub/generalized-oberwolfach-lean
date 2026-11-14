module

public import Oberwolfach.ActualResidualSumIndices
public import Oberwolfach.PackedPhysicalSpokePositions

@[expose] public section
/-! Build actual residual data with the selected positions defined directly
by the physical mixed packing at the hub. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def actualResidualDataFromPacking
    {X V U E L A B J:Type} [Fintype X] [DecidableEq X] [Fintype A] [Fintype B] [Fintype J]
    [DecidableEq A] [DecidableEq B] [DecidableEq J] [DecidableEq V] [DecidableEq U]
    (F:SimpleGraph X) (u v:A⊕B→X) (P:∀i,F.Walk (u i) (v i))
    (hp:∀i,(P i).IsPath) (hP:∀i j,i≠j→Disjoint (P i).support.toFinset (P j).support.toFinset)
    (c d:ℕ) (hc:3≤c) (hd:0<d) (hlen:∀i,(P i).length=c*d+4)
    (tail head:E→V) (ktail khead:L→V) (m b:ℕ) (π:Equiv.Perm V) (H₀ Hₖ:V→U→Prop)
    (M:Finset (MarkedWheel tail head ktail khead m π b H₀ Hₖ)) (hub:U) (targetRoot:A⊕B→V)
    (root:J→X) (C:∀j,F.Walk (root j) (root j)) (hcycle:∀j,(C j).IsCycle)
    (hC:∀i j,i≠j→Disjoint (C i).support.toFinset (C j).support.toFinset)
    (hcross:∀i j,Disjoint (P i).support.toFinset (C j).support.toFinset):
    ActualResidualData (K:=A⊕B) (J:=J) F:=
  actualResidualDataFromFamilies F u v P hp hP c d hc hd hlen
    (fun i=>packedPhysicalSpokePositions tail head ktail khead m b d π H₀ Hₖ M hub (targetRoot i))
    (fun _=>Finset.filter_subset _ _) root C hcycle hC hcross

theorem actual_residual_data_from_packing_facts
    {X V U E L A B J:Type} [Fintype X] [DecidableEq X] [Fintype A] [Fintype B] [Fintype J]
    [DecidableEq A] [DecidableEq B] [DecidableEq J] [DecidableEq V] [DecidableEq U]
    (F:SimpleGraph X) (u v:A⊕B→X) (P:∀i,F.Walk (u i) (v i))
    (hp:∀i,(P i).IsPath) (hP:∀i j,i≠j→Disjoint (P i).support.toFinset (P j).support.toFinset)
    (c d:ℕ) (hc:3≤c) (hd:0<d) (hlen:∀i,(P i).length=c*d+4)
    (tail head:E→V) (ktail khead:L→V) (m b:ℕ) (π:Equiv.Perm V) (H₀ Hₖ:V→U→Prop)
    (M:Finset (MarkedWheel tail head ktail khead m π b H₀ Hₖ)) (hub:U) (targetRoot:A⊕B→V)
    (root:J→X) (C:∀j,F.Walk (root j) (root j)) (hcycle:∀j,(C j).IsCycle)
    (hC:∀i j,i≠j→Disjoint (C i).support.toFinset (C j).support.toFinset)
    (hcross:∀i j,Disjoint (P i).support.toFinset (C j).support.toFinset):
    let data:=actualResidualDataFromPacking F u v P hp hP c d hc hd hlen tail head ktail khead m b π H₀ Hₖ M hub targetRoot root C hcycle hC hcross
    data.s₁=firstSumIndices ∧ data.s₂=secondSumIndices ∧ data.t=Finset.univ ∧
    (∀i,data.T i=packedPhysicalSpokePositions tail head ktail khead m b d π H₀ Hₖ M hub (targetRoot i)) ∧
    data.Cembed=data.t.biUnion (fun j=>(data.C j).support.toFinset):=by
  intro data
  exact ⟨rfl,rfl,rfl,fun _=>rfl,rfl⟩
end Oberwolfach
