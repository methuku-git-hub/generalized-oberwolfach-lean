module

public import Oberwolfach.ResidualActualData

@[expose] public section
/-! Package actual disjoint selected path and cycle families into the residual
data, retaining distinct index types for the final and partially selected
paths. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def firstSumIndices {A B:Type} [Fintype A] [DecidableEq A] [DecidableEq B]:Finset (A⊕B):=
  Finset.univ.image Sum.inl

def secondSumIndices {A B:Type} [Fintype B] [DecidableEq A] [DecidableEq B]:Finset (A⊕B):=
  Finset.univ.image Sum.inr

theorem first_second_sum_indices_disjoint {A B:Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]:
    Disjoint (firstSumIndices (A:=A) (B:=B)) (secondSumIndices (A:=A) (B:=B)):=by
  apply Finset.disjoint_left.mpr
  intro z hz₁ hz₂
  obtain ⟨a,_,ha⟩:=Finset.mem_image.mp hz₁
  obtain ⟨b,_,hb⟩:=Finset.mem_image.mp hz₂
  rw [←ha] at hb
  cases hb

def actualResidualDataFromFamilies
    {X A B J:Type} [Fintype X] [DecidableEq X] [Fintype A] [Fintype B] [Fintype J]
    [DecidableEq A] [DecidableEq B] [DecidableEq J]
    (F:SimpleGraph X) (u v:A⊕B→X) (P:∀i,F.Walk (u i) (v i))
    (hp:∀i,(P i).IsPath) (hP:∀i j,i≠j→Disjoint (P i).support.toFinset (P j).support.toFinset)
    (c d:ℕ) (hc:3≤c) (hd:0<d) (hlen:∀i,(P i).length=c*d+4)
    (T:A⊕B→Finset ℕ) (hT:∀i,T i⊆Finset.range d)
    (root:J→X) (C:∀j,F.Walk (root j) (root j)) (hcycle:∀j,(C j).IsCycle)
    (hC:∀i j,i≠j→Disjoint (C i).support.toFinset (C j).support.toFinset)
    (hcross:∀i j,Disjoint (P i).support.toFinset (C j).support.toFinset):
    ActualResidualData (K:=A⊕B) (J:=J) F where
  s₁:=firstSumIndices
  s₂:=secondSumIndices
  hs:=first_second_sum_indices_disjoint
  u:=u
  v:=v
  P:=P
  hp:=by intro i _;exact hp i
  hP:=by intro i _ j _ hij;exact hP i j hij
  c:=c
  d:=d
  hc:=hc
  hd:=hd
  hlen:=by intro i _;exact hlen i
  T:=T
  hT:=hT
  t:=Finset.univ
  root:=root
  C:=C
  hcycle:=by intro j _;exact hcycle j
  hC:=by intro i _ j _ hij;exact hC i j hij
  hcross:=by intro i _ j _;exact hcross i j
  Cembed:=Finset.univ.biUnion (fun j=>(C j).support.toFinset)
  hEmbed:=by rfl

end Oberwolfach
