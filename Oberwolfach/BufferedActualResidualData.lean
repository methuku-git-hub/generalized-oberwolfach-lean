module

public import Oberwolfach.ResidualActualData
public import Oberwolfach.BufferedPathEmbeddingEdgeCoverage

@[expose] public section
/-! Construct the existing actual residual data from disjoint buffered source
walks, with separate final and approximate index sets and the original cycle data. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem buffered_walk_support_finset
    {X:Type} [Fintype X] [DecidableEq X] (F:SimpleGraph X) (L:ℕ)
    (ext:Fin (L+5)↪X) (p:F.Walk (ext ⟨0,by omega⟩) (ext ⟨L+4,by omega⟩))
    (hsupport:p.support=List.ofFn ext) : p.support.toFinset=Finset.univ.image ext := by
  classical
  rw [hsupport]
  ext x
  simp only [List.mem_toFinset,List.mem_ofFn,Finset.mem_image,Finset.mem_univ,true_and]

def actualResidualDataOfBufferedWalks
    {X I J:Type} [Fintype X] [DecidableEq X] [Fintype I] [DecidableEq I] [DecidableEq J]
    (F:SimpleGraph X) (c d:ℕ) (hc:3≤c) (hd:0<d)
    (s₁ s₂:Finset I) (hs:Disjoint s₁ s₂)
    (ext:∀i:I,Fin (c*d+5)↪X)
    (P:∀i:I,F.Walk (ext i ⟨0,by omega⟩) (ext i ⟨c*d+4,by omega⟩))
    (hlen:∀i,(P i).length=c*d+4) (hsupport:∀i,(P i).support=List.ofFn (ext i))
    (hdis:∀i j,i≠j→Disjoint (Finset.univ.image (ext i)) (Finset.univ.image (ext j)))
    (T:I→Finset ℕ) (hT:∀i,T i⊆Finset.range d)
    (t:Finset J) (root:J→X) (C:∀j,F.Walk (root j) (root j))
    (hcycle:∀j∈t,(C j).IsCycle)
    (hC:(↑t:Set J).PairwiseDisjoint (fun j=>(C j).support.toFinset))
    (hcross:∀i∈s₁∪s₂,∀j∈t,Disjoint (Finset.univ.image (ext i)) (C j).support.toFinset)
    (Cembed:Finset X) (hEmbed:Cembed⊆t.biUnion (fun j=>(C j).support.toFinset)) :
    ActualResidualData (K:=I) (J:=J) F where
  s₁:=s₁
  s₂:=s₂
  hs:=hs
  u:=fun i=>ext i ⟨0,by omega⟩
  v:=fun i=>ext i ⟨c*d+4,by omega⟩
  P:=P
  hp:=by
    intro i _
    apply SimpleGraph.Walk.IsPath.mk'
    rw [hsupport i]
    exact List.nodup_ofFn_ofInjective (ext i).injective
  hP:=by
    intro i _ j _ hij
    change Disjoint (P i).support.toFinset (P j).support.toFinset
    rw [buffered_walk_support_finset F (c*d) (ext i) (P i) (hsupport i),
      buffered_walk_support_finset F (c*d) (ext j) (P j) (hsupport j)]
    exact hdis i j hij
  c:=c
  d:=d
  hc:=hc
  hd:=hd
  hlen:=by intro i _;exact hlen i
  T:=T
  hT:=hT
  t:=t
  root:=root
  C:=C
  hcycle:=hcycle
  hC:=hC
  hcross:=by
    intro i hi j hj
    rw [buffered_walk_support_finset F (c*d) (ext i) (P i) (hsupport i)]
    exact hcross i hi j hj
  Cembed:=Cembed
  hEmbed:=hEmbed
end Oberwolfach
