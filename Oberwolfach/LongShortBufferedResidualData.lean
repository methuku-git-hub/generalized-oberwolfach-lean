module

public import Oberwolfach.BufferedActualResidualData
public import Oberwolfach.LongShortComponentSeparation

@[expose] public section
/-! Build actual residual data directly from the manuscript's long-path and
short-cycle component bounds, only on the selected indices. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def actualResidualDataOfLongShortBufferedWalks
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
    (K:ℕ) (long:I→F.ConnectedComponent) (short:J→F.ConnectedComponent)
    (hLong:∀i∈s₁∪s₂,K<Fintype.card (long i))
    (hShort:∀j∈t,Fintype.card (short j)≤K)
    (hExt:∀i∈s₁∪s₂,∀p,ext i p∈(long i).supp)
    (hCshort:∀j∈t,∀x,x∈(C j).support.toFinset→x∈(short j).supp)
    (Cembed:Finset X) (hEmbed:Cembed⊆t.biUnion (fun j=>(C j).support.toFinset)) :
    ActualResidualData (K:=I) (J:=J) F := by
  have hcross:∀i∈s₁∪s₂,∀j∈t,Disjoint (Finset.univ.image (ext i)) (C j).support.toFinset:=by
    intro i hi j hj
    let I':={i // i∈s₁∪s₂}
    let J':={j // j∈t}
    have hsep:=long_paths_disjoint_short_component_sets F K
      (fun i:I'=>long i.val) (fun j:J'=>short j.val)
      (fun i=>hLong i.val i.property) (fun j=>hShort j.val j.property)
      (fun _ : I'=>c*d+5) (fun i:I'=>ext i.val)
      (fun j:J'=>(C j.val).support.toFinset)
      (fun i p=>hExt i.val i.property p) (fun j x hx=>hCshort j.val j.property x hx)
    exact hsep ⟨i,hi⟩ ⟨j,hj⟩
  exact actualResidualDataOfBufferedWalks F c d hc hd s₁ s₂ hs ext P hlen hsupport hdis T hT
    t root C hcycle hC hcross Cembed hEmbed
end Oberwolfach
