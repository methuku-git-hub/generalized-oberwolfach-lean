module

public import Oberwolfach.OrdinaryForcedTargetsAvoidReserved

@[expose] public section
/-! Free selected labels and forced targets need only avoid the protected
absorber labels; they need not avoid the whole selected reference layer. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_forced_placement_avoids_absorber
    {X V K J:Type} [Fintype X] [DecidableEq X] [Fintype V] [DecidableEq V] [DecidableEq K] [DecidableEq J]
    (F:SimpleGraph X) (a:ActualResidualData (K:=K) (J:=J) F)
    (hCycle:a.t.biUnion (fun j=>(a.C j).support.toFinset)⊆a.Cembed)
    (ψ:X→V) (f:X↪V) (Φ g:{x:X // x∈a.remaining}→V)
    (B:Finset {x:X // x∈a.remaining}) (Ends T L Bad:Finset V) (Old:Finset X)
    (hOld:∀x∈a.oldDomain,f x=ψ x)
    (hRem:∀x:{x:X // x∈a.remaining},f x.val=Φ x)
    (hOn:∀x∈B,Φ x=g x) (hOutside:∀x∉B,Φ x∈L)
    (hImage:B.image g=(residualSubtypeSet a.remaining a.prescribed).image (fun x=>ψ x.val)∪Ends∪((T\Old.image ψ)\Ends))
    (hEnds:Disjoint Ends Bad) (hT:Disjoint T Bad) (hL:Disjoint L Bad)
    (hOldBad:Disjoint (a.oldDomain.image ψ) Bad):
    ∀x,f x∉Bad :=by
  let Z:Finset V:=(T\Old.image ψ)\Ends
  have hZ:Disjoint Z Bad:=hT.mono_left (Finset.sdiff_subset.trans Finset.sdiff_subset)
  have hPres:a.prescribed⊆a.oldDomain:=by
    intro x hx
    simp only [ActualResidualData.oldDomain,Finset.mem_union]
    exact Or.inl (Or.inl (Or.inl hx))
  have hSafe:Disjoint ((L∪Ends)∪Z) Bad:=Finset.disjoint_union_left.mpr
    ⟨Finset.disjoint_union_left.mpr ⟨hL,hEnds⟩,hZ⟩
  have hh:=buffered_embedding_avoids_labels a.oldDomain a.remaining a.prescribed
    (a.old_domain_union_remaining hCycle) hPres ψ f Φ g B (Ends∪Z) ((L∪Ends)∪Z) Bad
    hOld hRem hOn (fun x hx=>Finset.mem_union_left _ (Finset.mem_union_left _ (hOutside x hx)))
    (by simpa only [Z,Finset.union_assoc] using hImage)
    (by intro v hv; rcases Finset.mem_union.mp hv with hv|hv
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ hv)
        · exact Finset.mem_union_right _ hv) hOldBad hSafe
  exact hh
end Oberwolfach
