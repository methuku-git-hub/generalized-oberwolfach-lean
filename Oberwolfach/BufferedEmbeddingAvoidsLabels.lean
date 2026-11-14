module

public import Oberwolfach.ResidualSubtypePositionBudget

@[expose] public section
/-! A buffered embedding avoids a reserved label set when the old image
avoids it and every new image lies in the protected unassigned list. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {X V:Type} [Fintype X] [DecidableEq X] [Fintype V] [DecidableEq V]

theorem buffered_embedding_avoids_labels
    (Old Rem Pres:Finset X) (hcover:Old∪Rem=Finset.univ) (hPres:Pres⊆Old)
    (ψ:X→V) (f:X↪V) (Φ g:{x:X // x∈Rem}→V) (B:Finset {x:X // x∈Rem})
    (Ends List Bad:Finset V)
    (hOld:∀x∈Old,f x=ψ x)
    (hRem:∀x:{x:X // x∈Rem},f x.val=Φ x)
    (hOn:∀x∈B,Φ x=g x)
    (hOutside:∀x∉B,Φ x∈List)
    (hImage:B.image g=(residualSubtypeSet Rem Pres).image (fun x=>ψ x.val)∪Ends)
    (hEnds:Ends⊆List) (hOldBad:Disjoint (Old.image ψ) Bad) (hListBad:Disjoint List Bad):
    ∀x,f x∉Bad:=by
  intro x
  by_cases hx:x∈Old
  · rw [hOld x hx]
    exact fun h=>Finset.disjoint_left.mp hOldBad (Finset.mem_image.mpr ⟨x,hx,rfl⟩) h
  · have hr:x∈Rem:=by
      have hxall:x∈Old∪Rem:=by rw [hcover];exact Finset.mem_univ _
      exact (Finset.mem_union.mp hxall).resolve_left hx
    let y:{x:X // x∈Rem}:=⟨x,hr⟩
    rw [show f x=Φ y from hRem y]
    by_cases hy:y∈B
    · rw [hOn y hy]
      have hg:g y∈B.image g:=Finset.mem_image.mpr ⟨y,hy,rfl⟩
      rw [hImage] at hg
      rcases Finset.mem_union.mp hg with hpres|hend
      · obtain ⟨z,hz,hzEq⟩:=Finset.mem_image.mp hpres
        have hzPres:z.val∈Pres:=(Finset.mem_filter.mp hz).2
        have hzOld:z.val∈Old:=hPres hzPres
        intro hb
        exact Finset.disjoint_left.mp hOldBad (Finset.mem_image.mpr ⟨z.val,hzOld,hzEq⟩) hb
      · exact fun hb=>Finset.disjoint_left.mp hListBad (hEnds hend) hb
    · exact fun hb=>Finset.disjoint_left.mp hListBad (hOutside y hy) hb
end Oberwolfach
