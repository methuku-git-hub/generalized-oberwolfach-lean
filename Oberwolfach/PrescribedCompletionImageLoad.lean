module

public import Oberwolfach.PrescribedAugmentedOccurrenceBound

@[expose] public section
/-! The per-vertex number of completion images is controlled by the
prescribed-anchor load and the actual free-embedding load. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem prescribed_completion_image_load
    {I V:Type} [Fintype I] [Fintype V] [DecidableEq I] [DecidableEq V]
    {X:I→Type} [∀i,Fintype (X i)] [∀i,DecidableEq (X i)]
    (Φ:∀i,X i→V) (B:∀i,Finset (X i)) (P:I→Finset V)
    (hAnchor:∀i x,x∈B i→Φ i x∈P i) (v:V):
    (Finset.univ.filter (fun i=>v∈Finset.univ.image (Φ i))).card≤
      (Finset.univ.filter (fun i=>v∈P i)).card+
      ((Finset.univ.filter (fun z:(Σi,X i)=>z.2∉B z.1)).filter (fun z=>Φ z.1 z.2=v)).card:=by
  let A:=Finset.univ.filter (fun i=>v∈P i)
  let Q:=((Finset.univ.filter (fun z:(Σi,X i)=>z.2∉B z.1)).filter (fun z=>Φ z.1 z.2=v))
  have hsub:Finset.univ.filter (fun i=>v∈Finset.univ.image (Φ i))⊆A∪Q.image Sigma.fst:=by
    intro i hi
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_image] at hi
    obtain ⟨x,hx⟩:=hi
    by_cases hb:x∈B i
    · apply Finset.mem_union_left
      simpa only [A,Finset.mem_filter,Finset.mem_univ,true_and,←hx] using hAnchor i x hb
    · apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      refine ⟨⟨i,x⟩,?_,rfl⟩
      simpa only [Q,Finset.mem_filter,Finset.mem_univ,true_and] using And.intro hb hx
  calc
    _ ≤ (A∪Q.image Sigma.fst).card:=Finset.card_le_card hsub
    _ ≤ A.card+(Q.image Sigma.fst).card:=Finset.card_union_le _ _
    _ ≤ A.card+Q.card:=Nat.add_le_add_left Finset.card_image_le _
end Oberwolfach
