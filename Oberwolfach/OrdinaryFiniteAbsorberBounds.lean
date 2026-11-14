module

public import Oberwolfach.OrdinaryFiniteTransformerAssembly
public import Oberwolfach.OrdinaryTransformerForbiddenEdges

@[expose] public section
/-! Host containment and explicit vertex bounds for the finite absorber. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem finite_four_absorber_bounds
    (D:ℕ→Finset (Sym2 V⊕(V×U))) (T:Fin 4→Finset (Sym2 V⊕(V×U)))
    (original extra L host:Finset (Sym2 V⊕(V×U))) (q k:ℕ)
    (hfirst:D 0=original∪extra) (hD:∀ i,i≤4→D i⊆L)
    (hDhost:∀ i,i≤4→D i⊆host) (hT:∀ i,T i⊆host)
    (hrow:(ordinaryResourceRows L).card≤q) (hhub:(ordinaryResourceHubs L).card≤q)
    (hbound:∀ i,(ordinaryResourceRows (T i)).card+(ordinaryResourceHubs (T i)).card≤k) :
    let C:=extra∪transformerChainEdges D (finiteTransformerAt T) 4∪D 4;
    C⊆host ∧ (ordinaryResourceRows C).card≤q+4*k ∧
      (ordinaryResourceHubs C).card≤q+4*k := by
  intro C
  have hsub (Z:Finset (Sym2 V⊕(V×U))) (hZ:∀ i,i≤4→D i⊆Z):C⊆Z∪Finset.univ.biUnion T:=by
    intro e he
    rcases Finset.mem_union.mp he with he|he
    · rcases Finset.mem_union.mp he with he|he
      · apply Finset.mem_union_left
        apply hZ 0 (by omega)
        rw [hfirst]
        exact Finset.mem_union_right _ he
      · rcases (mem_transformerChainEdges _ _ _ _).mp he with ⟨i,hi,he⟩|⟨i,_,hi,he⟩
        · apply Finset.mem_union_right
          exact Finset.mem_biUnion.mpr ⟨⟨i,hi⟩,Finset.mem_univ _,by simpa only [finiteTransformerAt_apply T ⟨i,hi⟩] using he⟩
        · exact Finset.mem_union_left _ (hZ i (by omega) he)
    · exact Finset.mem_union_left _ (hZ 4 (by omega) he)
  have hrows:(ordinaryResourceRows (Finset.univ.biUnion T)).card≤4*k:=by
    rw [ordinaryResourceRows_biUnion]
    apply Finset.card_biUnion_le.trans
    calc
      _ ≤ ∑ _i:Fin 4,k := Finset.sum_le_sum (fun i _=>by have h:=hbound i;omega)
      _ = 4*k := by simp
  have hhubs:(ordinaryResourceHubs (Finset.univ.biUnion T)).card≤4*k:=by
    rw [ordinaryResourceHubs_biUnion]
    apply Finset.card_biUnion_le.trans
    calc
      _ ≤ ∑ _i:Fin 4,k := Finset.sum_le_sum (fun i _=>by have h:=hbound i;omega)
      _ = 4*k := by simp
  have hsubL:=hsub L hD
  refine ⟨(hsub host hDhost).trans (Finset.union_subset (fun _ he=>he) (Finset.biUnion_subset.mpr (fun i _=>hT i))),?_,?_⟩
  · have hh:=Finset.card_le_card (ordinaryResourceRows_mono hsubL)
    apply hh.trans
    simpa only [ordinaryResourceRows_union] using (Finset.card_union_le (ordinaryResourceRows L) (ordinaryResourceRows (Finset.univ.biUnion T))).trans (Nat.add_le_add hrow hrows)
  · have hh:=Finset.card_le_card (ordinaryResourceHubs_mono hsubL)
    apply hh.trans
    simpa only [ordinaryResourceHubs_union] using (Finset.card_union_le (ordinaryResourceHubs L) (ordinaryResourceHubs (Finset.univ.biUnion T))).trans (Nat.add_le_add hhub hhubs)
end Oberwolfach
