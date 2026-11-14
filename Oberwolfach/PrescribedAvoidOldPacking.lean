module

public import Oberwolfach.PrescribedPositionsEmbeddingCombined

@[expose] public section
/-! If the prescribed matching and the free-embedding arcs avoid a physical
packing, then every physical edge in the completed image avoids it. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {X V:Type} [Fintype X] [Fintype V] [DecidableEq X] [DecidableEq V]

theorem prescribed_embedding_avoids_physical_packing
    (Q:SimpleGraph X) (Dsrc:X→X→Prop) (hrep:∀x y,Q.Adj x y→Dsrc x y ∨ Dsrc y x)
    (B:Finset X) (g Φ:X→V) (hold:∀x∈B,Φ x=g x)
    (M:Finset (V×V)) (hM:(prescribedInducedArcs Dsrc B).image (Prod.map g g)=M)
    (D:V→V→Prop) (harc:∀x y,Dsrc x y→(x∉B ∨ y∉B)→D (Φ x) (Φ y))
    (K:Finset (Sym2 V)) (hMavoid:Disjoint (M.image prescribedArcPhysical) K)
    (hDavoid:∀x y,D x y→s(x,y)∉K):
    Disjoint (Q.edgeFinset.image (Sym2.map Φ)) K := by
  have done:∀x y,Dsrc x y→s(Φ x,Φ y)∉K:=by
    intro x y hxy
    by_cases hx:x∈B
    · by_cases hy:y∈B
      · have hm:(g x,g y)∈M:=by
          rw [←hM]
          apply Finset.mem_image.mpr
          refine ⟨(x,y),?_,rfl⟩
          simp [prescribedInducedArcs,hx,hy,hxy]
        have hphys:s(g x,g y)∈M.image prescribedArcPhysical:=by
          exact Finset.mem_image.mpr ⟨(g x,g y),hm,rfl⟩
        rw [←hold x hx,←hold y hy] at hphys
        exact (Finset.disjoint_left.mp hMavoid) hphys
      · exact hDavoid _ _ (harc x y hxy (Or.inr hy))
    · exact hDavoid _ _ (harc x y hxy (Or.inl hx))
  apply Finset.disjoint_left.mpr
  intro e he hK
  obtain ⟨a,ha,hae⟩:=Finset.mem_image.mp he
  induction a using Sym2.ind with
  | _ x y =>
    have hxy:Q.Adj x y:=SimpleGraph.mem_edgeFinset.mp ha
    have h':s(Φ x,Φ y)∈K:=by
      rw [←hae] at hK
      exact hK
    rcases hrep x y hxy with h|h
    · exact done x y h h'
    · apply done y x h
      simpa [Sym2.eq_swap] using h'
end Oberwolfach
