module

public import Oberwolfach.RootedLargeSubsetCycle
public import Oberwolfach.OrdinaryRootedWheelEmbedding

@[expose] public section

/-! Attach a labelled wheel at one old root. The unused private label
at position zero is placed at a separate new isolated vertex; therefore
the map of the full finite attachment vertex type remains injective. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {W V : Type*}

def replaceEmbeddingVertex (g : W ↪ V) (z : W) (x : V) (hx : ∀ w,g w≠x) : W ↪ V where
  toFun w := if w=z then x else g w
  inj' := by
    intro a b he
    by_cases ha : a=z <;> by_cases hb : b=z
    · exact ha.trans hb.symm
    · simp only [ha,hb,if_true,if_false] at he
      exact False.elim (hx b he.symm)
    · simp only [ha,hb,if_true,if_false] at he
      exact False.elim (hx a he)
    · simp only [ha,hb,if_false] at he
      exact g.injective he

@[simp] theorem replaceEmbeddingVertex_at (g : W ↪ V) (z : W) (x : V) (hx : ∀ w,g w≠x) :
    replaceEmbeddingVertex g z x hx z=x := by simp [replaceEmbeddingVertex]

theorem replaceEmbeddingVertex_ne (g : W ↪ V) (z : W) (x : V) (hx : ∀ w,g w≠x)
    (w : W) (hw : w≠z) : replaceEmbeddingVertex g z x hx w=g w := by simp [replaceEmbeddingVertex,hw]

theorem ordinary_attachment_root_embedding (β : ℝ) (hβ : 0<β) (r b : ℕ) (hr : 3≤r) :
    ∃ n₀ : ℕ,∀ n : ℕ,n₀≤n →
    ∀ (V U : Type*) [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U],Fintype.card V=n →
    ∀ (G : SimpleGraph V) (H : V → U → Prop),
    (∀ a,(1/2+β)*(n:ℝ)≤G.degree a) →
    (∀ a,(1-1/(2*(r:ℝ)))*(Fintype.card U:ℝ)≤(Finset.univ.filter (H a)).card) →
    ∀ (S : Finset V) (B : Finset U) (x : V),S.card≤b → x∈S → 2*B.card<Fintype.card U →
    ∃ (f : Fin r ↪ V) (u : U),
      (∀ i j,i≠⟨0,by omega⟩ → j≠⟨0,by omega⟩ →
        (SimpleGraph.cycleGraph r).Adj i j → G.Adj (f i) (f j)) ∧
      (∀ j,(SimpleGraph.cycleGraph r).Adj ⟨0,by omega⟩ j → G.Adj x (f j)) ∧
      H x u ∧ (∀ j,j≠⟨0,by omega⟩ → H (f j) u) ∧
      (∀ j,f j∉S) ∧ u∉B := by
  obtain ⟨n₁,hcycle⟩ := rooted_cycle_inside_large_subset β hβ r b hr
  refine ⟨max n₁ (b+r+1),?_⟩
  intro n hn V U _ _ _ _ hV G H hdeg hH S B x hS hx hB
  obtain ⟨g,hg0,hhom,_hgA,havoid⟩ := hcycle n ((le_max_left _ _).trans hn) V hV.le G hdeg
    Finset.univ (S.erase x) (by simp;positivity) ((Finset.card_erase_le).trans hS) x
    (Finset.mem_univ _) (Finset.notMem_erase _ _)
  let z : Fin r := ⟨0,by omega⟩
  have hgn (w : Fin r) (hw : w≠z) : g w∉S := by
    intro hmem
    have hne : g w≠x := by intro he;exact hw (g.injective (he.trans hg0.symm))
    exact havoid w (Finset.mem_erase.mpr ⟨hne,hmem⟩)
  let A := Finset.univ.image g
  have hAc : A.card≤r := Finset.card_image_le.trans (by simp)
  obtain ⟨u,hu,hAu⟩ := common_spoke_hub_avoiding H A B r (by omega) hAc (fun v _ => hH v) hB
  have hSc : (S∪A).card<n := by
    have hh := Finset.card_union_le S A
    have hn' := (le_max_right n₁ (b+r+1)).trans hn
    omega
  obtain ⟨x',_hx',hx'SA⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (show (S∪A).card<(Finset.univ:Finset V).card by simpa [hV] using hSc)
  have hx'g : ∀ w,g w≠x' := by
    intro w he
    apply hx'SA
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨w,Finset.mem_univ _,he⟩)
  let f := replaceEmbeddingVertex g z x' hx'g
  have hf (w : Fin r) (hw : w≠z) : f w=g w := replaceEmbeddingVertex_ne g z x' hx'g w hw
  refine ⟨f,u,?_,?_,?_,?_,?_,hu⟩
  · intro i j hi hj hij
    rw [hf i hi,hf j hj]
    exact hhom i j hij
  · intro j hj
    have hjz : j≠z := hj.ne.symm
    rw [hf j hjz,←hg0]
    exact hhom z j hj
  · apply hAu
    exact Finset.mem_image.mpr ⟨z,Finset.mem_univ _,hg0⟩
  · intro j hj
    rw [hf j hj]
    exact hAu _ (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩)
  · intro j
    by_cases hj : j=z
    · subst j
      rw [show f z=x' from replaceEmbeddingVertex_at g z x' hx'g]
      exact fun h => hx'SA (Finset.mem_union_left _ h)
    · rw [hf j hj]
      exact hgn j hj

end Oberwolfach
