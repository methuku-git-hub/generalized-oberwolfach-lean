module

public import Oberwolfach.RootedPathCycleEmbedding
public import Oberwolfach.OrdinaryRootedWheelEmbedding

@[expose] public section

/-! Embed one expansion of an arbitrary formal rim pair. The two old
endpoints may coincide; every wheel vertex and its hub is fresh. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_rim_expansion_embedding (β : ℝ) (hβ : 0<β) (r b : ℕ) (hr : 3≤r) :
    ∃ n₀ : ℕ,∀ n : ℕ,n₀≤n →
    ∀ (V U : Type*) [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U],Fintype.card V≤n →
    ∀ (G : SimpleGraph V) (H : V → U → Prop),
    (∀ a,(1/2+β)*(n:ℝ)≤G.degree a) →
    (∀ a,(1-1/(2*(r:ℝ)))*(Fintype.card U:ℝ)≤(Finset.univ.filter (H a)).card) →
    ∀ (R : Finset V) (B : Finset U) (x y : V),R.card≤b → x∈R → y∈R → 2*B.card<Fintype.card U →
    ∃ (f : Fin r ↪ V) (u : U),
      (∀ i j,(SimpleGraph.cycleGraph r).Adj i j → G.Adj (f i) (f j)) ∧
      (∀ i,H (f i) u) ∧ (∀ i,f i∉R) ∧ u∉B ∧
      G.Adj y (f ⟨0,by omega⟩) ∧ G.Adj x (f ⟨r-1,by omega⟩) ∧
      (∀ i,f i≠x ∧ f i≠y) := by
  obtain ⟨n₁,hpath⟩ := fixed_length_path β hβ (r-1) b (by omega)
  let n₂ := Nat.ceil (((b:ℝ)+1)/β)+1
  refine ⟨max n₁ n₂,?_⟩
  intro n hn V U _ _ _ _ hV G H hdeg hH R B x y hR hx hy hB
  have hceil : (Nat.ceil (((b:ℝ)+1)/β):ℝ)<n := by
    exact_mod_cast (show Nat.ceil (((b:ℝ)+1)/β)<n by have h: n₂≤n:=(le_max_right _ _).trans hn;dsimp [n₂] at h;omega)
  have hmargin : (b:ℝ)+1<(n:ℝ)*β :=
    (div_lt_iff₀ hβ).mp ((Nat.le_ceil (((b:ℝ)+1)/β)).trans_lt hceil)
  have hRR : (R.card:ℝ)≤b := by exact_mod_cast hR
  have hnR : (0:ℝ)≤n := Nat.cast_nonneg _
  have hy_size : R.card<(G.neighborFinset x).card := by
    rw [SimpleGraph.card_neighborFinset_eq_degree]
    have hh : (R.card:ℝ)<G.degree x := by nlinarith [hdeg x]
    exact_mod_cast hh
  obtain ⟨y',hy',hy'R⟩ := Finset.exists_mem_notMem_of_card_lt_card hy_size
  have hxy' : G.Adj x y' := by simpa only [SimpleGraph.mem_neighborFinset] using hy'
  have hx_size : R.card<(G.neighborFinset y∩G.neighborFinset y').card := by
    have hh := dense_common_neighbours G n β hV hdeg y y'
    have hlt : (R.card:ℝ)<((G.neighborFinset y∩G.neighborFinset y').card:ℝ) := by nlinarith
    exact_mod_cast hlt
  obtain ⟨x',hx',hx'R⟩ := Finset.exists_mem_notMem_of_card_lt_card hx_size
  have hyx' : G.Adj y x' := by simpa only [SimpleGraph.mem_neighborFinset] using (Finset.mem_inter.mp hx').1
  have hy'x' : G.Adj y' x' := by simpa only [SimpleGraph.mem_neighborFinset] using (Finset.mem_inter.mp hx').2
  obtain ⟨p,hp,hlen,havoid⟩ := hpath n ((le_max_left _ _).trans hn) V hV G hdeg
    x' y' hy'x'.ne.symm R hR hx'R hy'R
  let f := pathCycleEmbedding p hp hlen
  have hfavoid : ∀ i,f i∉R := pathCycleEmbedding_avoids (R:Set V) p hp hlen havoid
  let A := Finset.univ.image f
  have hA : A.card≤r := by
    exact (Finset.card_image_le).trans (by simp)
  obtain ⟨u,hu,hAu⟩ := common_spoke_hub_avoiding H A B r (by omega) hA (fun a _ => hH a) hB
  refine ⟨f,u,pathCycleEmbedding_hom hr p hp hlen hy'x'.symm,?_,hfavoid,hu,?_,?_,?_⟩
  · intro i
    exact hAu _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
  · simpa only [f,pathCycleEmbedding_first] using hyx'
  · simpa only [f,pathCycleEmbedding_last (r:=r) (by omega) p hp hlen] using hxy'
  · intro i
    exact ⟨fun h => hfavoid i (h ▸ hx),fun h => hfavoid i (h ▸ hy)⟩

end Oberwolfach
