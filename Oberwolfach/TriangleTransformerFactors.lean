module

public import Oberwolfach.OrdinaryFactorGraphs
public import Oberwolfach.MinimumDegreeTriangleFactor

@[expose] public section

/-! The two actual edge-disjoint triangle factors used at a hub of the
ordinary transformer. The second factor contains no edge inside the old
vertex set. The hypothesis is a degree into the new set, for every vertex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

def triangleAugmentationGraph (G D : SimpleGraph V) (S : Finset V) : SimpleGraph V where
  Adj v w := G.Adj v w ∧ (v∈S ∨ w∈S) ∧ ¬D.Adj v w
  symm := ⟨by intro v w h;exact ⟨h.1.symm,h.2.1.symm,fun hd=>h.2.2 hd.symm⟩⟩
  loopless := ⟨by intro v h;exact h.1.ne rfl⟩

theorem triangleAugmentationGraph_degree (G D : SimpleGraph V) (S : Finset V)
    (hD : ∀ v,D.degree v≤2) (v : V) :
    ((G.neighborFinset v∩S).card:ℝ)-2≤(triangleAugmentationGraph G D S).degree v := by
  have hs : G.neighborFinset v∩S⊆
      (triangleAugmentationGraph G D S).neighborFinset v∪D.neighborFinset v := by
    intro w hw
    have hg : G.Adj v w := by simpa using (Finset.mem_inter.mp hw).1
    by_cases hd:D.Adj v w
    · apply Finset.mem_union_right;simpa using hd
    · apply Finset.mem_union_left
      have hh : (triangleAugmentationGraph G D S).Adj v w := ⟨hg,Or.inr (Finset.mem_inter.mp hw).2,hd⟩
      simpa using hh
  have hh:=(Finset.card_le_card hs).trans (Finset.card_union_le _ _)
  rw [SimpleGraph.card_neighborFinset_eq_degree,SimpleGraph.card_neighborFinset_eq_degree] at hh
  have hhR : ((G.neighborFinset v∩S).card:ℝ)≤
      (triangleAugmentationGraph G D S).degree v+(D.degree v:ℝ) := by exact_mod_cast hh
  have hdR : (D.degree v:ℝ)≤2 := by exact_mod_cast hD v
  linarith only [hhR,hdR]

theorem graph_induced_degree_as_intersection (G : SimpleGraph V) (S : Finset V)
    (v : (S:Set V)) :
    (G.induce (S:Set V)).degree v=(G.neighborFinset v.val∩S).card := by
  have hh:=SimpleGraph.map_neighborFinset_induce (G:=G) v
  have hc:=congrArg Finset.card hh
  simp only [Finset.card_map,SimpleGraph.card_neighborFinset_eq_degree] at hc
  convert hc using 1 <;> congr!
  ext x;simp

theorem two_triangle_factors_at_hub (β : ℝ) (hβ : 0<β) (q : ℕ) :
    ∃ s₀ : ℕ,∀ (V : Type) [Fintype V] [DecidableEq V],∀ (G : SimpleGraph V) (S : Finset V),
      s₀≤S.card → 3∣S.card → 3∣Fintype.card V → Fintype.card V-S.card≤q →
      (∀ v,(3/4+β/4)*(S.card:ℝ)≤((G.neighborFinset v∩S).card:ℝ)) →
      ∃ M₁ M₂ : Finset (OrdinaryCycle G 3),
        (∀ C∈M₁,∀ D∈M₁,C≠D → Disjoint (ordinaryCycleVertices G 3 C) (ordinaryCycleVertices G 3 D)) ∧
        M₁.biUnion (ordinaryCycleVertices G 3)=Finset.univ ∧
        (∀ C∈M₂,∀ D∈M₂,C≠D → Disjoint (ordinaryCycleVertices G 3 C) (ordinaryCycleVertices G 3 D)) ∧
        M₂.biUnion (ordinaryCycleVertices G 3)=S ∧
        (∀ C∈M₁,∀ D∈M₂,Disjoint C.val.val.edgeFinset D.val.val.edgeFinset) ∧
        (∀ C∈M₁,∀ v w,C.val.val.Adj v w → v∈S ∨ w∈S) := by
  obtain ⟨N,hN⟩:=minimum_degree_triangle_factor (β/4) (by positivity)
  obtain ⟨K,hK⟩:=bounded_augmentation_triangle_factor β hβ q
  refine ⟨max N K,?_⟩
  intro V _ _ G S hs hSdiv hdiv hq hdeg
  have hS : HasResourceDecomposition (ordinaryCycleVertices G 3) S := by
    apply ordinary_factor_induced_lift S
    apply hN (S:Set V)
    · simpa using (le_max_left N K).trans hs
    · simpa using hSdiv
    · intro v
      rw [graph_induced_degree_as_intersection]
      simpa using hdeg v.val
  obtain ⟨M₂,hM₂,hcover₂⟩:=hS
  let D:=ordinaryFactorGraph M₂
  let Q:=triangleAugmentationGraph G D S
  have hD : ∀ v,D.degree v≤2 := ordinaryFactorGraph_degree_le_two M₂ hM₂
  have hQ : Q≤G := fun _ _ h=>h.1
  have hf : HasResourceDecomposition (ordinaryCycleVertices Q 3) Finset.univ := by
    apply hK S.card (Fintype.card V-S.card) ((le_max_right N K).trans hs) hq V
      (by have hh:=Finset.card_le_univ S;omega) hdiv Q
    intro v
    exact (sub_le_sub_right (hdeg v) 2).trans (triangleAugmentationGraph_degree G D S hD v)
  let lift : OrdinaryCycle Q 3→OrdinaryCycle G 3 := fun C=>⟨C.val,C.property.trans hQ⟩
  obtain ⟨M₁,hM₁,hcover₁⟩:=hf
  have hdec := resource_decomposition_map (ordinaryCycleVertices Q 3) (ordinaryCycleVertices G 3)
    lift (fun _=>rfl) Finset.univ ⟨M₁,hM₁,hcover₁⟩
  have hpack : ∀ C∈M₁.image lift,∀ E∈M₁.image lift,C≠E →
      Disjoint (ordinaryCycleVertices G 3 C) (ordinaryCycleVertices G 3 E) := by
    intro C hC E hE hne
    obtain ⟨C,hCM,rfl⟩:=Finset.mem_image.mp hC
    obtain ⟨E,hEM,rfl⟩:=Finset.mem_image.mp hE
    exact hM₁ C hCM E hEM (fun he=>hne (congrArg lift he))
  have hcover : (M₁.image lift).biUnion (ordinaryCycleVertices G 3)=Finset.univ := by
    rw [←hcover₁]
    ext v
    simp only [Finset.mem_biUnion,Finset.mem_image]
    constructor
    · rintro ⟨_,⟨C,hC,rfl⟩,hv⟩;exact ⟨C,hC,hv⟩
    · rintro ⟨C,hC,hv⟩;exact ⟨lift C,⟨C,hC,rfl⟩,hv⟩
  refine ⟨M₁.image lift,M₂,hpack,hcover,hM₂,hcover₂,?_,?_⟩
  · intro C hC E hE
    obtain ⟨C,hCM,rfl⟩:=Finset.mem_image.mp hC
    apply Finset.disjoint_left.mpr
    intro e he hf
    induction e using Sym2.ind with
    | _ v w =>
      have hc : C.val.val.Adj v w := by simpa using he
      have hd : E.val.val.Adj v w := by simpa using hf
      have hQedge:=C.property hc
      have hDedge : D.Adj v w := by
        change (⨆ C∈M₂,C.val.val).Adj v w
        simp only [SimpleGraph.iSup_adj]
        exact ⟨E,hE,hd⟩
      exact hQedge.2.2 hDedge
  · intro C hC v w h
    obtain ⟨C,hCM,rfl⟩:=Finset.mem_image.mp hC
    exact (C.property h).2.1

end Oberwolfach
