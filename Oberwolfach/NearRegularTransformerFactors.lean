module

public import Oberwolfach.AlmostRegularCycleFactor
public import Oberwolfach.NearRegularAugmentationBounds

@[expose] public section
/-! Two factors for the actual near-regular host: the second avoids the old
vertex set and the first has no edge internal to that set. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem two_near_regular_cycle_factors_at_hub (m:ℕ) (hm:2≤m) (α:ℝ)
    (hα:0<α) (hα1:α≤1) (q:ℕ):
    ∃ η:ℝ,0<η ∧ ∃ s₀:ℕ,∀ (V:Type) [Fintype V] [DecidableEq V]
      (G:SimpleGraph V) (S:Finset V) (D:ℝ),
      s₀≤S.card → (m+1)∣S.card → (m+1)∣Fintype.card V → Fintype.card V-S.card≤q →
      (cycleThreshold (m+1)+α)*(S.card:ℝ)≤D → D≤S.card →
      (∀ v,|((G.neighborFinset v∩S).card:ℝ)-D|≤η*S.card) →
      ∃ M₁ M₂:Finset (OrdinaryCycle G (m+1)),
        (∀ C∈M₁,∀ E∈M₁,C≠E→Disjoint (ordinaryCycleVertices G (m+1) C) (ordinaryCycleVertices G (m+1) E)) ∧
        M₁.biUnion (ordinaryCycleVertices G (m+1))=Finset.univ ∧
        (∀ C∈M₂,∀ E∈M₂,C≠E→Disjoint (ordinaryCycleVertices G (m+1) C) (ordinaryCycleVertices G (m+1) E)) ∧
        M₂.biUnion (ordinaryCycleVertices G (m+1))=S ∧
        (∀ C∈M₁,∀ E∈M₂,Disjoint C.val.val.edgeFinset E.val.val.edgeFinset) ∧
        (∀ C∈M₁,∀ v w,C.val.val.Adj v w→v∈S ∨ w∈S):=by
  obtain ⟨ε,hε,N,hfactor⟩:=almost_regular_cycle_factor m hm (α/4) (by positivity)
  let c:=min α ε
  have hc:0<c:=lt_min hα hε
  obtain ⟨T,hT⟩:=exists_nat_gt (8*((q:ℝ)+2)/c)
  refine ⟨c/8,by positivity,max N (max T 1),?_⟩
  intro V _ _ G S D hs hSdiv hdiv hq hDlo hDhi hdeg
  have hspos:0<S.card:=by omega
  have hsR:(0:ℝ)<S.card:=by exact_mod_cast hspos
  have hT':(8*((q:ℝ)+2)/c)<S.card:=lt_of_lt_of_le hT (by exact_mod_cast (show T≤S.card by omega))
  have hlarge:(q:ℝ)+2≤min α ε*(S.card:ℝ)/8:=by
    have hh:8*((q:ℝ)+2)<c*S.card:=by simpa [mul_comm] using (div_lt_iff₀ hc).mp hT'
    change (q:ℝ)+2≤c*S.card/8
    linarith
  have hηα:c/8≤α/8:=by dsimp [c];exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have hηε:c/8≤ε/8:=by dsimp [c];exact div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  have hδ0:(1/2:ℝ)≤cycleThreshold (m+1):=cycleThreshold_half_le (by omega)
  have hδ1:cycleThreshold (m+1)≤1:=cycleThreshold_le_one _
  have hS : HasResourceDecomposition (ordinaryCycleVertices G (m+1)) S := by
    apply ordinary_factor_induced_lift S
    apply hfactor (S:Set V) (by simpa using (show N≤S.card by omega)) (G.induce (S:Set V)) D
    · simpa using (show (S.card:ℝ)/2≤D by nlinarith)
    · simpa using (show D≤2*(S.card:ℝ) by nlinarith)
    · intro v
      rw [graph_induced_degree_as_intersection]
      have hv:=abs_le.mp (hdeg v.val)
      have hsmall:(c/8)*(S.card:ℝ)≤(α/8)*S.card:=mul_le_mul_of_nonneg_right hηα hsR.le
      simpa using (show (cycleThreshold (m+1)+α/4)*(S.card:ℝ)≤((G.neighborFinset v.val∩S).card:ℝ) by nlinarith)
    · intro v
      rw [graph_induced_degree_as_intersection]
      have hh:=hdeg v.val
      have hsmall:(c/8)*(S.card:ℝ)≤ε*(S.card:ℝ):=by nlinarith
      simpa using le_trans hh hsmall
    · simpa using hSdiv
  obtain ⟨M₂,hM₂,hcover₂⟩:=hS
  let Dgraph:=ordinaryFactorGraph M₂
  let Q:=triangleAugmentationGraph G Dgraph S
  have hDgraph:∀ v,Dgraph.degree v≤2:=ordinaryFactorGraph_degree_le_two M₂ hM₂
  have hQ:Q≤G:=fun _ _ h=>h.1
  have hbounds:=near_regular_augmentation_bounds G Dgraph S D (cycleThreshold (m+1)) α (c/8) ε q
      hδ0 hδ1 hα hα1 (by positivity) hηα hηε hε hspos hq hlarge hDlo hDhi hdeg hDgraph
  have hf : HasResourceDecomposition (ordinaryCycleVertices Q (m+1)) Finset.univ := by
    apply hfactor V (by have hsV:=Finset.card_le_univ S;omega) Q D hbounds.1 hbounds.2.1
      hbounds.2.2.1 hbounds.2.2.2 hdiv
  let lift : OrdinaryCycle Q (m+1)→OrdinaryCycle G (m+1) := fun C=>⟨C.val,C.property.trans hQ⟩
  obtain ⟨M₁,hM₁,hcover₁⟩:=hf
  have hdec := resource_decomposition_map (ordinaryCycleVertices Q (m+1)) (ordinaryCycleVertices G (m+1))
    lift (fun _=>rfl) Finset.univ ⟨M₁,hM₁,hcover₁⟩
  have hpack : ∀ C∈M₁.image lift,∀ E∈M₁.image lift,C≠E →
      Disjoint (ordinaryCycleVertices G (m+1) C) (ordinaryCycleVertices G (m+1) E) := by
    intro C hC E hE hne
    obtain ⟨C,hCM,rfl⟩:=Finset.mem_image.mp hC
    obtain ⟨E,hEM,rfl⟩:=Finset.mem_image.mp hE
    exact hM₁ C hCM E hEM (fun he=>hne (congrArg lift he))
  have hcover : (M₁.image lift).biUnion (ordinaryCycleVertices G (m+1))=Finset.univ := by
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
      have hDedge : Dgraph.Adj v w := by
        change (⨆ C∈M₂,C.val.val).Adj v w
        simp only [SimpleGraph.iSup_adj]
        exact ⟨E,hE,hd⟩
      exact hQedge.2.2 hDedge
  · intro C hC v w h
    obtain ⟨C,hCM,rfl⟩:=Finset.mem_image.mp hC
    exact (C.property h).2.1

end Oberwolfach
