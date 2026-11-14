module

public import Oberwolfach.RootedNearRegularConflictFree
public import Oberwolfach.NearRegularRootSeparatedFactors
public import Oberwolfach.InducedSetEmbedding

@[expose] public section
/-! In a nearly regular host, choose one fresh bounded set and then find
both transformer factors using only the cycle-decomposition threshold. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem near_regular_host_conflict_free_root_separated_factors (m:ℕ) (hm:2≤m) (α:ℝ)
    (hα:0<α) (hα1:α≤1) (s:ℕ) (hdivs:(m+1)∣s):
    ∃ η:ℝ,0<η ∧ ∃ k:ℕ,(m+1)∣k ∧ ∀ L:ℝ,0≤L→∃ N:ℕ,
    ∀ (V:Type) [Fintype V] [DecidableEq V],N≤Fintype.card V→
    ∀ (G F:SimpleGraph V) (T:Finset V),T.card=s→∀ θ:ℝ,
      cycleThreshold (m+1)+α≤θ→θ≤1→
      (∀ v,(F.degree v:ℝ)≤L)→(∀ x∈T,∀ y∈T,¬F.Adj x y)→
      (∀ v,|((G.degree v):ℝ)-θ*Fintype.card V|≤η*Fintype.card V)→
      ∃ S:Finset V,S.card=k ∧ Disjoint S T ∧
        (∀ x∈S∪T,∀ y∈S∪T,¬F.Adj x y) ∧
        let R:=S∪T
        let H:=G.induce (R:Set V)
        let S':Finset (R:Set V):=S.subtype (fun v=>v∈R)
        ∃ M₁ M₂:Finset (OrdinaryCycle H (m+1)),
          (∀ C∈M₁,∀ E∈M₁,C≠E→Disjoint (ordinaryCycleVertices H (m+1) C) (ordinaryCycleVertices H (m+1) E)) ∧
          M₁.biUnion (ordinaryCycleVertices H (m+1))=Finset.univ ∧
          (∀ C∈M₂,∀ E∈M₂,C≠E→Disjoint (ordinaryCycleVertices H (m+1) C) (ordinaryCycleVertices H (m+1) E)) ∧
          M₂.biUnion (ordinaryCycleVertices H (m+1))=S' ∧
          (∀ C∈M₁,∀ E∈M₂,Disjoint C.val.val.edgeFinset E.val.val.edgeFinset) ∧
          (∀ C∈M₁,(ordinaryCycleVertices H (m+1) C∩(Finset.univ\S')).card≤1):=by
  obtain ⟨ηf,hηf,Kf,hfactor⟩:=near_regular_root_separated_factors m hm α hα hα1 s
  let ηs:=min ηf 1
  have hηs:0<ηs:=lt_min hηf (by norm_num)
  have hηsf:ηs≤ηf:=min_le_left _ _
  have hηs1:ηs≤1:=min_le_right _ _
  obtain ⟨Ks,hsample⟩:=rooted_near_regular_sample_conflict_free s ηs hηs hηs1
  let k:=(m+1)*max (max Ks Kf) 1
  have hk:Ks≤k ∧ Kf≤k:=by dsimp [k];constructor <;> nlinarith [Nat.le_max_left (max Ks Kf) 1,Nat.le_max_left Ks Kf,Nat.le_max_right Ks Kf]
  refine ⟨ηs/8,by positivity,k,dvd_mul_right _ _,?_⟩
  intro L hL
  obtain ⟨N,hN⟩:=hsample k hk.1 L hL
  refine ⟨N,?_⟩
  intro V _ _ hn G F T hT θ hθ hθ1 hF hTfree hnear
  have hθ0:0≤θ:=by have hh:=cycleThreshold_nonneg (m+1);linarith
  obtain ⟨S,hSc,hdis,hdegree,hfree⟩:=hN V hn G F T hT θ hθ0 hθ1 hF hTfree hnear
  let R:=S∪T
  let W:Type:={v:V // v∈R}
  let H:SimpleGraph W:=G.induce (R:Set V)
  let S':Finset W:=S.subtype (fun v=>v∈R)
  have hsub:S⊆R:=Finset.subset_union_left
  have hSc':S'.card=k:=by dsimp [S'];rw [Finset.card_subtype,Finset.filter_eq_self.mpr hsub,hSc]
  have hRc:R.card=k+s:=by dsimp [R];rw [Finset.card_union_of_disjoint hdis,hSc,hT]
  have hW:Fintype.card W=k+s:=by simpa [W] using hRc
  have hSmap:(inducedSetEmbedding R (⟨S',hSc'⟩:FixedSubset W k)).val=S:=by
    ext v
    simp only [inducedSetEmbedding,Finset.mem_map,Finset.mem_subtype]
    constructor
    · rintro ⟨w,hw,rfl⟩;exact Finset.mem_subtype.mp hw
    · intro hv;exact ⟨⟨v,hsub hv⟩,Finset.mem_subtype.mpr hv,rfl⟩
  have hcenter:(cycleThreshold (m+1)+α)*(S'.card:ℝ)≤θ*k:=by
    rw [hSc'];exact mul_le_mul_of_nonneg_right hθ (Nat.cast_nonneg _)
  have hcenterhi:θ*k≤S'.card:=by rw [hSc'];nlinarith [mul_le_mul_of_nonneg_right hθ1 (Nat.cast_nonneg (α:=ℝ) k)]
  have hnear':∀ v:W,|((H.neighborFinset v∩S').card:ℝ)-θ*k|≤ηf*S'.card:=by
    intro v
    have hh:=inducedSetEmbedding_degree G R (⟨S',hSc'⟩:FixedSubset W k) v
    change (H.neighborFinset v∩S').card=(G.neighborFinset v.val∩(inducedSetEmbedding R ⟨S',hSc'⟩).val).card at hh
    rw [hSmap] at hh
    rw [hh,hSc']
    exact (hdegree v.val v.property).trans (mul_le_mul_of_nonneg_right hηsf (Nat.cast_nonneg _))
  have hdivR:(m+1)∣Fintype.card W:=by rw [hW];exact dvd_add (dvd_mul_right _ _) hdivs
  have hq:Fintype.card W-S'.card≤s:=by rw [hW,hSc'];omega
  obtain ⟨M₁,M₂,hM₁,hcover₁,hM₂,hcover₂,hedge,havoid⟩:=hfactor W H S' (θ*k)
    (by rw [hSc'];exact hk.2) (by rw [hSc'];exact dvd_mul_right _ _) hdivR hq hcenter hcenterhi hnear'
  exact ⟨S,hSc,hdis,hfree,M₁,M₂,hM₁,hcover₁,hM₂,hcover₂,hedge,havoid⟩
end Oberwolfach
