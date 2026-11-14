module

public import Oberwolfach.NearRegularUniformConflictFactors
public import Oberwolfach.RegularSubgraphInducedNearRegular

@[expose] public section
/-! The near-regular host required by the sampled two-factor lemma is
obtained by restricting a regular graph to a sufficiently large domain. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem restricted_regular_subgraph_factors_uniform_roots (m:ℕ) (hm:2≤m) (α:ℝ)
    (hα:0<α) (hα1:α≤1):
    ∃ η:ℝ,0<η ∧ ∀ s:ℕ,(m+1)∣s→∃ k:ℕ,(m+1)∣k ∧ ∀ L:ℝ,0≤L→∃ N:ℕ,
    ∀ (V:Type) [Fintype V] [DecidableEq V] (G Q F:SimpleGraph V) (D:ℕ),
    G.IsRegularOfDegree D→Q≤G→(∀ v,(F.degree v:ℝ)≤L)→∀ (B T:Finset V) (t:ℝ),
    (∀ v,((G\Q).degree v:ℝ)≤t)→N≤B.card→T⊆B→T.card=s→(∀ x∈T,∀ y∈T,¬F.Adj x y)→
    ((Fintype.card V-B.card:ℕ):ℝ)+t≤η*B.card→
    cycleThreshold (m+1)+α≤(D:ℝ)/Fintype.card V→
    let W:Type:={v:V // v∈B}
    let H:SimpleGraph W:=Q.induce (B:Set V)
    let T':Finset W:=T.subtype (fun v=>v∈B);
    ∃ S:Finset W,S.card=k ∧ Disjoint S T' ∧
      (∀ x∈S∪T',∀ y∈S∪T',¬(F.induce (B:Set V)).Adj x y) ∧
      let R:=S∪T'
      let J:=H.induce (R:Set W)
      let S':Finset (R:Set W):=S.subtype (fun v=>v∈R)
      ∃ M₁ M₂:Finset (OrdinaryCycle J (m+1)),
        (∀ C∈M₁,∀ E∈M₁,C≠E→Disjoint (ordinaryCycleVertices J (m+1) C) (ordinaryCycleVertices J (m+1) E)) ∧
        M₁.biUnion (ordinaryCycleVertices J (m+1))=Finset.univ ∧
        (∀ C∈M₂,∀ E∈M₂,C≠E→Disjoint (ordinaryCycleVertices J (m+1) C) (ordinaryCycleVertices J (m+1) E)) ∧
        M₂.biUnion (ordinaryCycleVertices J (m+1))=S' ∧
        (∀ C∈M₁,∀ E∈M₂,Disjoint C.val.val.edgeFinset E.val.val.edgeFinset) ∧
        (∀ C∈M₁,(ordinaryCycleVertices J (m+1) C∩(Finset.univ\S')).card≤1):=by
  obtain ⟨η,hη,hbase⟩:=near_regular_host_conflict_free_factors_uniform_roots m hm α hα hα1
  refine ⟨η,hη,?_⟩
  intro s hdivs
  obtain ⟨k,hk,hbase⟩:=hbase s hdivs
  refine ⟨k,hk,?_⟩
  intro L hL
  obtain ⟨N,hbase⟩:=hbase L hL
  refine ⟨max N 1,?_⟩
  intro V _ _ G Q F D hreg hQ hF B T t hdel hB hTB hT hTfree hmissing hθ
  let W:Type:={v:V // v∈B}
  let H:SimpleGraph W:=Q.induce (B:Set V)
  let T':Finset W:=T.subtype (fun v=>v∈B)
  have hW:Fintype.card W=B.card:=Fintype.card_coe B
  have hT':T'.card=s:=by dsimp [T'];rw [Finset.card_subtype,Finset.filter_eq_self.mpr hTB,hT]
  have hBpos:0<B.card:=by omega
  obtain ⟨v,hv⟩:=Finset.card_pos.mp hBpos
  have hn:0<Fintype.card V:=Fintype.card_pos_iff.mpr ⟨v⟩
  have hnR:(0:ℝ)<Fintype.card V:=by exact_mod_cast hn
  have hD:D≤Fintype.card V:=by have hh:=G.degree_lt_card_verts v;rw [hreg v] at hh;omega
  have hDR:(D:ℝ)≤Fintype.card V:=by exact_mod_cast hD
  have hθ1:(D:ℝ)/Fintype.card V≤1:=(div_le_one hnR).mpr hDR
  have hnear:∀ v:W,|((H.degree v):ℝ)-((D:ℝ)/Fintype.card V)*Fintype.card W|≤η*Fintype.card W:=by
    intro v
    rw [hW]
    exact (regular_subgraph_induced_near_centre G Q D hreg hQ B t hdel v).trans hmissing
  have hF':∀ v:W,((F.induce (B:Set V)).degree v:ℝ)≤L:=by
    intro v
    have hh:((F.induce (B:Set V)).degree v:ℝ)≤F.degree v.val:=by
      exact_mod_cast induced_degree_le_ambient F B v
    exact hh.trans (hF v.val)
  have hTfree':∀ x∈T',∀ y∈T',¬(F.induce (B:Set V)).Adj x y:=by
    intro x hx y hy hxy
    exact hTfree x.val (Finset.mem_subtype.mp hx) y.val (Finset.mem_subtype.mp hy) hxy
  exact hbase W (by rw [hW];omega) H (F.induce (B:Set V)) T' hT'
    ((D:ℝ)/Fintype.card V) hθ hθ1 hF' hTfree' hnear
end Oberwolfach
