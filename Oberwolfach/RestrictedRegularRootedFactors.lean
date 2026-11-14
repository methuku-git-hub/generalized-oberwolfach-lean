module

public import Oberwolfach.NearRegularRootedTwoFactors
public import Oberwolfach.RegularInducedNearRegular

@[expose] public section
/-! The near-regular host required by the sampled two-factor lemma is
obtained by restricting a regular graph to a sufficiently large domain. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem restricted_regular_host_rooted_two_factors (m:ℕ) (hm:2≤m) (α:ℝ)
    (hα:0<α) (hα1:α≤1) (s:ℕ) (hdivs:(m+1)∣s):
    ∃ η:ℝ,0<η ∧ ∃ k:ℕ,(m+1)∣k ∧ ∃ N:ℕ,
    ∀ (V:Type) [Fintype V] [DecidableEq V] (G:SimpleGraph V) (D:ℕ),
    G.IsRegularOfDegree D→∀ (B T:Finset V),N≤B.card→T⊆B→T.card=s→
    ((Fintype.card V-B.card:ℕ):ℝ)≤η*B.card→
    cycleThreshold (m+1)+α≤(D:ℝ)/Fintype.card V→
    let W:Type:={v:V // v∈B}
    let H:SimpleGraph W:=G.induce (B:Set V)
    let T':Finset W:=T.subtype (fun v=>v∈B);
    ∃ S:Finset W,S.card=k ∧ Disjoint S T' ∧
      let R:=S∪T'
      let J:=H.induce (R:Set W)
      let S':Finset (R:Set W):=S.subtype (fun v=>v∈R)
      ∃ M₁ M₂:Finset (OrdinaryCycle J (m+1)),
        (∀ C∈M₁,∀ E∈M₁,C≠E→Disjoint (ordinaryCycleVertices J (m+1) C) (ordinaryCycleVertices J (m+1) E)) ∧
        M₁.biUnion (ordinaryCycleVertices J (m+1))=Finset.univ ∧
        (∀ C∈M₂,∀ E∈M₂,C≠E→Disjoint (ordinaryCycleVertices J (m+1) C) (ordinaryCycleVertices J (m+1) E)) ∧
        M₂.biUnion (ordinaryCycleVertices J (m+1))=S' ∧
        (∀ C∈M₁,∀ E∈M₂,Disjoint C.val.val.edgeFinset E.val.val.edgeFinset) ∧
        (∀ C∈M₁,∀ v w,C.val.val.Adj v w→v∈S' ∨ w∈S'):=by
  obtain ⟨η,hη,k,hk,N,hbase⟩:=near_regular_host_rooted_two_factors m hm α hα hα1 s hdivs
  refine ⟨η,hη,k,hk,max N 1,?_⟩
  intro V _ _ G D hreg B T hB hTB hT hmissing hθ
  let W:Type:={v:V // v∈B}
  let H:SimpleGraph W:=G.induce (B:Set V)
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
    exact (regular_induced_degree_near_centre G D hreg B v).trans hmissing
  exact hbase W (by rw [hW];omega) H T' hT' ((D:ℝ)/Fintype.card V) hθ hθ1 hnear
end Oberwolfach
