module

public import Oberwolfach.DegreeCodegreeCuts
public import Oberwolfach.NeighbourPairDomains

@[expose] public section

/-! Degree/codegree cut estimates on the actual finite endpoint domains. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem finite_domain_indicator_sum (B:Finset U) (P:U→Prop) :
    (∑ u:B,if P u.val then (1:ℝ) else 0)=(B.filter P).card := by
  rw [←finite_domain_predicate_card B P]
  simp only [Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]

theorem finite_domain_codegree_sum (B:Finset U) (P Q:U→Prop) :
    (∑ u:B,(if P u.val then (1:ℝ) else 0)*(if Q u.val then 1 else 0))=
      (B.filter (fun u=>P u∧Q u)).card := by
  trans (∑ u:B,if P u.val∧Q u.val then (1:ℝ) else 0)
  · apply Finset.sum_congr rfl
    intro u _
    by_cases hp:P u.val <;> by_cases hq:Q u.val <;> simp [hp,hq]
  · convert finite_domain_indicator_sum B (fun u=>P u∧Q u) using 1 <;> congr!

theorem degree_codegree_cuts_on_domains (H:V→U→Prop) (F:SimpleGraph V)
    (A:Finset V) (B:Finset U) (p ε η:ℝ) (d:ℕ)
    (hp:0<p) (hp1:p≤1) (hε:0≤ε) (hη:0<η) (hb:0<B.card)
    (hF:∀ v,F.degree v≤d)
    (hrow:∀ x∈A,(p-ε)*B.card≤((B.filter (H x)).card:ℝ))
    (hcodeg:∀ x∈A,∀ y∈A,x≠y → ¬F.Adj x y →
      ((B.filter (fun u=>H x u∧H y u)).card:ℝ)≤(p^2+ε)*B.card)
    (hsmall:ε≤p^2*η/24) (hlarge:(d+1:ℝ)≤p^2*η^2*B.card/8)
    (S:Finset V) (hSA:S⊆A) (T:Finset U) (hTB:T⊆B)
    (hS:η*B.card≤(S.card:ℝ)) (hT:η*B.card≤(T.card:ℝ)) :
    p/2*S.card*T.card≤(bipartiteMatrixCut (fun x u=>if H x u then 1 else 0) S T:ℝ) := by
  let e:A↪V:=⟨Subtype.val,Subtype.val_injective⟩
  let f:B↪U:=⟨Subtype.val,Subtype.val_injective⟩
  let H':A→B→Prop:=fun x u=>H x.val u.val
  let F':SimpleGraph A:=F.comap e
  let E:A→Finset A:=fun x=>insert x (F'.neighborFinset x)
  have hE (x:A):((E x).card:ℝ)≤d+1:=by
    have hh:(E x).card≤d+1:=by
      have h:=Finset.card_insert_le x (F'.neighborFinset x)
      rw [SimpleGraph.card_neighborFinset_eq_degree] at h
      exact h.trans (Nat.add_le_add_right ((embedding_comap_degree_le e F x).trans (hF x.val)) 1)
    exact_mod_cast hh
  have hrow' (x:A):(p-ε)*Fintype.card B≤∑ u,bipAdj H' x u:=by
    have he:(∑ u:B,bipAdj H' x u)=(B.filter (H x.val)).card:=finite_domain_indicator_sum B (H x.val)
    rw [he,Fintype.card_coe]
    exact hrow x.val x.property
  have hcodeg' (x y:A) (hy:y∉E x):
      (∑ u,bipAdj H' x u*bipAdj H' y u)≤(p^2+ε)*Fintype.card B:=by
    have hne:x.val≠y.val:=by
      intro he;have he':x=y:=Subtype.ext he;apply hy;simp [E,he']
    have hxy:¬F.Adj x.val y.val:=by
      intro ha;apply hy
      exact Finset.mem_insert_of_mem ((F'.mem_neighborFinset x y).mpr ha)
    have he:(∑ u:B,bipAdj H' x u*bipAdj H' y u)=(B.filter (fun u=>H x.val u∧H y.val u)).card:=
      finite_domain_codegree_sum B (H x.val) (H y.val)
    rw [he,Fintype.card_coe]
    exact hcodeg x.val x.property y.val y.property hne hxy
  let S':=embeddingPullFinset e S
  let T':=embeddingPullFinset f T
  have hSc:S'.card=S.card:=embeddingPullFinset_card e S (fun x hx=>⟨⟨x,hSA hx⟩,rfl⟩)
  have hTc:T'.card=T.card:=embeddingPullFinset_card f T (fun u hu=>⟨⟨u,hTB hu⟩,rfl⟩)
  have hSi:S'.image e=S:=embeddingPullFinset_image e S (fun x hx=>⟨⟨x,hSA hx⟩,rfl⟩)
  have hTi:T'.image f=T:=embeddingPullFinset_image f T (fun u hu=>⟨⟨u,hTB hu⟩,rfl⟩)
  have hh:=bipartite_cuts_from_degrees_and_codegrees H' p ε (d+1) η hp hp1 hε hη
    (by simpa only [Fintype.card_coe] using hb) E hE hrow' hcodeg' hsmall
    (by simpa only [Fintype.card_coe] using hlarge) S' T'
    (by simpa only [Fintype.card_coe,hSc] using hS) (by simpa only [Fintype.card_coe,hTc] using hT)
  have hcut:bipartiteMatrixCut (fun x u=>if H' x u then 1 else 0) S' T'=
      bipartiteMatrixCut (fun x u=>if H x u then 1 else 0) S T:=by
    rw [←hSi,←hTi]
    simp only [bipartiteMatrixCut]
    rw [Finset.sum_image (by intros a ha b hb he;exact e.injective he)]
    apply Finset.sum_congr rfl
    intro a ha
    rw [Finset.sum_image (by intros u hu v hv he;exact f.injective he)]
    rfl
  rw [hSc,hTc,hcut] at hh
  exact hh

end Oberwolfach
