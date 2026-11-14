module

public import Oberwolfach.PhysicalSampledCandidateDegrees
public import Oberwolfach.FractionalResourceMatching

@[expose] public section
/-! A weighted matching on physical resources for candidates realized in
the original typed sample. Typed resources may collide across candidates. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem physical_sampled_matching (r Bpow:ℕ) (hr:2≤r) (hB:1≤Bpow)
    (K α γ:ℝ) (hK:0<K) (hα:0<α) (hγ:0<γ):
    ∃ε:ℝ,0<ε ∧ ∃n₀:ℕ,∀n:ℕ,n₀≤n→
    ∀(A V C Test Row:Type) [Fintype A] [Fintype V] [Fintype C] [Fintype Test] [Fintype Row]
      [DecidableEq A] [DecidableEq V] [DecidableEq C],
    ∀(φ:A→V) (R:C→Finset A) (w:C→ℝ) (σ:A→Bool),
    let W:=PhysicalSampledActive φ σ
    let E:=PhysicalSampledCandidate R σ
    let Q:=physicalSampledCandidateSet φ R σ;
    ∀(g:Test→E→ℝ) (S:Row→Finset W),
    Fintype.card W≤n^Bpow→Fintype.card Test≤n^Bpow→Fintype.card Row≤n^Bpow→
    (∀c,Set.InjOn φ (↑(R c):Set A))→(∀c,2≤(R c).card ∧ (R c).card≤r)→
    (∀c,0≤w c)→
    (∀x:W,|(∑a∈Finset.univ.filter (fun a=>φ a=x.val),
      if σ a=true then resourcePatternLoad R w (fun _ _=>true) a σ else 0)-1|≤ε)→
    (∀x y:V,x≠y→(∑c,if x∈(R c).image φ ∧ y∈(R c).image φ then w c else 0)≤K/n)→
    (∀j,α*n≤(S j).card)→(∀i c,0≤g i c ∧ g i c≤1)→
    (∀i,α*n≤∑c:E,g i c*w c.val)→
    ∃M:Finset E,(∀c∈M,∀c'∈M,c≠c'→Disjoint (Q c) (Q c')) ∧
      (∀j,((S j\M.biUnion Q).card:ℝ)≤γ*(S j).card) ∧
      (∀i,(1-γ)*(∑c:E,g i c*w c.val)≤∑c∈M,g i c) ∧
      (∀i,(∑c∈M,g i c)≤(1+γ)*(∑c:E,g i c*w c.val)) :=by
  obtain ⟨ε,hε,n₀,hmatch⟩:=fractional_resource_matching r Bpow hr hB K α γ hK hα hγ
  refine ⟨ε,hε,n₀,?_⟩
  intro n hn A V C Test Row _ _ _ _ _ _ _ _ φ R w σ
  dsimp only
  intro g S hW hTest hRow hinj hsize hw hload hpair hS hg hmass
  apply hmatch n hn (PhysicalSampledActive φ σ) (PhysicalSampledCandidate R σ) Test Row
    (physicalSampledCandidateSet φ R σ) (fun c=>w c.val) g S hW hTest hRow
  · intro c
    rw [physical_sampled_candidate_set_card φ R σ c (hinj c.val)]
    exact hsize c.val
  · intro c;exact hw c.val
  · intro x
    rw [physical_sampled_candidate_degree φ R w σ hinj x]
    have hh:=abs_le.mp (hload x)
    constructor <;> linarith
  · intro x y hxy
    have hne:x.val≠y.val:=fun h=>hxy (Subtype.ext h)
    exact (physical_sampled_candidate_codegree_le φ R w σ hw x y).trans (hpair x.val y.val hne)
  · exact hS
  · exact hg
  · exact hmass
end Oberwolfach
