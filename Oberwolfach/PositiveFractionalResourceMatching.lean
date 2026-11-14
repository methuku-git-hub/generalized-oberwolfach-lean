module

public import Oberwolfach.PositiveResourceRestriction

@[expose] public section
/-! The resource matching can be chosen from positive-weight candidates;
zero-weight candidates never need to be added to the packing. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem fractional_resource_matching_positive (r B:ℕ) (hr:2≤r) (hB:1≤B)
    (K a γ:ℝ) (hK:0<K) (ha:0<a) (hγ:0<γ):
    ∃η₀:ℝ,0<η₀ ∧ ∃n₀:ℕ,∀n:ℕ,n₀≤n →
    ∀(V E A I:Type) [Fintype V] [Fintype E] [Fintype A] [Fintype I] [DecidableEq V],
    ∀(R:E→Finset V) (w:E→ℝ) (g:A→E→ℝ) (S:I→Finset V),
    Fintype.card V≤n^B → Fintype.card A≤n^B → Fintype.card I≤n^B →
    (∀e,0<w e→2≤(R e).card ∧ (R e).card≤r) → (∀e,0≤w e) →
    (∀v,1-η₀≤hypergraphWeightedDegree R w v ∧ hypergraphWeightedDegree R w v≤1+η₀) →
    (∀u v,u≠v → (∑e,if u∈R e ∧ v∈R e then w e else 0)≤K/n) →
    (∀i,a*n≤(S i).card) → (∀i e,0≤g i e ∧ g i e≤1) →
    (∀i,a*n≤∑e,g i e*w e) →
    ∃M:Finset E,(∀e∈M,0<w e) ∧ (∀e∈M,∀f∈M,e≠f→Disjoint (R e) (R f)) ∧
      (∀i,((S i\M.biUnion R).card:ℝ)≤γ*(S i).card) ∧
      (∀i,(1-γ)*(∑e,g i e*w e)≤∑e∈M,g i e) ∧
      (∀i,(∑e∈M,g i e)≤(1+γ)*(∑e,g i e*w e)) := by
  obtain ⟨η,hη,n₀,hmatch⟩:=fractional_resource_matching r B hr hB K a γ hK ha hγ
  refine ⟨η,hη,n₀,?_⟩
  intro n hn V E A I _ _ _ _ _ R w g S hV hA hI hsize hw hdeg hpair hS hg hmass
  let R' : PositiveResource w→Finset V := fun e=>R e.val
  let w' : PositiveResource w→ℝ := fun e=>w e.val
  let g' : A→PositiveResource w→ℝ := fun i e=>g i e.val
  have hdeg':∀v,1-η≤hypergraphWeightedDegree R' w' v ∧ hypergraphWeightedDegree R' w' v≤1+η := by
    intro v
    rw [show hypergraphWeightedDegree R' w' v=hypergraphWeightedDegree R w v from positive_resource_degree R w hw v]
    exact hdeg v
  have hpair':∀u v,u≠v → (∑e:PositiveResource w,if u∈R' e ∧ v∈R' e then w' e else 0)≤K/n := by
    intro u v huv
    rw [show (∑e:PositiveResource w,if u∈R' e ∧ v∈R' e then w' e else 0)=
      ∑e,if u∈R e ∧ v∈R e then w e else 0 from positive_resource_codegree R w hw u v]
    exact hpair u v huv
  have hmass':∀i,a*n≤∑e:PositiveResource w,g' i e*w' e:=by
    intro i
    rw [show (∑e:PositiveResource w,g' i e*w' e)=∑e,g i e*w e from positive_resource_weighted_sum w hw (g i)]
    exact hmass i
  obtain ⟨M,hdis,hcover,hlower,hupper⟩:=hmatch n hn V (PositiveResource w) A I R' w' g' S
    hV hA hI (fun e=>hsize e.val e.property) (fun e=>(e.property).le) hdeg' hpair' hS (fun i e=>hg i e.val) hmass'
  let N:Finset E:=M.image Subtype.val
  have hsum:∀i,(∑e∈N,g i e)=∑e∈M,g' i e:=by
    intro i
    dsimp [N,g']
    rw [Finset.sum_image]
    intro a _ b _ hab
    exact Subtype.ext hab
  have hunion:N.biUnion R=M.biUnion R':=by
    ext v
    simp [N,R',Finset.mem_biUnion]
  refine ⟨N,?_,?_,?_,?_,?_⟩
  · intro e he
    obtain ⟨x,_,rfl⟩:=Finset.mem_image.mp he
    exact x.property
  · intro e he f hf hne
    obtain ⟨x,hx,rfl⟩:=Finset.mem_image.mp he
    obtain ⟨y,hy,rfl⟩:=Finset.mem_image.mp hf
    exact hdis x hx y hy (fun h=>hne (congrArg Subtype.val h))
  · intro i;rw [hunion];exact hcover i
  · intro i
    rw [hsum,←positive_resource_weighted_sum w hw (g i)]
    exact hlower i
  · intro i
    rw [hsum,←positive_resource_weighted_sum w hw (g i)]
    exact hupper i
end Oberwolfach
