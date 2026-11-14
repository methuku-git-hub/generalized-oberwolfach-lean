module

public import Oberwolfach.ResourcePatternConcentration
public import Oberwolfach.InducedResourceWeights
public import Oberwolfach.FiniteSupportCounts
public import Oberwolfach.EdgeRetention

@[expose] public section

/-! Independent vertex retention with the original candidate identifiers.
Root loads omit the root's trial and therefore apply also to absent roots.
All supports and weights precede the sampling. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C]

def bernoulliVertexSet (σ:V→Bool):Finset V:=Finset.univ.filter (fun v=>σ v=true)

@[simp] theorem mem_bernoulliVertexSet (σ:V→Bool) (v:V):
    v∈bernoulliVertexSet σ ↔ σ v=true:=by simp [bernoulliVertexSet]

theorem bernoulliVertexSet_one_coordinate (x:V) (σ τ:V→Bool)
    (hagree:∀ v,v≠x→σ v=τ v):
    ((bernoulliVertexSet σ\bernoulliVertexSet τ).card+
      (bernoulliVertexSet τ\bernoulliVertexSet σ).card)≤1:=by
  let A:=bernoulliVertexSet σ\bernoulliVertexSet τ
  let B:=bernoulliVertexSet τ\bernoulliVertexSet σ
  have hd:Disjoint A B:=by
    apply Finset.disjoint_left.mpr
    intro v hv hw
    exact (Finset.mem_sdiff.mp hv).2 (Finset.mem_sdiff.mp hw).1
  have hs:A∪B⊆{x}:=by
    intro v hv
    by_contra hx
    have hne:v≠x:=by simpa using hx
    have he:=hagree v hne
    rcases Finset.mem_union.mp hv with hv|hv
    · have hh:=Finset.mem_sdiff.mp hv
      exact hh.2 (by simpa only [mem_bernoulliVertexSet,←he] using hh.1)
    · have hh:=Finset.mem_sdiff.mp hv
      exact hh.2 (by simpa only [mem_bernoulliVertexSet,he] using hh.1)
  have hh:=Finset.card_le_card hs
  rw [Finset.card_union_of_disjoint hd,Finset.card_singleton] at hh
  exact hh

theorem bernoulli_support_count_mean (R:C→Finset V) (h:ℕ)
    (hR:∀ i,(R i).card=h) (p:ℝ) (hp:0≤p) (hp1:p≤1):
    (FiniteLaw.pi (fun _:V=>FiniteLaw.retentionCoin p hp hp1)).expectation
      (fun σ=>(Fintype.card {i:C // R i⊆bernoulliVertexSet σ}:ℝ))=
      p^h*Fintype.card C:=by
  have he (σ:V→Bool):
      (Fintype.card {i:C // R i⊆bernoulliVertexSet σ}:ℝ)=
        ∑ i,patternValue (R i) (fun _=>true) σ:=by
    simp only [Fintype.card_subtype,Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
    apply Finset.sum_congr rfl
    intro i _
    rw [patternValue_indicator]
    congr 1
    simp only [Finset.subset_iff,mem_bernoulliVertexSet]
  simp_rw [he]
  unfold FiniteLaw.expectation
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  have hm (i:C):
      (FiniteLaw.pi (fun _:V=>FiniteLaw.retentionCoin p hp hp1)).expectation
        (patternValue (R i) (fun _=>true))=p^h:=by
    rw [finiteLaw_expectation_pattern]
    simp only [FiniteLaw.retentionCoin,Bool.true_eq,ite_true,Finset.prod_const,hR]
  change (∑ i,(FiniteLaw.pi (fun _:V=>FiniteLaw.retentionCoin p hp hp1)).expectation
    (patternValue (R i) (fun _=>true)))=_
  simp only [hm,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_comm]

theorem bernoulli_support_count_tail (R:C→Finset V) (h K:ℕ)
    (hR:∀ i,(R i).card=h)
    (hK:∀ v,Fintype.card {i:C // v∈R i}≤K)
    (p:ℝ) (hp:0≤p) (hp1:p≤1) (v t:ℝ) (hv:0<v) (ht:0<t)
    (hvar:(Fintype.card V:ℝ)*(K:ℝ)^2≤v):
    (FiniteLaw.pi (fun _:V=>FiniteLaw.retentionCoin p hp hp1)).probability
      (fun σ=>t≤|(Fintype.card {i:C // R i⊆bernoulliVertexSet σ}:ℝ)-p^h*Fintype.card C|)
      ≤2*Real.exp (-2*t^2/v):=by
  have hx (x:V) (σ τ:V→Bool) (ha:∀ y,y≠x→σ y=τ y):
      |(Fintype.card {i:C // R i⊆bernoulliVertexSet σ}:ℝ)-
        Fintype.card {i:C // R i⊆bernoulliVertexSet τ}|≤K:=by
    have hh:=finite_support_count_difference R (bernoulliVertexSet σ) (bernoulliVertexSet τ) K
      (fun y=>(Fintype.card_subtype_mono _ _ (fun i hi=>hi.2)).trans (hK y))
    have hs:(((bernoulliVertexSet σ\bernoulliVertexSet τ).card+
      (bernoulliVertexSet τ\bernoulliVertexSet σ).card:ℕ):ℝ)≤1:=
        by exact_mod_cast bernoulliVertexSet_one_coordinate x σ τ ha
    exact hh.trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hs (Nat.cast_nonneg K))
  have hh:=finiteLaw_boundedDifferences_variance_bound
    (fun _:V=>FiniteLaw.retentionCoin p hp hp1)
    (fun σ=>(Fintype.card {i:C // R i⊆bernoulliVertexSet σ}:ℝ))
    (fun _:V=>(K:ℝ)) (fun _=>Nat.cast_nonneg K) v hv
    (by simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using hvar) hx t ht
  simpa only [bernoulli_support_count_mean R h hR] using hh

theorem bernoulli_root_load_pattern (R:C→Finset V) (w:C→ℝ) (v:V) (σ:V→Bool):
    resourceRootOmittedLoad R w (fun x=>x∈bernoulliVertexSet σ) v=
      resourcePatternLoad R w (fun _ _=>true) v σ:=by
  unfold resourceRootOmittedLoad resourcePatternLoad
  apply Finset.sum_congr rfl
  intro i _
  rw [patternValue_indicator]
  have he:(∀ x∈R i\{v},σ x=true)↔∀ x∈R i,x≠v→x∈bernoulliVertexSet σ:=by
    simp only [Finset.mem_sdiff,Finset.mem_singleton,mem_bernoulliVertexSet]
    tauto
  simp only [he]
  by_cases hv:v∈R i <;> by_cases hh:∀ x∈R i,x≠v→x∈bernoulliVertexSet σ
  all_goals simp [hv,hh]

theorem bernoulli_root_load_mean (R:C→Finset V) (c:ℕ)
    (hR:∀ i,(R i).card=c) (w:C→ℝ) (v:V)
    (p:ℝ) (hp:0≤p) (hp1:p≤1):
    (FiniteLaw.pi (fun _:V=>FiniteLaw.retentionCoin p hp hp1)).expectation
      (fun σ=>resourceRootOmittedLoad R w (fun x=>x∈bernoulliVertexSet σ) v)=
      p^(c-1)*hypergraphWeightedDegree R w v:=by
  simp_rw [bernoulli_root_load_pattern]
  rw [resourcePatternLoad_expectation]
  unfold resourcePatternMean hypergraphWeightedDegree
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi:v∈R i
  · have hs:(R i\{v}).card=c-1:=by
      rw [Finset.sdiff_singleton_eq_erase,Finset.card_erase_of_mem hi,hR]
    simp only [hi,ite_true,FiniteLaw.retentionCoin,Bool.true_eq,Finset.prod_const,hs,mul_comm]
  · simp only [hi,ite_false,zero_mul,mul_zero]

theorem bernoulli_root_load_tail (R:C→Finset V) (c J:ℕ) (hc:2≤c)
    (hR:∀ i,(R i).card=c) (hJ:∀ Y:Finset V,Fintype.card {i:C // R i=Y}≤J)
    (w:C→ℝ) (B:ℝ) (hB:0≤B) (hw:∀ i,0≤w i ∧ w i≤B)
    (root:V) (p:ℝ) (hp:0≤p) (hp1:p≤1) (v t:ℝ) (hv:0<v) (ht:0<t)
    (hvar:(Fintype.card V:ℝ)*((J:ℝ)*(Fintype.card V:ℝ)^(c-2)*B)^2≤v):
    (FiniteLaw.pi (fun _:V=>FiniteLaw.retentionCoin p hp hp1)).probability
      (fun σ=>t≤|resourceRootOmittedLoad R w (fun x=>x∈bernoulliVertexSet σ) root-
        p^(c-1)*hypergraphWeightedDegree R w root|)≤2*Real.exp (-2*t^2/v):=by
  let K:ℝ:=(J:ℝ)*(Fintype.card V:ℝ)^(c-2)*B
  have hK:0≤K:=by dsimp [K];positivity
  have hpair (u:V):resourceOmittedPairWeight R w root u≤K:=by
    by_cases hu:u=root
    · simp only [resourceOmittedPairWeight,hu,ne_eq,not_true_eq_false,and_false,ite_false,Finset.sum_const_zero]
      exact hK
    · have hh:=induced_resource_pair_weight R c J hc hR hJ w B hB (fun i=>(hw i).2) Finset.univ root u (Ne.symm hu)
      unfold resourceOmittedPairWeight
      simp only [ne_eq,hu,not_false_eq_true,and_true]
      dsimp [K]
      simpa only [inducedResourceWeight,Finset.subset_univ,ite_true,Finset.card_univ] using hh
  have hchange (u:V) (σ τ:V→Bool) (ha:∀ y,y≠u→σ y=τ y):
      |resourceRootOmittedLoad R w (fun x=>x∈bernoulliVertexSet σ) root-
        resourceRootOmittedLoad R w (fun x=>x∈bernoulliVertexSet τ) root|≤K:=by
    simp_rw [bernoulli_root_load_pattern]
    exact (resourcePatternLoad_one_coordinate R w (fun i=>(hw i).1) (fun _ _=>true) root u σ τ ha).trans (hpair u)
  have hh:=finiteLaw_boundedDifferences_variance_bound
    (fun _:V=>FiniteLaw.retentionCoin p hp hp1)
    (fun σ=>resourceRootOmittedLoad R w (fun x=>x∈bernoulliVertexSet σ) root)
    (fun _:V=>K) (fun _=>hK) v hv
    (by simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using hvar) hchange t ht
  simpa only [bernoulli_root_load_mean R c hR] using hh

end Oberwolfach
