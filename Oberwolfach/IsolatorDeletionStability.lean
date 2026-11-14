module

public import Oberwolfach.IsolatorDeletionCounts
public import Oberwolfach.FiniteConfigurationLoss

@[expose] public section

/-! Isolator counts under physical deletions, at a retained rim root. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V U : Type*} [Fintype V] [DecidableEq V] [Fintype U]
  {P Q F : SimpleGraph V} {H : V → U → Prop} {k : ℕ} {θ α : ℝ} {x y : V}

def IsolatorAvoids (T : OrdinaryIsolatorConfiguration P Q F H k θ α x y)
    (D : SimpleGraph V) (E : V → U → Prop) : Prop :=
  (∀ z∈T.vertices.val,∀ t∈T.vertices.val,¬D.Adj z t) ∧
    (∀ z∈T.vertices.val,¬E z T.hub)

def isolatorAfterDeletion (D : SimpleGraph V) (E : V → U → Prop)
    (T : {T : OrdinaryIsolatorConfiguration P Q F H k θ α x y // IsolatorAvoids T D E}) :
    OrdinaryIsolatorConfiguration P (Q \ D) F (fun z a=>H z a ∧ ¬E z a) k θ α x y where
  hub := T.val.hub
  vertices := T.val.vertices
  endpoints := T.val.endpoints
  rim_edges := by
    intro z t hzt
    have he := (spanningRestriction_adj P T.val.vertices.val z t).mp hzt
    exact ⟨T.val.rim_edges hzt,T.property.1 z he.2.1 t he.2.2⟩
  spokes := fun z hz=>⟨T.val.spokes z hz,T.property.2 z hz⟩
  independent := T.val.independent
  density := T.val.density

theorem isolatorAfterDeletion_injective (D : SimpleGraph V) (E : V → U → Prop) :
    Function.Injective (isolatorAfterDeletion (P:=P) (Q:=Q) (F:=F) (H:=H) (k:=k) (θ:=θ) (α:=α) (x:=x) (y:=y) D E) := by
  intro T T' he
  apply Subtype.ext
  apply OrdinaryIsolatorConfiguration.encoding_injective
  exact congrArg (fun S=>(S.hub,S.vertices)) he

theorem isolator_avoidance_failure_bound
    (T : OrdinaryIsolatorConfiguration P Q F H k θ α x y)
    (D : SimpleGraph V) (E : V → U → Prop) :
    (if IsolatorAvoids T D E then (0 : ℝ) else 1)≤
      (∑ z,∑ t,if D.Adj z t then (if z∈T.vertices.val ∧ t∈T.vertices.val then (1 : ℝ) else 0) else 0)+
      (∑ z,∑ a,if E z a then (if T.hub=a ∧ z∈T.vertices.val then (1 : ℝ) else 0) else 0) := by
  classical
  have hR : (0 : ℝ)≤∑ z,∑ t,if D.Adj z t then
      (if z∈T.vertices.val ∧ t∈T.vertices.val then (1 : ℝ) else 0) else 0 := by
    apply Finset.sum_nonneg;intro z _;apply Finset.sum_nonneg;intro t _;split_ifs <;> norm_num
  have hS : (0 : ℝ)≤∑ z,∑ a,if E z a then
      (if T.hub=a ∧ z∈T.vertices.val then (1 : ℝ) else 0) else 0 := by
    apply Finset.sum_nonneg;intro z _;apply Finset.sum_nonneg;intro a _;split_ifs <;> norm_num
  by_cases hg : IsolatorAvoids T D E
  · rw [if_pos hg]
    linarith
  rw [if_neg hg]
  change ¬(_ ∧ _) at hg
  rcases not_and_or.mp hg with hg|hg
  · push_neg at hg
    obtain ⟨z,hz,t,ht,hzt⟩ := hg
    have hin := Finset.single_le_sum (s:=Finset.univ) (a:=t)
      (f:=fun t=>if D.Adj z t then (if z∈T.vertices.val ∧ t∈T.vertices.val then (1 : ℝ) else 0) else 0)
      (fun t _=>by split_ifs <;> norm_num) (Finset.mem_univ _)
    have hout := Finset.single_le_sum (s:=Finset.univ) (a:=z)
      (f:=fun z=>∑ t,if D.Adj z t then (if z∈T.vertices.val ∧ t∈T.vertices.val then (1 : ℝ) else 0) else 0)
      (fun z _=>by apply Finset.sum_nonneg;intro t _;split_ifs <;> norm_num) (Finset.mem_univ _)
    simp only [hzt,hz,ht,and_self,ite_true,true_and] at hin
    simp only [hz,true_and] at hout
    linarith
  · push_neg at hg
    obtain ⟨z,hz,he⟩ := hg
    have hin := Finset.single_le_sum (s:=Finset.univ) (a:=T.hub)
      (f:=fun a=>if E z a then (if T.hub=a ∧ z∈T.vertices.val then (1 : ℝ) else 0) else 0)
      (fun a _=>by split_ifs <;> norm_num) (Finset.mem_univ _)
    have hout := Finset.single_le_sum (s:=Finset.univ) (a:=z)
      (f:=fun z=>∑ a,if E z a then (if T.hub=a ∧ z∈T.vertices.val then (1 : ℝ) else 0) else 0)
      (fun z _=>by apply Finset.sum_nonneg;intro a _;split_ifs <;> norm_num) (Finset.mem_univ _)
    simp only [he,hz,and_self,ite_true,and_true] at hin
    simp only [hz,and_true] at hout
    linarith

theorem isolator_deleted_edges_count (hxy : x≠y) (hk : 4≤k)
    (hn : 0<Fintype.card V) (hu : Fintype.card U≤Fintype.card V)
    (D : SimpleGraph V) (E : V → U → Prop) (d : ℝ)
    (hD : ∀ z,(D.degree z : ℝ)≤d)
    (hEout : ∀ z,(∑ a,bipAdj E z a)≤d) (hEin : ∀ a,(∑ z,bipAdj E z a)≤d)
    (hroot : ¬D.Adj x y) :
    (∑ z,∑ t,if D.Adj z t then
      (∑ T : OrdinaryIsolatorConfiguration P Q F H k θ α x y,
      if z∈T.vertices.val ∧ t∈T.vertices.val then (1 : ℝ) else 0) else 0)+
    (∑ z,∑ a,if E z a then
      (∑ T : OrdinaryIsolatorConfiguration P Q F H k θ α x y,
      if T.hub=a ∧ z∈T.vertices.val then (1 : ℝ) else 0) else 0)≤
      8*d*(Fintype.card V : ℝ)^(k-2) := by
  let n : ℝ := Fintype.card V
  let M : ℝ := n^(k-2)
  let N : ℝ := n^(k-3)
  have hM : 0≤M := by dsimp [M,n];positivity
  have hN : 0≤N := by dsimp [N,n];positivity
  have hd (z : V) : (∑ t,bipAdj D.Adj z t)≤d := by
    have he : (∑ t,bipAdj D.Adj z t)=(D.degree z : ℝ) := by
      rw [SimpleGraph.degree,SimpleGraph.neighborFinset_eq_filter,Finset.card_filter]
      push_cast
      apply Finset.sum_congr rfl
      intro t _
      dsimp [bipAdj]
    rw [he]
    exact hD z
  have hdi (t : V) : (∑ z,bipAdj D.Adj z t)≤d := by
    have he : (∑ z,bipAdj D.Adj z t)=(∑ z,bipAdj D.Adj t z) := by
      apply Finset.sum_congr rfl
      intro z _
      simp only [bipAdj,D.adj_comm]
    rw [he]
    exact hd t
  have hR := relation_root_incident_cost D.Adj d hd hdi {x,y} {x,y} M N hM hN
  have hS := relation_root_incident_cost E d hEout hEin {x,y} ∅ M N hM hN
  have hc : ({x,y} : Finset V).card=2 := by simp [hxy]
  simp only [hc,Nat.cast_ofNat,Finset.card_empty,Nat.cast_zero,Finset.notMem_empty,or_false,add_zero] at hR hS
  calc
    _ ≤ (∑ z,∑ t,if D.Adj z t then (if z∈({x,y}:Finset V) ∨ t∈({x,y}:Finset V) then M else N) else 0)+
        (∑ z,∑ a,if E z a then (if z∈({x,y}:Finset V) then M else N) else 0) := by
      apply add_le_add
      · apply Finset.sum_le_sum
        intro z _
        apply Finset.sum_le_sum
        intro t _
        by_cases hzt : D.Adj z t
        · simp only [hzt,ite_true]
          have he : s(x,y)≠s(z,t) := by
            intro he
            have hm : s(z,t)∈D.edgeSet := by exact hzt
            rw [← he] at hm
            exact hroot hm
          exact isolator_vertex_pair_count hxy hk hn hu z t hzt.ne he
        · simp only [hzt,ite_false,le_refl]
      · apply Finset.sum_le_sum
        intro z _
        apply Finset.sum_le_sum
        intro a _
        by_cases he : E z a
        · simp only [he,ite_true]
          exact isolator_spoke_count (k:=k) hxy (by omega) z a
        · simp only [he,ite_false,le_refl]
    _ ≤ d*((2+2)*M+n*N)+d*(2*M+n*N) := add_le_add hR hS
    _ = _ := by
      have he : k-2=k-3+1 := by omega
      dsimp [M,N,n]
      rw [he,pow_succ]
      ring


/-- The hub, vertex subset, parent induced graph, forbidden graph and
minimum-degree condition are preserved by the restriction map. -/
theorem ordinary_isolator_deletion_stability (hxy : x≠y) (hk : 4≤k)
    (hn : 0<Fintype.card V) (hu : Fintype.card U≤Fintype.card V)
    (D : SimpleGraph V) (E : V → U → Prop) (d : ℝ)
    (hD : ∀ z,(D.degree z : ℝ)≤d)
    (hEout : ∀ z,(∑ a,bipAdj E z a)≤d) (hEin : ∀ a,(∑ z,bipAdj E z a)≤d)
    (hroot : ¬D.Adj x y) :
    (Fintype.card (OrdinaryIsolatorConfiguration P Q F H k θ α x y) : ℝ)-
      Fintype.card (OrdinaryIsolatorConfiguration P (Q \ D) F (fun z a=>H z a ∧ ¬E z a) k θ α x y)≤
        8*d*(Fintype.card V : ℝ)^(k-2) := by
  classical
  let A := OrdinaryIsolatorConfiguration P Q F H k θ α x y
  have hstart := finite_configuration_loss (fun T : A=>IsolatorAvoids T D E)
    (isolatorAfterDeletion D E) (isolatorAfterDeletion_injective D E)
  have hRcomm : (∑ T : A,∑ z,∑ t,if D.Adj z t then
      (if z∈T.vertices.val ∧ t∈T.vertices.val then (1 : ℝ) else 0) else 0)=
      (∑ z,∑ t,if D.Adj z t then
      (∑ T : A,if z∈T.vertices.val ∧ t∈T.vertices.val then (1 : ℝ) else 0) else 0) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro z _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro t _
    by_cases hzt : D.Adj z t <;> simp only [hzt,ite_true,ite_false,Finset.sum_const_zero]
  have hScomm : (∑ T : A,∑ z,∑ a,if E z a then
      (if T.hub=a ∧ z∈T.vertices.val then (1 : ℝ) else 0) else 0)=
      (∑ z,∑ a,if E z a then
      (∑ T : A,if T.hub=a ∧ z∈T.vertices.val then (1 : ℝ) else 0) else 0) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro z _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    by_cases hza : E z a <;> simp only [hza,ite_true,ite_false,Finset.sum_const_zero]
  apply hstart.trans
  calc
    _ ≤ ∑ T : A,((∑ z,∑ t,if D.Adj z t then
      (if z∈T.vertices.val ∧ t∈T.vertices.val then (1 : ℝ) else 0) else 0)+
      (∑ z,∑ a,if E z a then (if T.hub=a ∧ z∈T.vertices.val then (1 : ℝ) else 0) else 0)) :=
        Finset.sum_le_sum (fun T _=>isolator_avoidance_failure_bound T D E)
    _ ≤ _ := by
      rw [Finset.sum_add_distrib,hRcomm,hScomm]
      exact isolator_deleted_edges_count hxy hk hn hu D E d hD hEout hEin hroot

end Oberwolfach
