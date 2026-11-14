module

public import Oberwolfach.FixedClassBoundedFactors
public import Oberwolfach.FixedClassMarkedCycles
public import Oberwolfach.ForbiddenGraphPairs

@[expose] public section

/-! Construct the two marked factors from the original fixed-class weights
and absorber counts. Auxiliary pair disjointness is converted to physical
edge disjointness using the original typed representation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 512
set_option maxHeartbeats 14000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {Tpl:Type} [Fintype Tpl] [DecidableEq Tpl]

 theorem marked_bounded_two_factors (m:ℕ) (hm:2≤m)
    (S:Tpl→VertexAbsorberTemplate (m+1)) (α b₀ B₀:ℝ) (hα:0<α) (hb₀:0<b₀) (hB₀:0<B₀):
    ∃ η:ℝ,0<η ∧ ∀ q:ℕ,∃ t:ℕ,1≤t ∧ ∀ F₀ D:ℝ,0≤F₀→0≤D→
      ∃ k₀:ℝ,1<k₀ ∧ ∀ k:ℝ,k₀≤k→
      ∀ (V E K:Type) [Fintype V] [DecidableEq V],
      ∀ (tail head:E→V) (ktail khead:K→V) (π:Equiv.Perm V) (b:ℕ)
        (F:SimpleGraph V) (A B:Finset V),Disjoint A B→(A.card:ℝ)=k→(B.card:ℝ)=m*k→
      Function.Injective (markedPhysicalEdge tail head ktail khead π)→(∀ v,(F.degree v:ℝ)≤D)→
      ∀ w:ClassMarkedCycle tail head ktail khead m π b A B→ℝ,
      (∀ C,b₀/k^m≤w C ∧ w C≤B₀/k^m)→
      (∀ v∈A∪B,|1-hypergraphWeightedDegree classMarkedCycleVertices w v|≤η)→
      (∀ X:Finset V,X⊆A∪B→(X∩A).card=1→(X∩B).card=m→α*k^((m+1)*(m+1))≤
        Fintype.card (LabelledAbsorberFamily (classMarkedCycleVertices (tail:=tail) (head:=head)
          (ktail:=ktail) (khead:=khead) (m:=m) (π:=π) (b:=b) (A:=A) (B:=B)) S X))→
      ∀ (I Z:Finset V) (z:ℕ),(I.card:ℝ)≤F₀→Z⊆A∪B→(Z∩A).card=z→(Z∩B).card=m*z→z≤q→
      ∃ Y:Finset V,∃ M₀ M₁:Finset (ClassMarkedCycle tail head ktail khead m π b A B),
        Y⊆A∪B ∧ Disjoint Y (Z∪I) ∧ (Y∩A).card=t ∧ (Y∩B).card=m*t ∧
        (∀ x∈Y,∀ y∈Y,¬F.Adj x y) ∧
        ((∀ C∈M₀,∀ C'∈M₀,C≠C'→Disjoint (classMarkedCycleVertices C) (classMarkedCycleVertices C'))∧
          M₀.biUnion classMarkedCycleVertices=Y) ∧
        ((∀ C∈M₁,∀ C'∈M₁,C≠C'→Disjoint (classMarkedCycleVertices C) (classMarkedCycleVertices C'))∧
          M₁.biUnion classMarkedCycleVertices=Y∪Z) ∧
        Disjoint (M₀.biUnion (fun C=>markedCyclePhysicalEdges tail head ktail khead m π b (classMarkedCycleAsMarked C)))
          (M₁.biUnion (fun C=>markedCyclePhysicalEdges tail head ktail khead m π b (classMarkedCycleAsMarked C))) ∧
        ∀ C∈M₁,(classMarkedCycleVertices C∩Z).card≤1:=by
  let a:Fin 2→ℕ:=![1,m]
  have ha:∀ i,1≤a i:=by intro i;fin_cases i <;> simp [a] <;> omega
  have has:∑ i,a i=m+1:=by simp [a,Fin.sum_univ_two];omega
  have hJ:1≤(m+1)^(m+1):=by have hh:=pow_pos (by omega : 0<m+1) (m+1);omega
  obtain ⟨η,hη,hbase⟩:=fixed_class_bounded_factors 2 (by omega) a (m+1) ((m+1)^(m+1))
    (by omega) hJ ha has S α b₀ B₀ hα hb₀ hB₀
  refine ⟨η,hη,?_⟩
  intro q
  obtain ⟨t,ht,hbase⟩:=hbase q
  refine ⟨t,ht,?_⟩
  intro F₀ D hF₀ hD
  obtain ⟨k₀,hk₀,hbase⟩:=hbase F₀ ((m+1)*D) hF₀ (by positivity)
  refine ⟨k₀,hk₀,?_⟩
  intro k hk V E K _ _ tail head ktail khead π b F A B hAB hAc hBc hp hF w hw herr habs I Z z hI hZT hZA hZB hz
  let T:Fin 2→Finset V:=![A,B]
  have hT:Finset.univ.biUnion T=A∪B:=by simp [T,Fin.univ_succ]
  have hTd:∀ i j,i≠j→Disjoint (T i) (T j):=by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact False.elim (hij rfl)
    · exact hAB
    · exact hAB.symm
    · exact False.elim (hij rfl)
  have hTc:∀ i,((T i).card:ℝ)=a i*k:=by intro i;fin_cases i <;> simp [T,a,hAc,hBc]
  have hRp:∀ C:ClassMarkedCycle tail head ktail khead m π b A B,∀ i,(classMarkedCycleVertices C∩T i).card=a i:=by
    intro C i
    have hh:=classMarkedCycle_profile hAB C
    fin_cases i <;> simp only [T,a,Matrix.cons_val_zero,Matrix.cons_val_one] <;> tauto
  have hEc:((forbiddenGraphPairs F (A∪B)).card:ℝ)≤((m+1)*D)*k:=by
    apply (forbiddenGraphPairs_card F (A∪B) D hF).trans
    rw [Finset.card_union_of_disjoint hAB,Nat.cast_add,hAc,hBc]
    ring_nf
    exact le_rfl
  obtain ⟨Y,M₀,M₁,hYT,hYI,hYc,hYE,h₀,h₁,hdis,hcap⟩:=hbase k hk V
    (ClassMarkedCycle tail head ktail khead m π b A B) T classMarkedCycleVertices w hTd hTc
    (fun C=>by rw [hT];exact classMarkedCycle_supported C) hRp (classMarkedCycle_multiplicity A B)
    (by simpa only [Nat.add_sub_cancel] using hw) (by simpa only [hT] using herr)
    (by
      intro X hX hc
      exact habs X (by simpa only [hT] using hX)
        (by simpa only [T,a,Matrix.cons_val_zero] using hc 0)
        (by simpa only [T,a,Matrix.cons_val_one,Matrix.cons_val_zero] using hc 1))
    I Z z hI (by simpa only [hT] using hZT)
    (by intro i;fin_cases i <;> simp [T,a,hZA,hZB]) hz
    (forbiddenGraphPairs F (A∪B)) (forbiddenGraphPairs_distinct F (A∪B)) hEc classMarkedCyclePairs
    (classMarkedCycle_pairs_supported (by omega)) classMarkedCycle_pairs_card classMarkedCycle_pairs_degree
  have hYAB:Y⊆A∪B:=by simpa only [hT] using hYT
  exact ⟨Y,M₀,M₁,hYAB,hYI,
    by simpa only [T,a,Matrix.cons_val_zero,one_mul] using hYc 0,
    by simpa only [T,a,Matrix.cons_val_one,Matrix.cons_val_zero] using hYc 1,
    forbiddenGraphPairs_avoidance F (A∪B) Y hYAB hYE,h₀,h₁,
    classMarkedCycle_factor_physical_disjoint hp M₀ M₁ hdis,hcap⟩

end Oberwolfach
