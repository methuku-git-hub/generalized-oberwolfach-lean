module

public import Oberwolfach.SparseForbiddenPaths

@[expose] public section

/-! Construct the common path of a rim-edge transformer pair. The
four-cycle case uses the stated three-neighbour intersection; longer
cycles use only two-neighbour intersections. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

theorem graph_independent_insert (F:SimpleGraph V) (Z:Finset V) (a:V)
    (hZ:∀ v∈Z,∀ w∈Z,¬F.Adj v w) (ha:∀ v∈Z,¬F.Adj a v):
    ∀ v∈insert a Z,∀ w∈insert a Z,¬F.Adj v w:=by
  intro v hv w hw
  rcases Finset.mem_insert.mp hv with he|hvZ <;> rcases Finset.mem_insert.mp hw with he'|hwZ
  · rw [he,he'];exact F.loopless.irrefl _
  · rw [he];exact ha w hwZ
  · rw [he'];exact fun h=>ha v hvZ h.symm
  · exact hZ v hvZ w hwZ

theorem transformer_rim_common_path (Q F:SimpleGraph V) (A W Ω Z:Finset V)
    (hAΩ:A⊆Ω) (x y x' y':V) (hroots:x∈Z∧y∈Z∧x'∈Z∧y'∈Z)
    (hΩ:x∈Ω∧y∈Ω∧x'∈Ω∧y'∈Ω)
    (hZ:∀ v∈Z,∀ w∈Z,¬F.Adj v w)
    (r:ℕ) (hr:4≤r) (L b:ℝ) (hL:0≤L) (hF:∀ v,(F.degree v:ℝ)≤L)
    (hcount:∀ v∈Ω,∀ w∈Ω,b≤((A∩Q.neighborFinset v∩Q.neighborFinset w).card:ℝ))
    (hthree:r=4→∀ a∈A,b≤(((A∩Q.neighborFinset a)∩Q.neighborFinset y∩Q.neighborFinset y').card:ℝ))
    (hbudget:W.card+((Z.card:ℝ)+r+2)*(L+1)<b):
    ∃ a b',∃ p:Q.Walk a b',
      p.IsPath ∧ p.length=r-3 ∧ Q.Adj x a ∧ Q.Adj x' a ∧ Q.Adj y b' ∧ Q.Adj y' b' ∧
      (∀ v∈p.support,v∈A∧v∉W∧v∉Z) ∧
      (∀ v∈p.support,∀ w∈p.support,¬F.Adj v w) ∧
      (∀ v∈p.support,∀ w∈Z,¬F.Adj v w):=by
  have hL1:0≤L+1:=by linarith
  obtain ⟨a,haA,haW,haZ,hxa,hx'a,hFa⟩:=sparse_common_neighbour_avoiding Q F A W Z x x' L b
    hL hF (hcount x hΩ.1 x' hΩ.2.2.1) (by nlinarith only [hbudget,hL1,(show (0:ℝ)≤r from Nat.cast_nonneg r)])
  let A₁:=if r=4 then A∩Q.neighborFinset a else A
  have hcount₁:b≤((A₁∩Q.neighborFinset y∩Q.neighborFinset y').card:ℝ):=by
    dsimp only [A₁]
    split_ifs with hr4
    · exact hthree hr4 a haA
    · exact hcount y hΩ.2.1 y' hΩ.2.2.2
  have hZ₁:((insert a Z).card:ℝ)≤Z.card+1:=by exact_mod_cast Finset.card_insert_le a Z
  obtain ⟨c,hcA₁,hcW,hcZ₁,hyc,hy'c,hFc⟩:=sparse_common_neighbour_avoiding Q F A₁ W (insert a Z) y y' L b
    hL hF hcount₁ (by
      have hh:=mul_le_mul_of_nonneg_right hZ₁ hL1
      nlinarith only [hh,hbudget,hL1,(show (0:ℝ)≤r from Nat.cast_nonneg r)])
  have hcA:c∈A:=by
    dsimp only [A₁] at hcA₁
    split_ifs at hcA₁ with hr4
    · exact (Finset.mem_inter.mp hcA₁).1
    · exact hcA₁
  have hca:c≠a:=fun h=>hcZ₁ (by simp [h])
  have hcZ:c∉Z:=fun h=>hcZ₁ (Finset.mem_insert_of_mem h)
  let Z₁:=insert c (insert a Z)
  have hind:∀ v∈Z₁,∀ w∈Z₁,¬F.Adj v w:=
    graph_independent_insert F (insert a Z) c (graph_independent_insert F Z a hZ hFa) hFc
  have hex:∃ p:Q.Walk a c,p.IsPath ∧ p.length=r-3 ∧
      (∀ v∈p.support,v=a∨v=c∨v∈A∧v∉W∧v∉Z₁) ∧
      (∀ v∈p.support,∀ w∈p.support,¬F.Adj v w) ∧
      (∀ v∈p.support,∀ w∈Z₁,¬F.Adj v w):=by
    by_cases hr4:r=4
    · have hac:Q.Adj a c:=by
        have hh:c∈A∩Q.neighborFinset a:=by simpa only [A₁,hr4,ite_true] using hcA₁
        exact (Q.mem_neighborFinset a c).mp (Finset.mem_inter.mp hh).2
      let p:Q.Walk a c:=SimpleGraph.Walk.cons hac SimpleGraph.Walk.nil
      have hm (v:V):v∈p.support↔v=a∨v=c:=by simp [p]
      refine ⟨p,?_,by simp [p,hr4],?_,?_,?_⟩
      · exact SimpleGraph.Walk.IsPath.cons (by simp) (by simpa using hca.symm)
      · intro v hv
        rcases (hm v).mp hv with h|h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      · intro v hv w hw
        apply hind v _ w _
        · rcases (hm v).mp hv with rfl|rfl <;> simp [Z₁]
        · rcases (hm w).mp hw with rfl|rfl <;> simp [Z₁]
      · intro v hv w hw
        apply hind v _ w hw
        rcases (hm v).mp hv with rfl|rfl <;> simp [Z₁]
    · have hZ₁card:(Z₁.card:ℝ)≤Z.card+2:=by
        have hh:Z₁.card≤Z.card+2:=(Finset.card_insert_le c (insert a Z)).trans (by have hh:=Finset.card_insert_le a Z;omega)
        exact_mod_cast hh
      exact sparse_fixed_length_forbidden_path_within Q F A W Z₁ Ω hAΩ a c (hAΩ haA) (hAΩ hcA)
        hca.symm (by simp [Z₁]) (by simp [Z₁]) hind (r-3) (by omega) L b hL hF hcount (by
          have hrc:((r-3:ℕ):ℝ)≤r:=by exact_mod_cast Nat.sub_le r 3
          have hh:=mul_le_mul_of_nonneg_right (show (Z₁.card:ℝ)+(r-3:ℕ)≤Z.card+r+2 by linarith) hL1
          linarith only [hh,hbudget])
  obtain ⟨p,hp,hlen,hclass,hindp,hrootp⟩:=hex
  refine ⟨a,c,p,hp,hlen,hxa,hx'a,hyc,hy'c,?_,hindp,?_⟩
  · intro v hv
    rcases hclass v hv with rfl|rfl|hv
    · exact ⟨haA,haW,haZ⟩
    · exact ⟨hcA,hcW,hcZ⟩
    · exact ⟨hv.1,hv.2.1,fun h=>hv.2.2 (by simp [Z₁,h])⟩
  · intro v hv w hw
    exact hrootp v hv w (by simp [Z₁,hw])

end Oberwolfach
