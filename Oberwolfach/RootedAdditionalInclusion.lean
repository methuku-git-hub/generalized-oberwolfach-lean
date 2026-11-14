module

public import Oberwolfach.RootedSubsets
public import Oberwolfach.RelationIncidentWeights
public import Oberwolfach.FractionalCycleIncidence

@[expose] public section

/-! Joint inclusion probabilities for additional vertices after fixing the
original roots. The free vertices retain the fixed-size, without-replacement law. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem rootedSubset_additional_inclusion {V : Type*} [Fintype V] [DecidableEq V]
    (T R : Finset V) (k : ℕ) (hk : T.card+k≤Fintype.card V)
    [Nonempty (RootedSubset V T k)] :
    (FiniteLaw.uniform (RootedSubset V T k)).probability (fun S=>R⊆S.val.val)≤
      ((k:ℝ)/(Fintype.card V-T.card:ℕ))^(R\T).card := by
  have hn : Fintype.card {x : V // x∉T}=Fintype.card V-T.card := by
    rw [Fintype.card_subtype_compl]
    simp
  have hkn : k≤Fintype.card {x : V // x∉T} := by rw [hn];omega
  letI : Nonempty (FixedSubset {x : V // x∉T} k) := fixedSubset_nonempty hkn
  let A := R.subtype (fun x=>x∉T)
  have hA : A.card=(R\T).card := by
    rw [Finset.card_subtype]
    congr 1
    ext x;simp
  have he (S : RootedSubset V T k) :
      (A⊆(rootedSubsetFree T S).val) ↔ R⊆S.val.val := by
    constructor
    · intro h x hx
      by_cases ht : x∈T
      · exact S.property ht
      · have hh := h (by simpa only [A,Finset.mem_subtype] using hx : (⟨x,ht⟩:{x : V // x∉T})∈A)
        simpa only [rootedSubsetFree,Finset.mem_subtype] using hh
    · intro h x hx
      have hh : x.val∈R := by simpa only [A,Finset.mem_subtype] using hx
      simpa only [rootedSubsetFree,Finset.mem_subtype] using h hh
  have hh := fixedSubset_joint_inclusion_le hkn A
  rw [← rootedSubset_uniform_free T k,finiteLaw_map_probability] at hh
  simpa only [he,hA,hn] using hh


theorem rootedSubset_conflict_probability {V : Type*} [Fintype V] [DecidableEq V]
    (F : SimpleGraph V) (T : Finset V) (k : ℕ) (hk : T.card+k≤Fintype.card V)
    [Nonempty (RootedSubset V T k)] (L : ℝ)
    (hdeg : ∀ v,(F.degree v:ℝ)≤L)
    (hT : ∀ x∈T,∀ y∈T,¬F.Adj x y) :
    let q : ℝ := (k:ℝ)/(Fintype.card V-T.card:ℕ)
    (FiniteLaw.uniform (RootedSubset V T k)).probability
      (fun S=>∃ x∈S.val.val,∃ y∈S.val.val,F.Adj x y)≤
      L*(2*(T.card:ℝ)*q+Fintype.card V*q^2) := by
  intro q
  let μ := FiniteLaw.uniform (RootedSubset V T k)
  have hq : 0≤q := by dsimp [q];positivity
  have hpair (x y : V) (hxy : F.Adj x y) :
      μ.probability (fun S=>x∈S.val.val ∧ y∈S.val.val)≤
        if x∈T ∨ y∈T then q else q^2 := by
    have hh := rootedSubset_additional_inclusion T {x,y} k hk
    have hne : x≠y := hxy.ne
    have hnot : ¬(x∈T ∧ y∈T) := fun h=>hT x h.1 y h.2 hxy
    simp only [Finset.insert_subset_iff,Finset.singleton_subset_iff] at hh
    by_cases hx : x∈T <;> by_cases hy : y∈T
    · exact False.elim (hnot ⟨hx,hy⟩)
    · have hset : ({x,y}:Finset V)\T={y} := by
        ext z
        simp only [Finset.mem_sdiff,Finset.mem_insert,Finset.mem_singleton]
        aesop
      rw [hset] at hh
      simpa only [μ,q,Finset.card_singleton,pow_one,hx,true_or,ite_true] using hh
    · have hset : ({x,y}:Finset V)\T={x} := by
        ext z
        simp only [Finset.mem_sdiff,Finset.mem_insert,Finset.mem_singleton]
        aesop
      rw [hset] at hh
      simpa only [μ,q,Finset.card_singleton,pow_one,hy,or_true,ite_true] using hh
    · have hset : ({x,y}:Finset V)\T={x,y} := by
        ext z
        simp only [Finset.mem_sdiff,Finset.mem_insert,Finset.mem_singleton]
        aesop
      rw [hset] at hh
      have hcard : ({x,y}:Finset V).card=2 := by simp [hne]
      simpa only [μ,q,hcard,hx,hy,false_or,ite_false] using hh
  have hterm (a : V×V) :
      μ.probability (fun S=>a.1∈S.val.val ∧ a.2∈S.val.val ∧ F.Adj a.1 a.2)≤
        if F.Adj a.1 a.2 then (if a.1∈T ∨ a.2∈T then q else q^2) else 0 := by
    by_cases h : F.Adj a.1 a.2
    · simpa only [h,and_true,ite_true] using hpair a.1 a.2 h
    · simp only [h,and_false,FiniteLaw.probability,ite_false,Finset.sum_const_zero,le_refl]
  have hbad := finiteLaw_union_bound μ (Finset.univ : Finset (V×V))
    (fun a S=>a.1∈S.val.val ∧ a.2∈S.val.val ∧ F.Adj a.1 a.2)
  have hmono : μ.probability (fun S=>∃ x∈S.val.val,∃ y∈S.val.val,F.Adj x y)≤
      μ.probability (fun S=>∃ a∈(Finset.univ : Finset (V×V)),a.1∈S.val.val ∧ a.2∈S.val.val ∧ F.Adj a.1 a.2) := by
    apply finiteLaw_probability_mono
    rintro S ⟨x,hx,y,hy,hxy⟩
    exact ⟨(x,y),Finset.mem_univ _,hx,hy,hxy⟩
  have hout (x : V) : (∑ y,bipAdj F.Adj x y)≤L := by
    simpa only [bipAdj,graph_adjacency_row_sum] using hdeg x
  have hin (y : V) : (∑ x,bipAdj F.Adj x y)≤L := by
    have he : (∑ x,bipAdj F.Adj x y)=(∑ x,bipAdj F.Adj y x) := by
      apply Finset.sum_congr rfl
      intro x _
      simp only [bipAdj,F.adj_comm]
    rw [he]
    exact hout y
  calc
    _ ≤ ∑ a : V×V,μ.probability (fun S=>a.1∈S.val.val ∧ a.2∈S.val.val ∧ F.Adj a.1 a.2) := hmono.trans hbad
    _ ≤ ∑ a : V×V,if F.Adj a.1 a.2 then (if a.1∈T ∨ a.2∈T then q else q^2) else 0 := Finset.sum_le_sum (fun a _=>hterm a)
    _ ≤ _ := by
      rw [Fintype.sum_prod_type]
      convert relation_root_incident_cost F.Adj L hout hin T T q (q^2) hq (sq_nonneg q) using 1 <;> ring

end Oberwolfach
