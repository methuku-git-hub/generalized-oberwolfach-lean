module

public import Oberwolfach.EndpointTriangleCounts

@[expose] public section

/-! The two free vertices replacing one row root or one index root in an
endpoint triangle. The row-root index choice is used only for a distinct,
nonconflicting pair; the two original row roots are never paired together. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

def endpointPathClass (S T : Finset V) (indexRoot : Bool) (n : ℕ) : Finset V :=
  if indexRoot || n≠0 then S else T

def endpointPathRequirements (x y : V) (n : ℕ) (f : Fin n→V) : Finset V :=
  {x,y}∪Finset.univ.image f

theorem endpoint_path_common (Q F : SimpleGraph V) (S T : Finset V)
    (b : ℝ) (hb : EndpointNeighbourCounts Q F S T b)
    (j : Bool) (x y : V) (hxy : x≠y) (hFxy : ¬F.Adj x y)
    (hx : x∈if j then T else S) (hy : y∈if j then T else S)
    (n : ℕ) (hn : n<2) (f : Fin n→V)
    (hf : ClassSparseGreedyGood Q F (endpointPathClass S T j) {x,y} (endpointPathRequirements x y) f) :
    b≤((common (endpointPathClass S T j n) (endpointPathRequirements x y n f)
      (fun v=>Q.neighborFinset v)).card:ℝ) := by
  have hpair : ({x,y}:Finset V).card=2 := Finset.card_pair hxy
  interval_cases n
  · cases j
    · simpa [endpointPathClass,endpointPathRequirements,common] using hb.pairs x hx y hy hxy hFxy
    · have hh := hb.rows ∅ {x,y} (by simp) (by simpa [Finset.insert_subset_iff,Finset.singleton_subset_iff] using And.intro hx hy) (by simp) hpair.le (by simp [hpair])
      simpa [endpointPathClass,endpointPathRequirements] using hh
  · have he : Finset.univ.image f={f 0} := by
      ext v;simp only [Finset.mem_image,Finset.mem_univ,true_and,Finset.mem_singleton]
      constructor
      · rintro ⟨i,rfl⟩;rw [Subsingleton.elim i 0]
      · rintro rfl;exact ⟨0,rfl⟩
    have hf0 := (hf.2.1 0).1
    cases j
    · have hh := hb.rows {x,y} {f 0} (by simpa [Finset.insert_subset_iff,Finset.singleton_subset_iff] using And.intro hx hy)
        (by simpa [endpointPathClass] using hf0) hpair.le (by simp) (by simp [hpair])
      simpa only [endpointPathClass,Bool.false_or,ne_eq,one_ne_zero,not_false_eq_true,decide_true,ite_true,
        endpointPathRequirements,he] using hh
    · have hh := hb.rows {f 0} {x,y} (by simpa [endpointPathClass] using hf0)
        (by simpa [Finset.insert_subset_iff,Finset.singleton_subset_iff] using And.intro hx hy) (by simp) hpair.le (by simp [hpair])
      simpa [endpointPathClass,endpointPathRequirements,he,Finset.union_comm] using hh

theorem endpoint_path_count (Q F : SimpleGraph V) (S T : Finset V)
    (L b a : ℝ) (hL : 0≤L) (ha : 0≤a) (hF : ∀ v,(F.degree v:ℝ)≤L)
    (hb : EndpointNeighbourCounts Q F S T b) (hbudget : a≤b-4*(L+1))
    (j : Bool) (x y : V) (hxy : x≠y) (hFxy : ¬F.Adj x y)
    (hx : x∈if j then T else S) (hy : y∈if j then T else S) :
    a^2≤Fintype.card {f : Fin 2→V //
      ClassSparseGreedyGood Q F (endpointPathClass S T j) {x,y} (endpointPathRequirements x y) f} := by
  apply class_sparse_greedy_sequence_count Q F _ {x,y} (endpointPathRequirements x y) 2 L b a hL ha hF
  · simpa only [Finset.card_pair hxy,Nat.cast_ofNat,show (2:ℝ)+2=4 by norm_num] using hbudget
  · exact endpoint_path_common Q F S T b hb j x y hxy hFxy hx hy

theorem endpoint_path_edges (Q F : SimpleGraph V) (S T : Finset V) (j : Bool) (x y : V)
    (f : Fin 2→V)
    (hf : ClassSparseGreedyGood Q F (endpointPathClass S T j) {x,y} (endpointPathRequirements x y) f) :
    (∀ z∈({x,y}:Finset V),∀ i,Q.Adj z (f i)) ∧ Q.Adj (f 0) (f 1) := by
  refine ⟨fun z hz i=>hf.2.2.2.2 i z (Finset.mem_union_left _ hz),?_⟩
  apply hf.2.2.2.2 1
  exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨⟨0,by decide⟩,Finset.mem_univ _,rfl⟩)

end Oberwolfach
