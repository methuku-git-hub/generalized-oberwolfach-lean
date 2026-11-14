module

public import Oberwolfach.TripartiteTriangleMatching
public import Oberwolfach.TriangleCyclesFromMatchings
public import Oberwolfach.MinimumDegreeThreePartition

@[expose] public section

/-! The minimum-degree-only triangle-factor input follows from a balanced
random partition and two applications of Hall's theorem. No near-regularity,
fractional cycle decomposition or absorber assumption is needed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 512
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem graphCellDegree_subtype_card {k : ℕ} {d : Fin k→ℕ} (G : SimpleGraph V)
    (P : FixedPartition V k d) (v : V) (i : Fin k) :
    (Finset.univ.filter (fun w : {w // P.val w=i}=>G.Adj v w.val)).card=
      graphCellDegree G (Equiv.refl V) P v i := by
  unfold graphCellDegree
  apply Finset.card_bij (fun w _=>w.val)
  · intro w hw
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hw).2,w.property⟩
  · intro w _ z _ h;exact Subtype.ext h
  · intro w hw
    have hh := (Finset.mem_filter.mp hw).2
    exact ⟨⟨w,hh.2⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hh.1⟩,rfl⟩

theorem triangle_factor_from_three_partition (G : SimpleGraph V) (m : ℕ)
    (P : FixedPartition V 3 (fun _=>m))
    (hdegree : ∀ v i,(3/4:ℝ)*m≤graphCellDegree G (Equiv.refl V) P v i) :
    HasResourceDecomposition (ordinaryCycleVertices G 3) Finset.univ := by
  let X : Fin 3→Type _ := fun i=>{v // P.val v=i}
  have hcard (i : Fin 3) : Fintype.card (X i)=m := P.property i
  have hrow (v : V) (i : Fin 3) : 3*m≤4*(Finset.univ.filter (fun w : X i=>G.Adj v w.val)).card := by
    have hh := hdegree v i
    have hc := graphCellDegree_subtype_card G P v i
    have hcR : ((Finset.univ.filter (fun w : X i=>G.Adj v w.val)).card:ℝ)=
        graphCellDegree G (Equiv.refl V) P v i := by exact_mod_cast hc
    have hq : (3:ℝ)*m≤4*((Finset.univ.filter (fun w : X i=>G.Adj v w.val)).card:ℝ) := by linarith only [hh,hcR]
    exact_mod_cast hq
  have hcol (v : V) (i : Fin 3) : 3*m≤4*(Finset.univ.filter (fun w : X i=>G.Adj w.val v)).card := by
    have he : Finset.univ.filter (fun w : X i=>G.Adj w.val v)=
        Finset.univ.filter (fun w : X i=>G.Adj v w.val) := by ext w;simp [SimpleGraph.adj_comm]
    rw [he];exact hrow v i
  obtain ⟨σ,τ,h⟩ := tripartite_triangle_bijections
    (fun x : X 0=>fun y : X 1=>G.Adj x.val y.val)
    (fun x : X 0=>fun z : X 2=>G.Adj x.val z.val)
    (fun y : X 1=>fun z : X 2=>G.Adj y.val z.val)
    ((hcard 0).trans (hcard 1).symm) ((hcard 0).trans (hcard 2).symm)
    (fun x=>by rw [hcard];exact hrow x.val 1)
    (fun y=>by rw [hcard];exact hcol y.val 0)
    (fun x=>by rw [hcard];exact hrow x.val 2)
    (fun z=>by rw [hcard];exact hcol z.val 0)
    (fun y=>by rw [hcard];exact hrow y.val 2)
    (fun z=>by rw [hcard];exact hcol z.val 1)
  exact triangle_factor_from_bijections G P.val σ τ h

theorem minimum_degree_triangle_factor (α : ℝ) (hα : 0<α) :
    ∃ N : ℕ,∀ (V : Type) [Fintype V] [DecidableEq V],N≤Fintype.card V → 3∣Fintype.card V →
      ∀ G : SimpleGraph V,(∀ v,(3/4+α)*Fintype.card V≤(G.degree v:ℝ)) →
      HasResourceDecomposition (ordinaryCycleVertices G 3) Finset.univ := by
  obtain ⟨N,hN⟩ := minimum_degree_three_partition α hα
  refine ⟨N,?_⟩
  intro V _ _ hn hdiv G hG
  obtain ⟨m,P,_,hP⟩ := hN V hn hdiv G hG
  exact triangle_factor_from_three_partition G m P hP

end Oberwolfach

namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem bounded_augmentation_triangle_factor (β : ℝ) (hβ : 0<β) (q : ℕ) :
    ∃ s₀ : ℕ,∀ s z : ℕ,s₀≤s → z≤q →
      ∀ (V : Type) [Fintype V] [DecidableEq V],Fintype.card V=s+z → 3∣Fintype.card V →
      ∀ G : SimpleGraph V,(∀ v,(3/4+β/4)*s-2≤(G.degree v:ℝ)) →
      HasResourceDecomposition (ordinaryCycleVertices G 3) Finset.univ := by
  obtain ⟨N,hN⟩ := minimum_degree_triangle_factor (β/8) (by positivity)
  obtain ⟨M,hM⟩ := exists_nat_gt ((8/β)*(2+(3/4+β/8)*q))
  refine ⟨max N M,?_⟩
  intro s z hs hz V _ _ hn hdiv G hG
  apply hN V (by rw [hn];exact (le_max_left N M).trans hs |>.trans (Nat.le_add_right s z)) hdiv G
  intro v
  have hMs : (M:ℝ)≤s := by exact_mod_cast (le_max_right N M).trans hs
  have hq : (z:ℝ)≤q := by exact_mod_cast hz
  have hbeta : (8/β)*(β/8)=1 := by field_simp
  have hm := mul_le_mul_of_nonneg_right (hM.le.trans hMs) (by positivity : (0:ℝ)≤β/8)
  have hq' := mul_le_mul_of_nonneg_left hq (by positivity : (0:ℝ)≤3/4+β/8)
  have hnn : (Fintype.card V:ℝ)=s+z := by exact_mod_cast hn
  rw [hnn]
  have he : ((8/β)*(2+(3/4+β/8)*q))*(β/8)=2+(3/4+β/8)*q := by field_simp
  rw [he] at hm
  nlinarith only [hm,hq',hG v]

end Oberwolfach
