module

public import Oberwolfach.OrdinaryCycleCountBounds
public import Oberwolfach.PrescribedVertexCounts

@[expose] public section

/-! Counting physical cycles containing fixed distinct vertices. Embeddings
are used only to bound the number of subgraphs, not to weight representations. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem prescribed_root_positions_count {I V : Type*} [Fintype I] [Fintype V]
    [DecidableEq I] [DecidableEq V] (i₀ : I) (S : Finset V) (q : S → I) :
    (∑ f : I → V,if (∀ s : S,f (q s)=s.val) then (1:ℝ) else 0)≤
      (Fintype.card V:ℝ)^(Fintype.card I-S.card) := by
  let cl (v : V) := if hv : v∈S then q ⟨v,hv⟩ else i₀
  have hp (f : I → V) : (∀ s : S,f (q s)=s.val) ↔ ∀ v∈S,f (cl v)=v := by
    constructor
    · intro h v hv
      simpa only [cl,dif_pos hv] using h ⟨v,hv⟩
    · intro h s
      simpa only [cl,dif_pos s.property] using h s.val s.property
  have hh := prescribedVertices_weight_le S cl id
    (by intro u v huv;exact congrArg Prod.snd huv) (fun _ => (1:ℝ)) 1 (by norm_num) (by intro _;rfl)
  simp only [mul_one] at hh
  convert hh using 1
  apply Finset.sum_congr rfl
  intro f _
  simp only [hp,id_eq]
  split_ifs <;> rfl

theorem functions_cover_roots_count {I V : Type*} [Fintype I] [Fintype V]
    [DecidableEq I] [DecidableEq V] (i₀ : I) (S : Finset V) :
    (∑ f : I → V,if (∀ v∈S,v∈Set.range f) then (1:ℝ) else 0)≤
      (Fintype.card I:ℝ)^S.card*(Fintype.card V:ℝ)^(Fintype.card I-S.card) := by
  have hp (f : I → V) : (if (∀ v∈S,v∈Set.range f) then (1:ℝ) else 0)≤
      ∑ q : S → I,if (∀ s : S,f (q s)=s.val) then (1:ℝ) else 0 := by
    by_cases hf : ∀ v∈S,v∈Set.range f
    · let q (s : S) := Classical.choose (hf s.val s.property)
      have hq : ∀ s : S,f (q s)=s.val := fun s => Classical.choose_spec (hf s.val s.property)
      rw [if_pos hf]
      have hh := Finset.single_le_sum (s:=Finset.univ)
        (f:=fun q : S → I => if (∀ s : S,f (q s)=s.val) then (1:ℝ) else 0)
        (fun _ _ => by split_ifs <;> norm_num) (Finset.mem_univ q)
      simpa only [if_pos hq] using hh
    · rw [if_neg hf]
      exact Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num)
  calc
    _ ≤ ∑ f : I → V,∑ q : S → I,if (∀ s : S,f (q s)=s.val) then (1:ℝ) else 0 :=
      Finset.sum_le_sum (fun f _ => hp f)
    _ = ∑ q : S → I,∑ f : I → V,if (∀ s : S,f (q s)=s.val) then (1:ℝ) else 0 := Finset.sum_comm
    _ ≤ ∑ _q : S → I,(Fintype.card V:ℝ)^(Fintype.card I-S.card) :=
      Finset.sum_le_sum (fun q _ => prescribed_root_positions_count i₀ S q)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fun,
      Fintype.card_coe,nsmul_eq_mul,Nat.cast_pow]

theorem ordinary_cycle_root_count {V : Type*} [Fintype V] [DecidableEq V]
    (r : ℕ) (hr : 0<r) (S : Finset V) :
    (∑ C : EmbeddedCycleFamily V r,if (↑S:Set V)⊆C.val.support then (1:ℝ) else 0)≤
      (r:ℝ)^S.card*(Fintype.card V:ℝ)^(r-S.card) := by
  let g (f : Fin r → V) := if (∀ v∈S,v∈Set.range f) then (1:ℝ) else 0
  have hg (f : Fin r → V) : 0≤g f := by dsimp [g];split_ifs <;> norm_num
  have hC (C : EmbeddedCycleFamily V r) :
      (if (↑S:Set V)⊆C.val.support then (1:ℝ) else 0)≤g (embeddedCycleEmbedding C) := by
    by_cases hS : (↑S:Set V)⊆C.val.support
    · have hf : ∀ v∈S,v∈Set.range (embeddedCycleEmbedding C : Fin r → V) := by
        intro v hv
        have hh := hS hv
        rw [embeddedCycleEmbedding_spec C,SimpleGraph.support_map] at hh
        obtain ⟨i,hi,hiv⟩ := hh
        exact ⟨i,hiv⟩
      rw [if_pos hS]
      dsimp only [g]
      split_ifs <;> norm_num
    · simp only [hS,ite_false]
      exact hg _
  calc
    _ ≤ ∑ C : EmbeddedCycleFamily V r,g (embeddedCycleEmbedding C) := Finset.sum_le_sum (fun C _ => hC C)
    _ ≤ ∑ f : Fin r → V,g f := finite_injective_sum_le _ embeddedCycleEmbedding_injective g hg
    _ ≤ _ := by
      simpa only [Fintype.card_fin] using functions_cover_roots_count (⟨0,hr⟩:Fin r) S

end Oberwolfach
