module

public import Oberwolfach.SparseTypedCorrectionMatrices
public import Oberwolfach.TypedMatrixRemainders

@[expose] public section

/-! Sparse fixed-type correction with the original graph and the allowed
subgraphs distinguished. All four remaining degree equations are exact. -/
set_option autoImplicit false
set_option maxHeartbeats 1400000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem sparse_typed_balanced_remainder (q : ℕ) (hq : 1≤q) (ω h δ ξ : ℝ)
    (hω : 0<ω) (hδ : 0<δ) (hδsmall : δ<1/4) (hξ : 0<ξ)
    (hξh : ((q:ℝ)+1)*ξ≤h/100) :
    ∃ η₀ : ℝ,0<η₀ ∧ ∃ n₀ : ℕ,∀ η : ℝ,0≤η → η≤η₀ →
    ∀ (V U : Type) [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U],
      n₀≤Fintype.card V → ω*Fintype.card V≤Fintype.card U → Fintype.card U≤Fintype.card V →
    ∀ (R₀ Rₖ A₀ Aₖ : V → V → ℕ) (H₀ Hₖ T₀ Tₖ : V → U → ℕ),
      (∀ x y,A₀ x y≤R₀ x y) → (∀ x y,Aₖ x y≤Rₖ x y) →
      (∀ v u,T₀ v u≤H₀ v u) → (∀ v u,Tₖ v u≤Hₖ v u) →
      (∀ v,|(∑ x,(R₀ v x : ℝ))+(∑ x,(Rₖ v x : ℝ))-
        (∑ u,(H₀ v u : ℝ))-(∑ u,(Hₖ v u : ℝ))|≤η*Fintype.card V) →
      (∀ v,|(∑ x,(R₀ x v : ℝ))+(∑ x,(Rₖ x v : ℝ))-
        (∑ u,(H₀ v u : ℝ))-(∑ u,(Hₖ v u : ℝ))|≤η*Fintype.card V) →
      (∀ v,|(∑ x,(Rₖ x v : ℝ))-(∑ u,(Hₖ v u : ℝ))|≤η*Fintype.card V) →
      (∀ u,|(∑ v,(H₀ v u : ℝ))-(q:ℝ)*(∑ v,(Hₖ v u : ℝ))|≤η*Fintype.card V) →
      BipartiteLargeCut A₀ δ h → BipartiteLargeCut Aₖ δ h →
      BipartiteLargeCut T₀ δ h → BipartiteLargeCut Tₖ δ h →
    ∃ (J₀ Jₖ : V → V → ℕ) (L₀ Lₖ : V → U → ℕ),
      (∀ x y,J₀ x y≤A₀ x y) ∧ (∀ x y,Jₖ x y≤Aₖ x y) ∧
      (∀ v u,L₀ v u≤T₀ v u) ∧ (∀ v u,Lₖ v u≤Tₖ v u) ∧
      TypedMatrixBalanced q (fun x y=>R₀ x y-J₀ x y) (fun x y=>Rₖ x y-Jₖ x y)
        (fun v u=>H₀ v u-L₀ v u) (fun v u=>Hₖ v u-Lₖ v u) ∧
      (∀ v,(∑ x,(J₀ v x : ℝ))≤2*((q:ℝ)+1)*ξ*Fintype.card V ∧
        (∑ x,(J₀ x v : ℝ))≤2*((q:ℝ)+1)*ξ*Fintype.card V ∧
        (∑ x,(Jₖ v x : ℝ))≤2*((q:ℝ)+1)*ξ*Fintype.card V ∧
        (∑ x,(Jₖ x v : ℝ))≤2*((q:ℝ)+1)*ξ*Fintype.card V ∧
        (∑ u,(L₀ v u : ℝ))≤2*((q:ℝ)+1)*ξ*Fintype.card V ∧
        (∑ u,(Lₖ v u : ℝ))≤2*((q:ℝ)+1)*ξ*Fintype.card V) ∧
      (∀ u,(∑ v,(L₀ v u : ℝ))≤2*((q:ℝ)+1)*ξ*Fintype.card V ∧
        (∑ v,(Lₖ v u : ℝ))≤2*((q:ℝ)+1)*ξ*Fintype.card V) := by
  obtain ⟨η₀,hη₀,N,hN⟩ := sparse_typed_correction_matrices q hq ω h δ ξ hω hδ hδsmall hξ hξh
  refine ⟨η₀,hη₀,N,?_⟩
  intro η hη hηsmall V U _ _ _ _ hn hωn hsn R₀ Rₖ A₀ Aₖ H₀ Hₖ T₀ Tₖ hA0 hAK hT0 hTK
    hbp hbm hbk hbw hcut0 hcutK hcutH0 hcutHK
  let bp (v : V) : ℤ := (∑ x,(R₀ v x : ℤ))+(∑ x,(Rₖ v x : ℤ))-
    (∑ u,(H₀ v u : ℤ))-(∑ u,(Hₖ v u : ℤ))
  let bm (v : V) : ℤ := (∑ x,(R₀ x v : ℤ))+(∑ x,(Rₖ x v : ℤ))-
    (∑ u,(H₀ v u : ℤ))-(∑ u,(Hₖ v u : ℤ))
  let bk (v : V) : ℤ := (∑ x,(Rₖ x v : ℤ))-(∑ u,(Hₖ v u : ℤ))
  let bw (u : U) : ℤ := (∑ v,(H₀ v u : ℤ))-(q:ℤ)*(∑ v,(Hₖ v u : ℤ))
  have hbp' : ∀ v,|(bp v : ℝ)|≤η*Fintype.card V := by
    intro v;simpa only [bp,Int.cast_sub,Int.cast_add,Int.cast_sum,Int.cast_natCast] using hbp v
  have hbm' : ∀ v,|(bm v : ℝ)|≤η*Fintype.card V := by
    intro v;simpa only [bm,Int.cast_sub,Int.cast_add,Int.cast_sum,Int.cast_natCast] using hbm v
  have hbk' : ∀ v,|(bk v : ℝ)|≤η*Fintype.card V := by
    intro v;simpa only [bk,Int.cast_sub,Int.cast_sum,Int.cast_natCast] using hbk v
  have hbw' : ∀ u,|(bw u : ℝ)|≤η*Fintype.card V := by
    intro u;simpa only [bw,Int.cast_sub,Int.cast_mul,Int.cast_sum,Int.cast_natCast] using hbw u
  obtain ⟨J₀,Jₖ,L₀,Lₖ,hJ0,hJK,hL0,hLK,hp,hm,hk,hw,hvb,hub⟩ := hN η hη hηsmall
    V U hn hωn hsn A₀ Aₖ T₀ Tₖ bp bm bk bw
    (typed_matrix_imbalance_totals R₀ Rₖ H₀ Hₖ) hbp' hbm' hbk' hbw' hcut0 hcutK hcutH0 hcutHK
  refine ⟨J₀,Jₖ,L₀,Lₖ,hJ0,hJK,hL0,hLK,?_,hvb,hub⟩
  exact typed_matrix_remainder_balanced q R₀ Rₖ J₀ Jₖ H₀ Hₖ L₀ Lₖ
    (fun x y=>(hJ0 x y).trans (hA0 x y)) (fun x y=>(hJK x y).trans (hAK x y))
    (fun v u=>(hL0 v u).trans (hT0 v u)) (fun v u=>(hLK v u).trans (hTK v u)) hp hm hk hw

end Oberwolfach
