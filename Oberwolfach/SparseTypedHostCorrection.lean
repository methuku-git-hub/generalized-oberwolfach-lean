module

public import Oberwolfach.SparseTypedBalancedRemainder
public import Oberwolfach.TypedMatrixRealization

@[expose] public section

/-! Sparse typed degree correction for an actual host. The selected matrices
are supported in the supplied allowed subgraphs, and their removal retains
the original occurrence types as subtypes. The order threshold is uniform in
the host and in the admitted near-balance error. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem sparse_typed_host_correction (q : ℕ) (hq : 1≤q) (ω h δ ξ : ℝ)
    (hω : 0<ω) (hδ : 0<δ) (hδsmall : δ<1/4) (hξ : 0<ξ)
    (hξh : ((q:ℝ)+1)*ξ≤h/100) :
    ∃ η₀ : ℝ,0<η₀ ∧ ∃ n₀ : ℕ,∀ η : ℝ,0≤η → η≤η₀ →
    ∀ (V U E K : Type) [Fintype V] [Fintype U] [Fintype E] [Fintype K]
      [DecidableEq V] [DecidableEq U],
      n₀≤Fintype.card V → ω*Fintype.card V≤Fintype.card U → Fintype.card U≤Fintype.card V →
    ∀ (tail head : E → V) (ktail khead : K → V),
      Function.Injective (fun e=>(tail e,head e)) → Function.Injective (fun e=>(ktail e,khead e)) →
    ∀ (H₀ Hₖ : V → U → Prop) (A₀ Aₖ : V → V → ℕ) (T₀ Tₖ : V → U → ℕ),
      (∀ x y,A₀ x y≤occurrenceMultiplicity tail head x y) →
      (∀ x y,Aₖ x y≤occurrenceMultiplicity ktail khead x y) →
      (∀ v u,T₀ v u≤relationMultiplicity H₀ v u) → (∀ v u,Tₖ v u≤relationMultiplicity Hₖ v u) →
      (∀ v,|occurrenceDegree (Sum.elim tail ktail) v-
        (∑ u,if H₀ v u then (1:ℝ) else 0)-(∑ u,if Hₖ v u then (1:ℝ) else 0)|≤η*Fintype.card V) →
      (∀ v,|occurrenceDegree (Sum.elim head khead) v-
        (∑ u,if H₀ v u then (1:ℝ) else 0)-(∑ u,if Hₖ v u then (1:ℝ) else 0)|≤η*Fintype.card V) →
      (∀ v,|occurrenceDegree khead v-(∑ u,if Hₖ v u then (1:ℝ) else 0)|≤η*Fintype.card V) →
      (∀ u,|(∑ v,if H₀ v u then (1:ℝ) else 0)-(q:ℝ)*(∑ v,if Hₖ v u then (1:ℝ) else 0)|≤η*Fintype.card V) →
      BipartiteLargeCut A₀ δ h → BipartiteLargeCut Aₖ δ h →
      BipartiteLargeCut T₀ δ h → BipartiteLargeCut Tₖ δ h →
    ∃ (J₀ Jₖ : V → V → ℕ) (L₀ Lₖ : V → U → ℕ),
      (∀ x y,J₀ x y≤A₀ x y) ∧ (∀ x y,Jₖ x y≤Aₖ x y) ∧
      (∀ v u,L₀ v u≤T₀ v u) ∧ (∀ v u,Lₖ v u≤Tₖ v u) ∧
      TypedMatrixBalanced q
        (occurrenceMultiplicity (fun e : {e // J₀ (tail e) (head e)=0}=>tail e.val) (fun e=>head e.val))
        (occurrenceMultiplicity (fun e : {e // Jₖ (ktail e) (khead e)=0}=>ktail e.val) (fun e=>khead e.val))
        (relationMultiplicity (fun v u=>H₀ v u ∧ L₀ v u=0))
        (relationMultiplicity (fun v u=>Hₖ v u ∧ Lₖ v u=0)) ∧
      (∀ v,(∑ x,(J₀ v x : ℝ))≤2*((q:ℝ)+1)*ξ*Fintype.card V ∧
        (∑ x,(J₀ x v : ℝ))≤2*((q:ℝ)+1)*ξ*Fintype.card V ∧
        (∑ x,(Jₖ v x : ℝ))≤2*((q:ℝ)+1)*ξ*Fintype.card V ∧
        (∑ x,(Jₖ x v : ℝ))≤2*((q:ℝ)+1)*ξ*Fintype.card V ∧
        (∑ u,(L₀ v u : ℝ))≤2*((q:ℝ)+1)*ξ*Fintype.card V ∧
        (∑ u,(Lₖ v u : ℝ))≤2*((q:ℝ)+1)*ξ*Fintype.card V) ∧
      (∀ u,(∑ v,(L₀ v u : ℝ))≤2*((q:ℝ)+1)*ξ*Fintype.card V ∧
        (∑ v,(Lₖ v u : ℝ))≤2*((q:ℝ)+1)*ξ*Fintype.card V) := by
  obtain ⟨η₀,hη₀,N,hN⟩ := sparse_typed_balanced_remainder q hq ω h δ ξ hω hδ hδsmall hξ hξh
  refine ⟨η₀,hη₀,N,?_⟩
  intro η hη hηsmall V U E K _ _ _ _ _ _ hn hωn hun tail head ktail khead hinj hkinj
    H₀ Hₖ A₀ Aₖ T₀ Tₖ hA0 hAK hT0 hTK hbp hbm hbk hbw hcut0 hcutK hcutH0 hcutHK
  obtain ⟨J₀,Jₖ,L₀,Lₖ,hJ0,hJK,hL0,hLK,hbalance,hV,hU⟩ := hN η hη hηsmall V U hn hωn hun
    (occurrenceMultiplicity tail head) (occurrenceMultiplicity ktail khead) A₀ Aₖ
    (relationMultiplicity H₀) (relationMultiplicity Hₖ) T₀ Tₖ hA0 hAK hT0 hTK
    (by intro v;simpa only [occurrenceMultiplicity_row,relationMultiplicity_cast,occurrenceDegree_sum] using hbp v)
    (by intro v;simpa only [occurrenceMultiplicity_col,relationMultiplicity_cast,occurrenceDegree_sum] using hbm v)
    (by intro v;simpa only [occurrenceMultiplicity_col,relationMultiplicity_cast] using hbk v)
    (by intro u;simpa only [relationMultiplicity_cast] using hbw u)
    hcut0 hcutK hcutH0 hcutHK
  refine ⟨J₀,Jₖ,L₀,Lₖ,hJ0,hJK,hL0,hLK,?_,hV,hU⟩
  exact typed_matrix_remainder_realized q tail head ktail khead hinj hkinj H₀ Hₖ J₀ Jₖ L₀ Lₖ
    (fun x y=>(hJ0 x y).trans (hA0 x y)) (fun x y=>(hJK x y).trans (hAK x y))
    (fun v u=>(hL0 v u).trans (hT0 v u)) (fun v u=>(hLK v u).trans (hTK v u)) hbalance

end Oberwolfach
