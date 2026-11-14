module

public import Oberwolfach.SparseTypedHostCorrection
public import Oberwolfach.MarkedMatrixCorrectionRemainder
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

theorem sparse_typed_finite_host_correction (q : ℕ) (hq : 1≤q) (ω h δ ξ : ℝ)
    (hω : 0<ω) (hδ : 0<δ) (hδsmall : δ<1/4) (hξ : 0<ξ)
    (hξh : ((q:ℝ)+1)*ξ≤h/100) :
    ∃ η₀ : ℝ,0<η₀ ∧ ∃ n₀ : ℕ,∀ η : ℝ,0≤η → η≤η₀ →
    ∀ (V U E K : Type) [Fintype V] [Fintype U] [Fintype E] [Fintype K]
      [DecidableEq V] [DecidableEq U],
      n₀≤Fintype.card V → ω*Fintype.card V≤Fintype.card U → Fintype.card U≤Fintype.card V →
    ∀ (tail head : E → V) (ktail khead : K → V),
      Function.Injective (fun e=>(tail e,head e)) → Function.Injective (fun e=>(ktail e,khead e)) →
    ∀ (H₀ Hₖ : V → U → Prop),(∀ v u,¬(H₀ v u∧Hₖ v u))→
    ∀ (A₀ Aₖ : V → V → ℕ) (T₀ Tₖ : V → U → ℕ),
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
        (∑ v,(Lₖ v u : ℝ))≤2*((q:ℝ)+1)*ξ*Fintype.card V) ∧
      MarkedRemainderDivisible tail head ktail khead Hₖ
        (Finset.univ.filter (Sum.elim (fun e=>J₀ (tail e) (head e)=0) (fun e=>Jₖ (ktail e) (khead e)=0)))
        (Finset.univ.filter (fun z:V×U=>(H₀ z.1 z.2∧L₀ z.1 z.2=0)∨(Hₖ z.1 z.2∧Lₖ z.1 z.2=0))) q ∧
      ∀ (π:Equiv.Perm V) (T:Finset V) (W:Finset U),(∀ v,π v∈T↔v∈T)→
      (∀ v∈T,∀ w∈T,A₀ v w=0)→(∀ v∈T,∀ w∈T,Aₖ v w=0)→
      (∀ v∈T,∀ u∈W,T₀ v u=0)→(∀ v∈T,∀ u∈W,Tₖ v u=0)→
      let A:=Finset.univ.filter (Sum.elim (fun e=>J₀ (tail e) (head e)≠0) (fun e=>Jₖ (ktail e) (khead e)≠0))
      let S:=Finset.univ.filter (fun z:V×U=>(H₀ z.1 z.2∧L₀ z.1 z.2≠0)∨(Hₖ z.1 z.2∧Lₖ z.1 z.2≠0))
      (A.image (fun a=>Sum.inl (markedPhysicalEdge tail head ktail khead π a))∪S.image Sum.inr).filter
        (markedInnerResource T W)=∅ :=by
  obtain ⟨η₀,hη₀,N,hN⟩:=sparse_typed_host_correction q hq ω h δ ξ hω hδ hδsmall hξ hξh
  refine ⟨η₀,hη₀,N,?_⟩
  intro η hη hηsmall V U E K _ _ _ _ _ _ hn hωn hun tail head ktail khead hinj hkinj
    H₀ Hₖ hH A₀ Aₖ T₀ Tₖ hA0 hAK hT0 hTK hbp hbm hbk hbw hcut0 hcutK hcutH0 hcutHK
  obtain ⟨J₀,Jₖ,L₀,Lₖ,hJ0,hJK,hL0,hLK,hbalance,hV,hU⟩:=hN η hη hηsmall
    V U E K hn hωn hun tail head ktail khead hinj hkinj H₀ Hₖ A₀ Aₖ T₀ Tₖ
    hA0 hAK hT0 hTK hbp hbm hbk hbw hcut0 hcutK hcutH0 hcutHK
  refine ⟨J₀,Jₖ,L₀,Lₖ,hJ0,hJK,hL0,hLK,hbalance,hV,hU,
    marked_matrix_correction_finite_divisible tail head ktail khead H₀ Hₖ q hH J₀ Jₖ L₀ Lₖ hbalance,?_⟩
  intro π T W hT hz0 hzk ht0 htk
  apply marked_matrix_deletion_avoids_protected_pair tail head ktail khead π H₀ Hₖ J₀ Jₖ L₀ Lₖ T W hT
  · intro v hv w hw;exact Nat.eq_zero_of_le_zero (by simpa only [hz0 v hv w hw] using hJ0 v w)
  · intro v hv w hw;exact Nat.eq_zero_of_le_zero (by simpa only [hzk v hv w hw] using hJK v w)
  · intro v hv u hu;exact Nat.eq_zero_of_le_zero (by simpa only [ht0 v hv u hu] using hL0 v u)
  · intro v hv u hu;exact Nat.eq_zero_of_le_zero (by simpa only [htk v hv u hu] using hLK v u)

end Oberwolfach
