module

public import Oberwolfach.SparseTypedFiniteHostCorrection
public import Oberwolfach.MarkedFiniteMatrixDeletionBounds
public import Oberwolfach.FiniteFibreCardBound
public import Oberwolfach.MarkedFiniteResourceOperations

@[expose] public section

/-! The four correction matrices produce actual finite deletion sets, with
all incidence and cardinality bounds needed by prescribed-edge covering.
Only the corrected remainder is divisible; no divisibility of the deletion
itself is assumed or asserted. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 16000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem sparse_typed_edge_set_correction (q : ℕ) (hq : 1≤q) (ω h δ ξ : ℝ)
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
    let S:=Finset.univ.filter (fun z:V×U=>H₀ z.1 z.2∨Hₖ z.1 z.2)
    ∃ (DA:Finset (E⊕K)) (DS:Finset (V×U)), DS⊆S ∧
      (∀ v,((DA.filter (fun a=>v=Sum.elim tail ktail a∨v=Sum.elim head khead a)).card:ℝ)≤
        8*((q:ℝ)+1)*ξ*Fintype.card V) ∧
      (∀ v,((DS.filter (fun z=>v=z.1)).card:ℝ)≤4*((q:ℝ)+1)*ξ*Fintype.card V) ∧
      (∀ u,((DS.filter (fun z=>z.2=u)).card:ℝ)≤4*((q:ℝ)+1)*ξ*Fintype.card V) ∧
      (DA.card:ℝ)≤8*((q:ℝ)+1)*ξ*(Fintype.card V:ℝ)^2 ∧
      (DS.card:ℝ)≤4*((q:ℝ)+1)*ξ*(Fintype.card V:ℝ)^2 ∧
      MarkedRemainderDivisible tail head ktail khead Hₖ (Finset.univ\DA) (S\DS) q ∧
      ∀ (π:Equiv.Perm V) (T:Finset V) (W:Finset U),(∀ v,π v∈T↔v∈T)→
      (∀ v∈T,∀ w∈T,A₀ v w=0)→(∀ v∈T,∀ w∈T,Aₖ v w=0)→
      (∀ v∈T,∀ u∈W,T₀ v u=0)→(∀ v∈T,∀ u∈W,Tₖ v u=0)→
      (markedFiniteResources tail head ktail khead π DA DS).filter (markedInnerResource T W)=∅ :=by
  obtain ⟨η₀,hη₀,N,hN⟩:=sparse_typed_finite_host_correction q hq ω h δ ξ hω hδ hδsmall hξ hξh
  refine ⟨η₀,hη₀,N,?_⟩
  intro η hη hηsmall V U E K _ _ _ _ _ _ hn hωn hun tail head ktail khead hinj hkinj
    H₀ Hₖ hH A₀ Aₖ T₀ Tₖ hA0 hAK hT0 hTK hbp hbm hbk hbw hcut0 hcutK hcutH0 hcutHK S
  obtain ⟨J₀,Jₖ,L₀,Lₖ,hJ0,hJK,hL0,hLK,hbalance,hV,hU,hdiv,havoid⟩:=hN η hη hηsmall
    V U E K hn hωn hun tail head ktail khead hinj hkinj H₀ Hₖ hH A₀ Aₖ T₀ Tₖ
    hA0 hAK hT0 hTK hbp hbm hbk hbw hcut0 hcutK hcutH0 hcutHK
  let DA:=Finset.univ.filter (Sum.elim (fun e=>J₀ (tail e) (head e)≠0) (fun e=>Jₖ (ktail e) (khead e)≠0))
  let DS:=Finset.univ.filter (fun z:V×U=>(H₀ z.1 z.2∧L₀ z.1 z.2≠0)∨(Hₖ z.1 z.2∧Lₖ z.1 z.2≠0))
  have hDA (v:V):((DA.filter (fun a=>v=Sum.elim tail ktail a∨v=Sum.elim head khead a)).card:ℝ)≤
      8*((q:ℝ)+1)*ξ*Fintype.card V:=by
    have hh:=marked_matrix_deleted_arc_incidence tail head ktail khead hinj hkinj J₀ Jₖ
      (fun x y=>(hJ0 x y).trans (hA0 x y)) (fun x y=>(hJK x y).trans (hAK x y)) v
    have hh':((DA.filter (fun a=>v=Sum.elim tail ktail a∨v=Sum.elim head khead a)).card:ℝ)≤
        (∑ x,(J₀ v x:ℝ))+(∑ x,(J₀ x v:ℝ))+(∑ x,(Jₖ v x:ℝ))+(∑ x,(Jₖ x v:ℝ)):=by
      convert hh using 1 <;> congr!
    linarith only [hh',(hV v).1,(hV v).2.1,(hV v).2.2.1,(hV v).2.2.2.1]
  have hs:=marked_matrix_deleted_spoke_degrees H₀ Hₖ L₀ Lₖ
  have hrow (v:V):((DS.filter (fun z=>v=z.1)).card:ℝ)≤4*((q:ℝ)+1)*ξ*Fintype.card V:=by
    have hh:((DS.filter (fun z=>v=z.1)).card:ℝ)≤(∑ u,(L₀ v u:ℝ))+(∑ u,(Lₖ v u:ℝ)):=by
      convert hs.1 v using 1 <;> congr!
    linarith only [hh,(hV v).2.2.2.2.1,(hV v).2.2.2.2.2]
  have hcol (u:U):((DS.filter (fun z=>z.2=u)).card:ℝ)≤4*((q:ℝ)+1)*ξ*Fintype.card V:=by
    have hh:((DS.filter (fun z=>z.2=u)).card:ℝ)≤(∑ v,(L₀ v u:ℝ))+(∑ v,(Lₖ v u:ℝ)):=by
      convert hs.2 u using 1 <;> congr!
    linarith only [hh,(hU u).1,(hU u).2]
  refine ⟨DA,DS,?_,hDA,hrow,hcol,?_,?_,?_,?_⟩
  · intro z hz
    rcases (Finset.mem_filter.mp hz).2 with hz|hz
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,Or.inl hz.1⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,Or.inr hz.1⟩
  · have hh:=finite_arc_card_le_uniform_incidence DA (Sum.elim tail ktail) (Sum.elim head khead)
      (8*((q:ℝ)+1)*ξ*Fintype.card V) hDA
    nlinarith only [hh]
  · have hh:=finite_card_le_uniform_fibre DS Prod.fst (4*((q:ℝ)+1)*ξ*Fintype.card V)
      (fun v=>by simpa only [eq_comm] using hrow v)
    nlinarith only [hh]
  · have ha:Finset.univ\DA=Finset.univ.filter
        (Sum.elim (fun e=>J₀ (tail e) (head e)=0) (fun e=>Jₖ (ktail e) (khead e)=0)):=by
      ext a;cases a <;> simp [DA]
    have hb:S\DS=Finset.univ.filter (fun z:V×U=>
        (H₀ z.1 z.2∧L₀ z.1 z.2=0)∨(Hₖ z.1 z.2∧Lₖ z.1 z.2=0)):=by
      ext z
      have hh:=hH z.1 z.2
      simp only [S,DS,Finset.mem_sdiff,Finset.mem_filter,Finset.mem_univ,true_and]
      tauto
    rw [ha,hb]
    exact hdiv
  · intro π T W hT hz0 hzK ht0 htK
    exact havoid π T W hT hz0 hzK ht0 htK

end Oberwolfach
