module

public import Oberwolfach.MarkedIncidentResources
public import Oberwolfach.FiniteFibreCardBound

@[expose] public section

/-! The actual unused arc and spoke sets inherit their incidence bounds
from the auxiliary remainder. No bound on the size of the earlier packing
is used, and the marked head remains the auxiliary head in this calculation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U] [Fintype E] [Fintype K]
  [DecidableEq V] [DecidableEq U]
  {tail head:E→V} {ktail khead:K→V} {π:Equiv.Perm V} {H₀ HK:V→U→Prop}

theorem marked_incident_remainder_filter {m b:ℕ}
    (M:Finset (MarkedWheel tail head ktail khead m π b H₀ HK)) (physical:Bool) (x:V⊕U):
    markedIncidentEdges tail head ktail khead π H₀ HK physical x\M.biUnion markedActiveResources=
      (markedIncidentEdges tail head ktail khead π H₀ HK physical x).filter
        (fun e=>markedActivePhysical tail head ktail khead π H₀ HK e∉M.biUnion markedWheelPhysicalResources):=by
  ext e
  simp only [Finset.mem_sdiff,Finset.mem_filter,Finset.mem_biUnion,markedActiveResources,
    Finset.mem_univ,true_and]

theorem marked_unused_incidence_bounds (B:Finset (Finset V⊕(V×U)))
    (A:Finset (E⊕K)) (S:Finset (V×U)) (δ:ℝ) (keep:MarkedActiveEdge E K H₀ HK→Prop)
    (hA:∀ a∈A,Sum.inl (markedPhysicalEdge tail head ktail khead π a)∉B∧keep (Sum.inl a))
    (hS:∀ z∈S,∃ hz:H₀ z.1 z.2∨HK z.1 z.2,Sum.inr z∉B∧keep (Sum.inr ⟨z,hz⟩))
    (hleft:∀ x:V⊕U,(((markedIncidentEdges tail head ktail khead π H₀ HK false x).filter
      (fun e=>markedActivePhysical tail head ktail khead π H₀ HK e∉B∧keep e)).card:ℝ)≤δ):
    (∀ v,((A.filter (fun a=>v=Sum.elim tail ktail a∨v=Sum.elim head khead a)).card:ℝ)≤δ)∧
    (∀ v,((S.filter (fun z=>v=z.1)).card:ℝ)≤δ)∧
    (∀ u,((S.filter (fun z=>u=z.2)).card:ℝ)≤δ)∧
    (A.card:ℝ)≤δ*Fintype.card V∧(S.card:ℝ)≤δ*Fintype.card V∧
    Disjoint (A.image (fun a=>Sum.inl (markedPhysicalEdge tail head ktail khead π a))∪S.image Sum.inr) B:=by
  classical
  have ha (v:V):((A.filter (fun a=>v=Sum.elim tail ktail a∨v=Sum.elim head khead a)).card:ℝ)≤δ:=by
    apply le_trans _ (hleft (Sum.inl v))
    apply Nat.cast_le.mpr
    apply Finset.card_le_card_of_injOn (Sum.inl (β:={vu:V×U//H₀ vu.1 vu.2∨HK vu.1 vu.2}))
    · intro a ha
      obtain ⟨ha,hi⟩:=Finset.mem_filter.mp ha
      refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,hA a ha⟩
      cases a <;> simpa only [markedResourceIncident,Bool.false_eq_true,ite_false,Sum.elim_inl,Sum.elim_inr,eq_comm] using hi
    · intro a ha b hb hab;exact Sum.inl.inj hab
  let s:S→MarkedActiveEdge E K H₀ HK:=fun z=>Sum.inr ⟨z.val,Classical.choose (hS z.val z.property)⟩
  have hs (x:V⊕U):((S.filter (fun z=>match x with | Sum.inl v=>v=z.1 | Sum.inr u=>u=z.2)).card:ℝ)≤δ:=by
    apply le_trans _ (hleft x)
    apply Nat.cast_le.mpr
    let T:=S.filter (fun z=>match x with | Sum.inl v=>v=z.1 | Sum.inr u=>u=z.2)
    let f:T→MarkedActiveEdge E K H₀ HK:=fun z=>s ⟨z.val,(Finset.mem_filter.mp z.property).1⟩
    have hf:Function.Injective f:=by
      intro a b hab
      dsimp only [f,s] at hab
      apply Subtype.ext
      exact congrArg (fun z:{vu:V×U//H₀ vu.1 vu.2∨HK vu.1 vu.2}=>z.val) (Sum.inr.inj hab)
    have hsub:(Finset.univ.image f)⊆(markedIncidentEdges tail head ktail khead π H₀ HK false x).filter
        (fun e=>markedActivePhysical tail head ktail khead π H₀ HK e∉B∧keep e):=by
      intro e he
      obtain ⟨z,_,rfl⟩:=Finset.mem_image.mp he
      have hz:=Finset.mem_filter.mp z.property
      refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,Classical.choose_spec (hS z.val hz.1)⟩
      cases x <;> exact hz.2.symm
    have hc:=Finset.card_le_card hsub
    simpa only [Finset.card_image_of_injective _ hf,Finset.card_univ,Fintype.card_coe] using hc
  have hsrow (v:V):((S.filter (fun z=>v=z.1)).card:ℝ)≤δ:=by
    convert hs (Sum.inl v) using 1 <;> congr!
  have hscol (u:U):((S.filter (fun z=>u=z.2)).card:ℝ)≤δ:=by
    convert hs (Sum.inr u) using 1 <;> congr!
  refine ⟨ha,hsrow,hscol,finite_arc_card_le_uniform_incidence A _ _ δ ha,?_,?_⟩
  · apply finite_card_le_uniform_fibre S Prod.fst δ
    intro v
    simpa only [eq_comm] using hsrow v
  · apply Finset.disjoint_left.mpr
    intro e he hb
    rcases Finset.mem_union.mp he with he|he
    · obtain ⟨a,ha,rfl⟩:=Finset.mem_image.mp he;exact (hA a ha).1 hb
    · obtain ⟨z,hz,rfl⟩:=Finset.mem_image.mp he;exact (Classical.choose_spec (hS z hz)).1 hb
end Oberwolfach
