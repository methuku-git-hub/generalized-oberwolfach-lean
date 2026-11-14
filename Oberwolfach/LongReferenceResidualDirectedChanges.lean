module

public import Oberwolfach.LongReferenceResidualDirectedAgreement
public import Oberwolfach.LongReferenceResidualChangeGraph
public import Oberwolfach.LongReferenceTypedGraphExact
public import Oberwolfach.LongResidualTypedGraphExact

@[expose] public section
/-! Directed rim edits are charged to the same physical change graph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [LinearOrder V] [Nonempty V] [Fintype U] [DecidableEq U] [Fintype Γ] [Fintype Color]
local instance directedChangesDecEq : DecidableEq V := Classical.decEq V
local instance directedChangesArc (P:V×V→Prop):DecidableEq {e:V×V // P e}:=Classical.decEq _

theorem long_reference_residual_directed_changes
    (G S Del Small:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (ω:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)
    (M:V→V→ℕ) (τ:RawMarkedOutcome V U Γ Color)
    (hphysical:∀x y,M x y+M y x=if S.Adj x y then 1 else 0)
    (hcorrect:orientationDisagreementGraph (longPhysicalStateGraph G ω {0,1,2,3,4}) (fun e=>(ω (Sum.inl e)).2) M≤Del):
    let P:=longEligibleResidualArc M Small ⊥
    let T₁:=longDualInitialMarked G (fun e=>ω (Sum.inl e)) M Small (longOrdinaryArcEligible π d) (longMarkedArcEligible π d);
    ∀T:Finset {e:V×V // P e},
    (∀mark x y,markedPhysicalRim G π (3*d) (fun e=>τ (Sum.inl e)) mark x y=1 ↔
      if mark then ∃e:residualMarkedArc P T,e.val.val.1=x∧π.symm e.val.val.2=y
      else ∃e:residualOrdinaryArc P T,e.val.val.1=x∧e.val.val.2=y)→
    let Ref:=longSelectedPhysicalGraph G π d ω
    let Now:=S\Small
    let Retype:=physicalEdgeGraph (changedDirectedPhysicalEdges P T T₁)
    let FR:=longReferenceResidualChangeGraph Ref Now Del Retype
    let raw:RawMarkedOutcome V U Γ Color:=fun e=>rawExpandedMarkedCollapse e (ω e)
    ∀a,¬(rawMarkedPairRims G π d raw a↔rawMarkedPairRims G π d τ a)→markedPairPhysical π a∈FR.edgeFinset:=by
  intro P T₁ T hRims Ref Now Retype FR raw a hchange
  have core:∀mark x y,
      ¬(markedPhysicalRim G π (3*d) (fun e=>raw (Sum.inl e)) mark x (if mark then π.symm y else y)=1 ↔
        markedPhysicalRim G π (3*d) (fun e=>τ (Sum.inl e)) mark x (if mark then π.symm y else y)=1)→
      s(x,y)∈FR.edgeFinset:=by
    intro mark x y hne
    by_contra hnot
    have hFR:¬FR.Adj x y:=by
      intro h
      exact hnot (SimpleGraph.mem_edgeFinset.mpr h)
    have hd:¬Del.Adj x y:=fun h=>hFR (Or.inl (Or.inr h))
    have hc:¬Retype.Adj x y:=fun h=>hFR (Or.inr h)
    have hforward:Ref.Adj x y→Now.Adj x y:=by
      intro h
      by_contra hn
      exact hFR (Or.inl (Or.inl (Or.inl ⟨h,hn⟩)))
    have hback:Now.Adj x y→Ref.Adj x y:=by
      intro h
      by_contra hn
      exact hFR (Or.inl (Or.inl (Or.inr ⟨h,hn⟩)))
    have href:markedPhysicalRim G π (3*d) (fun e=>raw (Sum.inl e)) mark x (if mark then π.symm y else y)=1→Ref.Adj x y:=by
      intro h
      apply (long_reference_typed_subgraph G π d ω mark)
      apply (long_reference_typed_graph_exact G π d ω mark x y).mpr
      cases mark <;> simp only [Bool.false_eq_true,↓reduceIte] at h ⊢ <;> exact Or.inl h
    have hnow:markedPhysicalRim G π (3*d) (fun e=>τ (Sum.inl e)) mark x (if mark then π.symm y else y)=1→Now.Adj x y:=by
      intro h
      apply (long_residual_typed_subgraph S Small M T mark)
      apply (long_residual_typed_graph_exact S Small M hphysical T mark x y).mpr
      cases mark with
      | false =>
        obtain ⟨e,hx,hy⟩:=(hRims false x y).mp h
        exact ⟨e,Or.inl (Prod.ext hx hy)⟩
      | true =>
        obtain ⟨e,hx,hy⟩:=(hRims true x (π.symm y)).mp h
        have hy':e.val.val.2=y:=π.symm.injective hy
        exact ⟨e,Or.inl (Prod.ext hx hy')⟩
    have heq:Ref.Adj x y∧Now.Adj x y:=by
      by_cases h:markedPhysicalRim G π (3*d) (fun e=>raw (Sum.inl e)) mark x (if mark then π.symm y else y)=1
      · exact ⟨href h,hforward (href h)⟩
      · have ht:markedPhysicalRim G π (3*d) (fun e=>τ (Sum.inl e)) mark x (if mark then π.symm y else y)=1:=by
          by_contra ht; exact hne (iff_of_false h ht)
        exact ⟨hback (hnow ht),hnow ht⟩
    have hagree:=long_reference_residual_directed_agreement G S Del Small π d ω M hphysical hcorrect T x y heq.1 heq.2 hd hc
    apply hne
    cases mark with
    | false =>
      simp only [Bool.false_eq_true,↓reduceIte]
      change (markedPhysicalRim G π (3*d) (fun z=>markedExpandedPhysicalCollapse (ω (Sum.inl z))) false x y=1 ↔ _)
      rw [hagree.1]
      exact ⟨by rintro ⟨e,he⟩; exact (hRims false x y).mpr ⟨e,congrArg Prod.fst he,congrArg Prod.snd he⟩,
        by intro h; obtain ⟨e,hx,hy⟩:=(hRims false x y).mp h; exact ⟨e,Prod.ext hx hy⟩⟩
    | true =>
      simp only [↓reduceIte]
      change (markedPhysicalRim G π (3*d) (fun z=>markedExpandedPhysicalCollapse (ω (Sum.inl z))) true x (π.symm y)=1 ↔ _)
      rw [hagree.2]
      exact ⟨by rintro ⟨e,he⟩; exact (hRims true x (π.symm y)).mpr ⟨e,congrArg Prod.fst he,by simpa only [he]⟩,
        by intro h; obtain ⟨e,hx,hy⟩:=(hRims true x (π.symm y)).mp h; exact ⟨e,Prod.ext hx (π.symm.injective hy)⟩⟩
  cases a with
  | inl a => exact core false a.1 a.2 (by simpa only [rawMarkedPairRims,Sum.elim_inl,Bool.false_eq_true,↓reduceIte] using hchange)
  | inr a =>
    have h:=core true a.1 (π a.2)
    simpa only [rawMarkedPairRims,markedPairPhysical,Sum.elim_inr,↓reduceIte,Equiv.symm_apply_apply] using h (by simpa only [rawMarkedPairRims,Sum.elim_inr,↓reduceIte,Equiv.symm_apply_apply] using hchange)
end Oberwolfach
