module

public import Oberwolfach.MarkedBoundaryExtensionCoins
public import Oberwolfach.BernoulliPatternLowerEvent

@[expose] public section

/-! The host consisting of all inner resources and the retained boundary.
The same physical coin is used for every test of an edge. Parent occurrence
identities, directions and marked heads are preserved by subtype restriction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

def markedBoundaryRimAllowed (π:Equiv.Perm V) (X:Finset V) (σ:Sym2 (V⊕U)→Bool)
    (j:Bool) (x y:V):Prop:=
  (x∈X∧y∈X)∨((x∈X∨y∈X)∧σ s(Sum.inl x,Sum.inl (if j then π y else y))=true)
def markedBoundarySpokeAllowed (X:Finset V) (Z:Finset U) (σ:Sym2 (V⊕U)→Bool)
    (x:V) (u:U):Prop:=
  (x∈X∧u∈Z)∨((x∈X∨u∈Z)∧σ s(Sum.inl x,Sum.inr u)=true)

theorem marked_arc_pair_restriction (tail head:E→V) (ktail khead:K→V)
    (P₀ P₁:V→V→Prop) (j:Bool) (x y:V):
    markedArcPresent (fun e:{e:E//P₀ (tail e) (head e)}=>tail e.val) (fun e=>head e.val)
      (fun e:{e:K//P₁ (ktail e) (khead e)}=>ktail e.val) (fun e=>khead e.val) j x y↔
      markedArcPresent tail head ktail khead j x y∧(if j then P₁ x y else P₀ x y):=by
  cases j <;> simp only [markedArcPresent,Bool.false_eq_true,ite_false,ite_true]
  all_goals
    constructor
    · rintro ⟨e,ht,hh⟩
      exact ⟨⟨e.val,ht,hh⟩,by simpa only [ht,hh] using e.property⟩
    · rintro ⟨⟨e,ht,hh⟩,he⟩
      exact ⟨⟨e,by simpa only [ht,hh] using he⟩,ht,hh⟩

theorem marked_retained_boundary_free_counts
    (tail head:E→V) (ktail khead:K→V) (H₀ HK:V→U→Prop)
    (π:Equiv.Perm V) (X:Finset V) (Z:Finset U) (σ:Sym2 (V⊕U)→Bool) (c:ℝ)
    (hstep:∀ j x u,c≤((retainedPatternSet (X.filter (fun z=>markedArcPresent tail head ktail khead j x z∧
      (if j then HK z u else H₀ z u))) (markedBoundaryStepCoins π j x u) σ).card:ℝ))
    (hjoin:∀ j x y u,x≠(if j then π y else y)→c≤
      ((retainedPatternSet (X.filter (fun z=>markedArcPresent tail head ktail khead false x z∧
        markedArcPresent tail head ktail khead j z y∧H₀ z u))
        (markedBoundaryJoinCoins x (if j then π y else y) u) σ).card:ℝ)):
    let P₀:=markedBoundaryRimAllowed π X σ false
    let P₁:=markedBoundaryRimAllowed π X σ true
    let E':={e:E//P₀ (tail e) (head e)}
    let K':={e:K//P₁ (ktail e) (khead e)}
    let t':=fun e:E'=>tail e.val
    let h':=fun e:E'=>head e.val
    let kt':=fun e:K'=>ktail e.val
    let kh':=fun e:K'=>khead e.val
    let H₀':=fun x u=>H₀ x u∧markedBoundarySpokeAllowed X Z σ x u
    let HK':=fun x u=>HK x u∧markedBoundarySpokeAllowed X Z σ x u;
    (∀ j x u,c≤((X.filter (fun z=>markedArcPresent t' h' kt' kh' j x z∧
      (if j then HK' z u else H₀' z u))).card:ℝ))∧
    (∀ j x y u,x≠(if j then π y else y)→c≤((X.filter (fun z=>markedArcPresent t' h' kt' kh' false x z∧
      markedArcPresent t' h' kt' kh' j z y∧H₀' z u)).card:ℝ)):=by
  intro P₀ P₁ E' K' t' h' kt' kh' H₀' HK'
  have harc (j:Bool) (x y:V):markedArcPresent t' h' kt' kh' j x y↔
      markedArcPresent tail head ktail khead j x y∧markedBoundaryRimAllowed π X σ j x y:=by
    have h:=marked_arc_pair_restriction tail head ktail khead P₀ P₁ j x y
    cases j <;> exact h
  constructor
  · intro j x u
    apply (hstep j x u).trans
    apply Nat.cast_le.mpr
    apply Finset.card_le_card
    intro z hz
    obtain ⟨hz,hcoins⟩:=Finset.mem_filter.mp hz
    obtain ⟨hzX,hr,hs⟩:=Finset.mem_filter.mp hz
    have he:σ s(Sum.inl x,Sum.inl (if j then π z else z))=true:=hcoins _ (by simp [markedBoundaryStepCoins])
    have hf:σ s(Sum.inl z,Sum.inr u)=true:=hcoins _ (by simp [markedBoundaryStepCoins])
    have ha:markedBoundaryRimAllowed π X σ j x z:=Or.inr ⟨Or.inr hzX,he⟩
    have hb:markedBoundarySpokeAllowed X Z σ z u:=Or.inr ⟨Or.inl hzX,hf⟩
    refine Finset.mem_filter.mpr ⟨hzX,(harc j x z).mpr ⟨hr,ha⟩,?_⟩
    cases j <;> exact ⟨hs,hb⟩
  · intro j x y u hxy
    apply (hjoin j x y u hxy).trans
    apply Nat.cast_le.mpr
    apply Finset.card_le_card
    intro z hz
    obtain ⟨hz,hcoins⟩:=Finset.mem_filter.mp hz
    obtain ⟨hzX,hr₀,hr₁,hs⟩:=Finset.mem_filter.mp hz
    have he:σ s(Sum.inl x,Sum.inl z)=true:=hcoins _ (by simp [markedBoundaryJoinCoins])
    have hf:σ s(Sum.inl z,Sum.inl (if j then π y else y))=true:=hcoins _ (by simp [markedBoundaryJoinCoins])
    have hg:σ s(Sum.inl z,Sum.inr u)=true:=hcoins _ (by simp [markedBoundaryJoinCoins])
    have ha:markedBoundaryRimAllowed π X σ false x z:=Or.inr ⟨Or.inr hzX,he⟩
    have hb:markedBoundaryRimAllowed π X σ j z y:=Or.inr ⟨Or.inl hzX,hf⟩
    have hc:markedBoundarySpokeAllowed X Z σ z u:=Or.inr ⟨Or.inl hzX,hg⟩
    exact Finset.mem_filter.mpr ⟨hzX,(harc false x z).mpr ⟨hr₀,ha⟩,(harc j z y).mpr ⟨hr₁,hb⟩,hs,hc⟩
end Oberwolfach
