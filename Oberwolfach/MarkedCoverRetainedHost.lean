module

public import Oberwolfach.MarkedBoundaryRetainedHost
public import Oberwolfach.MarkedBoundaryHubRetention

@[expose] public section

/-! The cover host also keeps outside edges. Its constructed packing later
uses only prescribed outside resources; all other resources lie inside
the inner pair or in the retained boundary.
The same physical coin is used for every test of an edge. Parent occurrence
identities, directions and marked heads are preserved by subtype restriction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

def markedCoverRimAllowed (π:Equiv.Perm V) (X:Finset V) (σ:Sym2 (V⊕U)→Bool)
    (j:Bool) (x y:V):Prop:=
  (x∉X∧y∉X)∨markedBoundaryRimAllowed π X σ j x y
def markedCoverSpokeAllowed (X:Finset V) (Z:Finset U) (σ:Sym2 (V⊕U)→Bool)
    (x:V) (u:U):Prop:=
  (x∉X∧u∉Z)∨markedBoundarySpokeAllowed X Z σ x u

theorem marked_retained_cover_free_counts
    (tail head:E→V) (ktail khead:K→V) (H₀ HK:V→U→Prop)
    (π:Equiv.Perm V) (X:Finset V) (Z:Finset U) (σ:Sym2 (V⊕U)→Bool) (c:ℝ)
    (hstep:∀ j x u,c≤((retainedPatternSet (X.filter (fun z=>markedArcPresent tail head ktail khead j x z∧
      (if j then HK z u else H₀ z u))) (markedBoundaryStepCoins π j x u) σ).card:ℝ))
    (hjoin:∀ j x y u,x≠(if j then π y else y)→c≤
      ((retainedPatternSet (X.filter (fun z=>markedArcPresent tail head ktail khead false x z∧
        markedArcPresent tail head ktail khead j z y∧H₀ z u))
        (markedBoundaryJoinCoins x (if j then π y else y) u) σ).card:ℝ)):
    let P₀:=markedCoverRimAllowed π X σ false
    let P₁:=markedCoverRimAllowed π X σ true
    let E':={e:E//P₀ (tail e) (head e)}
    let K':={e:K//P₁ (ktail e) (khead e)}
    let t':=fun e:E'=>tail e.val
    let h':=fun e:E'=>head e.val
    let kt':=fun e:K'=>ktail e.val
    let kh':=fun e:K'=>khead e.val
    let H₀':=fun x u=>H₀ x u∧markedCoverSpokeAllowed X Z σ x u
    let HK':=fun x u=>HK x u∧markedCoverSpokeAllowed X Z σ x u;
    (∀ j x u,c≤((X.filter (fun z=>markedArcPresent t' h' kt' kh' j x z∧
      (if j then HK' z u else H₀' z u))).card:ℝ))∧
    (∀ j x y u,x≠(if j then π y else y)→c≤((X.filter (fun z=>markedArcPresent t' h' kt' kh' false x z∧
      markedArcPresent t' h' kt' kh' j z y∧H₀' z u)).card:ℝ)):=by
  intro P₀ P₁ E' K' t' h' kt' kh' H₀' HK'
  have harc (j:Bool) (x y:V):markedArcPresent t' h' kt' kh' j x y↔
      markedArcPresent tail head ktail khead j x y∧markedCoverRimAllowed π X σ j x y:=by
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
    have ha:markedCoverRimAllowed π X σ j x z:=Or.inr (Or.inr ⟨Or.inr hzX,he⟩)
    have hb:markedCoverSpokeAllowed X Z σ z u:=Or.inr (Or.inr ⟨Or.inl hzX,hf⟩)
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
    have ha:markedCoverRimAllowed π X σ false x z:=Or.inr (Or.inr ⟨Or.inr hzX,he⟩)
    have hb:markedCoverRimAllowed π X σ j z y:=Or.inr (Or.inr ⟨Or.inl hzX,hf⟩)
    have hc:markedCoverSpokeAllowed X Z σ z u:=Or.inr (Or.inr ⟨Or.inl hzX,hg⟩)
    exact Finset.mem_filter.mpr ⟨hzX,(harc false x z).mpr ⟨hr₀,ha⟩,(harc j z y).mpr ⟨hr₁,hb⟩,hs,hc⟩

theorem marked_retained_cover_hub_counts
    (H₀ HK:V→U→Prop) (X:Finset V) (Z:Finset U) (σ:Sym2 (V⊕U)→Bool)
    (j:Bool) (x y:V) (c:ℝ)
    (h:c≤((retainedPatternSet (Z.filter (fun u=>H₀ x u∧(if j then HK y u else H₀ y u)))
      (markedBoundaryHubCoins x y) σ).card:ℝ)):
    c≤((Z.filter (fun u=>(H₀ x u∧markedCoverSpokeAllowed X Z σ x u)∧
      (if j then HK y u∧markedCoverSpokeAllowed X Z σ y u
        else H₀ y u∧markedCoverSpokeAllowed X Z σ y u))).card:ℝ):=by
  apply h.trans
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro u hu
  obtain ⟨hu,hcoins⟩:=Finset.mem_filter.mp hu
  obtain ⟨huZ,hx,hy⟩:=Finset.mem_filter.mp hu
  have hxu:markedCoverSpokeAllowed X Z σ x u:=
    Or.inr (Or.inr ⟨Or.inr huZ,hcoins _ (by simp [markedBoundaryHubCoins])⟩)
  have hyu:markedCoverSpokeAllowed X Z σ y u:=
    Or.inr (Or.inr ⟨Or.inr huZ,hcoins _ (by simp [markedBoundaryHubCoins])⟩)
  refine Finset.mem_filter.mpr ⟨huZ,⟨hx,hxu⟩,?_⟩
  cases j <;> exact ⟨hy,hyu⟩
end Oberwolfach
