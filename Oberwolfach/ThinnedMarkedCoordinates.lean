module

public import Oberwolfach.ThinnedMarkedLaw

@[expose] public section

/-! Actual primitive supports for common spokes and their vertex coins.
Coin coordinates at a potential root are omitted together with its two
spokes. Distinct resources of a separated parent cycle have disjoint
supports even though different cycles need not have disjoint supports. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

def commonResourceAtHub (u : U) : ((V×V)⊕(V×V))⊕(Bool×V×Unit)→((V×V)⊕(V×V))⊕(Bool×V×U)
  | Sum.inl e=>Sum.inl e
  | Sum.inr a=>Sum.inr (a.1,a.2.1,u)

theorem commonResourceAtHub_injective (u : U) : Function.Injective (commonResourceAtHub (V:=V) u) := by
  intro a b h
  cases a with
  | inl a=>cases b <;> simp_all [commonResourceAtHub]
  | inr a=>
    cases b with
    | inl b=>simp [commonResourceAtHub] at h
    | inr b=>
      apply congrArg Sum.inr
      have hh := Sum.inr.inj h
      have h₁ : a.1=b.1 := congrArg (fun z : Bool×V×U=>z.1) hh
      have h₂ : a.2.1=b.2.1 := congrArg (fun z : Bool×V×U=>z.2.1) hh
      exact Prod.ext h₁ (Prod.ext h₂ (Subsingleton.elim _ _))

def thinnedMarkedResourceCoordinates (π : Equiv.Perm V) (d : ℕ) (u u' : U)
    (a : ((V×V)⊕(V×V))⊕(Bool×V×Unit)) : Finset (RawWheelCoordinate V U⊕V) :=
  ((rawMarkedResourceCoordinates π d (commonResourceAtHub u a) ∪
    rawMarkedResourceCoordinates π d (commonResourceAtHub u' a)).image Sum.inl) ∪
  (match a with | Sum.inl _=>∅ | Sum.inr a=>{Sum.inr a.2.1})

theorem thinnedMarkedResourceState_supported
    (P : SimpleGraph V) (π : Equiv.Perm V) (d : ℕ) (g : Γ) (j : Color) (u u' : U)
    (a : ((V×V)⊕(V×V))⊕(Bool×V×Unit)) (σ τ : ThinnedMarkedOutcome V U Γ Color)
    (h : ∀ e∈thinnedMarkedResourceCoordinates π d u u' a,σ e=τ e) :
    typedMarkedResourceState (rawMarkedPairRims P π d (fun e=>σ (Sum.inl e))) (thinnedMarkedSpokes π d g j u u' σ) a=
    typedMarkedResourceState (rawMarkedPairRims P π d (fun e=>τ (Sum.inl e))) (thinnedMarkedSpokes π d g j u u' τ) a := by
  have h₁ := rawMarkedResourceState_supported P π d g j (commonResourceAtHub u a)
    (fun e=>σ (Sum.inl e)) (fun e=>τ (Sum.inl e)) (by
      intro e he
      exact h _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨e,Finset.mem_union_left _ he,rfl⟩)))
  have h₂ := rawMarkedResourceState_supported P π d g j (commonResourceAtHub u' a)
    (fun e=>σ (Sum.inl e)) (fun e=>τ (Sum.inl e)) (by
      intro e he
      exact h _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨e,Finset.mem_union_right _ he,rfl⟩)))
  apply congrArg (fun Q : Prop=>decide Q)
  apply propext
  cases a with
  | inl e=>exact h₁
  | inr a=>
    have hc := h (Sum.inr a.2.1) (Finset.mem_union_right _ (Finset.mem_singleton_self _))
    simpa only [commonResourceAtHub,Sum.elim_inr,thinnedMarkedSpokes,hc] using
      and_congr h₁ (and_congr h₂ (Iff.rfl : (a.1=false → τ (Sum.inr a.2.1)=true) ↔ _))

theorem thinnedMarkedResourceCoordinates_card (π : Equiv.Perm V) (d : ℕ) (u u' : U)
    (a : ((V×V)⊕(V×V))⊕(Bool×V×Unit)) :
    (thinnedMarkedResourceCoordinates π d u u' a).card≤16*d+14 := by
  have h₁ := rawMarkedResourceCoordinates_card π d (commonResourceAtHub u a)
  have h₂ := rawMarkedResourceCoordinates_card π d (commonResourceAtHub u' a)
  have hsum := Finset.card_union_le (rawMarkedResourceCoordinates π d (commonResourceAtHub u a))
    (rawMarkedResourceCoordinates π d (commonResourceAtHub u' a))
  have himg := Finset.card_image_le (f:=Sum.inl (β:=V))
    (s:=rawMarkedResourceCoordinates π d (commonResourceAtHub u a) ∪ rawMarkedResourceCoordinates π d (commonResourceAtHub u' a))
  unfold thinnedMarkedResourceCoordinates
  have hh := Finset.card_union_le
    ((rawMarkedResourceCoordinates π d (commonResourceAtHub u a) ∪ rawMarkedResourceCoordinates π d (commonResourceAtHub u' a)).image (Sum.inl (β:=V)))
    (match a with | Sum.inl _=>∅ | Sum.inr a=>{Sum.inr a.2.1})
  cases a <;> dsimp only at hh ⊢ <;> simp only [Finset.card_empty,Finset.card_singleton] at hh <;> omega

theorem thinnedMarkedResourceCoordinates_reverse_card (π : Equiv.Perm V) (d : ℕ) (u u' : U)
    (e : RawWheelCoordinate V U⊕V) :
    (Finset.univ.filter (fun a=>e∈thinnedMarkedResourceCoordinates π d u u' a)).card≤16*d+14 := by
  cases e with
  | inl e=>
    let T (w : U) := Finset.univ.filter (fun a=>e∈rawMarkedResourceCoordinates π d (commonResourceAtHub w a))
    have hc (w : U) : (T w).card≤8*d+6 := by
      have hh : (T w).card≤(Finset.univ.filter (fun a=>e∈rawMarkedResourceCoordinates π d a)).card := by
        apply Finset.card_le_card_of_injOn (commonResourceAtHub w)
        · intro a ha
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp ha).2⟩
        · exact fun _ _ _ _ h=>(commonResourceAtHub_injective w) h
      exact hh.trans (rawMarkedResourceCoordinates_reverse_card π d e)
    have hsub : Finset.univ.filter (fun a=>Sum.inl e∈thinnedMarkedResourceCoordinates π d u u' a)⊆T u∪T u' := by
      intro a ha
      cases a <;> simpa [thinnedMarkedResourceCoordinates,T] using ha
    have hbound := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have h₁ := hc u
    have h₂ := hc u'
    omega
  | inr v=>
    let T : Finset (((V×V)⊕(V×V))⊕(Bool×V×Unit)) := {Sum.inr (false,v,()),Sum.inr (true,v,())}
    have hsub : Finset.univ.filter (fun a=>Sum.inr v∈thinnedMarkedResourceCoordinates π d u u' a)⊆T := by
      intro a ha
      cases a with
      | inl e=>simp [thinnedMarkedResourceCoordinates] at ha
      | inr a=>
        have hv : v=a.2.1 := by simpa [thinnedMarkedResourceCoordinates] using ha
        rcases a with ⟨b,x,z⟩
        cases z
        cases b <;> simp [T,hv]
    have hc : T.card≤2 := by exact Finset.card_le_two
    exact (Finset.card_le_card hsub).trans (hc.trans (by omega))

end Oberwolfach
