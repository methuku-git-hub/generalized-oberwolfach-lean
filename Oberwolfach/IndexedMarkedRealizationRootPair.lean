module

public import Oberwolfach.IndexedMarkedRealizationMaps
public import Oberwolfach.IndexedMarkedRealizationResources

@[expose] public section

/-! Construct the transformer input from two actual host realisations,
including the exact source and image resource identities. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V₀ U₀ V U E K A S:Type} [Fintype V₀] [Fintype U₀]
    [Fintype V] [Fintype U] [Fintype A] [Fintype S]
    [DecidableEq V₀] [DecidableEq U₀] [DecidableEq V] [DecidableEq U]
    {tail head:E→V} {ktail khead:K→V} {H₀ HK:V→U→Prop} {π:Equiv.Perm V} {b m:ℕ}

def indexedMarkedRealizationRootPair (G:IndexedMarkedGraph V₀ U₀ A S) (hG:G.IsBalanced m)
    (R T:IndexedMarkedHostRealization G tail head ktail khead H₀ HK π b)
    (hRi:Function.Injective R.rows) (hHi:Function.Injective R.hubs)
    (Z Z':Finset V) (B:Finset U)
    (hr:∀ v,R.rows v∈Z) (ht:∀ v,T.rows v∈Z') (hhr:∀ u,R.hubs u∈B) (hht:∀ u,T.hubs u∈B)
    (hZZ:Disjoint Z Z') (hsep:∀ v∈Z,∀ w∈Z',¬PermutationClose π b v w)
    (hubs:∀ s,R.hubs (G.hub s)≠T.hubs (G.hub s)):
    MarkedRootPair tail head ktail khead H₀ HK π b m A S:=by
  apply indexedMarkedRootPair G hG R.rows T.rows R.hubs T.hubs hRi hHi Z Z' B
    hr ht hhr hht hZZ hsep hubs R.arcSeparated T.arcSeparated R.rimInjective T.rimInjective
    R.spokeInjective T.spokeInjective
  · intro a
    have h₁:=R.rimPresent a
    have h₂:=T.rimPresent a
    cases hj:G.jr a <;> simp only [markedArcPresent,hj,Bool.false_eq_true,ite_false,ite_true] at h₁ h₂ ⊢
    all_goals exact ⟨h₁,h₂⟩
  · intro s
    have h₁:=R.spokePresent s
    have h₂:=T.spokePresent s
    cases hj:G.js s <;> simp only [hj,Bool.false_eq_true,ite_false,ite_true] at h₁ h₂ ⊢
    all_goals exact ⟨h₁,h₂⟩

theorem indexedMarkedRealizationRootPair_endpoints (G:IndexedMarkedGraph V₀ U₀ A S) (hG:G.IsBalanced m)
    (R T:IndexedMarkedHostRealization G tail head ktail khead H₀ HK π b)
    (hRi:Function.Injective R.rows) (hHi:Function.Injective R.hubs)
    (Z Z':Finset V) (B:Finset U)
    (hr:∀ v,R.rows v∈Z) (ht:∀ v,T.rows v∈Z') (hhr:∀ u,R.hubs u∈B) (hht:∀ u,T.hubs u∈B)
    (hZZ:Disjoint Z Z') (hsep:∀ v∈Z,∀ w∈Z',¬PermutationClose π b v w)
    (hubs:∀ s,R.hubs (G.hub s)≠T.hubs (G.hub s)):
    let P:=indexedMarkedRealizationRootPair G hG R T hRi hHi Z Z' B hr ht hhr hht hZZ hsep hubs
    P.source=R.resources∧P.image=T.resources:=by
  dsimp only
  constructor
  · rfl
  · change markedRootGraphResources π
      (fun a=>Function.extend R.rows T.rows id (R.rows (G.src a)))
      (fun a=>Function.extend R.rows T.rows id (R.rows (G.dst a)))
      (fun s=>Function.extend R.rows T.rows id (R.rows (G.row s))) G.jr (T.hubs∘G.hub)=T.resources
    simp only [hRi.extend_apply]
    rfl

end Oberwolfach
