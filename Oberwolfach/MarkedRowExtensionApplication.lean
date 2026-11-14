module

public import Oberwolfach.MarkedExtensionLowerBounds

@[expose] public section

/-! Apply the existing simultaneous row estimate to the four extension
patterns. Hub-dependent supplied marginals remain unchanged. The same
realized outcome supplies every root and hub, including external roots. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_rows_supply_extension_patterns
    (P : SimpleGraph V) (π : Equiv.Perm V) (d h : ℕ) (hh : 2≤h)
    (A : Finset V) (p k : ℝ) (q : U→Γ→ℝ) (s : U→Color→ℝ) (g : Γ) (j : Color)
    (ε : ℝ) (σ : RawMarkedOutcome V U Γ Color) (H : Bool→V→U→Prop)
    (hrows : MarkedRowsWithSpokes P π d h A p k q s g j (ε*A.card) σ H) :
    (∀ b v u,(if b then k else p)*(if b then q u g else s u j)*
      (markedRowDomain P π (3*d) A (markedOneExtensionRequests b v) ∅).card-ε*A.card≤
      markedRelationRowCount (rawMarkedPairRims P π d σ) H
        (markedRowDomain P π (3*d) A (markedOneExtensionRequests b v) ∅)
        (markedOneExtensionRequests b v) {(b,u)}) ∧
    (∀ b v w u,p*(if b then k else p)*s u j*
      (markedRowDomain P π (3*d) A (markedTwoExtensionRequests b v w) ∅).card-ε*A.card≤
      markedRelationRowCount (rawMarkedPairRims P π d σ) H
        (markedRowDomain P π (3*d) A (markedTwoExtensionRequests b v w) ∅)
        (markedTwoExtensionRequests b v w) {(false,u)}) := by
  have hinj (b : Bool) (u : U) : Set.InjOn (fun a:Bool×U=>a.2) ({(b,u)}:Finset (Bool×U)) := by
    intro a ha c hc he
    have ha' : a=(b,u) := by simpa using ha
    have hc' : c=(b,u) := by simpa using hc
    exact ha'.trans hc'.symm
  constructor
  · intro b v u
    have hS : (markedOneExtensionRequests b v).card≤h := by simp [markedOneExtensionRequests];omega
    have hc:=hrows (markedOneExtensionRequests b v) ∅ {(b,u)} hS (by simp) (by simp;omega) (hinj b u)
    have hc' : |markedRelationRowCount (rawMarkedPairRims P π d σ) H
        (markedRowDomain P π (3*d) A (markedOneExtensionRequests b v) ∅)
        (markedOneExtensionRequests b v) {(b,u)}-
        (if b then k else p)*(if b then q u g else s u j)*
        (markedRowDomain P π (3*d) A (markedOneExtensionRequests b v) ∅).card|<ε*A.card := by
      simpa [markedOneExtensionRequests,markedRelationRowCount,markedRowCountWithSpokes] using hc
    have hl:=(abs_lt.mp hc').1
    linarith only [hl]
  · intro b v w u
    have hS : (markedTwoExtensionRequests b v w).card≤h := by
      have hb : (markedTwoExtensionRequests b v w).card≤2 := by simp [markedTwoExtensionRequests]
      exact hb.trans hh
    have hc:=hrows (markedTwoExtensionRequests b v w) ∅ {(false,u)} hS (by simp) (by simp;omega) (hinj false u)
    have hc' : |markedRelationRowCount (rawMarkedPairRims P π d σ) H
        (markedRowDomain P π (3*d) A (markedTwoExtensionRequests b v w) ∅)
        (markedTwoExtensionRequests b v w) {(false,u)}-
        p*(if b then k else p)*s u j*
        (markedRowDomain P π (3*d) A (markedTwoExtensionRequests b v w) ∅).card|<ε*A.card := by
      simpa [markedTwoExtensionRequests,markedRelationRowCount,markedRowCountWithSpokes] using hc
    have hl:=(abs_lt.mp hc').1
    linarith only [hl]

theorem marked_row_event_extension_sets
    (P : SimpleGraph V) (π : Equiv.Perm V) (d h : ℕ) (hh : 2≤h)
    (A : Finset V) (hA : A.image π=A) (p k : ℝ) (q : U→Γ→ℝ) (s : U→Color→ℝ)
    (g : Γ) (j : Color) (γ pstar ε : ℝ)
    (hγ : 0<γ) (hγ1 : γ≤1) (hpstar : 0<pstar) (hpstar1 : pstar≤1)
    (hp : pstar≤p) (hk : pstar≤k) (hq : ∀ u,pstar≤q u g) (hs : ∀ u,pstar≤s u j)
    (hloss : 2*(2*(3*d:ℕ)+1:ℝ)≤γ*A.card/2) (hε : ε≤pstar^3*γ/4)
    (hdeg : ∀ v,(1/2+γ/2)*A.card≤((A∩P.neighborFinset v).card:ℝ))
    (σ : RawMarkedOutcome V U Γ Color) (H : Bool→V→U→Prop)
    (hrows : MarkedRowsWithSpokes P π d h A p k q s g j (ε*A.card) σ H) :
    (∀ b v u,(pstar^3*γ/4)*A.card≤
      ((markedOneExtensionSet (rawMarkedPairRims P π d σ) H A b v u).card:ℝ)) ∧
    (∀ b v w u,v≠(if b then π w else w) →
      (pstar^3*γ/4)*A.card≤((markedTwoExtensionSet (rawMarkedPairRims P π d σ) H A b v w u).card:ℝ)) := by
  obtain ⟨h₁,h₂⟩:=marked_rows_supply_extension_patterns P π d h hh A p k q s g j ε σ H hrows
  have hr (b : Bool) : pstar ≤ (if b then k else p) := by cases b;exact hp;exact hk
  have hc (b : Bool) (u : U) : pstar ≤ (if b then q u g else s u j) := by cases b;exact hs u;exact hq u
  constructor
  · intro b v u
    exact marked_one_extension_lower P π (3*d) (rawMarkedPairRims P π d σ) H A hA b v u
      γ pstar (if b then k else p) (if b then q u g else s u j) ε
      hγ hγ1 hpstar hpstar1 (hr b) (hc b u) hloss hε hdeg (h₁ b v u)
  · intro b v w u hne
    exact marked_two_extension_lower P π (3*d) (rawMarkedPairRims P π d σ) H A b v w u hne
      γ pstar p (if b then k else p) (s u j) ε
      hγ hγ1 hpstar hp (hr b) (hs u) hloss hε hdeg (h₂ b v w u)

end Oberwolfach
