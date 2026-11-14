module

public import Oberwolfach.MarkedActualVortexBalanceProperty
public import Oberwolfach.MarkedVortexTerminalDeeperBalanceZero
public import Oberwolfach.MarkedLevelFiniteBalanceBound

@[expose] public section
/-! Include the final parent level, whose deeper domains are empty, without
requiring a separate random estimate there. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 16384
set_option maxHeartbeats 20000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [Nonempty V] [DecidableEq U]

theorem marked_vortex_deeper_bounds_with_terminal
    (P:SimpleGraph V) (π:Equiv.Perm V) (D m:ℕ) (β ε:ℝ) (Q:Vortex U P D β ε m)
    (hpres:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (d c L:ℕ) (a:Γ) (j:Color) (epsBal ζBal:ℝ) (heps:0≤epsBal) (hζ:0≤ζBal)
    (hterminal:L+1=Q.length) (z:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a)
    (hDeep:L=0 ∨ MarkedActualVortexBalanceProperty Q π hpres d c (L-1) a j epsBal ζBal
      (markedVortexDeeperVertices Q) (markedVortexDeeperHubs Q) z):
    ∀ i≤L,MarkedLevelFiniteBalanceBound (P.comap (markedVortexVertexEmbedding Q i))
      (markedVortexPermutation Q π hpres i) d c (markedVortexDeeperVertices Q i) (markedVortexDeeperHubs Q i)
      ((epsBal+(c+2:ℕ)*ζBal)*(markedVortexDeeperVertices Q i).card)
      (rawMarkedRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i) z.1)
      (fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
        (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j b
          (markedVortexVertexEmbedding Q i x) (markedVortexHubEmbedding Q i u)) := by
  intro i hi
  by_cases hlast:i=L
  · subst i
    intro v j'
    let f:=markedVortexVertexEmbedding Q L
    let g:=markedVortexHubEmbedding Q L
    let ρ:=markedVortexPermutation Q π hpres L
    let σ:=rawMarkedRestrictPair f g z.1
    let H:=fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
      (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j b (f x) (g u)
    let E:=MarkedSampleArc (P.comap f) ρ (3*d) (fun e=>σ (Sum.inl e)) false
    let K:=MarkedSampleArc (P.comap f) ρ (3*d) (fun e=>σ (Sum.inl e)) true
    let S:=Finset.univ.filter (fun s:markedVortexVertexType Q L×markedVortexHubType Q L=>H false s.1 s.2∨H true s.1 s.2)
    have hz:markedFiniteDomainBalance (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) (H true) Finset.univ S c
      (markedVortexDeeperVertices Q L) (markedVortexDeeperHubs Q L) v j'=0:=
      (marked_vortex_terminal_deeper_balance_zero Q L hterminal).2.2 E K _ _ _ _ (H true) Finset.univ S c v j'
    have hdecW:(fun x y:markedVortexVertexType Q L=>Classical.propDecidable (x=y))=
        (Subtype.instDecidableEq:DecidableEq (markedVortexVertexType Q L)):=Subsingleton.elim _ _
    rw [hdecW]
    change |markedFiniteDomainBalance (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) (H true) Finset.univ S c
      (markedVortexDeeperVertices Q L) (markedVortexDeeperHubs Q L) v j'|≤_
    rw [hz,abs_zero]
    positivity
  · have hp:=hDeep.resolve_left (by omega:L≠0)
    dsimp only [MarkedActualVortexBalanceProperty] at hp
    exact (hp i (by omega:i≤L-1)).1
end Oberwolfach
