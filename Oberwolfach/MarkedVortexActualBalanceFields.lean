module

public import Oberwolfach.MarkedActualVortexBalanceProperty
public import Oberwolfach.MarkedTerminalBalance

@[expose] public section
/-! The actual balance inputs at every selected parent level, including the
appended empty terminal pair. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 35000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [Nonempty V] [DecidableEq U]
variable {G:SimpleGraph V} {D m:ℕ} {β ε:ℝ} (Q:Vortex U G D β ε m)

theorem marked_vortex_actual_balance_fields
    (π:Equiv.Perm V) (hπ:∀ i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (d c L:ℕ) (a:Γ) (j:Color) (epsBal ζ η:ℝ)
    (heps:0≤epsBal) (hζ:0≤ζ) (heta:epsBal+(c+2:ℕ)*ζ≤η)
    (hterminal:L+1=Q.length)
    (z:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a)
    (hI:MarkedActualVortexBalanceProperty Q π hπ d c L a j epsBal ζ
      (markedVortexInnerVertices Q) (markedVortexInnerHubs Q) z)
    (hT:L=0 ∨ MarkedActualVortexBalanceProperty Q π hπ d c (L-1) a j epsBal ζ
      (markedVortexDeeperVertices Q) (markedVortexDeeperHubs Q) z):
    ∀ i≤L,
      let W:=markedVortexVertexType Q i
      let Z:=markedVortexHubType Q i
      let f:=markedVortexVertexEmbedding Q i
      let g:=markedVortexHubEmbedding Q i
      let ρ:=markedVortexPermutation Q π hπ i
      let σ:=rawMarkedRestrictPair f g z.1
      let H:=fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
        (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j b (f x) (g u)
      let E:=MarkedSampleArc (G.comap f) ρ (3*d) (fun e=>σ (Sum.inl e)) false
      let K:=MarkedSampleArc (G.comap f) ρ (3*d) (fun e=>σ (Sum.inl e)) true
      let S:=Finset.univ.filter (fun s:W×Z=>H false s.1 s.2∨H true s.1 s.2)
      let I:=markedVortexInnerVertices Q i
      let J:=markedVortexInnerHubs Q i
      let T:=markedVortexDeeperVertices Q i
      let R:=markedVortexDeeperHubs Q i
      let bal:=markedFiniteDomainBalance (fun e:E=>e.val.1) (fun e=>e.val.2)
        (fun e:K=>e.val.1) (fun e=>e.val.2) (H true) Finset.univ S c;
      (∀ v j,|bal I J v j|≤(epsBal+(c+2:ℕ)*ζ)*I.card) ∧
      (∀ v j,|bal T R v j|≤(epsBal+(c+2:ℕ)*ζ)*T.card) ∧
      (∀ v j,|bal I J v j|≤η*I.card):=by
  intro i hi W Z f g ρ σ H E K S I J T R bal
  have hinner:=hI
  dsimp only [MarkedActualVortexBalanceProperty] at hinner
  have heq:(fun (t:ℕ) (x y:markedVortexVertexType Q t)=>Classical.propDecidable (x=y))=
      (fun (t:ℕ) (x y:markedVortexVertexType Q t)=>Subtype.instDecidableEq x y):=Subsingleton.elim _ _
  rw [heq] at hinner
  have hbase:∀ v j,|bal I J v j|≤(epsBal+(c+2:ℕ)*ζ)*I.card:=by
    have hh:=(hinner i hi).1
    exact hh
  have hdeep:∀ v j,|bal T R v j|≤(epsBal+(c+2:ℕ)*ζ)*T.card:=by
    intro v j
    by_cases hlast:i=L
    · have hempty:=marked_vortex_deeper_terminal_empty Q i (by omega)
      have hz:=marked_vortex_terminal_balance_zero Q i (by omega) (fun e:E=>e.val.1) (fun e=>e.val.2)
        (fun e:K=>e.val.1) (fun e=>e.val.2) (H true) Finset.univ S c v j
      change bal T R v j=0 at hz
      rw [hz]
      simp only [abs_zero]
      have hc:0≤(epsBal+(c+2:ℕ)*ζ):=by positivity
      exact mul_nonneg hc (Nat.cast_nonneg _)
    · have hi':i≤L-1:=by omega
      have hprop:=hT.resolve_left (by omega)
      dsimp only [MarkedActualVortexBalanceProperty] at hprop
      rw [heq] at hprop
      have hh:=(hprop i hi').1 v j
      exact hh
  refine ⟨hbase,hdeep,?_⟩
  intro v j
  exact (hbase v j).trans (mul_le_mul_of_nonneg_right heta (Nat.cast_nonneg _))
end Oberwolfach
