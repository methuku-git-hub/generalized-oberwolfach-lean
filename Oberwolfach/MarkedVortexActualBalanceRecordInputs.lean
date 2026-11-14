module

public import Oberwolfach.MarkedVortexActualBalanceFields
public import Oberwolfach.MarkedBalanceRecordMargins

@[expose] public section
/-! Actual balance estimates with the error margins required by the level record. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [Nonempty V] [DecidableEq U]
variable {G:SimpleGraph V} {D m:ℕ} {β ε:ℝ} (Q:Vortex U G D β ε m)
theorem marked_vortex_actual_balance_record_inputs
    (π:Equiv.Perm V) (hπ:∀ i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (d c L:ℕ) (a:Γ) (j:Color) (epsBal ζ η x:ℝ)
    (heps:0≤epsBal) (hζ:0≤ζ) (hx:0≤x) (heta:epsBal+(c+2:ℕ)*ζ≤η) (hmargin:epsBal+(c+2:ℕ)*ζ≤x/2)
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
      ∃ errInner errDeep:ℝ, 0≤errDeep ∧
      errInner≤(x/2)*Fintype.card W ∧ errDeep≤(x/2)*Fintype.card W ∧
      (∀ v j,|bal I J v j|≤errInner) ∧
      (∀ v j,|bal T R v j|≤errDeep) ∧
      (∀ v j,|bal I J v j|≤η*I.card)  :=by
  have hfields:=marked_vortex_actual_balance_fields Q π hπ d c L a j epsBal ζ η heps hζ heta hterminal z hI hT
  intro i hi W Z f g ρ σ H E K S I J T R bal
  have hbounds:=hfields i hi
  have hIcard:(I.card:ℝ)≤Fintype.card W:=by exact_mod_cast (Finset.card_le_univ I)
  have hTcard:(T.card:ℝ)≤Fintype.card W:=by exact_mod_cast (Finset.card_le_univ T)
  have hmargins:=marked_balance_record_error_bounds η x epsBal ζ c I.card T.card (Fintype.card W)
    hx (Nat.cast_nonneg _) (Nat.cast_nonneg _) hIcard hTcard heta hmargin
  refine ⟨(epsBal+(c+2:ℕ)*ζ)*I.card,(epsBal+(c+2:ℕ)*ζ)*T.card,?_,hmargins.2.1,hmargins.2.2,?_⟩
  · positivity
  · exact hbounds
end Oberwolfach
