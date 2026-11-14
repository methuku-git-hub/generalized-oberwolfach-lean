module

public import Oberwolfach.MarkedVortexActualBalanceFields

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

theorem marked_vortex_actual_initial_balance_with_slack
    (π:Equiv.Perm V) (hπ:∀ i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (d c L:ℕ) (a:Γ) (j:Color) (epsBal ζ etaBal x:ℝ)
    (heps:0≤epsBal) (hζ:0≤ζ)
    (hrelative:epsBal+(c+2:ℕ)*ζ≤etaBal/2)
    (hambient:epsBal+(c+2:ℕ)*ζ≤x/4)
    (hterminal:L+1=Q.length)
    (z:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a)
    (hI:MarkedActualVortexBalanceProperty Q π hπ d c L a j epsBal ζ
      (markedVortexInnerVertices Q) (markedVortexInnerHubs Q) z)
    (hT:L=0 ∨ MarkedActualVortexBalanceProperty Q π hπ d c (L-1) a j epsBal ζ
      (markedVortexDeeperVertices Q) (markedVortexDeeperHubs Q) z):
    let i:=0
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
      (∀ v j,|bal I J v j|≤(x/4)*Fintype.card W) ∧
      (∀ v j,|bal I J v j|≤(etaBal/2)*I.card) ∧
      (∀ v j,|bal T R v j|≤(x/4)*Fintype.card W):=by
  intro i W Z f g ρ σ H E K S I J T R bal
  have hbase:=marked_vortex_actual_balance_fields Q π hπ d c L a j epsBal ζ (etaBal/2)
    heps hζ hrelative hterminal z hI hT 0 (Nat.zero_le L)
  dsimp only at hbase
  have hcoeff:0≤epsBal+(c+2:ℕ)*ζ:=by positivity
  have hcardI:(I.card:ℝ)≤Fintype.card W:=by exact_mod_cast Finset.card_le_univ I
  have hcardT:(T.card:ℝ)≤Fintype.card W:=by exact_mod_cast Finset.card_le_univ T
  have hIB:(epsBal+(c+2:ℕ)*ζ)*I.card≤(x/4)*Fintype.card W:=
    (mul_le_mul_of_nonneg_left hcardI hcoeff).trans (mul_le_mul_of_nonneg_right hambient (Nat.cast_nonneg _))
  have hTB:(epsBal+(c+2:ℕ)*ζ)*T.card≤(x/4)*Fintype.card W:=
    (mul_le_mul_of_nonneg_left hcardT hcoeff).trans (mul_le_mul_of_nonneg_right hambient (Nat.cast_nonneg _))
  exact ⟨fun v j=>(hbase.1 v j).trans hIB,hbase.2.2,fun v j=>(hbase.2.1 v j).trans hTB⟩
end Oberwolfach
