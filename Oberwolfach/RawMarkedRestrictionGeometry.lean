module

public import Oberwolfach.RawMarkedVertexRestriction
public import Oberwolfach.RawIntervalVertexRestriction

@[expose] public section

/-! Physical rims and both spoke types agree under an order-preserving
embedding commuting with the successor permutations. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V W U Γ Color : Type} [Fintype V] [Fintype W] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [LinearOrder W] [DecidableEq U]

theorem orientationBit_orderEmbedding (f : W↪oV) (x y : W) :
    orientationBit (f x) (f y)=orientationBit x y := by simp [orientationBit]

theorem markedPhysicalRim_orderEmbedding
    (f : W↪oV) (π : Equiv.Perm V) (ρ : Equiv.Perm W) (hcomm : ∀ x,f (ρ x)=π (f x))
    (P : SimpleGraph V) (b : ℕ) (σ : Sym2 V→Option (Bool×Bool)) (a : Bool) (x y : W) :
    markedPhysicalRim (P.comap f) ρ b (fun e=>σ (Sym2.map f e)) a x y=1 ↔
      markedPhysicalRim P π b σ a (f x) (f y)=1 := by
  rw [markedPhysicalRim_eq_one_iff,markedPhysicalRim_eq_one_iff]
  rw [permutationClose_embedding f π ρ hcomm f.injective]
  cases a <;> simp only [Bool.false_eq_true,ite_false,ite_true,SimpleGraph.comap_adj,Sym2.map_mk,
    ← hcomm,orientationBit_orderEmbedding]

theorem rawMarkedRestrictVertices_rims
    (f : W↪oV) (π : Equiv.Perm V) (ρ : Equiv.Perm W) (hcomm : ∀ x,f (ρ x)=π (f x))
    (P : SimpleGraph V) (d : ℕ) (σ : RawMarkedOutcome V U Γ Color)
    (e : (W×W)⊕(W×W)) :
    rawMarkedPairRims (P.comap f) ρ d (rawMarkedRestrictVertices f σ) e ↔
      rawMarkedPairRims P π d σ (Sum.map (Prod.map f f) (Prod.map f f) e) := by
  cases e with
  | inl xy=>exact markedPhysicalRim_orderEmbedding f π ρ hcomm P (3*d) (fun e=>σ (Sum.inl e)) false xy.1 xy.2
  | inr xy=>exact markedPhysicalRim_orderEmbedding f π ρ hcomm P (3*d) (fun e=>σ (Sum.inl e)) true xy.1 xy.2

theorem rawMarkedRestrictVertices_spokes
    (f : W↪oV) (π : Equiv.Perm V) (ρ : Equiv.Perm W) (hcomm : ∀ x,f (ρ x)=π (f x))
    (d : ℕ) (σ : RawMarkedOutcome V U Γ Color) (g : Γ) (j : Color) (a : Bool) (x : W) (u : U) :
    rawMarkedPairSpokes ρ d (rawMarkedRestrictVertices f σ) g j a x u ↔
      rawMarkedPairSpokes π d σ g j a (f x) u := by
  have hσ : (fun e=>rawMarkedRestrictVertices f σ (Sum.inr (u,e)))=
      rawIntervalRestrictVertices f (fun e=>σ (Sum.inr (u,e))) := by
    funext e
    cases e with
    | inl e=>rfl
    | inr e=>cases e <;> rfl
  cases a <;> change rawIntervalState ρ d (fun e=>rawMarkedRestrictVertices f σ (Sum.inr (u,e))) x=_ ↔ _
  all_goals rw [hσ,rawIntervalState_restrict f f.injective π ρ hcomm]
  all_goals rfl

end Oberwolfach
