module

public import Oberwolfach.OrdinaryRawIntervalSampling
public import Oberwolfach.RawMarkedVertexRestriction

@[expose] public section
/-! Restrict both domains of the ordinary raw experiment. This is an exact
product-law identity for fixed injections, not an independence assumption. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W U Z Γ Color:Type} [Fintype V] [Fintype W] [Fintype U] [Fintype Z]
  [Fintype Γ] [Fintype Color] [LinearOrder V] [LinearOrder W] [DecidableEq U] [DecidableEq Z]

def ordinaryRawPairCoordinate (f:W→V) (g:Z→U):RawWheelCoordinate W Z→RawWheelCoordinate V U :=
  fun e=>rawMarkedVertexCoordinate f (rawMarkedHubCoordinate g e)

def ordinaryRawPairState (f:W→V) (g:Z→U) : ∀e:RawWheelCoordinate W Z,
    RawWheelCoordinateState Γ Color (ordinaryRawPairCoordinate f g e)→RawWheelCoordinateState Γ Color e
  | Sum.inl _,a=>a
  | Sum.inr (_,Sum.inl _),a=>a
  | Sum.inr (_,Sum.inr (Sum.inl _)),a=>a
  | Sum.inr (_,Sum.inr (Sum.inr _)),a=>a

def ordinaryRawRestrictPair (f:W→V) (g:Z→U) (σ:RawWheelOutcome V U Γ Color):RawWheelOutcome W Z Γ Color :=
  fun e=>ordinaryRawPairState f g e (σ (ordinaryRawPairCoordinate f g e))

theorem ordinaryRawPairCoordinate_injective (f:W→V) (hf:Function.Injective f)
    (g:Z→U) (hg:Function.Injective g):Function.Injective (ordinaryRawPairCoordinate f g):=
  (rawMarkedVertexCoordinate_injective f hf).comp (rawMarkedHubCoordinate_injective g hg)

theorem ordinary_raw_pair_restriction_probability
    (f:W→V) (hf:Function.Injective f) (g:Z→U) (hg:Function.Injective g)
    (p:ℝ) (hp:0≤p) (hp1:p≤1) (d:ℕ) (hd:2≤d)
    (q:U→Γ→ℝ) (hq:∀u a,0≤q u a) (hQ:∀u,∑a,q u a≤1/8)
    (s:U→Color→ℝ) (hs:∀u a,0≤s u a)
    (hS:∀u,∑a,s u a≤ intervalUncoveredProbability d (∑a,q u a))
    (E:RawWheelOutcome W Z Γ Color→Prop):
    (FiniteLaw.pi (rawWheelLaw (V:=V) (fun _=>p) (fun _=>hp) (fun _=>hp1) d hd q hq hQ s hs hS)).probability
      (fun σ=>E (ordinaryRawRestrictPair f g σ))=
    (FiniteLaw.pi (rawWheelLaw (V:=W) (fun _=>p) (fun _=>hp) (fun _=>hp1) d hd
      (fun z=>q (g z)) (fun z=>hq (g z)) (fun z=>hQ (g z))
      (fun z=>s (g z)) (fun z=>hs (g z)) (fun z=>hS (g z)))).probability E:=by
  let μ:=rawWheelLaw (V:=V) (fun _=>p) (fun _=>hp) (fun _=>hp1) d hd q hq hQ s hs hS
  have hh:=finiteLaw_pi_injective_projection_event μ (ordinaryRawPairCoordinate f g)
    (ordinaryRawPairCoordinate_injective f hf g hg) (fun σ=>E (fun e=>ordinaryRawPairState f g e (σ e)))
  change (FiniteLaw.pi μ).probability (fun σ=>E (fun e=>ordinaryRawPairState f g e (σ (ordinaryRawPairCoordinate f g e))))=_
  rw [hh,←finiteLaw_map_probability,finiteLaw_pi_map]
  have he (e:RawWheelCoordinate W Z):
      ((μ (ordinaryRawPairCoordinate f g e)).map (ordinaryRawPairState (Γ:=Γ) (Color:=Color) f g e))=
      rawWheelLaw (V:=W) (fun _=>p) (fun _=>hp) (fun _=>hp1) d hd
        (fun z=>q (g z)) (fun z=>hq (g z)) (fun z=>hQ (g z))
        (fun z=>s (g z)) (fun z=>hs (g z)) (fun z=>hS (g z)) e:=by
    apply finiteLaw_ext
    intro a
    cases e with
    | inl e=>cases a <;> simp [μ,rawWheelLaw,ordinaryRawPairCoordinate,ordinaryRawPairState,rawMarkedHubCoordinate,rawMarkedVertexCoordinate,FiniteLaw.map]
    | inr e=>
      rcases e with ⟨z,i⟩
      cases i with
      | inl i=>simp [μ,rawWheelLaw,ordinaryRawPairCoordinate,ordinaryRawPairState,rawMarkedHubCoordinate,rawMarkedVertexCoordinate,FiniteLaw.map,rawIntervalFamilyLaw,rawIntervalVertexCoordinate,rawIntervalCoordinateLaw]
      | inr i=>cases i <;> simp [μ,rawWheelLaw,ordinaryRawPairCoordinate,ordinaryRawPairState,rawMarkedHubCoordinate,rawMarkedVertexCoordinate,FiniteLaw.map,rawIntervalFamilyLaw,rawIntervalVertexCoordinate,rawIntervalCoordinateLaw]
  simp_rw [he]
end Oberwolfach
