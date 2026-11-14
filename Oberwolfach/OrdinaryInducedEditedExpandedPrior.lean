module

public import Oberwolfach.OrdinaryInducedRawEditedCommon
public import Oberwolfach.FiniteLawIntersectionLower
public import Oberwolfach.OrdinaryTriangleFullExpandedJoint

@[expose] public section
/-! The inner-domain potential event is attached to the same expanded
outcome as an earlier raw event, an expanded prior, and reference cuts. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 4096
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

def ordinaryInducedEditedPotentialConcentration (P F : SimpleGraph V) (A : Set V)
    (π : Equiv.Perm V) (d r : ℕ) (j : Color)
    (φ : OrdinaryCycle (P.induce A) r → ℝ)
    (μ : ∀ e : RawWheelCoordinate V U, FiniteLaw (RawWheelCoordinateState Γ Color e))
    (B t M L : ℝ) (σ : RawWheelOutcome V U Γ Color) : Prop :=
  ∀ (v : A) (u : U) (Q' : SimpleGraph A) (T' : Finset A),
    (∀ x, ((((rawWheelGraph P σ).induce A) \ Q').degree x : ℝ) ≤ M) →
    (∀ x, ((Q' \ ((rawWheelGraph P σ).induce A)).degree x : ℝ) ≤ M) →
    (((((Finset.univ.filter (fun x : A => rawWheelSpokes π d σ j x.val u)) \ T') ∪
      (T' \ (Finset.univ.filter (fun x : A => rawWheelSpokes π d σ j x.val u)))).card : ℝ) ≤ L) →
    |ordinaryLocalPotential (P.induce A) Q' (F.induce A) T' φ v -
      (FiniteLaw.pi μ).expectation (fun τ =>
        ordinaryLocalPotential (P.induce A) ((rawWheelGraph P τ).induce A) (F.induce A)
          (Finset.univ.filter (fun x : A => rawWheelSpokes π d τ j x.val u)) φ v)| ≤
      t + (r : ℝ)^2 * B * L / Fintype.card A +
        2 * (3 * (r : ℝ)^4 * B * M / Fintype.card A)

theorem ordinary_induced_edited_potential_with_expanded_prior
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1) (d:ℕ) (hd:2≤d)
    (q:U→Γ→ℝ) (hq:∀u g,0≤q u g) (hQ:∀u,∑g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀u j,0≤s u j)
    (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑g,q u g))
    {R:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)→Type}
    [∀σ,Fintype (R σ)] (ρ:∀σ,FiniteLaw (R σ)) (ν:FiniteLaw (Sym2 V→Bool))
    (E:(Σσ,R σ)→Prop) (J:RawWheelOutcome V U Γ Color→Prop) (a b c:ℝ)
    (P F:SimpleGraph V) (π:Equiv.Perm V) (j:Color) (δ h:ℝ)
    (hn:0<Fintype.card V) (hU:0<Fintype.card U)
    (A:Set V) (r:ℕ) (hr:2≤r) (hA:0<Fintype.card A)
    (φ:OrdinaryCycle (P.induce A) r→ℝ) (B:ℝ) (hB:0<B)
    (hφ:∀ C,0≤φ C ∧ φ C≤B/(Fintype.card A:ℝ)^(r-1))
    (t M L:ℝ) (ht:0<t):
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS);
    let raw:=rawWheelLaw (V:=V) (fun _=>2*p) (fun _=>by linarith) (fun _=>by linarith) d hd q hq hQ s hs hS;
    let μraw:=FiniteLaw.pi raw;
    let err:=(Fintype.card A:ℝ)*Fintype.card U *
      (2*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*((r:ℝ)^4*B/Fintype.card A)*(2*r)*((r:ℝ)^2*B))));
    1-a≤(μ.sigma ρ).probability E→1-b≤μraw.probability J→
    1-c≤(μraw.prod ν).probability (fun z=>OrdinaryTriangleReferenceMatrixCuts P F π d j δ h z.1 z.2)→
    1-a-b-err-c≤((μ.sigma ρ).prod ν).probability (fun z=>
      let σ:=fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e);
      (E z.1 ∧ (J σ ∧ ordinaryInducedEditedPotentialConcentration P F A π d r j φ raw B t M L σ)) ∧
        OrdinaryTriangleReferenceNormalizedCuts P F π d j δ h σ z.2):=by
  intro μ raw μraw err hE hJ hC
  have hpot : 1-b-err ≤ μraw.probability (fun σ=>J σ ∧
      ordinaryInducedEditedPotentialConcentration P F A π d r j φ raw B t M L σ) := by
    have hh := ordinary_induced_raw_edited_common P F A π d r j hr hA φ B hB hφ raw t M L ht
    exact finiteLaw_intersection_lower μraw J
      (ordinaryInducedEditedPotentialConcentration P F A π d r j φ raw B t M L)
      b err hJ hh
  have hpot' : 1-(b+err) ≤ μraw.probability (fun σ=>J σ ∧
      ordinaryInducedEditedPotentialConcentration P F A π d r j φ raw B t M L σ) := by linarith
  have hh:=ordinary_triangle_raw_and_reference_with_expanded_prior p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS
    ρ ν E (fun σ=>J σ ∧ ordinaryInducedEditedPotentialConcentration P F A π d r j φ raw B t M L σ)
    a (b+err) c P F π j δ h hn hU hE hpot' hC
  convert hh using 1 <;> try ring
end Oberwolfach
