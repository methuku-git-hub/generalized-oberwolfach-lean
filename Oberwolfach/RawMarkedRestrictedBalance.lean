module

public import Oberwolfach.MarkedRestrictedDegreeEvent
public import Oberwolfach.RawMarkedRestrictedSpokeDegrees
public import Oberwolfach.RestrictedBalanceArithmetic
public import Oberwolfach.RawMarkedPotentialSampling
public import Oberwolfach.FiniteSumProduct
public import Oberwolfach.ProductGoodEvents

@[expose] public section

/-! Restricted marked balance on one raw sample. All vertex and hub roots
are ambient roots; the parent estimate at pi(v) is used for incoming marked arcs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

def RawMarkedRestrictedBalance (P : SimpleGraph V) (π : Equiv.Perm V) (d m : ℕ)
    (g : Γ) (j : Color) (A : Finset V) (B : Finset U) (η : ℝ)
    (σ : RawMarkedOutcome V U Γ Color) : Prop :=
  let R := fun mark incoming x=>(markedRestrictedDegree P π (3*d) (fun e=>σ (Sum.inl e)) mark incoming x A:ℝ)
  let H := fun b x=>rawMarkedRestrictedSpokeRow π d (fun e=>σ (Sum.inr e)) g j b x B
  let C := fun b u=>rawMarkedRestrictedSpokeCol π d (fun e=>σ (Sum.inr e)) g j b u A
  (∀ x,(∀ incoming,|R false incoming x+R true incoming x-(H false x+H true x)|≤η) ∧
    |R true true x-H true x|≤η) ∧ (∀ u,|C false u-(m:ℝ)*C true u|≤η)

theorem rawMarked_restricted_balance_event
    (P : SimpleGraph V) (π : Equiv.Perm V) (d m : ℕ) (hd : 2≤d)
    (A : Finset V) (B : Finset U) (hA : A.Nonempty) (hB : B.Nonempty) (hInv : ∀ x,π x∈A ↔ x∈A)
    (D δ ε : ℝ) (hδ : 0≤δ) (hε : 0<ε)
    (hP : ∀ x,|((P.neighborFinset x∩A).card:ℝ)-D|≤δ)
    (p k : ℝ) (hp : 0≤p) (hk : 0≤k) (hsum : 2*p+2*k≤1)
    (q : U→Γ→ℝ) (hq : ∀ u g,0≤q u g) (hQ : ∀ u,∑ g,q u g≤1/8)
    (s : U→Color→ℝ) (hs : ∀ u j,0≤s u j)
    (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
    (hnoshort : ∀ x l,0<l → l<2*d+1 → (π^l) x≠x)
    (g : Γ) (j : Color) (s₀ t₀ : ℝ) (hg : ∀ u,q u g=t₀) (hj : ∀ u,s u j=s₀)
    (hD0 : p*D=s₀*B.card) (hDK : k*D=t₀*B.card) (hratio : s₀=(m:ℝ)*t₀) :
    1-8*Fintype.card V*Real.exp (-2*ε^2/A.card)-
      4*Fintype.card V*Real.exp (-2*ε^2/((4*(d:ℝ)+3)^2*B.card))-
      4*Fintype.card U*Real.exp (-2*ε^2/((4*(d:ℝ)+3)^2*Fintype.card V))≤
    (FiniteLaw.pi (rawMarkedWheelLaw p k hp hk hsum d hd q hq hQ s hs hS)).probability
      (RawMarkedRestrictedBalance P π d m g j A B (((m:ℝ)+4)*ε+2*(6*(d:ℝ)+1)+δ)) := by
  have hn : 0<Fintype.card V := hA.card_pos.trans_le A.card_le_univ
  let L := 6*(d:ℝ)+1
  let η := ((m:ℝ)+4)*ε+2*L+δ
  let μ := FiniteLaw.pi (rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS)
  let ν := FiniteLaw.pi (fun _ : Sym2 V=>markedPhysicalLaw p k hp hk hsum)
  let Rgood := fun σ=>∀ (mark incoming : Bool) (x : V),
    |(markedRestrictedDegree P π (3*d) σ mark incoming x A:ℝ)-
      (if mark then k else p)*(P.neighborFinset (if mark && incoming then π x else x)∩A).card|≤ε+L
  let Hgood := fun (σ : RawIntervalFamilyOutcome V U Γ Color)=>
    (∀ b v,|rawMarkedRestrictedSpokeRow π d σ g j b v B-(if b then t₀ else s₀)*B.card|<ε) ∧
    (∀ b u,|rawMarkedRestrictedSpokeCol π d σ g j b u A-(if b then t₀ else s₀)*A.card|<ε)
  let errR := 8*Fintype.card V*Real.exp (-2*ε^2/A.card)
  let errRow := 4*Fintype.card V*Real.exp (-2*ε^2/((4*(d:ℝ)+3)^2*B.card))
  let errCol := 4*Fintype.card U*Real.exp (-2*ε^2/((4*(d:ℝ)+3)^2*Fintype.card V))
  have hR : 1-errR≤ν.probability Rgood := by
    have hh := markedRestrictedDegree_common_event P π (3*d) p k hp hk hsum A hInv ε hε.le
    have he : 2*(3*(d:ℝ))+1=L := by dsimp [L];ring
    simpa only [Nat.cast_mul,Nat.cast_ofNat,he] using hh
  have hH : 1-(errRow+errCol)≤μ.probability Hgood := by
    have hh := rawMarkedRestrictedSpoke_common_event π d hd q hq hQ s hs hS hnoshort hn A B hB g j s₀ t₀ hg hj ε hε
    convert hh using 1 <;> ring
  have hprod := finiteLaw_product_good_lower μ ν Hgood (fun _ σ=>Rgood σ) (errRow+errCol) errR (by dsimp [errR];positivity) hH (fun _ _=>hR)
  let Good := fun (σ : RawIntervalFamilyOutcome V U Γ Color) (τ : Sym2 V→Option (Bool×Bool))=>
    RawMarkedRestrictedBalance P π d m g j A B η (fun e=>match e with
      | Sum.inl e=>τ e | Sum.inr e=>σ e)
  have hgood : (μ.prod ν).probability (fun z=>Hgood z.1 ∧ Rgood z.2)≤(μ.prod ν).probability (fun z=>Good z.1 z.2) := by
    apply finiteLaw_probability_mono
    intro z hz
    have hcent (mark incoming : Bool) (x : V) :
        |(markedRestrictedDegree P π (3*d) z.2 mark incoming x A:ℝ)-(if mark then k else p)*D|≤ε+L+(if mark then k else p)*δ :=
      degree_centre_transfer _ (if mark then k else p) D _ (ε+L) δ
        (by cases mark <;> assumption) (hz.2 mark incoming x) (hP _)
    have hpδ : (p+k)*δ≤δ := by nlinarith only [mul_le_mul_of_nonneg_right hsum hδ,hδ]
    have hkδ : k*δ≤δ := by nlinarith only [mul_le_mul_of_nonneg_right hsum hδ,mul_nonneg hp hδ,hδ]
    have hL : 0≤L := by dsimp [L];positivity
    have hmε : 0≤(m:ℝ)*ε := by positivity
    constructor
    · intro x
      constructor
      · intro incoming
        have hh := restricted_vertex_balance_error _ _ _ _ p k s₀ t₀ D (B.card:ℝ) ε L δ hD0 hDK
          (by simpa using hcent false incoming x) (by simpa using hcent true incoming x)
          (by simpa using (hz.1.1 false x).le) (by simpa using (hz.1.1 true x).le)
        dsimp [Good,RawMarkedRestrictedBalance]
        dsimp [η]
        linarith only [hh,hpδ,hmε]
      · have hh := restricted_marked_balance_error _ _ k t₀ D (B.card:ℝ) ε L δ hDK
          (by simpa using hcent true true x) (by simpa using (hz.1.1 true x).le)
        dsimp [η]
        linarith only [hh,hkδ,hmε,hL,hε]
    · intro u
      have hh := restricted_hub_balance_error _ _ s₀ t₀ (A.card:ℝ) ε (m:ℝ) (Nat.cast_nonneg _) hratio
        (by simpa using (hz.1.2 false u).le) (by simpa using (hz.1.2 true u).le)
      dsimp [η]
      linarith only [hh,hL,hε,hδ]
  have heq := finiteLaw_pi_sum_probability (rawMarkedWheelLaw p k hp hk hsum d hd q hq hQ s hs hS) Good
  change (FiniteLaw.pi (rawMarkedWheelLaw p k hp hk hsum d hd q hq hQ s hs hS)).probability
    (RawMarkedRestrictedBalance P π d m g j A B η)=(μ.prod ν).probability (fun z=>Good z.1 z.2) at heq
  rw [heq]
  convert hprod.trans hgood using 1 <;> ring

end Oberwolfach
