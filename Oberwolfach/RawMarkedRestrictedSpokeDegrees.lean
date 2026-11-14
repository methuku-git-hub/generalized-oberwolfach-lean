module

public import Oberwolfach.RawIntervalRestrictedLabels
public import Oberwolfach.RawIntervalSelectedNeighbours
public import Oberwolfach.GoodPlacementEvents

@[expose] public section

/-! Both spoke types on fixed vertex and hub domains. Every ambient root
is tested, including roots outside the restriction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

def rawMarkedRestrictedSpokeRow (π : Equiv.Perm V) (d : ℕ)
    (σ : RawIntervalFamilyOutcome V U Γ Color) (g : Γ) (j : Color) (b : Bool) (v : V) (B : Finset U) : ℝ :=
  ∑ u∈B,if rawIntervalFamilyState π d σ (v,u)=some (if b then Sum.inl g else Sum.inr j) then 1 else 0

def rawMarkedRestrictedSpokeCol (π : Equiv.Perm V) (d : ℕ)
    (σ : RawIntervalFamilyOutcome V U Γ Color) (g : Γ) (j : Color) (b : Bool) (u : U) (A : Finset V) : ℝ :=
  ∑ v∈A,if rawIntervalFamilyState π d σ (v,u)=some (if b then Sum.inl g else Sum.inr j) then 1 else 0

theorem rawMarkedRestrictedSpoke_common_event
    (π : Equiv.Perm V) (d : ℕ) (hd : 2≤d)
    (q : U→Γ→ℝ) (hq : ∀ u g,0≤q u g) (hQ : ∀ u,∑ g,q u g≤1/8)
    (s : U→Color→ℝ) (hs : ∀ u j,0≤s u j)
    (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
    (hnoshort : ∀ x l,0<l → l<2*d+1 → (π^l) x≠x)
    (hn : 0<Fintype.card V) (A : Finset V) (B : Finset U) (hB : B.Nonempty)
    (g : Γ) (j : Color) (s₀ t₀ : ℝ) (hg : ∀ u,q u g=t₀) (hj : ∀ u,s u j=s₀)
    (ε : ℝ) (hε : 0<ε) :
    1-4*Fintype.card V*Real.exp (-2*ε^2/((4*(d:ℝ)+3)^2*B.card))-
      4*Fintype.card U*Real.exp (-2*ε^2/((4*(d:ℝ)+3)^2*Fintype.card V))≤
      (FiniteLaw.pi (rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS)).probability
        (fun σ=>(∀ b v,|rawMarkedRestrictedSpokeRow π d σ g j b v B-(if b then t₀ else s₀)*B.card|<ε) ∧
          (∀ b u,|rawMarkedRestrictedSpokeCol π d σ g j b u A-(if b then t₀ else s₀)*A.card|<ε)) := by
  let μ := FiniteLaw.pi (rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS)
  have hmass (b : Bool) (u : U) : Sum.elim (q u) (s u) (if b then Sum.inl g else Sum.inr j)=if b then t₀ else s₀ := by
    cases b <;> simp [hg,hj]
  have hrow := rawIntervalSelectedLabelCountOn_common_event π d hd q hq hQ s hs hS hnoshort B hB
    (fun (i : Bool×V) (_ : V)=>if i.1 then Sum.inl g else Sum.inr j) (fun i=>{i.2})
    (by intro i x hx y hy hxy;simp only [Finset.mem_singleton] at hx hy;exact (hxy (hx.trans hy.symm)).elim)
    (fun i=>Finset.singleton_nonempty _) 1 (by omega) (by intro i;simp) ε hε
  have hcol := rawIntervalSelectedNeighbourCount_common_event π d hd q hq hQ s hs hS hnoshort hn
    (fun (i : Bool×U) (_ : U)=>if i.1 then Sum.inl g else Sum.inr j) (fun _=>A) (fun i=>{i.2})
    (fun i=>Finset.singleton_nonempty _) 1 (by omega) (by intro i;simp) ε hε
  simp only [Fintype.card_prod,Fintype.card_bool,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one,one_mul,
    Finset.prod_singleton,hmass,Finset.sum_const,nsmul_eq_mul] at hrow hcol
  let GoodR := fun (σ : RawIntervalFamilyOutcome V U Γ Color)=>∀ b v,|rawMarkedRestrictedSpokeRow π d σ g j b v B-(if b then t₀ else s₀)*B.card|<ε
  let GoodC := fun (σ : RawIntervalFamilyOutcome V U Γ Color)=>∀ b u,|rawMarkedRestrictedSpokeCol π d σ g j b u A-(if b then t₀ else s₀)*A.card|<ε
  have hR : 1-4*Fintype.card V*Real.exp (-2*ε^2/((4*(d:ℝ)+3)^2*B.card))≤μ.probability GoodR := by
    have he : 2*(Fintype.card V:ℝ)*(2*Real.exp (-2*ε^2/((4*(d:ℝ)+3)^2*B.card)))=
      4*Fintype.card V*Real.exp (-2*ε^2/((4*(d:ℝ)+3)^2*B.card)) := by ring
    rw [he] at hrow
    apply hrow.trans
    apply finiteLaw_probability_mono
    intro σ hσ b v
    simpa only [rawMarkedRestrictedSpokeRow,rawIntervalSelectedLabelCountOn,Finset.mem_singleton,forall_eq,mul_comm] using hσ (b,v)
  have hC : 1-4*Fintype.card U*Real.exp (-2*ε^2/((4*(d:ℝ)+3)^2*Fintype.card V))≤μ.probability GoodC := by
    have he : 2*(Fintype.card U:ℝ)*(2*Real.exp (-2*ε^2/((4*(d:ℝ)+3)^2*Fintype.card V)))=
      4*Fintype.card U*Real.exp (-2*ε^2/((4*(d:ℝ)+3)^2*Fintype.card V)) := by ring
    rw [he] at hcol
    apply hcol.trans
    apply finiteLaw_probability_mono
    intro σ hσ b u
    simpa only [rawMarkedRestrictedSpokeCol,rawIntervalSelectedNeighbourCount,Finset.mem_singleton,forall_eq,mul_comm] using hσ (b,u)
  exact (sub_le_sub_right hR _).trans (finiteLaw_good_intersection μ GoodR GoodC _ hC)

end Oberwolfach
