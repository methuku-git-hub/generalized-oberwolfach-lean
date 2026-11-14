module

public import Oberwolfach.OrdinaryBoundaryReserveJointEvent
public import Oberwolfach.TwoStageEvents
public import Oberwolfach.ProductFailureBounds
public import Oberwolfach.FiniteProductProjection

@[expose] public section
/-! Sample a boundary reserve after adaptive root selection using the same
ambient physical coins; the induced coordinates are an injective projection. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_adaptive_nonroot_reserve_high_probability (q:ℕ) (ε:ℝ) (hε:0<ε):
    ∃N:ℕ,∀(V U Ω:Type) [Fintype V] [Fintype U] [Fintype Ω] [DecidableEq V] [DecidableEq U],
      ∀(μ:FiniteLaw Ω) (E:Ω→Prop) (e₀ δ:ℝ),0≤δ→1-e₀≤μ.probability E→
      ∀(T:Ω→Finset V) (W:Ω→Finset U),
      let A:=fun s=>↥(Finset.univ\T s);let B:=fun s=>↥(Finset.univ\W s);
      ∀(Q:∀s,SimpleGraph (A s)) (H:∀s,A s→B s→Prop) (I:∀s,Finset (A s)) (J:∀s,Finset (B s)),
      (∀s,E s→N≤Fintype.card (A s⊕B s))→
      (∀s,E s→1/(Fintype.card (A s⊕B s):ℝ)^q≤δ)→
      ∀(τ:ℝ) (hτ:0≤τ) (hτ1:τ≤1),
      let ν:=FiniteLaw.pi (fun _:Sym2 (V⊕U)=>FiniteLaw.retentionCoin τ hτ hτ1);
      1-(e₀+δ)≤(μ.sigma (fun _=>ν)).probability (fun z=>E z.1 ∧
        OrdinaryBoundaryReserveGood (Q z.1) (H z.1) (I z.1) (J z.1) τ ε
          (fun e=>z.2 (Sym2.map ((⟨Subtype.val,Subtype.val_injective⟩:A z.1↪V).sumMap
            (⟨Subtype.val,Subtype.val_injective⟩:B z.1↪U)) e))):=by
  obtain ⟨N,hN⟩:=ordinary_boundary_reserve_joint_high_probability q ε hε
  refine ⟨N,?_⟩
  intro V U Ω _ _ _ _ _ μ E e₀ δ hδ hE T W A B Q H I J hsize hbound τ hτ hτ1 ν
  have hP:μ.probability E≤1:=finiteLaw_probability_le_one' μ E
  have hconditional:∀s,E s→1-δ≤ν.probability (fun σ=>
      OrdinaryBoundaryReserveGood (Q s) (H s) (I s) (J s) τ ε
        (fun e=>σ (Sym2.map ((⟨Subtype.val,Subtype.val_injective⟩:A s↪V).sumMap
          (⟨Subtype.val,Subtype.val_injective⟩:B s↪U)) e))):=by
    intro s hs
    let φ:A s↪V:=⟨Subtype.val,Subtype.val_injective⟩
    let ψ:B s↪U:=⟨Subtype.val,Subtype.val_injective⟩
    let f:Sym2 (A s⊕B s)→Sym2 (V⊕U):=Sym2.map (φ.sumMap ψ)
    have hf:Function.Injective f:=Sym2.map.injective (φ.sumMap ψ).injective
    have hp:=hN (A s) (B s) (hsize s hs) (Q s) (H s) (I s) (J s) τ hτ hτ1
    have hproj:=finiteLaw_pi_injective_projection_event
      (fun _:Sym2 (V⊕U)=>FiniteLaw.retentionCoin τ hτ hτ1) f hf
      (OrdinaryBoundaryReserveGood (Q s) (H s) (I s) (J s) τ ε)
    change 1-δ≤ν.probability (fun σ=>OrdinaryBoundaryReserveGood (Q s) (H s) (I s) (J s) τ ε (fun e=>σ (f e)))
    rw [hproj]
    linarith [hbound s hs]
  have ht:=finiteLaw_twoStage_survival μ (fun _=>ν) E
    (fun s σ=>OrdinaryBoundaryReserveGood (Q s) (H s) (I s) (J s) τ ε
      (fun e=>σ (Sym2.map ((⟨Subtype.val,Subtype.val_injective⟩:A s↪V).sumMap
        (⟨Subtype.val,Subtype.val_injective⟩:B s↪U)) e))) δ hconditional
  have hm:δ*μ.probability E≤δ:=by nlinarith only [hδ,hP]
  nlinarith only [ht,hm,hE]
end Oberwolfach
