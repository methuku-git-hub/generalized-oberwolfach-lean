module

public import Oberwolfach.OrdinaryAdaptiveNonrootReserve

@[expose] public section
/-! Add any deterministically constructed packing input to the adaptive
reserve event on the same ambient physical coins. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_adaptive_nonroot_reserve_to_input (q:ℕ) (ε:ℝ) (hε:0<ε):
    ∃N:ℕ,∀(V U Ω:Type) [Fintype V] [Fintype U] [Fintype Ω] [DecidableEq V] [DecidableEq U],
      ∀(μ:FiniteLaw Ω) (E:Ω→Prop) (e₀ δ:ℝ),0≤δ→1-e₀≤μ.probability E→
      ∀(T:Ω→Finset V) (W:Ω→Finset U),
      let A:=fun s=>↥(Finset.univ\T s);let B:=fun s=>↥(Finset.univ\W s);
      ∀(Q:∀s,SimpleGraph (A s)) (H:∀s,A s→B s→Prop) (I:∀s,Finset (A s)) (J:∀s,Finset (B s))
        (Input:∀s,(Sym2 (A s⊕B s)→Bool)→Prop),
      (∀s,E s→N≤Fintype.card (A s⊕B s))→
      (∀s,E s→1/(Fintype.card (A s⊕B s):ℝ)^q≤δ)→
      ∀(τ:ℝ) (hτ:0≤τ) (hτ1:τ≤1),
      (∀s,E s→∀σ,OrdinaryBoundaryReserveGood (Q s) (H s) (I s) (J s) τ ε σ→Input s σ)→
      let ν:=FiniteLaw.pi (fun _:Sym2 (V⊕U)=>FiniteLaw.retentionCoin τ hτ hτ1);
      1-(e₀+δ)≤(μ.sigma (fun _=>ν)).probability (fun z=>E z.1 ∧ Input z.1
          (fun e=>z.2 (Sym2.map ((⟨Subtype.val,Subtype.val_injective⟩:A z.1↪V).sumMap
            (⟨Subtype.val,Subtype.val_injective⟩:B z.1↪U)) e))):=by
  obtain ⟨N,hN⟩:=ordinary_adaptive_nonroot_reserve_high_probability q ε hε
  refine ⟨N,?_⟩
  intro V U Ω _ _ _ _ _ μ E e₀ δ hδ hE T W A B Q H I J Input hsize hbound τ hτ hτ1 hinput ν
  have hh:=hN V U Ω μ E e₀ δ hδ hE T W Q H I J hsize hbound τ hτ hτ1
  apply hh.trans
  apply finiteLaw_probability_mono
  intro z hz
  exact ⟨hz.1,hinput z.1 hz.1 _ hz.2⟩
end Oberwolfach
