module

public import Oberwolfach.OrderedOrdinaryLoadBound
public import Oberwolfach.OrderedOrdinaryPairBound
public import Oberwolfach.OrderedOrdinaryLocality
public import Oberwolfach.ResourcePatternConcentration

@[expose] public section
/-! Concentration from the ordinary-wheel size, load, and pair bounds. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
  {m b:ℕ} {π:Equiv.Perm V}

 theorem orderedOrdinary_supported_tail (hm:2≤m) (hn:0<Fintype.card V) (hu:Fintype.card U≤Fintype.card V)
    (w:OrderedOrdinaryWheel (U:=U) π b (m+1)→ℝ) (B:ℝ) (hB:0<B)
    (hw:∀ W,0≤w W ∧ w W≤B/(Fintype.card V:ℝ)^m)
    {J:Type} [Fintype J] [DecidableEq J] {Base:J→Type} [∀ e,Fintype (Base e)]
    (μ:∀ e,FiniteLaw (Base e)) (S:((V×V)⊕(V×U))→Finset J)
    (state:(∀ e,Base e)→((V×V)⊕(V×U))→Bool)
    (hs:∀ a σ τ,(∀ e∈S a,σ e=τ e)→state σ a=state τ a)
    (L:ℝ) (hL:0<L) (hread:∀ a,((S a).card:ℝ)≤L)
    (haffect:∀ e,((Finset.univ.filter (fun a=>e∈S a)).card:ℝ)≤L)
    (root:(V×V)⊕(V×U)) (t:ℝ) (ht:0<t):
    (FiniteLaw.pi μ).probability (fun σ=>t≤
      |resourcePatternLoad orderedOrdinaryResources w (fun _ _=>true) root (state σ)-
        (FiniteLaw.pi μ).expectation (fun τ=>resourcePatternLoad orderedOrdinaryResources w (fun _ _=>true) root (state τ))|)≤
      2*Real.exp (-2*t^2/(L^2*(((m:ℝ)+1)^3*B/Fintype.card V)*(2*((m:ℝ)+1))*(((m:ℝ)+1)^2*B))):=by
  have hn0:(0:ℝ)<Fintype.card V:=by exact_mod_cast hn
  have hh:=resourcePatternLoad_supported_tail μ orderedOrdinaryResources w (fun W=>(hw W).1)
    (fun _ _=>true) S state hs L hL hread haffect root
    (2*((m:ℝ)+1)) (((m:ℝ)+1)^2*B) (((m:ℝ)+1)^3*B/Fintype.card V) (by positivity) (by positivity) (by positivity)
    (by
      intro W _
      have hc:=Finset.card_le_card (Finset.sdiff_subset : orderedOrdinaryResources W\{root}⊆orderedOrdinaryResources W)
      exact_mod_cast hc.trans (orderedOrdinaryResources_card W))
    (orderedOrdinary_root_load_bound hm hn hu w B hB.le hw root)
    (orderedOrdinary_omitted_pair_bound hm hn hu w B hB.le hw root) t ht
  exact hh
end Oberwolfach
