module

public import Oberwolfach.OrdinaryFullHostSeedBounds
public import Oberwolfach.OrdinaryEditedParentWeightFromPotential
public import Oberwolfach.OrdinaryConflictFreeEditBounds

@[expose] public section
/-! The original fixed parent cycle weights and sampled potential-load
estimates supply wheel weights in the edited parent host. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
set_option synthInstance.maxSize 2048
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_edited_seed_weights_from_sample
    (P Q F:SimpleGraph V) (H₀ H:V→U→Prop) (r:ℕ) (hr:2≤r)
    (weight:OrdinaryCycle P r→ℝ) (pR pH ω pstar c B ε₀ εstar d:ℝ) (σ:Sym2 V→Bool)
    (hn:0<Fintype.card V) (hm:0<Fintype.card U) (hω:0<ω) (hp:0<pstar)
    (hUlo:ω*Fintype.card V≤Fintype.card U) (hUhi:Fintype.card U≤Fintype.card V)
    (hRlo:pstar≤pR) (hRhi:pR≤1) (hHlo:pstar≤pH) (hHhi:pH≤1)
    (hc:0≤c) (hB:0≤B) (hd:0≤d) (hQP:Q≤P\F)
    (hw:∀C,c/(Fintype.card V:ℝ)^(r-2)≤weight C ∧ weight C≤B/(Fintype.card V:ℝ)^(r-2))
    (hR:∀v,((changed ((retainedGraph P σ).neighborFinset v) (Q.neighborFinset v)).card:ℝ)≤d)
    (hRow:∀v,((changed (Finset.univ.filter (H₀ v)) (Finset.univ.filter (H v))).card:ℝ)≤d)
    (hCol:∀u,((changed (Finset.univ.filter (fun v=>H₀ v u)) (Finset.univ.filter (fun v=>H v u))).card:ℝ)≤d)
    (hRload:∀x y,P.Adj x y→¬F.Adj x y→
      |ordinaryPotentialLoad (ordinaryFullHostSeed (U:=U) P F r weight pR pH) (Sum.inl s(x,y)) (retainedGraph P σ\F) H₀-1|≤ε₀)
    (hSload:∀v u,
      |ordinaryPotentialLoad (ordinaryFullHostSeed (U:=U) P F r weight pR pH) (Sum.inr (v,u)) (retainedGraph P σ\F) H₀-1|≤ε₀)
    (hmargin:ε₀+8*(r:ℝ)^4*(B/(ω*pstar^(2*r-1)))*d/Fintype.card V≤εstar):
    ∃w:OrdinaryWheel Q F H r→ℝ,
      (∀W,c/(Fintype.card V:ℝ)^(r-1)≤w W ∧
        w W≤(B/(ω*pstar^(2*r-1)))/(Fintype.card V:ℝ)^(r-1)) ∧
      (∀x y,Q.Adj x y→|ordinaryRimLoad w x y-1|≤εstar) ∧
      (∀v u,H v u→|ordinarySpokeLoad w v u-1|≤εstar):=by
  let seed:=ordinaryFullHostSeed (U:=U) P F r weight pR pH
  let Bseed:=B/(ω*pstar^(2*r-1))
  have hBseed:0≤Bseed:=by dsimp [Bseed];positivity
  have hQF:Disjoint Q F:=by
    apply disjoint_iff_inf_le.mpr
    intro x y hxy
    exact (hQP hxy.1).2 hxy.2
  have hedit:=ordinary_conflict_free_edit_bounds (retainedGraph P σ) Q F H₀ H d hQF hR hRow hCol
  have hseed:∀W,c/(Fintype.card V:ℝ)^(r-1)≤seed W ∧ seed W≤Bseed/(Fintype.card V:ℝ)^(r-1):=by
    intro W
    exact ordinaryFullHostSeed_bounds P F r hr weight pR pH ω pstar c B hn hm hω hp hUlo hUhi
      hRlo hRhi hHlo hHhi hc hB hw W
  apply ordinary_edited_parent_weight_from_potential P (retainedGraph P σ\F) Q F H₀ H r hr hn hUhi
    seed c Bseed ε₀ εstar d hc hBseed hd (hQP.trans sdiff_le) hseed hedit.1 hedit.2.1 hedit.2.2
  · intro x y hxy
    exact hRload x y (hQP hxy).1 (hQP hxy).2
  · intro v u _
    exact hSload v u
  · exact hmargin
end Oberwolfach
