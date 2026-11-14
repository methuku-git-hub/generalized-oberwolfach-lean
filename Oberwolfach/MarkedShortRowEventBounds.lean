module

public import Oberwolfach.MarkedSameDirectionDomains
public import Oberwolfach.MarkedTransformerRowBounds

@[expose] public section

/-! Read one- and two-arc intersections with up to two fixed hubs from
the simultaneous row event. All error terms retain the original outer
domain. The marginal arrays and the sampled outcome are unchanged. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [LinearOrder V] [DecidableEq U]

theorem marked_short_row_event_lower
    (P:SimpleGraph V) (π:Equiv.Perm V) (d h:ℕ) (hh:2≤h) (A:Finset V)
    (p k:ℝ) (q:U→Γ→ℝ) (s:U→Color→ℝ) (g:Γ) (j:Color) (ε γ pstar:ℝ)
    (hpstar:0<pstar) (hpstar1:pstar≤1) (hγ:0<γ)
    (hp:pstar≤p) (hk:pstar≤k) (hq:∀ u,pstar≤q u g) (hs:∀ u,pstar≤s u j)
    (hε:ε≤pstar^4*γ/4)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (hrows:MarkedRowsWithSpokes P π d h A p k q s g j (ε*A.card) σ H)
    (T:Finset (Bool×Bool×V)) (J:Finset (Bool×U)) (hT:T.card≤2) (hJ:J.card≤2)
    (hinj:Set.InjOn (fun a:Bool×U=>a.2) J)
    (hdom:γ*A.card/2≤((markedRowDomain P π (3*d) A T ∅).card:ℝ)):
    (pstar^4*γ/4)*A.card≤
      ((A.filter (fun z=>(∀ a∈T,rawMarkedPairRims P π d σ (markedRowRim a z))∧
        ∀ a∈J,H a.1 z a.2)).card:ℝ):=by
  have he:=hrows T ∅ J (hT.trans hh) (by simp) (hJ.trans hh) hinj
  have hlo:=(abs_lt.mp he).1
  apply marked_transformer_row_lower P π (3*d) (rawMarkedPairRims P π d σ) H A T J
    γ pstar p k ε (γ*A.card/2) (fun t u=>if t then q u g else s u j)
    hγ hpstar hpstar1 hp hk (by intro t u;cases t;exact hs u;exact hq u) hT hJ
    (by linarith only [hdom]) (le_refl _) hε
  change (∏ a∈T,if a.1 then k else p)*(∏ a∈J,if a.1 then q a.2 g else s a.2 j)*
    (markedRowDomain P π (3*d) A T ∅).card-ε*A.card≤
      markedRowCountWithSpokes P π d σ H (markedRowDomain P π (3*d) A T ∅) T J
  linarith only [hlo]


theorem marked_short_same_direction_row_bound
    (P:SimpleGraph V) (π:Equiv.Perm V) (d h:ℕ) (hh:2≤h) (A:Finset V) (hA:A.image π=A)
    (p k:ℝ) (q:U→Γ→ℝ) (s:U→Color→ℝ) (g:Γ) (j:Color) (ε γ pstar:ℝ)
    (hpstar:0<pstar) (hpstar1:pstar≤1) (hγ:0<γ) (hγ1:γ≤1)
    (hp:pstar≤p) (hk:pstar≤k) (hq:∀ u,pstar≤q u g) (hs:∀ u,pstar≤s u j)
    (hε:ε≤pstar^4*γ/4) (hloss:2*(2*(3*d:ℕ)+1:ℝ)≤γ*A.card/2)
    (hdeg:∀ x,(1/2+γ/2)*A.card≤((A∩P.neighborFinset x).card:ℝ))
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (hrows:MarkedRowsWithSpokes P π d h A p k q s g j (ε*A.card) σ H)
    (t a:Bool) (X:Finset V) (hX:X.card≤2) (J:Finset (Bool×U)) (hJ:J.card≤2)
    (hinj:Set.InjOn (fun a:Bool×U=>a.2) J):
    (pstar^4*γ/4)*A.card≤
      ((A.filter (fun z=>(∀ x∈X,rawMarkedPairRims P π d σ (markedRowRim (t,a,x) z))∧
        ∀ a∈J,H a.1 z a.2)).card:ℝ):=by
  have hdom:=marked_same_direction_set_domain_lower P π (3*d) A hA t a X hX γ hγ1 hdeg
  have hhdom:γ*A.card/2≤((markedRowDomain P π (3*d) A (markedSameDirectionSetRequests t a X) ∅).card:ℝ):=by
    push_cast at hloss hdom
    linarith only [hdom,hloss]
  have he:=marked_short_row_event_lower P π d h hh A p k q s g j ε γ pstar hpstar hpstar1 hγ
    hp hk hq hs hε σ H hrows (markedSameDirectionSetRequests t a X) J
    ((Finset.card_image_le).trans hX) hJ hinj hhdom
  simpa only [markedSameDirectionSetRequests,Finset.forall_mem_image] using he

end Oberwolfach
