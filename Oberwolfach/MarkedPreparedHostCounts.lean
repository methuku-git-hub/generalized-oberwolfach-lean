module

public import Oberwolfach.MarkedShortRowEventBounds
public import Oberwolfach.MarkedIndexExtensionApplication
public import Oberwolfach.MarkedHostExtensionCounts

@[expose] public section

/-! The actual simultaneous row and index estimates imply every count
used by the marked absorber. This is a deterministic consequence of one
realised event, uniform over all later roots and choices of up to two hubs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color E K:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [LinearOrder V] [DecidableEq U]

def markedSameTypeHubRequests (k:Bool) (B:Finset U):Finset (Bool×U):=B.image (fun u=>(k,u))

theorem marked_same_type_hubs_injective (k:Bool) (B:Finset U):
    Set.InjOn (fun a:Bool×U=>a.2) (markedSameTypeHubRequests k B):=by
  intro a ha e he h
  obtain ⟨u,hu,rfl⟩:=Finset.mem_image.mp ha
  obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp he
  exact congrArg (fun u=>(k,u)) h

theorem marked_prepared_host_counts
    (P:SimpleGraph V) (π:Equiv.Perm V) (d l:ℕ)
    (p k:ℝ) (q:U→Γ→ℝ) (s:U→Color→ℝ) (g:Γ) (j:Color) (ε γ pstar:ℝ)
    (hpstar:0<pstar) (hpstar1:pstar≤1) (hγ:0<γ) (hγ1:γ≤1)
    (hp:pstar≤p) (hk:pstar≤k) (hq:∀ u,pstar≤q u g) (hs:∀ u,pstar≤s u j)
    (hε:ε≤pstar^4*γ/4) (hεh:ε≤pstar^(l+11)/2)
    (hloss:2*(2*(3*d:ℕ)+1:ℝ)≤γ*Fintype.card V/2)
    (hdeg:∀ x,(1/2+γ/2)*Fintype.card V≤(P.degree x:ℝ))
    (σ:RawMarkedOutcome V U Γ Color) (H₀ HK:V→U→Prop)
    (tail head:E→V) (ktail khead:K→V)
    (harcs:∀ t x y,markedArcPresent tail head ktail khead t x y↔
      rawMarkedPairRims P π d σ (if t then Sum.inr (x,y) else Sum.inl (x,y)))
    (hrows:MarkedRowsWithSpokes P π d (l+11) Finset.univ p k q s g j (ε*Fintype.card V) σ
      (fun t v u=>if t then HK v u else H₀ v u))
    (hindices:MarkedIndicesWithSpokes π d (l+11) Finset.univ q s g j (ε*Fintype.card U) σ
      (fun t v u=>if t then HK v u else H₀ v u)):
    MarkedHostExtensionCounts tail head ktail khead H₀ HK π (3*d) l
      ((pstar^4*γ/4)*Fintype.card V) ((pstar^(l+11)/2)*Fintype.card U):=by
  let H:Bool→V→U→Prop:=fun t v u=>if t then HK v u else H₀ v u
  have hdeg':∀ x,(1/2+γ/2)*(Finset.univ:Finset V).card≤
      (((Finset.univ:Finset V)∩P.neighborFinset x).card:ℝ):=by simpa using hdeg
  have hrow':MarkedRowsWithSpokes P π d (l+11) Finset.univ p k q s g j
      (ε*(Finset.univ:Finset V).card) σ H:=by simpa only [Finset.card_univ] using hrows
  have hsame (t a z:Bool) (X:Finset V) (hX:X.card≤2) (B:Finset U) (hB:B.card≤2):
      ((pstar^4*γ/4)*Fintype.card V)≤
      ((Finset.univ.filter (fun v=>(∀ x∈X,if a then markedArcPresent tail head ktail khead t v x
        else markedArcPresent tail head ktail khead t x v)∧markedSpokesTo H₀ HK z B v)).card:ℝ):=by
    have he:=marked_short_same_direction_row_bound P π d (l+11) (by omega) Finset.univ (by simp)
      p k q s g j ε γ pstar hpstar hpstar1 hγ hγ1 hp hk hq hs hε
      (by simpa using hloss) hdeg' σ H hrow' t a X hX (markedSameTypeHubRequests z B)
      (Finset.card_image_le.trans hB) (marked_same_type_hubs_injective z B)
    cases a <;> simpa only [Finset.card_univ,markedRowRim,ite_false,ite_true,Bool.false_eq_true,
      markedSameTypeHubRequests,Finset.forall_mem_image,←harcs,H,markedSpokesTo] using he
  constructor
  · intro t z x B hB
    simpa using hsame t false z {x} (by simp) B hB
  · intro t z x B hB
    simpa using hsame t true z {x} (by simp) B hB
  · intro z x y B hxy hB
    simpa [and_assoc] using hsame false false z {x,y} ((Finset.card_insert_le _ _).trans (by simp)) B hB
  · intro t z x y B hxy hB
    simpa [and_assoc] using hsame t true z {x,y} ((Finset.card_insert_le _ _).trans (by simp)) B hB
  · intro z x y B hxy hB
    have hdom:=marked_two_extension_domain_lower P π (3*d) Finset.univ false x y (by simpa using hxy) γ hγ1 hdeg'
    have hdom':γ*(Finset.univ:Finset V).card/2≤
        ((markedRowDomain P π (3*d) Finset.univ (markedTwoExtensionRequests false x y) ∅).card:ℝ):=by
      simp only [Finset.card_univ] at hdom ⊢
      linarith only [hdom,hloss]
    have he:=marked_short_row_event_lower P π d (l+11) (by omega) Finset.univ p k q s g j ε γ pstar
      hpstar hpstar1 hγ hp hk hq hs hε σ H hrow' (markedTwoExtensionRequests false x y)
      (markedSameTypeHubRequests z B) (by simp [markedTwoExtensionRequests])
      (Finset.card_image_le.trans hB) (marked_same_type_hubs_injective z B) hdom'
    simpa only [Finset.card_univ,markedTwoExtensionRequests,Finset.forall_mem_insert,Finset.mem_singleton,forall_eq,
      markedRowRim,ite_false,ite_true,Bool.false_eq_true,markedSameTypeHubRequests,
      Finset.forall_mem_image,H,markedSpokesTo,←harcs,and_assoc] using he
  · intro A Q hAQ hsize hsep
    have hsize':(A∪Q).card≤l+11:=by rwa [Finset.card_union_of_disjoint hAQ]
    have he:=marked_index_event_extension_lower π d (l+11) Finset.univ q s g j pstar ε hpstar hpstar1
      (fun u _=>hq u) (fun u _=>hs u) hεh σ H hindices A Q hAQ hsize' (by
        intro x hx y hy hne
        exact hsep x (by simpa using hx) y (by simpa using hy) hne)
    simpa only [common,Finset.mem_filter,Finset.mem_univ,true_and,Finset.card_univ,H,
      ite_false,ite_true,Bool.false_eq_true,Finset.filter_filter,and_assoc] using he

end Oberwolfach
