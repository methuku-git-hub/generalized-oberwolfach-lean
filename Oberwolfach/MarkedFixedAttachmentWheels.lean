module

public import Oberwolfach.MarkedFixedAttachmentPaths
public import Oberwolfach.MarkedRootedPathCycles
public import Oberwolfach.PermutationConflictDegree
public import Oberwolfach.MarkedPathParent

@[expose] public section

/-! Construct a vertex-wheel pair through the assigned attachments and
hub. Their old spokes and attachment arcs are used without replacement. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [DecidableEq V]

 theorem marked_fixed_attachment_wheels
    (tail head:E→V) (ktail khead:K→V) (H₀ HK:V→U→Prop)
    (π:Equiv.Perm V) (b l:ℕ) (hl:2≤l) (v v' a z:V) (u:U) (j:Bool)
    (W Z:Finset V) (hv:v∈Z) (hv':v'∈Z)
    (haW:a∉W) (hzW:z∉W) (haZ:a∉Z) (hzZ:z∉Z)
    (haz:¬PermutationClose π b a z)
    (haF:∀ x∈Z,¬PermutationClose π b a x) (hzF:∀ x∈Z,¬PermutationClose π b z x)
    (hsp:H₀ a u∧H₀ z u)
    (hroot:if j then HK v u∧HK v' u else H₀ v u∧H₀ v' u)
    (hopen:(∃ e,tail e=v∧head e=a)∧(∃ e,tail e=v'∧head e=a))
    (hclose:if j then (∃ e,ktail e=z∧khead e=v)∧(∃ e,ktail e=z∧khead e=v')
      else (∃ e,tail e=z∧head e=v)∧(∃ e,tail e=z∧head e=v'))
    (c:ℝ)
    (hstep:∀ t:Bool,∀ x,c≤((Finset.univ.filter (fun y=>
      (if t then ∃ e,ktail e=x∧khead e=y else ∃ e,tail e=x∧head e=y)∧
      (if t then HK y u else H₀ y u))).card:ℝ))
    (hjoin:∀ x y,x≠y→c≤((Finset.univ.filter (fun q=>(∃ e,tail e=x∧head e=q)∧
      (∃ e,tail e=q∧head e=y)∧H₀ q u)).card:ℝ))
    (hbudget:W.card+((Z.card:ℝ)+l+4)*(2*b+1)<c):
    ∃ p:Fin (l+3)↪V,∃ A D:MarkedWheel tail head ktail khead (l+3) π b H₀ HK,
      p 0=a∧p (Fin.last (l+2))=z∧A.2.val=u∧D.2.val=u∧
      (∀ i,A.1.val i=rootedCycleOrder (markedRootOrder (l+3) j) v p i)∧
      (∀ i,D.1.val i=rootedCycleOrder (markedRootOrder (l+3) j) v' p i)∧
      (∀ i,p i∉W∧p i∉Z∧∀ x∈Z,¬PermutationClose π b (p i) x)∧
      PermutationSeparated π b p:=by
  let F:=permutationConflictGraph π b
  have hF:∀ x,(F.degree x:ℝ)≤2*b:=by intro x;exact_mod_cast permutationConflictGraph_degree_le π b x
  obtain ⟨p,hp0,hplast,hpa,hspoke,hav,hsep⟩:=marked_path_between_attachments F
    (fun x y=>∃ e,tail e=x∧head e=y) (fun x y=>∃ e,ktail e=x∧khead e=y)
    H₀ HK u u j W Z l hl a z (fun he=>haz (Or.inl he)) (fun he=>haz he.2)
    haW hzW haZ hzZ (fun x hx he=>haF x hx he.2) (fun x hx he=>hzF x hx he.2)
    ⟨hsp.1,hsp.1⟩ ⟨hsp.2,hsp.2⟩ (2*b) c (by positivity) hF
    (by intro t x;simpa only [and_self] using hstep t x)
    (by intro x y hxy;simpa only [and_self] using hjoin x y hxy) hbudget
  have hfree:PermutationSeparated π b p:=by
    intro i k hik hc
    exact hsep i k ⟨fun he=>hik (p.injective he),hc⟩
  have hout (i:Fin (l+3)) (x:V) (hx:x∈Z):¬PermutationClose π b (p i) x:=by
    intro hc
    exact (hav i).2.2 x hx ⟨fun he=>(hav i).2.1 (he ▸ hx),hc⟩
  have hcons (x:V) (hx:x∈Z):PermutationSeparated π b (Fin.cons x p):=
    permutationSeparated_cons π b x p hfree (fun i he=>hout i x hx ((permutationClose_symm π b x (p i)).mp he))
  have ho₁:∃ e,tail e=v∧head e=p 0:=by rw [hp0];exact hopen.1
  have ho₂:∃ e,tail e=v'∧head e=p 0:=by rw [hp0];exact hopen.2
  have hc₁:if j then ∃ e,ktail e=p (Fin.last (l+2))∧khead e=v else ∃ e,tail e=p (Fin.last (l+2))∧head e=v:=by
    rw [hplast];cases j <;> exact hclose.1
  have hc₂:if j then ∃ e,ktail e=p (Fin.last (l+2))∧khead e=v' else ∃ e,tail e=p (Fin.last (l+2))∧head e=v':=by
    rw [hplast];cases j <;> exact hclose.2
  have hr₁:if j then HK v u else H₀ v u:=by cases j <;> exact hroot.1
  have hr₂:if j then HK v' u else H₀ v' u:=by cases j <;> exact hroot.2
  have hs:∀ i,if j=false∧i.val=2 then HK (p i) u else H₀ (p i) u:=by
    intro i
    have hh:=hspoke i
    split_ifs at hh ⊢ <;> exact hh.1
  obtain ⟨A,hAu,hA⟩:=marked_wheel_from_rooted_path tail head ktail khead (l+2) (by omega)
    π b H₀ HK j v u p (hcons v hv) ho₁ hc₁ hpa hr₁ hs
  obtain ⟨D,hDu,hD⟩:=marked_wheel_from_rooted_path tail head ktail khead (l+2) (by omega)
    π b H₀ HK j v' u p (hcons v' hv') ho₂ hc₂ hpa hr₂ hs
  exact ⟨p,A,D,hp0,hplast,hAu,hDu,hA,hD,fun i=>⟨(hav i).1,(hav i).2.1,hout i⟩,hfree⟩

end Oberwolfach
