import DelReveladoAlLog
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Data.Fin.Rev
open scoped BigOperators
namespace ArticuloA.Revelado
noncomputable section
open Classical
variable {N : ℕ}
def despues (t : Fin N) := Finset.univ.filter (fun r : Fin N => t<r)

theorem tamano_despues (t : Fin N) : (despues t).card=t.rev.val := by
  have eq : despues t=Finset.Ioi t := by ext r; simp [despues]
  rw [eq,Fin.card_Ioi,Fin.val_rev]; omega

private theorem peso_fibra (t p : Fin N) (T : Finset (Fin N))
    (mem : T∈(Finset.univ.erase p).powersetCard t.rev.val) :
    (Fintype.card {s : Equiv.Perm (Fin N) // s t=p ∧ (despues t).image s=T}:ℝ)/N.factorial =
    1 / ((N:ℝ)*(((Finset.univ.erase p).powersetCard t.rev.val).card:ℝ)) := by
  obtain ⟨sub,sz⟩ := Finset.mem_powersetCard.mp mem
  have hp : p∉T := fun h => (Finset.mem_erase.mp (sub h)).1 rfl
  unfold despues
  rw [masa_rango_y_conjunto t p T hp ((tamano_despues t).trans sz.symm)]
  rw [Finset.card_powersetCard,Finset.card_erase_of_mem (Finset.mem_univ p),Finset.card_univ,Fintype.card_fin,sz]
  have le : t.rev.val≤N-1 := by have := t.rev.isLt; omega
  have npos : 0<N := Nat.zero_lt_of_lt t.isLt
  have prod : N*((N-1).choose t.rev.val)*((N-1-t.rev.val).factorial*t.rev.val.factorial)=N.factorial := by
    rw [show N*((N-1).choose t.rev.val)*((N-1-t.rev.val).factorial*t.rev.val.factorial)=
      N*((N-1).choose t.rev.val*t.rev.val.factorial*(N-1-t.rev.val).factorial) by ring,
      Nat.choose_mul_factorial_mul_factorial le]
    cases N with
    | zero => omega
    | succ m => simp [Nat.factorial_succ]
  apply (div_eq_div_iff (by exact_mod_cast (Nat.factorial_pos N).ne')
    (mul_ne_zero (by exact_mod_cast npos.ne') (by exact_mod_cast (Nat.choose_pos le).ne'))).mpr
  rw [one_mul,mul_comm]
  exact_mod_cast (by simpa only [mul_assoc] using prod)

theorem ordenar_una_posicion (t : Fin N) (f : Fin N→ Finset (Fin N)→ℝ) :
    (∑ s : Equiv.Perm (Fin N),f (s t) ((despues t).image s))/N.factorial =
      (∑ p,porRango (Finset.univ.erase p) t.rev.val (f p))/(N:ℝ) := by
  let S := fun p : Fin N => (Finset.univ.erase p).powersetCard t.rev.val
  let U := despues t
  let d := fun (s : Equiv.Perm (Fin N)) (p : Fin N) (T : Finset (Fin N)) =>
    if s t=p ∧ U.image s=T then (1:ℝ) else 0
  have mem (s : Equiv.Perm (Fin N)) : U.image s∈S (s t) := by
    apply Finset.mem_powersetCard.mpr
    refine ⟨?_,(Finset.card_image_of_injective _ s.injective).trans (tamano_despues t)⟩
    intro y hy; obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hy
    exact Finset.mem_erase.mpr ⟨fun eq => (ne_of_gt (Finset.mem_filter.mp hr).2) (s.injective eq),Finset.mem_univ _⟩
  have one (s : Equiv.Perm (Fin N)) : (∑ p,∑ T∈S p,d s p T*f p T)=f (s t) (U.image s) := by
    rw [Finset.sum_eq_single (s t)]
    · simp [d,mem s]
    · intro p _ neq; exact Finset.sum_eq_zero (fun T _ => by simp [d,Ne.symm neq])
    · simp
  have cardinal (p : Fin N) (T : Finset (Fin N)) :
      ∑ s,d s p T=(Fintype.card {s : Equiv.Perm (Fin N) // s t=p ∧ U.image s=T}:ℝ) := by
    unfold d
    rw [← Finset.sum_filter]
    simp [Fintype.card_subtype]
  calc
    _ = (∑ s,∑ p,∑ T∈S p,d s p T*f p T)/N.factorial := by simp_rw [one]; rfl
    _ = (∑ p,∑ T∈S p, ((∑ s,d s p T)/(N.factorial:ℝ))*f p T) := by
      rw [Finset.sum_comm,Finset.sum_div]
      apply Finset.sum_congr rfl; intro p _
      rw [Finset.sum_comm,Finset.sum_div]
      apply Finset.sum_congr rfl; intro T _
      rw [←Finset.sum_mul]; ring
    _ = _ := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl; intro p _
      unfold porRango
      rw [Finset.sum_div,Finset.sum_div]
      apply Finset.sum_congr rfl; intro T h
      rw [cardinal,peso_fibra t p T h]; ring
/-- Average over the entire uniform order, counted once per marked piece. -/
theorem media_del_orden (f : Fin N→ Finset (Fin N)→ℝ) :
    (∑ s : Equiv.Perm (Fin N), ∑ t,f (s t) ((despues t).image s))/N.factorial =
    (∑ p,∑ m ∈ Finset.range N,porRango (Finset.univ.erase p) m (f p))/(N:ℝ) := by
  rw [Finset.sum_comm,Finset.sum_div]
  simp_rw [ordenar_una_posicion]
  rw [←Finset.sum_div,Finset.sum_comm]
  apply congrArg (fun z : ℝ => z/N)
  apply Finset.sum_congr rfl; intro p _
  let a := fun (m : ℕ) => porRango (Finset.univ.erase p) m (f p)
  have rev := Equiv.sum_comp (@Fin.revPerm N) (fun t : Fin N => a t.val)
  exact rev.trans (Fin.sum_univ_eq_sum_range a N)

theorem cota_del_orden (f : Fin N→ Finset (Fin N)→ℝ) (b : Fin N→ℝ)
    (cap : ∀ p, (∑ m ∈ Finset.range N,porRango (Finset.univ.erase p) m (f p))≤b p) :
    (∑ s : Equiv.Perm (Fin N), ∑ t,f (s t) ((despues t).image s))/N.factorial ≤ (∑ p,b p)/(N:ℝ) := by
  rw [media_del_orden]
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun p _ => cap p)) (Nat.cast_nonneg N)
end
end ArticuloA.Revelado
#print axioms ArticuloA.Revelado.media_del_orden
#print axioms ArticuloA.Revelado.cota_del_orden
#print axioms ArticuloA.Revelado.ordenar_una_posicion
