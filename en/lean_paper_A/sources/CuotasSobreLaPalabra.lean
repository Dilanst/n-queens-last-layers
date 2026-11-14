import CuotasDelEstado
import ConcentracionCoordenadaE2
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.ProfileKernel E2 RealFinita E2.Regular
noncomputable section
variable {n q : ℕ}

def cuotaLetra (bs : List Bool) (i : Fin bs.length) : ℝ :=
  (((bs.drop i.val).count bs[i.val]:ℕ):ℝ)/(bs.drop i.val).length

theorem producto_palabra (bs : List Bool) : ∏ i,cuotaLetra bs i = productoCuotas bs := by
  induction bs with
  | nil => simp [productoCuotas]
  | cons b bs ih =>
    change (∏ i : Fin (bs.length+1),cuotaLetra (b::bs) i)=_
    rw [Fin.prod_univ_succ]
    have eq (i : Fin bs.length) : cuotaLetra (b::bs) i.succ=cuotaLetra bs i := by
      simp [cuotaLetra]
    simp_rw [eq]
    rw [ih]
    rfl

def cuotaElegida (x : State n) (v : Pieza n) : ℝ≥0 :=
  quota masas x (·⁻¹) (if esReal v then x.reals else x.virtuals)

theorem cuota_como_fraccion (x : State n) (a : ℕ) :
    (quota masas x (·⁻¹) a).val = (a:ℝ)/((x.reals+x.virtuals:ℕ):ℝ) := by
  change ((ns masas x.reals+ns masas x.virtuals)⁻¹*ns masas a:ℝ≥0).val=_
  simp [ns_real,div_eq_mul_inv,mul_comm]

private theorem extension (xs : List Bool) : xs.count true+xs.count false=xs.length := by
  induction xs with
  | nil => rfl
  | cons b xs ih => cases b <;> simp [List.count_cons] at * <;> omega

theorem cuotas_reales_del_camino (H : Historia n q) (h : ℕ) (lev : q=n-h) :
    ∏ t, (cuotaElegida (estado H h t.val) (secuencia H t)).val = masaPalabra n q := by
  have len : (palabra H).length=2*n-1 := by simp [palabra,lista]
  let perm : Indice n ≃ Fin (palabra H).length := finCongr len.symm
  have elem (t : Indice n) : (palabra H)[t.val]'(by simpa only [len] using t.isLt)=esReal (secuencia H t) := by simp [palabra,lista]
  have step (t : Indice n) :
      (cuotaElegida (estado H h t.val) (secuencia H t)).val=cuotaLetra (palabra H) (perm t) := by
    obtain ⟨hr,hv,_⟩ := cuotas_del_estado H h lev t.val t.isLt.le
    unfold cuotaElegida
    rw [cuota_como_fraccion,hr,hv,extension]
    unfold cuotaLetra
    change _ = (((((palabra H).drop t.val).count ((palabra H)[t.val]'(by simpa only [len] using t.isLt))):ℕ):ℝ)/_
    rw [elem]
    cases esReal (secuencia H t) <;> rfl
  calc _ = ∏ t, cuotaLetra (palabra H) (perm t) := Finset.prod_congr rfl (fun t _ => step t)
       _ = ∏ i, cuotaLetra (palabra H) i := perm.prod_comp _
       _ = _ := (producto_palabra _).trans (cuotas_de_la_historia H)
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.cuotas_reales_del_camino
