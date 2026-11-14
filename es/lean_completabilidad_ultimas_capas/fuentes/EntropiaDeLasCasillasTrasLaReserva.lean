import NormalizacionFisicaDeLaReserva
namespace ArticuloA.Historias
open Repair Limites Real
open scoped BigOperators
noncomputable section
open Classical

def aporteCelda (x : ℝ) : ℝ := -x*log x
def entropiaCeldas {n} (w : Cell n→ℝ) : ℝ := ∑ e : Cell n,aporteCelda (w e)

theorem aporte_no_excede_uno {x : ℝ} (hx : 0≤x) : aporteCelda x≤1 := by
  rcases hx.eq_or_lt with h|h
  · simp [aporteCelda,←h]
  · have a:=log_le_sub_one_of_pos (inv_pos.mpr h)
    rw [log_inv] at a
    have b:=mul_le_mul_of_nonneg_left a h.le
    rw [mul_sub,mul_inv_cancel₀ h.ne',mul_one] at b
    unfold aporteCelda
    linarith only [b,h]

theorem aporte_borrado_a_escala_n {n : ℕ} (np : 0<(n:ℝ)) {x : ℝ} (p : 0≤x) :
    aporteCelda x ≤ 2*x*log n+1/(n:ℝ)^2 := by
  rcases p.eq_or_lt with z|xp
  · simp [←z,aporteCelda]
  · have nn : 0<(n:ℝ)^2:=sq_pos_of_pos np
    have a:=aporte_no_excede_uno (mul_nonneg nn.le xp.le)
    unfold aporteCelda at a ⊢
    rw [log_mul nn.ne' xp.ne',Real.log_pow] at a
    norm_num only [Nat.cast_ofNat] at a
    apply le_of_mul_le_mul_right _ nn
    have id : (2*x*log n+1/(n:ℝ)^2)*(n:ℝ)^2=2*x*log n*(n:ℝ)^2+1 := by field_simp [np.ne']
    rw [id]
    linarith only [a]

theorem entropia_al_escalar {n} (w : Cell n→ℝ) (factor : ℝ) (lp : 0<factor) :
    entropiaCeldas (fun e=>factor*w e)=factor*entropiaCeldas w-factor*log factor*(∑ e : Cell n,w e) := by
  unfold entropiaCeldas
  rw [Finset.mul_sum,Finset.mul_sum,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro e _
  by_cases z : w e=0
  · simp [z,aporteCelda]
  · unfold aporteCelda
    rw [log_mul lp.ne' z]
    ring

theorem perdida_de_entropia_en_las_celdas {n : ℕ} (np : 0<(n:ℝ)) (w : Cell n→ℝ) (u : LineaReservable n→Bool)
    (q X : ℝ) (pos : ∀ e,0≤w e) (cap : ∀ e,w e≤1) (mass : (∑ e : Cell n,w e)=q)
    (ret : (∑ e : Cell n,pesoRetenido w u e)=X) (xp : 0<X) (loss : X≤q) (two : q/X≤2) :
    entropiaCeldas w-entropiaCeldas (fun e=>(q/X)*pesoRetenido w u e)≤2*(q-X)*log n+1+2*(q-X) := by
  let y:=pesoRetenido w u
  let b (e : Cell n):=if quedaTrasReserva u e then 0 else w e
  have part (e : Cell n) : y e+b e=w e := by by_cases h : quedaTrasReserva u e <;> simp [y,b,pesoRetenido,h]
  have split (e : Cell n) : aporteCelda (y e)+aporteCelda (b e)=aporteCelda (w e) := by
    by_cases h : quedaTrasReserva u e <;> simp [y,b,pesoRetenido,h,aporteCelda]
  have val : (∑ e : Cell n,b e)=q-X := by
    have a : (∑ e : Cell n,(y e+b e))=∑ e : Cell n,w e := Finset.sum_congr rfl (fun e _=>part e)
    rw [Finset.sum_add_distrib,mass] at a; change (∑ e,y e)=X at ret; linarith only [a,ret]
  have eq : entropiaCeldas y+entropiaCeldas b=entropiaCeldas w := by
    unfold entropiaCeldas; rw [←Finset.sum_add_distrib]; exact Finset.sum_congr rfl (fun e _=>split e)
  have eb (e : Cell n) : aporteCelda (b e)≤2*b e*log n+1/(n:ℝ)^2 := by
    apply aporte_borrado_a_escala_n np; dsimp [b]; split <;> simp [pos]
  have sum:=Finset.sum_le_sum (s:=Finset.univ) (fun e _=>eb e)
  have rhs : (∑ e : Cell n,(2*b e*log n+1/(n:ℝ)^2))=2*(q-X)*log n+1 := by
    rw [Finset.sum_add_distrib,←Finset.sum_mul,←Finset.mul_sum,val]
    simp [Cell,Fintype.card_prod,pow_two,np.ne']; field_simp [np.ne']
  rw [rhs] at sum
  have ge : 1≤q/X := (le_div_iff₀ xp).mpr (by simpa using loss)
  have posq : 0<q := xp.trans_le loss
  have hy : 0≤entropiaCeldas y := by
    apply Finset.sum_nonneg; intro e _
    by_cases keep : quedaTrasReserva u e
    · simp only [y,pesoRetenido,if_pos keep,aporteCelda]
      exact mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr (pos e)) (log_nonpos (pos e) (cap e))
    · simp [y,pesoRetenido,keep,aporteCelda]
  have eqx : (q/X)*X=q := div_mul_cancel₀ q xp.ne'
  have pen := mul_le_mul_of_nonneg_left (log_le_sub_one_of_pos (div_pos posq xp)) posq.le
  have ex : q*(q/X-1)=(q/X)*(q-X) := by field_simp [xp.ne']
  rw [ex] at pen
  have pr := pen.trans (mul_le_mul_of_nonneg_right two (sub_nonneg.mpr loss))
  change entropiaCeldas w-entropiaCeldas (fun e=>(q/X)*y e)≤_
  rw [entropia_al_escalar _ _ (div_pos posq xp),show (∑ e : Cell n,y e)=X from ret]
  have prod : q/X*log (q/X)*X=q*log (q/X) := by rw [mul_right_comm,eqx]
  rw [prod]
  change entropiaCeldas b≤_ at sum
  linarith only [eq,sum,pr,mul_le_mul_of_nonneg_right ge hy]

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.perdida_de_entropia_en_las_celdas
