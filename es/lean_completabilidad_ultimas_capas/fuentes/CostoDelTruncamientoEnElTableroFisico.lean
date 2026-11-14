import EntropiaAcumuladaDeLasEleccionesDelTablero
namespace ArticuloA.Historias
open Repair RealFinita Trayectoria Trayectoria.ProfileKernel Real
open scoped NNReal BigOperators
noncomputable section
open Classical

def marcaLogaritmica (a v : ℝ) : ℝ := log (max 1 (a*v))

theorem truncamiento_de_un_peso {a v : ℝ} (ap : 0<a) (vn : 0≤v) :
    v*marcaLogaritmica a v≤v*log v+v*log a+1/a := by
  by_cases zero : v=0
  · subst v; simp [ap.le]
  have vp:=lt_of_le_of_ne vn (Ne.symm zero)
  have uv:=mul_pos ap vp
  have l:=Real.log_mul ap.ne' vp.ne'
  by_cases cut : 1≤a*v
  · rw [marcaLogaritmica,max_eq_right cut,l]
    linarith only [mul_add v (log a) (log v),one_div_nonneg.mpr ap.le]
  · rw [marcaLogaritmica,max_eq_left (le_of_not_ge cut),Real.log_one,mul_zero]
    have lg:=Real.log_le_sub_one_of_pos (inv_pos.mpr uv)
    rw [Real.log_inv,l] at lg
    have cost:=mul_le_mul_of_nonneg_left lg vn
    have cancel : v*(a*v)⁻¹=1/a:=by field_simp; ring
    rw [mul_sub,mul_one,cancel] at cost
    linarith only [cost,mul_add v (log a) (log v),vn,mul_neg v (log a+log v)]

theorem truncamiento_agregado_de_la_entrada {n q : ℕ} (hn : 0<n) (v : Cell n→ℝ≥0)
    (mass : ∑ e,(v e:ℝ)=q) :
    (∑ e,(v e:ℝ)*marcaLogaritmica ((n:ℝ)^2) (v e))≤
      (∑ e,(v e:ℝ)*log (v e:ℝ))+(q:ℝ)*log ((n:ℝ)^2)+1 := by
  have nr : 0<(n:ℝ):=by exact_mod_cast hn
  have bd:=Finset.sum_le_sum (s:=(Finset.univ : Finset (Cell n)))
    (fun e _=>truncamiento_de_un_peso (a:=(n:ℝ)^2) (sq_pos_of_pos nr) (NNReal.coe_nonneg (v e)))
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib,←Finset.sum_mul,mass] at bd
  have total : (∑ _e : Cell n,(1:ℝ)/(n:ℝ)^2)=1:=by
    simp [Cell,Fintype.card_prod,nsmul_eq_mul,pow_two,nr.ne']; field_simp
  rwa [total] at bd

theorem entropia_de_celda_y_marca_truncada {X : Type} [Fintype X] (p v : X→ℝ)
    {a : ℝ} (ap : 0<a) (pn : ∀ e,0≤p e) (norm : ∑ e,p e=1) (vn : ∀ e,0≤v e)
    (support : ∀ e,v e=0→p e=0) :
    log a-(∑ e,p e*marcaLogaritmica a (v e))≤ -(∑ e,p e*log (v e)) := by
  have each e : p e*(log a+log (v e))≤p e*marcaLogaritmica a (v e):=by
    by_cases zero : v e=0
    · simp [support e zero]
    · rw [←Real.log_mul ap.ne' zero]
      apply mul_le_mul_of_nonneg_left _ (pn e)
      exact Real.log_le_log (mul_pos ap (lt_of_le_of_ne (vn e) (Ne.symm zero))) (le_max_right _ _)
  have s:=Finset.sum_le_sum (s:=Finset.univ) (fun e _=>each e)
  simp_rw [mul_add] at s
  rw [Finset.sum_add_distrib,←Finset.sum_mul,norm,one_mul] at s
  linarith only [s]
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.truncamiento_agregado_de_la_entrada
#print axioms ArticuloA.Historias.entropia_de_celda_y_marca_truncada
