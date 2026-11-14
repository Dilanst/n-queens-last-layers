import ExclusionFisicaDeLaPrimeraSalidaDeG
import DerivaDeUnaMarcaSobreElTableroSeguido
namespace ArticuloA.Historias
open Repair RealFinita Trayectoria Trayectoria.ProfileKernel Real
open scoped NNReal BigOperators
noncomputable section
open Classical

theorem marca_seguida_hasta_el_extremo {I : Type} {n q t : ℕ} (v : Cell n→ℝ≥0) (qp : 0<q)
    (f : I→Cell n→ℝ) (j : I) (fn : ∀ e,0≤f j e) (ft : ∀ e,f j e≤1)
    (h : List (EstadoGuiado n)) (path : transicionesDeCamino (pasoDeG v q) 0 (some []) h)
    (length : h.length=q) (tq : t≤q) (last : List (Cell n)) (ep : estadoTrasPrefijo (some []) h t=some last)
    {η U E cw : ℝ} (hp : 0<η) (h1 : η≤1) (up : 0≤U) (cap : ∀ e,(v e:ℝ)≤U)
    (slack : ∀ i e,(masaDeLineaG v i e:ℝ)≤1-η) (sm : (5/4)/(η*q)≤1/16)
    (en : 0≤E) (small : E≤1/10)
    (parents : ∀ s<t,∃ l,estadoTrasPrefijo (some []) h s=some l ∧ sigueTableroYLineas v q s l E)
    (bw : |innovacionDePrefijo v q f (.inl j) h t|≤cw) :
    |observacionFisica v q f (.inl j) t last-(∑ e,(v e:ℝ)*f j e)|/q≤
      cw/q+(11/10:ℝ)*(4*E/((9/10)*η)+q*restoDePadre q η U) := by
  let state:=estadoTrasPrefijo (some []) h
  let d (s : ℕ):=derivaFisica v q f (.inl j) s (state s)
  let bound:=(11/10:ℝ)*q*(4*(E/((9/10)*η*q))+restoDePadre q η U)
  have qr : 0<(q:ℝ):=by exact_mod_cast qp
  have rn : 0≤restoDePadre q η U:=by unfold restoDePadre; positivity
  have bn : 0≤bound:=by dsimp [bound]; positivity
  have safe s (st : s<t) : regionSeguraDelPaso v q s (state s):=by
    obtain ⟨p,eq,err⟩:=parents s st
    change state s=some p at eq
    rw [eq]
    exact regularidad_del_padre_fisico v qp (st.trans_le tq) p hp.le small slack err
  have per s (st : s<t) : |d s|≤bound:=by
    obtain ⟨p,eq,err⟩:=parents s st
    change state s=some p at eq
    dsimp [d]
    rw [eq]
    exact deriva_de_una_marca_tras_seguimiento v qp (st.trans_le tq) p f j fn ft hp h1 up cap slack sm small err
  have eq:=descomposicion_del_prefijo_fisico v qp f (.inl j) h (length.symm ▸ tq) path last ep trivial safe
  change innovacionDePrefijo v q f (.inl j) h t+(∑ s∈Finset.range t,d s)=
    observacionFisica v q f (.inl j) t last-pesoObservable _ (some []) at eq
  rw [masa_global_inicial] at eq
  have sb : |∑ s∈Finset.range t,d s|≤q*bound:=by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply (Finset.sum_le_sum (fun s (hs : s∈Finset.range t)=>per s (Finset.mem_range.mp hs))).trans
    simpa using mul_le_mul_of_nonneg_right (show (t:ℝ)≤q by exact_mod_cast tq) bn
  rw [←eq]
  apply (div_le_div_of_nonneg_right ((abs_add_le _ _).trans (add_le_add bw sb)) qr.le).trans
  apply le_of_eq
  dsimp [bound]
  field_simp [hp.ne',qr.ne']
  ring

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.marca_seguida_hasta_el_extremo
