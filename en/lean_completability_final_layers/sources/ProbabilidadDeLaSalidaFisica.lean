import DerivaCentradaAntesDelCorte
import ParadaFisicaPorDesviacion
import DeLaDerivaALaSalida
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte
noncomputable section
open Classical

def cruzaElUmbral {n} (p : FactoresContinuos) (h T : ℕ) (um : ℝ≥0) (l : List (ℕ×State n)) : Prop :=
  ∃ s≤T,um≤errorDelEstado p h (estadoEn (0,initial n h) l s).2 (fraccionAntes n s)

theorem probabilidad_de_salida_desde_el_tablero {n h : ℕ} {p : FactoresContinuos} {κ m ζ C um : ℝ≥0} {L : ℝ}
    (hn : 2≤n) (hh : h≤n) (sp : ControlEspacial p κ m L) (kp : 0<κ) (m1 : 1≤m)
    (zp : 0<ζ) (bal : BalanceMalla n h p C) (hu : um/n≤piso κ ζ) (ho : 2*C/n≤piso κ ζ)
    (halt : ℕ→State n→Bool) (sigue : ∀ j X,errorDelEstado p h X (fraccionAntes n j)<um → halt j X=false)
    (T : ℕ) (tN : T≤2*n-1) (floor : ζ≤fraccionAntes n T)
    (θ g : ℝ) (θ0 : 0≤θ) (small : θ*limiteSalto (m^4) m≤1) (g0 : 0≤g)
    (margin : (g+1)*Real.exp (T*((coefSeguimiento m κ ζ C:ℝ)/n))<um) :
    let S:=pasoParado (coloresDelPerfil n h p) halt
    let R:=rutas S 0 T (0,initial n h)
    (avg masas R (mark masas (cruzaElUmbral p h T um))).val ≤
      (6+4*(↑(2*n-1):ℝ))*(T+1)*(2*Real.exp (T*(θ*limiteSalto (m^4) m)^2-θ*g)) := by
  intro S R
  let x:ℕ×State n:=(0,initial n h)
  let w:=coloresDelPerfil n h p
  let Y:=(fun (l : List (ℕ×State n)) j => estadoEn x l j)
  let K:=coefSeguimiento m κ ζ C
  let evento:=fun l => ∃ b : ℝ≥0,(b,l)∈R ∧ b≠0 ∧ cruzaElUmbral p h T um l
  have pos : 0<n := by omega
  have sub:=misma_masa_en_el_soporte R (cruzaElUmbral p h T um) evento (fun i mem nz yes => ⟨i.1,mem,nz,yes⟩)
  apply (NNReal.coe_le_coe.mpr sub).trans
  apply salida_por_deriva pos.ne' (vInicial p) w halt x T (m^4) m (cota_de_un_peso sp)
    (fun t y _ f j hj _ => cap_virtual_fisico pos hh sp m1 f ⟨j,hj⟩)
    θ g ((K:ℝ)/n) um θ0 small g0 (by positivity) margin evento
  intro atom _ hab
  obtain ⟨b,mem,nz,hit⟩:=hab
  let l:=atom.2
  let E:=fun t => errorDelEstado p h (Y l t).2 (fraccionAntes n t)
  have ex : ∃ t,t≤T ∧ um≤E t := hit
  let s:=Nat.find ex
  have se : s≤T ∧ um≤E s := Nat.find_spec ex
  have before (t : ℕ) (ts : t<s) : E t<um := by
    apply lt_of_not_ge; intro le; exact Nat.find_min ex ts ⟨by omega,le⟩
  have path:=hasta_el_primer_cruce hn hh sp kp m1 zp bal hu ho halt sigue T floor (b,l) mem nz s se.1 before
  let blancoT:=fun (c : Activa n) t => (blanco (n:=n) p h (coordenada c) (fraccionAntes n t):ℝ)
  let D:=fun c => derivaEn S (medidaCoord (vInicial p) w (coordenada c) 0) (blancoT c) x l
  refine ⟨s,fun t => (E t:ℝ),D,se.1,NNReal.coe_le_coe.mpr se.2,?_,?_⟩
  · intro c t ts
    let y:=Y l t
    obtain ⟨yt,ok,num⟩:=path.2 t ts.le
    change y.1=t at yt
    have reg:=el_maximo_da_seguimiento p h y.2 _ (reloj_de_las_cuotas hn num)
    have lt:=before t ts
    have he : E t/n≤piso κ ζ := (div_le_div_of_nonneg_right lt.le (zero_le _)).trans hu
    have go : halt y.1 y.2=false := by rw [yt]; exact sigue t y.2 lt
    have drift:=deriva_centrada_fisica hn hh sp kp m1 zp (fraccion_antes_del_horizonte (ts.le.trans se.1) floor)
      (fraccion_a_lo_sumo_uno hn t) bal he ho y.2 reg y.1 ok (fraccion_disminuye (by omega : t<2*n-1))
      (coordenada c) (dentro_del_maximo p h y.2 _ c)
    have row:=media_del_paso_activo p h y.2 y.1 t halt go (coordenada c)
    change |(avg masas (S t y) (fun b => lectura p h b.2 (coordenada c))).val - lectura p h y.2 (coordenada c) -
      (blancoT c (t+1)-blancoT c t)|≤_
    rw [row]; calc _ ≤ (K*(E t+1)/n).val := drift
                   _ = _ := by
                     change (↑(K*(E t+1)/n):ℝ)=_; simp only [NNReal.coe_div,NNReal.coe_mul,NNReal.coe_natCast,NNReal.coe_add,NNReal.coe_one]; ring
  · intro t ts
    obtain ⟨c,eq⟩:=error_alcanzado p h (Y l t).2 (fraccionAntes n t)
    refine ⟨c,le_of_eq ?_⟩
    have ini : blancoT c 0=(medidaCoord (vInicial p) w (coordenada c) 0 x:ℝ) := by
      simp only [blancoT,blanco,fraccion_al_empezar hn,one_pow,mul_one]; rfl
    have rep:=error_real_en_prefijo (vInicial p) w halt (coordenada c) (blancoT c) x l t
      (by rw [path.1]; omega) ini
    exact (congrArg NNReal.toReal eq).trans (congrArg abs rep)

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.probabilidad_de_salida_desde_el_tablero
