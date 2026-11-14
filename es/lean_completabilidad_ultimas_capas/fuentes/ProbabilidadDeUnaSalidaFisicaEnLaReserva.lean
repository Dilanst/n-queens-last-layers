import ExclusionFisicaDeLaPrimeraSalidaDeG
import PresupuestoDelErrorEnLaEscalaTemporal
namespace ArticuloA.Historias
open Repair RealFinita Trayectoria Trayectoria.ProfileKernel Real
open scoped NNReal BigOperators
noncomputable section
open Classical

def fallaElSeguimiento {n} (v : Cell n→ℝ≥0) (q : ℕ) (E : ℝ) (h : List (EstadoGuiado n)) : Prop :=
  ∃ t≤q,¬∃ l,estadoTrasPrefijo (some []) h t=some l ∧ sigueTableroYLineas v q t l E

theorem probabilidad_de_primera_salida {I : Type} [Fintype I] {n q : ℕ} (np : 0<n) (qp : 0<q)
    (qn : q≤n) (v : Cell n→ℝ≥0) (mass : ∑ e,(v e:ℝ)=q) (f : I→Cell n→ℝ) (i0 : I)
    (one : ∀ e,f i0 e=1) (fn : ∀ i e,0≤f i e) (ft : ∀ i e,f i e≤1)
    {η ν a : ℝ} (hp : 0<η) (h4 : η≤1/4) (v1 : 1≤ν) (a1 : 1≤a) (scale : a≤sqrt (q:ℝ))
    (cap : ∀ e,(v e:ℝ)≤ν/n) (slack : ∀ i e,(masaDeLineaG v i e:ℝ)≤1-η)
    (sm : (5/4)/(η*q)≤1/16) (tiny : (430*(ν/η^4)*a/sqrt q)*(1/η)^12≤1/10) :
    let E:=(430*(ν/η^4)*a/sqrt q)*(1/η)^12
    (avg masas (rutas (pasoDeG v q) 0 q (some [])) (mark masas (fallaElSeguimiento v q E))).val≤
      (Fintype.card (IndiceDeSeguimiento n I):ℝ)*(q+1)*(2*exp (-(a^2))) := by
  classical
  let J:=IndiceDeSeguimiento n I
  let U:=ν/(n:ℝ)
  let A:=430*(ν/η^4)*a/sqrt q
  let E:=A*(1/η)^12
  let S:J→ℝ:=escalaDelSalto n q η U
  let bad (h : List (EstadoGuiado n)):=∃ j : J,∃ r : Fin (q+1),
    2*S j*sqrt q*a≤|innovacionDePrefijo v q f j h r.val|
  have qr : 0<(q:ℝ):=by exact_mod_cast qp
  have nr : 0<(n:ℝ):=by exact_mod_cast np
  have vp : 0<ν:=by linarith
  have up : 0<U:=by dsimp [U]; positivity
  have an : 0≤a:=by linarith
  have An : 0≤A:=by dsimp [A]; positivity
  have h1 : η≤1:=by linarith
  have small : 1/(η*q)≤1/16:=(div_le_div_of_nonneg_right (by norm_num : (1:ℝ)≤5/4)
    (mul_nonneg hp.le qr.le)).trans sm
  have tail:=cola_fisica_de_todas_las_innovaciones np v qp f fn ft hp h1 up small cap slack an scale
  let Bw:=4*(n:ℝ)*(U/η^4)
  let Bz:=(11/10)*(6*(1/(η*q)))+3*(U/η^3)
  let cw:=2*Bw*sqrt q*a
  let cz:=2*Bz*sqrt q*a
  have czn : 0≤cz:=by dsimp [cz,Bz,U]; positivity
  obtain ⟨rr,wb,zb⟩:=presupuesto_de_resto_y_saltos (n:=(n:ℝ)) qr (by exact_mod_cast qn) hp h1 v1
  have budget : cw/q+cz+(22/10)*q*restoDePadre q η U≤A:=
    presupuesto_de_la_envolvente (by exact_mod_cast qp : (1:ℝ)≤q) (by positivity) a1 rr wb zb
  have incl (h : ℝ≥0×List (EstadoGuiado n)) (mem : h∈rutas (pasoDeG v q) 0 q (some [])) :
      fallaElSeguimiento v q E h.2→bad h.2:=by
    intro fail
    by_contra good
    have prefixBd (j : J) t (tq : t≤q) : |innovacionDePrefijo v q f j h.2 t|≤2*S j*sqrt q*a:=
      (lt_of_not_ge (fun ex=>good ⟨j,⟨t,by omega⟩,ex⟩)).le
    obtain ⟨path,len⟩:=rutas_siguen_su_ley _ _ _ _ h mem
    obtain ⟨t,tq,absent⟩:=fail
    obtain ⟨l,ep,err⟩:=no_hay_primera_salida_en_el_camino v qp f i0 one h.2 path len mass hp h4 up.le cap slack
      sm An tiny czn budget (prefixBd (.inl i0)) (fun s hs i z=>prefixBd (.inr (i,z)) s hs) t tq
    exact absent ⟨l,ep,ampliar_error_de_seguimiento v l err (techo_del_umbral qp tq hp h4 An)⟩
  have cmp:=avg_mono masas (rutas (pasoDeG v q) 0 q (some [])) (mark masas (fallaElSeguimiento v q E))
    (mark masas bad) (by
      intro h hm
      by_cases fail : fallaElSeguimiento v q E h.2
      · simp [mark,fail,incl h hm fail]
      · simp [mark,fail,masas])
  exact (NNReal.coe_le_coe.mpr cmp).trans tail

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.probabilidad_de_primera_salida
