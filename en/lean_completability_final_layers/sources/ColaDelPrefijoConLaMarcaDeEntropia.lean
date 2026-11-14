import ProbabilidadDeUnaSalidaFisicaEnLaReserva
import B2EnCadaPrefijoFisicoDeLaMismaHistoria
import ProbabilidadDeUnaLineaVivaAntesDelCorte
import UnaLeyParaTodasLasRaicesYTiempos
namespace ArticuloA.Historias
open Repair RealFinita Trayectoria Trayectoria.ProfileKernel Real
open scoped NNReal BigOperators
noncomputable section
open Classical

def prefijoParaEntropia {I : Type} {n} (v : Cell n→ℝ≥0) (q : ℕ) (f : I→Cell n→ℝ)
    (j : I) (η E : ℝ) (t : ℕ) (hist : List (EstadoGuiado n)) : Prop :=
  prefijoRegular (guardaDelErrorFisico v q E) 0 (some []) hist ∧
  ∃ l,ultimoEstado (some []) hist=some l ∧ sigueTableroYLineas v q t l E ∧
    |observacionFisica v q f (.inl j) t l-(∑ e,(v e:ℝ)*f j e)|/q≤8*E/η

theorem cola_del_prefijo_con_una_marca_real {I : Type} [Fintype I] {n q : ℕ} (np : 0<n) (qp : 0<q)
    (qn : q≤n) (v : Cell n→ℝ≥0) (mass : ∑ e,(v e:ℝ)=q) (f : I→Cell n→ℝ) (i0 : I)
    (jmark : I) (s : ℕ) (sq : s≤q) (one : ∀ e,f i0 e=1) (fn : ∀ i e,0≤f i e) (ft : ∀ i e,f i e≤1)
    {η ν a : ℝ} (hp : 0<η) (h4 : η≤1/4) (v1 : 1≤ν) (a1 : 1≤a) (scale : a≤sqrt (q:ℝ))
    (cap : ∀ e,(v e:ℝ)≤ν/n) (slack : ∀ i e,(masaDeLineaG v i e:ℝ)≤1-η)
    (sm : (5/4)/(η*q)≤1/16) (tiny : (430*(ν/η^4)*a/sqrt q)*(1/η)^12≤1/10) :
    let E:=(430*(ν/η^4)*a/sqrt q)*(1/η)^12
    (avg masas (rutas (pasoDeG v q) 0 s (some [])) (mark masas (fun hist=>¬prefijoParaEntropia v q f jmark η E s hist))).val≤
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
  let pred (h : List (EstadoGuiado n)):=prefijoParaEntropia v q f jmark η E s h
  have success (a' : ℝ≥0×List (EstadoGuiado n)) (mem : a'∈rutas (pasoDeG v q) 0 q (some []))
      (good : ¬bad a'.2) : pred (a'.2.take s):=by
    have pb (j : J) t (tq : t≤q) : |innovacionDePrefijo v q f j a'.2 t|≤2*S j*sqrt q*a:=
      (lt_of_not_ge (fun ex=>good ⟨j,⟨t,by omega⟩,ex⟩)).le
    obtain ⟨path,len⟩:=rutas_siguen_su_ley _ _ _ _ a' mem
    have all:=no_hay_primera_salida_en_el_camino v qp f i0 one a'.2 path len mass hp h4 up.le cap slack sm
      An tiny czn budget (pb (.inl i0)) (fun t ht i z=>pb (.inr (i,z)) t ht)
    have get t (tq : t≤q) : ∃ l,estadoTrasPrefijo (some []) a'.2 t=some l ∧ sigueTableroYLineas v q t l E:=by
      obtain ⟨l,ep,err⟩:=all t tq
      exact ⟨l,ep,ampliar_error_de_seguimiento v l err (techo_del_umbral qp tq hp h4 An)⟩
    obtain ⟨l,ep,err⟩:=get s sq
    have en : 0≤E:=by dsimp [E]; positivity
    have rn : 0≤restoDePadre q η U:=by unfold restoDePadre; positivity
    have ae : A≤E:=le_mul_of_one_le_right An (one_le_pow₀ ((one_le_div hp).mpr h1))
    have w : 0≤cw:=by dsimp [cw,Bw]; positivity
    have cost:=costo_de_una_marca_en_funcion_del_error hp h1 qr w czn rn ae budget
    refine ⟨seguridad_hasta_el_ultimo_salto 0 (some []) a'.2 s ?_,l,(extremo_del_prefijo _ _ _).trans ep,err,?_⟩
    · intro i lt
      obtain ⟨u,eq,bd⟩:=get i (lt.le.trans sq)
      simpa only [Nat.zero_add,eq,guardaDelErrorFisico] using bd
    · exact (marca_seguida_hasta_el_extremo v qp f jmark (fn _) (ft _) a'.2 path len sq l ep hp h1 up.le cap slack sm
          en tiny (fun t ht=>get t (ht.le.trans sq)) (pb (.inl jmark) s sq)).trans cost
  have eq:=probabilidad_del_prefijo (pasoDeG v q) (G_es_ley v q) (mark masas (fun h=>¬pred h)) (some []) 0 s q sq
  change (avg masas (rutas (pasoDeG v q) 0 s (some [])) (mark masas (fun h=>¬pred h))).val≤_
  rw [←eq]
  apply le_trans (NNReal.coe_le_coe.mpr (avg_mono masas _ _ (mark masas bad) ?_)) tail
  intro h mem
  by_cases yes : bad h.2
  · by_cases ok : pred (h.2.take s) <;> simp [mark,masas,yes,ok]
  · simp [mark,masas,yes,success h mem yes]
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.cola_del_prefijo_con_una_marca_real
