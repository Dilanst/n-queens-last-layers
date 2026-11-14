import B2EnCadaPrefijoFisicoDeLaMismaHistoria
import PresupuestoDelErrorEnLaEscalaTemporal
namespace ArticuloA.Historias
open Repair RealFinita Trayectoria Trayectoria.ProfileKernel Real
open scoped NNReal BigOperators
noncomputable section
open Classical

def cotaDeSalidaDeB2 {n} (v : Cell n→ℝ≥0) (q : ℕ) (S : Cell n→Cell n→Prop) (d : ℝ≥0) (a : ℝ) : Prop :=
  (avg masas (rutas (pasoDeG v q) 0 q (some []))
    (mark masas (fun h=>¬prefijoRegular (condicionDeSeguimientoG v q S d) 0 (some []) h))).val≤
      (Fintype.card (IndiceDeSeguimiento n (Option (Cell n))):ℝ)*(q+1)*(2*exp (-(a^2)))

theorem cola_fisica_de_B2 {n q : ℕ} (np : 0<n) (qp : 0<q) (qn : q≤n) (v : Cell n→ℝ≥0)
    (mass : ∑ e,(v e:ℝ)=q) (S : Cell n→Cell n→Prop) (d : ℝ≥0)
    (marks : ∀ z,(d:ℝ)*q≤∑ e,(v e:ℝ)*(mark masas (S z) e).val)
    {η ν a : ℝ} (hp : 0<η) (h4 : η≤1/4) (v1 : 1≤ν) (a1 : 1≤a) (scale : a≤sqrt (q:ℝ))
    (cap : ∀ e,(v e:ℝ)≤ν/n) (slack : ∀ i e,(masaDeLineaG v i e:ℝ)≤1-η)
    (sm : (5/4)/(η*q)≤1/16) (tiny : (430*(ν/η^4)*a/sqrt q)*(1/η)^12≤1/80)
    (mt : 8*((430*(ν/η^4)*a/sqrt q)*(1/η)^12)/η≤(d:ℝ)/16) :
    cotaDeSalidaDeB2 v q S d a := by
  classical
  let I:=Option (Cell n)
  let f : I→Cell n→ℝ:=fun i e=>match i with
    | none=>1
    | some z=>(mark masas (S z) e).val
  have fn i e : 0≤f i e:=by cases i with
    | none=>exact zero_le_one
    | some z=>exact NNReal.coe_nonneg _
  have ft i e : f i e≤1:=by cases i with
    | none=>exact le_rfl
    | some z=>by_cases yes : S z e <;> simp [f,mark,masas,yes]
  let U:=ν/(n:ℝ)
  let J:=IndiceDeSeguimiento n I
  let B:J→ℝ:=escalaDelSalto n q η U
  let bad (h : List (EstadoGuiado n)):=∃ j : J,∃ r : Fin (q+1),2*B j*sqrt q*a≤|innovacionDePrefijo v q f j h r.val|
  have qr : 0<(q:ℝ):=by exact_mod_cast qp
  have nr : 0<(n:ℝ):=by exact_mod_cast np
  have vp : 0<ν:=by linarith
  have up : 0<U:=by dsimp [U]; positivity
  have an : 0≤a:=by linarith
  have h1 : η≤1:=by linarith
  have small : 1/(η*q)≤1/16:=(div_le_div_of_nonneg_right (by norm_num : (1:ℝ)≤5/4)
    (mul_nonneg hp.le qr.le)).trans sm
  have tail:=cola_fisica_de_todas_las_innovaciones np v qp f fn ft hp h1 up small cap slack an scale
  let cw:=2*(4*(n:ℝ)*(U/η^4))*sqrt q*a
  let cz:=2*((11/10)*(6*(1/(η*q)))+3*(U/η^3))*sqrt q*a
  have wn : 0≤cw:=by dsimp [cw]; positivity
  have zn : 0≤cz:=by dsimp [cz]; positivity
  obtain ⟨rr,wb,zb⟩:=presupuesto_de_resto_y_saltos (n:=(n:ℝ)) qr (by exact_mod_cast qn) hp h1 v1
  have budget : cw/q+cz+(22/10)*q*restoDePadre q η U≤430*(ν/η^4)*a/sqrt q:=
    presupuesto_de_la_envolvente (by exact_mod_cast qp : (1:ℝ)≤q) (by positivity) a1 rr wb zb
  let guard:=prefijoRegular (condicionDeSeguimientoG v q S d) 0 (some [])
  have incl h (mem : h∈rutas (pasoDeG v q) 0 q (some [])) : ¬guard h.2→bad h.2:=by
    intro failed
    by_contra good
    have b (j : J) t (tq : t≤q) : |innovacionDePrefijo v q f j h.2 t|≤2*B j*sqrt q*a:=
      (lt_of_not_ge (fun ex=>good ⟨j,⟨t,by omega⟩,ex⟩)).le
    obtain ⟨path,len⟩:=rutas_siguen_su_ley _ _ _ _ h mem
    exact failed (B2_sobre_el_mismo_camino v qp f none (fun _=>rfl) fn ft S some (fun _ _=>rfl) d marks h.2
      path len mass hp h4 up.le cap slack sm (by positivity) wn zn tiny mt budget
      (fun t ht i=>b (.inl i) t ht) (fun t ht i z=>b (.inr (i,z)) t ht))
  have cmp:=avg_mono masas (rutas (pasoDeG v q) 0 q (some [])) (mark masas (fun h=>¬guard h)) (mark masas bad) (by
    intro h hm
    by_cases no : ¬guard h.2
    · simp [mark,no,incl h hm no]
    · simp [mark,no,masas])
  exact (NNReal.coe_le_coe.mpr cmp).trans tail
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.cola_fisica_de_B2
