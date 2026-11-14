import LineasQueMatanElPatron
open scoped NNReal
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical

def naceDelPar {n} (X : State n) (e f : Cell n) (o v j l : Bool) (a : Choice n) (primera : Bool) : Prop :=
  if primera then o=true ∧ bornHere e a ∧ patronInverso X e f false v j l
  else v=true ∧ bornHere f a ∧ patronInverso X e f o false j l

private theorem nacimiento_ausente {n} (X : State n) (e : Cell n) (a : Choice n)
    (fresh : admissible X a) (new : bornHere e a) : ¬estadoFuente X e true := by
  cases a with
  | fail => exact new.elim
  | virtual _ => exact new.elim
  | real c => change e=c at new; subst c; exact fresh

/-- The true one-transition balance for any of the sixteen marks, before averaging.
The positive excess corrects counting one killed pattern once per line hit. -/
theorem balance_del_paso_inverso {n} (X : State n) (e f : Cell n) (o v j l : Bool) (a : Choice n)
    (ok : compatible e f) (coh : coherent X) (live : allowed X a) :
    let U:=patronInverso X e f o v j l
    let d:=deathsOn (diez e f) (golpeDelPar e f o v j l a)
    indicator (patronInverso (next X a) e f o v j l)+indicator U*d =
      indicator U+indicator (naceDelPar X e f o v j l a true)+indicator (naceDelPar X e f o v j l a false)+
      indicator U*(d-1) := by
  intro U d
  let B₁:=naceDelPar X e f o v j l a true
  let B₂:=naceDelPar X e f o v j l a false
  have step : patronInverso (next X a) e f o v j l ↔ (U ∧ d=0) ∨ B₁ ∨ B₂ := by
    rw [paso_exacto_del_patron X e f o v j l a ok coh live,supervivencia_equivale_a_cero]
    rfl
  have fresh:=choice_adm coh a live
  have no₁ (old : U) (b : B₁) : False := by
    change o=true ∧ bornHere e a ∧ _ at b
    exact nacimiento_ausente X e a fresh b.2.1 (b.1 ▸ old.1)
  have no₂ (old : U) (b : B₂) : False := by
    change v=true ∧ bornHere f a ∧ _ at b
    exact nacimiento_ausente X f a fresh b.2.1 (b.1 ▸ old.2.1)
  have disj (b : B₁) (c : B₂) : False := by
    change o=true ∧ bornHere e a ∧ _ at b
    change v=true ∧ bornHere f a ∧ _ at c
    obtain ⟨_,el,_⟩:=b
    obtain ⟨_,fl,_⟩:=c
    cases a with
    | fail => exact el.elim
    | virtual _ => exact el.elim
    | real z => exact ok.1 (congrArg Prod.fst (el.trans fl.symm))
  change indicator _+indicator U*d=indicator U+indicator B₁+indicator B₂+indicator U*(d-1)
  by_cases old : U
  · have nb : ¬B₁ := no₁ old
    have nc : ¬B₂ := no₂ old
    by_cases zero : d=0
    · simp [indicator,step,old,nb,nc,zero]
    · simp [indicator,step,old,nb,nc,zero]; omega
  · by_cases b : B₁
    · have nc : ¬B₂ := disj b
      simp [indicator,step,old,b,nc]
    · simp [indicator,step,old,b]

theorem resto_del_paso_ponderado {n h : ℕ} {p : FactoresContinuos} {κ m ζ z C E : ℝ≥0} {L : ℝ}
    (hn : 2≤n) (hh : h≤n) (sp : ControlEspacial p κ m L) (kp : 0<κ) (m1 : 1≤m)
    (zp : 0<ζ) (hz : ζ≤z) (z1 : z≤1) (bal : BalanceMalla n h p C)
    (he : E/n≤piso κ ζ) (ho : 2*C/n≤piso κ ζ) (X : State n) (reg : Seguimiento h p X z E)
    (leg : Legal X.physical) (o v j l : Bool) :
    let row:=choices masas X (coloresDelPerfil n h p) (·⁻¹)
    (pesoDeUnaFuente n o*pesoDeUnaFuente n v)*masas.sum (soporteDeParejas X o v j l)
      (fun u => meanN masas row (fun a => deathsOn (diez u.1 u.2) (golpeDelPar u.1 u.2 o v j l a)-1))≤
      45*(m^4/piso κ ζ+4*(m^4/(piso κ ζ)^4)) :=
  doble_borrado_sumado hn hh sp kp m1 zp hz z1 bal he ho X reg leg o v j l
    (fun u => golpeDelPar u.1 u.2 o v j l) (fun _ _ _ hit => hit.1)
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.balance_del_paso_inverso
#print axioms ArticuloA.Historias.resto_del_paso_ponderado
