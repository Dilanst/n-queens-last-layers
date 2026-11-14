import VariacionFisicaEnTodaHistoria
import DelHorizonteFisicoALaUltimaCapa
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
theorem camino_real_de_una_historia {n h T} (w : ColorWeights ℝ≥0) (i : ℝ≥0×List (State n))
    (mem : i∈rutas (kernel masas w (·⁻¹)) 0 T (initial n h)) (nz : i.1≠0)
    (u v : ℕ) (uv : u≤v) (vT : v≤T) :
    let X:=estadoEn (initial n h) i.2
    Legal (X u).physical ∧ Legal (X v).physical ∧
      ∃ r≤v-u,TerminalPath (X u).physical r (X v).physical := by
  intro X
  obtain ⟨_,chain⟩:=pasos_con_peso mem nz
  have good (j) (jj : j≤T) : coherent (X j) := by
    induction j with
    | zero => exact initial_coherent _ _
    | succ j ih =>
      obtain ⟨a,ha,_,eq⟩:=chain j (by omega)
      rw [←show a.2=X (j+1) from eq]
      exact (salto_del_contador_fisico w _ _ (ih (by omega)) a ha).1
  have segment (d : ℕ) (room : u+d≤T) :
      ∃ r≤d, TerminalPath (X u).physical r (X (u+d)).physical := by
    induction d with
    | zero => exact ⟨0,le_rfl,TerminalPath.start _⟩
    | succ d ih =>
      obtain ⟨r,rle,path⟩:=ih (by omega)
      obtain ⟨a,ha,_,eq⟩:=chain (u+d) (by omega)
      have coh:=good (u+d) (by omega)
      change a.2=X (u+d+1) at eq
      rw [←Nat.add_assoc,←eq]
      rw [Nat.zero_add] at ha
      rcases kernel_child masas w (·⁻¹) (u+d) (X (u+d)) a ha with same | ⟨choice,ad,child⟩
      · rw [same]; exact ⟨r,by omega,path⟩
      rw [child]
      cases choice with
      | virtual _ => exact ⟨r,by omega,path⟩
      | fail => exact ⟨r,by omega,path⟩
      | real e => exact ⟨r+1,by omega,TerminalPath.real path e coh.1 (choice_adm coh (.real e) ad)⟩
  exact ⟨(good u (by omega)).1,(good v vT).1,by
    simpa only [Nat.add_sub_of_le uv] using segment (v-u) (by omega)⟩

theorem error_terminal_inverso_de_una_historia {n hProc hObs T} (w : ColorWeights ℝ≥0)
    (i : ℝ≥0×List (State n)) (mem : i∈rutas (kernel masas w (·⁻¹)) 0 T (initial n hProc)) (nz : i.1≠0)
    (hn : 0<n) (u : ℕ) (uT : u≤T) (g : Cell n→ℝ) (W : ℝ) (wp : 0≤W) (cap : ∀ e,|g e|≤W)
    (size : pieces (estadoEn (initial n hProc) i.2 T).physical=n-hObs+1) :
    let X:=estadoEn (initial n hProc) i.2
    |Limites.Iobs n hObs g (X T).physical-inversasDelTablero (X u).physical g/(n:ℝ)^2|≤
      4*((↑(T-u):ℝ)/n)*W := by
  intro X
  obtain ⟨leg,last,r,bound,path⟩:=camino_real_de_una_historia w i mem nz u T uT le_rfl
  have e:=continuacion_fisica_desde_el_horizonte hn path leg last size g W wp cap
  exact e.trans (by gcongr)
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.camino_real_de_una_historia
#print axioms ArticuloA.Historias.error_terminal_inverso_de_una_historia
