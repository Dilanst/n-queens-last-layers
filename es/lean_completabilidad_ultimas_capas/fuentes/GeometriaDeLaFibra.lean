import IndicesFisicosDelPerfil
open scoped BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2
noncomputable section

def inicioR (n j : ℕ) := j-(n-1)
def inicioC (n j : ℕ) := (n-1)-j
def longitudFibra (n j : ℕ) := n-max (inicioR n j) (inicioC n j)
def verticeOblicuo (anti : Bool) : Fin 4 := if anti then 3 else 2
abbrev Fibra (n : ℕ) (anti : Bool) (j : Indice n) :=
  {e : Cell n // lines e (verticeOblicuo anti)=j.val}

theorem extremos_fibra {n : ℕ} (hn : 0<n) (j : Indice n) :
    inicioR n j.val<n ∧ inicioC n j.val<n ∧
    inicioR n j.val+longitudFibra n j.val≤n ∧ inicioC n j.val+longitudFibra n j.val≤n ∧
    0<longitudFibra n j.val ∧ longitudFibra n j.val≤n := by
  have hj := j.isLt; change j.val<2*n-1 at hj
  simp only [inicioR,inicioC,longitudFibra]
  omega

def columnaOrientada (n : ℕ) (a : Bool) (c : ℕ) := if a then n-1-c else c

theorem etiqueta_fibra {n : ℕ} (e : Cell n) (a : Bool) (j : Indice n) :
    lines e (verticeOblicuo a)=j.val ↔
      e.1.val+inicioC n j.val=columnaOrientada n a e.2.val+inicioR n j.val := by
  have hr := e.1.isLt; have hc := e.2.isLt; have hj := j.isLt
  change j.val<2*n-1 at hj
  cases a <;> simp [lines,verticeOblicuo,columnaOrientada,inicioR,inicioC] <;> omega

def celdaFibra {n : ℕ} (hn : 0<n) (a : Bool) (j : Indice n) (z : Fin (longitudFibra n j.val)) : Fibra n a j := by
  have hr := (extremos_fibra hn j).2.2.1
  have hc := (extremos_fibra hn j).2.2.2.1
  have iz := z.isLt
  let r : Fin n := ⟨inicioR n j.val+z.val,by omega⟩
  let c : Fin n := ⟨columnaOrientada n a (inicioC n j.val+z.val),by cases a <;> simp [columnaOrientada] <;> omega⟩
  refine ⟨(r,c),(etiqueta_fibra (r,c) a j).mpr ?_⟩
  cases a <;> simp [r,c,columnaOrientada] <;> omega

def indiceFibra {n : ℕ} (a : Bool) (j : Indice n) (z : Fibra n a j) : Fin (longitudFibra n j.val) := by
  refine ⟨z.val.1.val-inicioR n j.val,?_⟩
  obtain ⟨⟨r,c⟩,eq⟩:=z
  have hr:=r.isLt; have hc:=c.isLt
  have d := (etiqueta_fibra (r,c) a j).mp eq
  cases a <;> simp [columnaOrientada,inicioR,inicioC] at d <;> simp [longitudFibra,inicioR,inicioC] <;> omega

def equivFibra {n : ℕ} (hn : 0<n) (a : Bool) (j : Indice n) : Fin (longitudFibra n j.val) ≃ Fibra n a j where
  toFun := celdaFibra hn a j
  invFun := indiceFibra a j
  left_inv z := by apply Fin.ext; change inicioR n j.val+z.val-inicioR n j.val=z.val; omega
  right_inv z := by
    obtain ⟨⟨r,c⟩,eq⟩:=z
    have hr:=r.isLt; have hc:=c.isLt
    have e:=(etiqueta_fibra (r,c) a j).mp eq
    apply Subtype.ext; apply Prod.ext <;> apply Fin.ext
    · change inicioR n j.val+(r.val-inicioR n j.val)=r.val
      cases a <;> simp [columnaOrientada,inicioR,inicioC] at e <;> simp [inicioR] <;> omega
    · change columnaOrientada n a (inicioC n j.val+(r.val-inicioR n j.val))=c.val
      cases a <;> simp [columnaOrientada,inicioR,inicioC] at e ⊢ <;> omega

theorem suma_fibra_fisica {n : ℕ} (hn : 0<n) (a : Bool) (j : Indice n) (v : Cell n→ℝ) :
    (∑ e : Fibra n a j,v e.val)=∑ i : Fin (longitudFibra n j.val),v (celdaFibra hn a j i).val :=
  (Fintype.sum_equiv (equivFibra hn a j) _ _ (fun _ => rfl)).symm
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.equivFibra
#print axioms ArticuloA.Historias.suma_fibra_fisica
