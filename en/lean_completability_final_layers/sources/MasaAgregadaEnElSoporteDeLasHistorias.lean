import SoporteDeLasHistoriasDelProcesoGuiado
namespace ArticuloA.Historias
open Trayectoria Trayectoria.ProfileKernel Trayectoria.Adjunto RealFinita
open scoped NNReal BigOperators
noncomputable section
open Classical

def masaAgregada {X : Type} (xs : Atoms ℝ≥0 X) (x : X) : ℝ :=
  (avg masas xs (mark masas (fun y=>y=x))).val

theorem sumar_masas_en_un_evento {X : Type} (xs : Atoms ℝ≥0 X) (S : Finset X) :
    ∑ x∈S,masaAgregada xs x=(avg masas xs (mark masas (·∈S))).val := by
  induction xs with
  | nil=>change (∑ _x∈S,(0:ℝ))=0; simp
  | cons v l ih=>
    have term (x : X) : masaAgregada (v::l) x=(if v.2=x then (v.1:ℝ) else 0)+masaAgregada l x := by
      change ((v.1*mark masas (fun y=>y=x) v.2+avg masas l (mark masas (fun y=>y=x)):ℝ≥0):ℝ)=_
      by_cases eq : v.2=x <;> simp [masaAgregada,mark,masas,eq]
    simp_rw [term]
    rw [Finset.sum_add_distrib,ih]
    change (∑ x∈S,if v.2=x then (v.1:ℝ) else 0)+_=
      ((v.1*mark masas (·∈S) v.2+avg masas l (mark masas (·∈S)):ℝ≥0):ℝ)
    by_cases m : v.2∈S <;> simp [mark,masas,m]

theorem masa_agregada_total {X : Type} (xs : Atoms ℝ≥0 X) (S : Finset X)
    (cover : ∀ a∈xs,a.2∈S) : ∑ x∈S,masaAgregada xs x=(total masas xs).val := by
  rw [sumar_masas_en_un_evento]
  congr 1
  induction xs with
  | nil=>rfl
  | cons a l ih=>
    have sub : ∀ b∈l,b.2∈S:=fun b hb=>cover b (List.mem_cons_of_mem _ hb)
    have m:=cover a List.mem_cons_self
    change a.1*mark masas (·∈S) a.2+avg masas l (mark masas (·∈S))=a.1*1+total masas l
    have remaining:=ih sub
    simp only [mark,if_pos m] at *
    change a.1*1+_=a.1*1+_
    rw [remaining]
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.masa_agregada_total
#print axioms ArticuloA.Historias.sumar_masas_en_un_evento
