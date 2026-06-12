import Mathlib.Tactic

namespace AntaresCategory

structure RegistryObject where id : ℕ; data : String
structure Kernel where seed : String
structure Governance where allowed : String → Bool
structure Export where value : String

structure SystemState where
  registry   : List RegistryObject
  kernel     : Kernel
  governance : Governance
  export     : Export

def Transition : Type :=
  List (List String
        × (List RegistryObject → List RegistryObject)
        × (Kernel → Kernel)
        × (Kernel → Export))

def composeT (t₁ t₂ : Transition) : Transition := t₁ ++ t₂

def stepF (s : SystemState)
    (st : List String
          × (List RegistryObject → List RegistryObject)
          × (Kernel → Kernel)
          × (Kernel → Export)) : SystemState :=
  { registry   := st.2.1 s.registry
  , kernel     := st.2.2.1 s.kernel
  , governance := s.governance
  , export     := st.2.2.2 s.kernel }

def apply (s : SystemState) (t : Transition) : SystemState :=
  t.foldl stepF s

theorem apply_append (s : SystemState) (t1 t2 : Transition) :
    apply (apply s t1) t2 = apply s (t1 ++ t2) := by
  simp only [apply]
  induction t1 generalizing s with
  | nil => rfl
  | cons h t ih => exact ih (stepF s h)

structure Morphism (a b : SystemState) where
  t  : Transition
  ok : apply a t = b

def compM {a b c : SystemState} (f : Morphism a b) (g : Morphism b c) :
    Morphism a c :=
  { t  := composeT f.t g.t
  , ok := by
      simp only [composeT]
      rw [← apply_append, f.ok, g.ok] }

structure Category where
  Obj      : Type
  Hom      : Obj → Obj → Type
  id       : ∀ {a}, Hom a a
  comp     : ∀ {a b c}, Hom a b → Hom b c → Hom a c
  id_left  : ∀ {a b} (f : Hom a b), comp id f = f
  id_right : ∀ {a b} (f : Hom a b), comp f id = f
  assoc    : ∀ {a b c d} (f : Hom a b) (g : Hom b c) (h : Hom c d),
               comp (comp f g) h = comp f (comp g h)

def ACI_Category : Category :=
  { Obj      := SystemState
  , Hom      := Morphism
  , id       := ⟨[], rfl⟩
  , comp     := compM
  , id_left  := by intros; cases f; simp [compM, composeT, apply]
  , id_right := by intros; cases f; simp [compM, composeT, apply, apply_append]
  , assoc    := by
      intros; cases f; cases g; cases h
      simp [compM, composeT, List.append_assoc] }

end AntaresCategory
