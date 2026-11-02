import TetraStereo.UniversalProof.GeneralParserStateBridge
import TetraStereo.UniversalProof.SecondSpherePhysicalFamilyRecordsProofs.SecondSpherePhysicalFamilyRecords

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NativeBracketAtomSpecContinuationsProofs.NativeBracketAtomSpecContinuations

open TetraStereo.OneCenter
open TetraStereo.UniversalProof.GeneralParserStateBridge
open TetraStereo.UniversalProof.SecondSpherePhysicalFamilyRecordsProofs.SecondSpherePhysicalFamilyRecords













/-! ## Role-to-accepted-atom mapping -/

/-- The accepted `FamilyAtom` whose `atomSpec` spells the atom of a frozen 543 role.  Only
`tagCarbon` is parity-annotated; the other eleven roles are ordinary `[C]`, `[H]`, `[F]`. -/
def roleFamilyAtom (parity : TetrahedralInputParity) : FamilyRole → FamilyAtom
  | .backboneCarbon => .carbon
  | .backboneHydrogen => .hydrogen
  | .bridgeCarbon => .carbon
  | .bridgeHydrogenA => .hydrogen
  | .bridgeHydrogenB => .hydrogen
  | .tagCarbon => .taggedCarbon parity
  | .tagHydrogen => .hydrogen
  | .fluorine => .fluorine
  | .methylCarbon => .carbon
  | .methylHydrogenA => .hydrogen
  | .methylHydrogenB => .hydrogen
  | .methylHydrogenC => .hydrogen

/-- Actual bracket spelling of a role: the accepted `atomChars` of its `FamilyAtom`. -/
def roleChars (parity : TetrahedralInputParity) (role : FamilyRole) : List Char :=
  atomChars (roleFamilyAtom parity role)

/-- Role spec equality: the accepted `atomSpec` of the role's `FamilyAtom` is exactly the accepted
543 `roleAtom`.  This is the load-bearing join between the two committed surfaces. -/
theorem native_roleAtom_spec (parity : TetrahedralInputParity) (role : FamilyRole) :
    atomSpec (roleFamilyAtom parity role) = roleAtom parity role := by
  cases role <;> rfl

/-! ## Preserved metadata fields

The accepted values here are exactly those of `GeneralParserStateBridge.atomSpec` through the 543
`roleAtom`: `isotope? none`, `charge 0`, `aromatic false`, `explicitHydrogens? (some 0)`.  We do
NOT identify these with `AtomSpec.aliphatic`, which leaves `explicitHydrogens? none`; the `some 0`
field below is the actual accepted bracket value.  Only `tagCarbon` carries an input parity. -/

theorem native_role_atom_metadata (parity : TetrahedralInputParity) (role : FamilyRole) :
    (roleAtom parity role).isotope? = none ∧
      (roleAtom parity role).charge = 0 ∧
      (roleAtom parity role).aromatic = false ∧
      (roleAtom parity role).explicitHydrogens? = some 0 ∧
      (roleAtom parity role).tetrahedral? =
        (if role = .tagCarbon then some parity else none) := by
  refine ⟨?_, ?_, ?_, ?_, roleAtom_tetrahedral parity role⟩ <;> cases role <;> rfl

/-! ## Actual bracket token and arbitrary-tail parse -/

/-- Actual `parseAtomToken?` consumes exactly the role spelling and returns the role spec, with an
arbitrary remaining stream. -/
theorem native_role_atom_token (parity : TetrahedralInputParity) (role : FamilyRole)
    (tail : List Char) :
    parseAtomToken? (roleChars parity role ++ tail) = some (roleAtom parity role, tail) := by
  unfold roleChars
  rw [parse_family_atom_token (roleFamilyAtom parity role) tail, native_roleAtom_spec]

/-- One actual `parseCharsFuel` recursion consumes one complete role bracket token, whatever the
fuel/continuation and any older parser state. -/
theorem native_role_atom_step (parity : TetrahedralInputParity) (role : FamilyRole)
    (fuel : ℕ) (tail : List Char) (state : ParseState) :
    parseCharsFuel (fuel + 1) (roleChars parity role ++ tail) state =
      parseCharsFuel fuel tail (state.addAtom (roleAtom parity role)) := by
  unfold roleChars
  rw [parse_family_atom_step (roleFamilyAtom parity role) fuel tail state, native_roleAtom_spec]

/-- Explicit-single continuation (`-` then the role token): two actual parser recursions. -/
theorem native_role_single_step (parity : TetrahedralInputParity) (role : FamilyRole)
    (fuel : ℕ) (tail : List Char) (state : ParseState) (parent : ℕ)
    (current : state.current? = some parent) :
    parseCharsFuel (fuel + 2) ('-' :: (roleChars parity role ++ tail)) state =
      parseCharsFuel fuel tail (attachSingle state parent (roleAtom parity role)) := by
  unfold roleChars
  rw [parse_single_family_atom_step (roleFamilyAtom parity role) fuel tail state parent current,
    native_roleAtom_spec]

/-- One-atom single-bond branch continuation `( - role )`: four actual parser recursions. -/
theorem native_role_branch_continuation (parity : TetrahedralInputParity) (role : FamilyRole)
    (fuel : ℕ) (tail : List Char) (state : ParseState) (parent : ℕ)
    (current : state.current? = some parent) :
    parseCharsFuel (fuel + 4)
        ('(' :: '-' :: (roleChars parity role ++ ')' :: tail)) state =
      parseCharsFuel fuel tail (singleBranchResult state parent (roleAtom parity role)) := by
  unfold roleChars
  rw [parse_single_branch_continuation (roleFamilyAtom parity role) fuel tail state parent
      current,
    native_roleAtom_spec]

/-! ## Exact `@` / `@@` spelling, character length, and the three fuel offsets

Fuel is token recursion fuel: `+1` for an atom token, `+2` for an explicit-single atom token, `+4`
for a one-atom branch.  It is NOT character-count equality: the `@@` spelling is one character
longer but consumes the same number of tokens as `@`. -/

theorem native_role_tagged_spelling (parity : TetrahedralInputParity) :
    roleChars parity .tagCarbon =
      (if parity = .clockwise then ['[', 'C', '@', '@', ']'] else ['[', 'C', '@', ']']) := by
  cases parity <;> simp [roleChars, roleFamilyAtom, atomChars]

/-- Spelling/character-length and the three token-recursion fuel continuations, uniformly. -/
theorem native_role_atom_spelling_fuel (parity : TetrahedralInputParity) (role : FamilyRole) :
    (roleChars parity .tagCarbon =
        (if parity = .clockwise then ['[', 'C', '@', '@', ']'] else ['[', 'C', '@', ']'])) ∧
      ((roleChars parity role).length =
        (if role = .tagCarbon then (if parity = .clockwise then 5 else 4) else 3)) ∧
      (∀ (fuel : ℕ) (tail : List Char) (state : ParseState),
        parseCharsFuel (fuel + 1) (roleChars parity role ++ tail) state =
          parseCharsFuel fuel tail (state.addAtom (roleAtom parity role))) ∧
      (∀ (fuel : ℕ) (tail : List Char) (state : ParseState) (parent : ℕ),
        state.current? = some parent →
          parseCharsFuel (fuel + 2) ('-' :: (roleChars parity role ++ tail)) state =
            parseCharsFuel fuel tail (attachSingle state parent (roleAtom parity role))) ∧
      (∀ (fuel : ℕ) (tail : List Char) (state : ParseState) (parent : ℕ),
        state.current? = some parent →
          parseCharsFuel (fuel + 4)
              ('(' :: '-' :: (roleChars parity role ++ ')' :: tail)) state =
            parseCharsFuel fuel tail (singleBranchResult state parent (roleAtom parity role))) := by
  refine ⟨native_role_tagged_spelling parity, ?_, native_role_atom_step parity role, ?_, ?_⟩
  · cases role <;> cases parity <;> simp [roleChars, roleFamilyAtom, atomChars]
  · intro fuel tail state parent current
    exact native_role_single_step parity role fuel tail state parent current
  · intro fuel tail state parent current
    exact native_role_branch_continuation parity role fuel tail state parent current

end TetraStereo.UniversalProof.NativeBracketAtomSpecContinuationsProofs.NativeBracketAtomSpecContinuations
