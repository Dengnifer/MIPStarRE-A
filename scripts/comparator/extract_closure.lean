import MIPStarRE.LDT.Test.MainTheorem.MainFormal
import MIPStarRE.QPBT.Test.QubitForm

/-!
# Comparator closure extractor

Computes the transitive closure of repository-local constants referenced by
the statements of the target theorems of one comparator challenge, mirroring
comparator's `runForUsedConsts` traversal (types, definition bodies, inductive
constructors, and recursor rules; theorem proof bodies are traversed for the
constants they use).  Auto-generated auxiliaries (`_proof_`, `match_`,
`_autoParam`, constructors, projections) are collapsed into their parent
declarations.

The targets are read from the `COMPARATOR_TARGETS` environment variable
(whitespace-separated fully qualified names) and default to the LDT challenge
root `MIPStarRE.LDT.Test.mainFormal`, so the extractor is shared by every
challenge configured in `check_challenge_drift.py`.  This file imports the
root module of every configured challenge; targets outside those imports are
reported as errors.

Output: one TSV row per declaration — name, module path, start line, end
line (`NORANGE` for compiler-generated declarations without a source range)
— consumed by `assemble_challenge.py`.  See README.md in this directory for
the full regeneration pipeline.
-/

open Lean

def defaultTargets : List Name := [`MIPStarRE.LDT.Test.mainFormal]

/-- Targets of this extraction run, from `COMPARATOR_TARGETS`. -/
def readTargets : IO (List Name) := do
  match ← IO.getEnv "COMPARATOR_TARGETS" with
  | none => return defaultTargets
  | some s =>
    let flat := ((s.replace "\n" " ").replace "\t" " ").replace "," " "
    let names := (flat.splitOn " ").filter (· ≠ "")
    if names.isEmpty then return defaultTargets
    return names.map String.toName

def isLocal (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some idx => (`MIPStarRE).isPrefixOf env.header.moduleNames[idx.toNat]!
  | none => true

/-- Name tails of compiler-generated companions of an inductive/structure
declaration; occurrences are collapsed into the parent so the assembler emits
each structure's source exactly once. -/
def generatedTails : List String :=
  ["casesOn", "rec", "recOn", "brecOn", "below", "ibelow", "binductionOn",
   "noConfusion", "noConfusionType", "injEq", "sizeOf_spec",
   "mk.inj", "mk.injEq", "mk.noConfusion", "mk.sizeOf_spec"]

def canon (env : Environment) (closure : NameSet) (n : Name) : Name :=
  let s := n.toString
  let s := (s.splitOn "._proof_").head!
  let s := (s.splitOn ".match_").head!
  let s := (s.splitOn "._autoParam").head!
  let c := s.toName
  -- collapse compiler-generated companions into their parent inductive
  let byTail := generatedTails.findSome? fun tail =>
    if s.endsWith ("." ++ tail) then
      let parent := (s.dropRight (tail.length + 1)).toName
      match env.find? parent with
      | some (.inductInfo _) => if closure.contains parent then some parent else none
      | _ => none
    else none
  match byTail with
  | some parent => parent
  | none =>
    -- collapse constructors, recursors, and projections likewise
    let structural :=
      match env.find? c with
      | some (.ctorInfo v) => some v.induct
      | some (.recInfo v) => v.all.head?
      | _ =>
        if (env.getProjectionFnInfo? c).isSome then some c.getPrefix
        else none
    match structural with
    | some parent => if closure.contains parent then parent else c
    | none => c

/-- All local constants referenced by declaration `n`.
Mirrors comparator's `runForUsedConsts`: type + value (incl. theorem proofs)
+ inductive ctors + recursor rule RHSs. -/
def refsOf (env : Environment) (n : Name) : Array Name :=
  match env.find? n with
  | some ci =>
    let fromType := ci.type.getUsedConstants
    let fromValue := match ci.value? (allowOpaque := true) with
      | some v => v.getUsedConstants
      | none => #[]
    let extra : Array Name :=
      match ci with
      | .inductInfo v => v.ctors.toArray ++ v.all.toArray
      | .ctorInfo v => #[v.induct]
      | .recInfo v => v.rules.foldl (fun acc r => (acc.push r.ctor) ++ r.rhs.getUsedConstants) #[]
      | _ => #[]
    (fromType ++ fromValue ++ extra).filter (isLocal env)
  | none => #[]

partial def collect (env : Environment) (queue : List Name) (seen : NameSet) : NameSet :=
  match queue with
  | [] => seen
  | n :: rest =>
    if seen.contains n || !isLocal env n then collect env rest seen
    else collect env ((refsOf env n).toList ++ rest) (seen.insert n)

def runExtract : MetaM Unit := do
  let env ← getEnv
  let targets ← readTargets
  let mut roots : List Name := []
  for t in targets do
    let some ci := env.find? t | throwError "target not found: {t}"
    roots := roots ++ ci.type.getUsedConstants.toList.filter (isLocal env ·)
  let closure := collect env roots {}
  let mut canonSet : NameSet := {}
  for n in closure.toArray do
    canonSet := canonSet.insert (canon env closure n)
  -- topological ordering happens downstream in assemble_challenge.py
  -- (module import rank, then line number)
  for c in canonSet.toArray do
    let mod := match env.getModuleIdxFor? c with
      | some idx => env.header.moduleNames[idx.toNat]!
      | none => Name.anonymous
    let path := mod.toString.replace "." "/" ++ ".lean"
    match ← Lean.findDeclarationRanges? c with
    | some r => IO.println s!"{c}\t{path}\t{r.range.pos.line}\t{r.range.endPos.line}"
    | none => IO.println s!"{c}\t{path}\tNORANGE\tNORANGE"

#eval runExtract
