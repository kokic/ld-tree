
import Lean.Meta.Tactic.TryThis
import Lean.Elab.Tactic.ElabTerm


import Lean.Meta.Tactic.LibrarySearch
import Lean.Meta.LazyDiscrTree

open Lean Meta
open LazyDiscrTree (InitEntry findMatches)

open LibrarySearch

namespace Lean.Elab.LibrarySearch

open Lean Meta LibrarySearch
open Elab Tactic Term TryThis

def hackedAddImport (name : Name) (constInfo : ConstantInfo) :
    MetaM (Array (Lean.Meta.LazyDiscrTree.InitEntry (Name × DeclMod))) :=
  forallTelescope constInfo.type fun _ type => do
    let e ← Lean.Meta.LazyDiscrTree.InitEntry.fromExpr type (name, DeclMod.none)
    let a := #[e]
    if e.key == .const ``Iff 2 then
      let a := a.push (←e.mkSubEntry 0 (name, DeclMod.mp))
      let a := a.push (←e.mkSubEntry 1 (name, DeclMod.mpr))
      pure a
    else
      pure a


def emoji (e : Except ε α) := if e.toBool then checkEmoji else crossEmoji

def constantsPerImportTask : Nat := 6500

def hackedLibSearchFindDecls : Expr → MetaM (Array (Name × DeclMod))
  | expr => do
    let result ← libSearchFindDecls expr
    -- dbg_trace "size: {result.size}"
    dbg_trace "{result.map (fun (name, _) => name)}"
    return result

-- def hackedLibSearchFindDecls : Expr → MetaM (Array (Name × DeclMod)) :=
--   Lean.Meta.LazyDiscrTree.findMatches hackedExt hackedAddImport
--       (droppedKeys := droppedKeys)
--       (constantsPerTask := constantsPerImportTask)

def hackedLibrarySearchLemma (cfg : ApplyConfig) (act : List MVarId → MetaM (List MVarId))
    (allowFailure : MVarId → MetaM Bool) (cand : Candidate)  : MetaM (List MVarId) := do
  let ((goal, mctx), (name, mod)) := cand
  let ppMod (mod : DeclMod) : MessageData :=
        match mod with | .none => "" | .mp => " with mp" | .mpr => " with mpr"
  withTraceNode `Tactic.librarySearch (return m!"{emoji ·} trying {name}{ppMod mod} ") do
    setMCtx mctx
    let lem ← mkLibrarySearchLemma name mod
    let newGoals ← goal.apply lem cfg
    try
      act newGoals
    catch _ =>
      if ← allowFailure goal then
        pure newGoals
      else
        failure

def librarySearchEmoji : Except ε (Option α) → String
| .error _ => bombEmoji
| .ok (some _) => crossEmoji
| .ok none => checkEmoji

def hackedLibrarySearch' (goal : MVarId)
    (tactic : List MVarId → MetaM (List MVarId))
    (allowFailure : MVarId → MetaM Bool)
    (leavePercentHeartbeats : Nat) :
    MetaM (Option (Array (List MVarId × MetavarContext))) := do
  withTraceNode `Tactic.librarySearch (return m!"{librarySearchEmoji ·} {← goal.getType}") do
  profileitM Exception "librarySearch" (← getOptions) do
    -- Create predicate that returns true when running low on heartbeats.
    let candidates ← librarySearchSymm hackedLibSearchFindDecls goal
    let cfg : ApplyConfig := { allowSynthFailures := true }
    let shouldAbort ← mkHeartbeatCheck leavePercentHeartbeats
    let act := fun cand => do
        if ←shouldAbort then
          abortSpeculation
        hackedLibrarySearchLemma cfg tactic allowFailure cand
    tryOnEach act candidates


def hackedLibrarySearch (goal : MVarId)
    (tactic : Bool → List MVarId → MetaM (List MVarId) :=
      fun initial g => solveByElim [] (maxDepth := 6) (exfalso := initial) g)
    (allowFailure : MVarId → MetaM Bool := fun _ => pure true)
    (leavePercentHeartbeats : Nat := 10) :
    MetaM (Option (Array (List MVarId × MetavarContext))) := do
  (tactic true [goal] *> pure none) <|>
  hackedLibrarySearch' goal (tactic false) allowFailure leavePercentHeartbeats


def hacked_exact? (ref : Syntax) (required : Option (Array (TSyntax `term))) (requireClose : Bool) :
    TacticM Unit := do
  let mvar ← getMainGoal
  let (_, goal) ← (← getMainGoal).intros
  dbg_trace "[!] hacked_exact?"
  goal.withContext do
    let required := (← (required.getD #[]).mapM getFVarId).toList.map .fvar
    let tactic := fun exfalso =>
          solveByElim required (exfalso := exfalso) (maxDepth := 6)
    let allowFailure := fun g => do
      let g ← g.withContext (instantiateMVars (.mvar g))
      return required.all fun e => e.occurs g
    match ← hackedLibrarySearch goal tactic allowFailure with
    -- Found goal that closed problem
    | none =>
      let expr := (← instantiateMVars (mkMVar mvar)).headBeta
      let msgd := m!"{expr}"
      logInfoAt ref m!"log: {msgd}"
      addExactSuggestion ref expr
    -- Found suggestions
    | some suggestions =>
      dbg_trace "{suggestions.map (fun (s, _) => s.map (MVarId.name))}"
      if requireClose then throwError
        "`exact?` could not close the goal. Try `apply?` to see partial suggestions."
      reportOutOfHeartbeats `library_search ref
      for (_, suggestionMCtx) in suggestions do
        withMCtx suggestionMCtx do
          addExactSuggestion ref (← instantiateMVars (mkMVar mvar)).headBeta (addSubgoalsMsg := true)
      if suggestions.isEmpty then logError "apply? didn't find any relevant lemmas"
      admitGoal goal

elab "hacked_exact?" : tactic =>
  let required: Option (Array (TSyntax `term)) := none
  let requireClose := false
  Lean.Elab.Tactic.withMainContext do
    let ref := (← getRef)
    hacked_exact? ref required requireClose
-- Lean.Elab.Tactic.evalTactic (← `(tactic| hacked_exact?))
-- Lean.Elab.Tactic.evalTactic (← `(tactic| exact?))

def target_goal: ∀ (n m : Nat), n + m = m + n := by
  hacked_exact?
  -- sorry

def main : IO Unit :=
  IO.println s!"Hello!"
