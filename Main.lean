-- import «LdTree»

import Lean.Meta.Tactic.LibrarySearch
import Lean.Meta.Tactic.TryThis
import Lean.Elab.Tactic.ElabTerm

namespace Lean.Elab.LibrarySearch

open Lean Meta LibrarySearch
open Elab Tactic Term TryThis

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
    match ← librarySearch goal tactic allowFailure with
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

def main : IO Unit :=
  IO.println s!"Hello!"
