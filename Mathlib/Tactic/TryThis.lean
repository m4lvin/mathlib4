/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Std.Tactic.TryThis
import Lean.Meta.Tactic.Util

/-!
# Additions to "Try this" support

This file could be upstreamed to `Std`.
-/

open Lean Elab Elab.Tactic PrettyPrinter Meta Std.Tactic.TryThis

/-- Add a suggestion for `have : t := e`. -/
def addHaveSuggestion (ref : Syntax) (t? : Option Expr) (e : Expr) :
    TermElabM Unit := do
  let estx ← delabToRefinableSyntax e
  let prop ← isProp (← inferType e)
  let tac ← if let some t := t? then
    let tstx ← delabToRefinableSyntax t
    if prop then
      `(tactic| have : $tstx := $estx)
    else
      `(tactic| let this : $tstx := $estx)
  else
    if prop then
      `(tactic| have := $estx)
    else
      `(tactic| let this := $estx)
  addSuggestion ref tac

/-- Add a suggestion for `rw [h] at loc`. -/
def addRewriteSuggestion (ref : Syntax) (e : Expr) (symm : Bool)
  (type? : Option Expr := none) (loc? : Option Expr := none)
  (origSpan? : Option Syntax := none) :
    TermElabM Unit := do
  let estx ← delabToRefinableSyntax e
  let tac ← do
    let loc ← loc?.mapM fun loc => do `(Lean.Parser.Tactic.location| at $(← delab loc):term)
    if symm then `(tactic| rw [← $estx] $(loc)?) else `(tactic| rw [$estx:term] $(loc)?)

  let mut tacMsg :=
    if let some loc := loc? then
      if symm then m!"rw [← {e}] at {loc}" else m!"rw [{e}] at {loc}"
    else
      if symm then m!"rw [← {e}]" else m!"rw [{e}]"
  let mut extraMsg := ""
  if let some type := type? then
    tacMsg := tacMsg ++ m!"\n-- {type}"
    extraMsg := extraMsg ++ s!"\n-- {← PrettyPrinter.ppExpr type}"
  addSuggestion ref tac (suggestionForMessage? := tacMsg)
    (extraMsg := extraMsg) (origSpan? := origSpan?)

open Lean.Parser.Tactic

def Lean.Syntax.TSepArray.ofArray {k : SyntaxNodeKinds} {sep : String} (e : Array (TSyntax k)) :
    Syntax.TSepArray k sep :=
  e.foldl (init := .mk #[]) fun a r => a.push r

open Lean.Syntax

/-- Add a suggestion for `rw [h₁, ← h₂] at loc`. -/
def addRewritesSuggestion (ref : Syntax) (rules : List (Expr × Bool))
  (type? : Option Expr := none) (loc? : Option Expr := none)
  (origSpan? : Option Syntax := none) :
    TermElabM Unit := do
  let rules_stx := TSepArray.ofArray <| ← rules.toArray.mapM fun ⟨e, symm⟩ => do
    let t ← delabToRefinableSyntax e
    if symm then `(rwRule| ← $t:term) else `(rwRule| $t:term)
  let tac ← do
    let loc ← loc?.mapM fun loc => do `(location| at $(← delab loc):term)
    `(tactic| rw [$rules_stx,*] $(loc)?)

  let mut tacMsg :=
    let rulesMsg := MessageData.sbracket <| MessageData.joinSep
      (rules.map fun ⟨e, symm⟩ => (if symm then "← " else "") ++ m!"{e}") ", "
    if let some loc := loc? then
      m!"rw {rulesMsg} at {loc}"
    else
      m!"rw {rulesMsg}"
  let mut extraMsg := ""
  if let some type := type? then
    tacMsg := tacMsg ++ m!"\n-- {type}"
    extraMsg := extraMsg ++ s!"\n-- {← PrettyPrinter.ppExpr type}"
  addSuggestion ref tac (suggestionForMessage? := tacMsg)
    (extraMsg := extraMsg) (origSpan? := origSpan?)
