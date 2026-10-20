import Lean

/-!
Helper for the companion book: `#stmt name` displays the *source* of a declaration of the library
(its statement for theorems, its definition for definitions) instead of the fully elaborated term.
This keeps the pages readable: the variables of the surrounding section, the instance arguments and
the proofs are not repeated.
-/

open Lean Elab Command

namespace Book

/-- The first index of `s` at which `:=` occurs outside of any brackets. -/
private def findDefEq (s : String) : Option Nat := Id.run do
  let cs := s.toList.toArray
  let mut depth : Int := 0
  let mut i := 0
  while i < cs.size do
    let c := cs[i]!
    if c == '(' || c == '[' || c == '{' || c == '⟨' then depth := depth + 1
    else if c == ')' || c == ']' || c == '}' || c == '⟩' then depth := depth - 1
    else if c == ':' && depth == 0 && i + 1 < cs.size && cs[i+1]! == '=' then return some i
    i := i + 1
  return none

/-- Drop a leading docstring and attribute lines. -/
private def dropDocAndAttrs (s : String) : String := Id.run do
  let mut t := s
  if t.startsWith "/--" then
    match t.splitOn "-/" with
    | _ :: rest => t := ("-/".intercalate rest).trimAsciiStart.toString
    | [] => pure ()
  return t

private def isTheoremLike (s : String) : Bool :=
  ["theorem ", "lemma ", "protected theorem ", "private theorem "].any
    fun p => (s.dropWhile (fun c => c == ' ')).toString.startsWith p || s.contains ("\ntheorem ")

/-- Maximal number of lines of a definition that is displayed. -/
private def maxLines : Nat := 16

elab "#stmt " id:ident : command => do
  let env ← getEnv
  let cands ← liftCoreM <| realizeGlobalConstWithInfos id
  let n ← match cands with
    | [n] => pure n
    | [] => throwError "unknown constant {id}"
    | ns => pure ((ns.find? fun n => !(`EntireLaurent).isPrefixOf n).getD ns.head!)
  let some mod := env.getModuleIdxFor? n | throwError "no module for {n}"
  let modName := env.header.moduleNames[mod.toNat]!
  let path : System.FilePath :=
    (System.FilePath.mk (".".intercalate (modName.components.map toString) |>.replace "." "/")).withExtension "lean"
  let some ranges ← liftCoreM <| findDeclarationRanges? n | throwError "no declaration range for {n}"
  let src ← IO.FS.readFile path
  let lines := src.splitOn "\n"
  let startLine := ranges.range.pos.line - 1
  let endLine := ranges.range.endPos.line
  let mut text := "\n".intercalate ((lines.drop startLine).take (endLine - startLine))
  text := dropDocAndAttrs text
  -- attributes on their own lines
  while text.startsWith "@[" do
    match text.splitOn "\n" with
    | _ :: rest => text := "\n".intercalate rest
    | [] => break
  let thm := (text.dropWhile (· == ' ')).toString.startsWith "theorem " ||
    (text.dropWhile (· == ' ')).toString.startsWith "lemma " ||
    text.startsWith "protected theorem "
  if thm then
    if let some i := findDefEq text then
      text := (text.take i).trimAsciiEnd.toString
  else
    let ls := text.splitOn "\n"
    if ls.length > maxLines then
      text := "\n".intercalate (ls.take maxLines) ++ "\n  …"
  -- the standing assumptions of the book are not repeated in every statement
  for b in ["[NontriviallyNormedField K]", "[IsUltrametricDist K]", "[CompleteSpace K]"] do
    text := (text.replace (" " ++ b) "").replace b ""
  logInfo text

end Book
