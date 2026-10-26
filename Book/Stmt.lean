import Lean

/-!
Helper for the companion book: `#stmt name` displays a declaration of the library.

* For a theorem or a definition it prints the signature `theorem name (binders) : statement`,
  as pretty-printed terms with hover information (the identifiers are linked to their
  declarations on the rendered pages).  The standing assumptions `K` of the book (a local field) are
  not repeated.  For a definition the body is appended as source text.
* For other declarations (structures, classes, inductive types) it prints the *source* of the
  declaration.
-/

open Lean Elab Command Meta

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

/-- The index at which the body of a definition starts: its first top-level `:=` or ` where`. -/
private def findBody (s : String) : Option Nat := Id.run do
  let cs := s.toList.toArray
  let mut depth : Int := 0
  let mut i := 0
  while i < cs.size do
    let c := cs[i]!
    if c == '(' || c == '[' || c == '{' || c == '⟨' then depth := depth + 1
    else if c == ')' || c == ']' || c == '}' || c == '⟩' then depth := depth - 1
    else if depth == 0 && c == ':' && i + 1 < cs.size && cs[i+1]! == '=' then return some i
    else if depth == 0 && c == ' ' && i + 6 < cs.size && cs[i+1]! == 'w' && cs[i+2]! == 'h' &&
        cs[i+3]! == 'e' && cs[i+4]! == 'r' && cs[i+5]! == 'e' && (cs[i+6]! == '\n' || cs[i+6]! == ' ')
      then return some (i + 1)
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

/-- The standing assumptions of the book: `K` is a local field. -/
private def standingClasses : List Name :=
  [`NontriviallyNormedField, `IsUltrametricDist, `CompleteSpace]

private def isStanding (ty : Expr) : MetaM Bool := do
  let isK (e : Expr) : MetaM Bool := do
    if e.isFVar then return (← e.fvarId!.getDecl).userName == `K else return false
  if ty.isSort then return false
  match ty.getAppFn.constName? with
  | some c =>
    if standingClasses.contains c then ty.getAppArgs.anyM isK else return false
  | none => return false

/-- The signature of a theorem or definition as a message with term information, or `none` for other
declarations. -/
private def signatureMessage (n : Name) (body? : Option String) : MetaM (Option MessageData) := do
  let ci ← getConstInfo n
  let isThm := ci matches .thmInfo _
  unless isThm || ci matches .defnInfo _ do return none
  let env ← getEnv
  let isInst ← isInstance n
  let red ← getReducibilityStatus n
  let kw : String :=
    if isThm then "theorem"
    else if isInst then "instance"
    else if red == ReducibilityStatus.reducible then "abbrev"
    else "def"
  let pre := if !isThm && isNoncomputable env n then "noncomputable " else ""
  forallTelescope ci.type fun xs concl => do
    let mut groups : Array (BinderInfo × Array Expr × Expr) := #[]
    for x in xs do
      let decl ← x.fvarId!.getDecl
      let ty := decl.type
      if ← isStanding ty then continue
      if decl.userName == `K && ty.isSort then continue
      match groups.back? with
      | some (bi, ns, t) =>
        if bi == decl.binderInfo && t == ty && bi != .instImplicit then
          groups := groups.pop.push (bi, ns.push x, t)
        else groups := groups.push (decl.binderInfo, #[x], ty)
      | none => groups := groups.push (decl.binderInfo, #[x], ty)
    let names (ns : Array Expr) : MessageData :=
      MessageData.joinSep (ns.toList.map MessageData.ofExpr) " "
    let render : BinderInfo × Array Expr × Expr → MessageData
      | (.default, ns, t) => m!"({names ns} : {t})"
      | (.implicit, ns, t) => m!"\{{names ns} : {t}}"
      | (.strictImplicit, ns, t) => m!"⦃{names ns} : {t}⦄"
      | (.instImplicit, _, t) => m!"[{t}]"
    -- fill lines greedily, so that a long signature does not put every binder on its own line
    let head := m!"{pre}{kw} {MessageData.ofConstName n}"
    let headLen := (← (← addMessageContext head).toString).length
    let mut lines : Array MessageData := #[]
    let mut cur : MessageData := m!""
    let mut curEmpty := true
    let mut curLen := headLen
    for g in groups do
      let r := render g
      let len := (← (← addMessageContext r).toString).length
      if curEmpty then
        cur := r
        curEmpty := false
        curLen := curLen + 1 + len
      else if curLen + 1 + len > 100 then
        lines := lines.push cur
        cur := r
        curLen := 4 + len
      else
        cur := m!"{cur} {r}"
        curLen := curLen + 1 + len
    let single := lines.isEmpty
    unless curEmpty do lines := lines.push cur
    let binders := MessageData.joinSep lines.toList (MessageData.ofFormat "\n    ")
    let sp : MessageData := if curEmpty then m!"" else m!" "
    let conclLen := (← (← addMessageContext m!"{concl}").toString).length
    let sig :=
      if single && curLen + 3 + conclLen ≤ 100 then m!"{head}{sp}{binders} : {concl}"
      else m!"{head}{sp}{binders} :\n  {concl}"
    let msg := match body? with
      | some t => m!"{sig} {t}"
      | none => sig
    return some (← addMessageContext msg)

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
  let body? : Option String :=
    if thm then none
    else (findBody text).map fun i =>
      let ls := (text.drop i).toString.splitOn "\n"
      let ls := if ls.length > maxLines then ls.take maxLines ++ ["  …"] else ls
      "\n".intercalate ls
  match ← liftTermElabM (signatureMessage n body?) with
  | some msg => logInfo msg
  | none => logInfo text

end Book
