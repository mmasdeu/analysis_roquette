// Companion book: foldable Lean layer.
//
// Every Lean block of a page (the `#stmt` code boxes, together with the quoted Lean docstring that
// precedes them) is grouped into a foldable unit (`details.lean-unit`), folded into a one-line bar by
// default.  Unfolded, a unit looks like in the companion to Analysis I: the docstring as a plain
// label, followed by the Lean declaration in an ordinary code block.  The toolbar in the title bar
// folds or unfolds all units of the page.

(function () {
  "use strict";

  const isProse = (el) => el && el.classList && el.classList.contains("mod-doc");
  const isBox = (el) => el && el.classList && el.classList.contains("code-box");

  // The blockquotes at the very end of a prose block (descending into its last section): these are
  // the Lean docstrings quoted before a `#stmt`.
  function trailingQuotes(prose) {
    let container = prose;
    while (container.lastElementChild && container.lastElementChild.tagName === "SECTION") {
      container = container.lastElementChild;
    }
    const quotes = [];
    let el = container.lastElementChild;
    while (el && el.tagName === "BLOCKQUOTE") {
      quotes.unshift(el);
      el = el.previousElementSibling;
    }
    return quotes;
  }

  const isBlank = (el) => el.textContent.trim() === "" && !el.querySelector("img, .math");

  // The first keyword of a code block (`#stmt`, `example`, `variable`, ...).
  function keywordOf(code) {
    const kw = code.querySelector(".keyword.token");
    return kw ? kw.textContent.trim() : "";
  }

  // The declaration names shown by the `#stmt` commands of a code box.
  function namesOf(box) {
    const names = [];
    box.querySelectorAll("code.hl.lean.block").forEach((code) => {
      if (keywordOf(code) === "#stmt") {
        const c = code.querySelector(".const.token");
        if (c) names.push(c.textContent.trim());
      }
    });
    return names;
  }

  function otherLabel(body) {
    const code = body.querySelector("code.hl.lean.block");
    const k = code ? keywordOf(code) : "";
    if (k === "example") return "a worked example";
    if (k === "universe" || k === "variable") return "the variables of this page";
    return k || "Lean";
  }

  // `#stmt` boxes: the command line is hidden and only the statement it prints is shown.
  function markStatementBoxes(box) {
    const codes = [...box.querySelectorAll("code.hl.lean.block")];
    if (codes.length && codes.every((c) => keywordOf(c) === "#stmt")) box.classList.add("stmt-box");
  }

  function buildUnits(content) {
    const units = [];
    let child = content.firstElementChild;
    while (child) {
      if (!isBox(child)) { child = child.nextElementSibling; continue; }
      const unit = document.createElement("details");
      unit.className = "lean-unit";
      const summary = document.createElement("summary");
      const body = document.createElement("div");
      body.className = "lean-unit-body";
      unit.append(summary, body);
      content.insertBefore(unit, child);
      // the quoted docstring before the first box
      const prev = unit.previousElementSibling;
      if (isProse(prev)) {
        for (const q of trailingQuotes(prev)) body.appendChild(q);
        if (isBlank(prev)) prev.classList.add("lean-emptied");
      }
      // the consecutive boxes, and the quotes between them
      const names = [];
      let next = unit.nextElementSibling;
      while (next) {
        if (isBox(next)) {
          names.push(...namesOf(next));
          markStatementBoxes(next);
          const after = next.nextElementSibling;
          body.appendChild(next);
          next = after;
        } else if (isProse(next) && next.textContent.trim() !== "" &&
                   trailingQuotes(next).length > 0 &&
                   trailingQuotes(next).length === next.querySelectorAll("blockquote").length &&
                   isBox(next.nextElementSibling) &&
                   [...next.querySelectorAll("p, li")].every((p) => p.closest("blockquote"))) {
          // a prose block consisting only of a quoted docstring, followed by another box
          const after = next.nextElementSibling;
          for (const q of trailingQuotes(next)) body.appendChild(q);
          next.classList.add("lean-emptied");
          next = after;
        } else break;
      }
      const label = document.createElement("span");
      label.className = "lean-unit-label";
      label.textContent = "Lean";
      const what = document.createElement("span");
      what.className = "lean-unit-names";
      what.textContent = names.length ? names.join(", ") : otherLabel(body);
      summary.append(label, what);
      units.push(unit);
      child = unit.nextElementSibling;
    }
    return units;
  }

  function setupToolbar(units) {
    const bar = document.querySelector(".title-bar");
    if (!bar || units.length === 0) return;
    const tools = document.createElement("div");
    tools.className = "lean-tools";
    const mk = (text, open) => {
      const b = document.createElement("button");
      b.type = "button";
      b.textContent = text;
      b.addEventListener("click", () => units.forEach((u) => (u.open = open)));
      return b;
    };
    tools.append(mk("Expand all Lean", true), mk("Fold all Lean", false));
    bar.appendChild(tools);
  }

  document.addEventListener("DOMContentLoaded", () => {
    const units = [];
    document.querySelectorAll(".code-content").forEach((c) => units.push(...buildUnits(c)));
    setupToolbar(units);
    // a link to a declaration inside a folded unit opens it
    const openTarget = () => {
      if (!location.hash) return;
      let t = null;
      try { t = document.querySelector(location.hash); } catch (e) { return; }
      const u = t && t.closest("details.lean-unit");
      if (u) { u.open = true; t.scrollIntoView(); }
    };
    window.addEventListener("hashchange", openTarget);
    openTarget();
  });
})();
