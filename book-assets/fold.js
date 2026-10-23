// Companion book: folding of the Lean layer.
//
// Every Lean block of a page (the `#stmt` code boxes, together with the quoted Lean docstring that
// precedes them) is grouped into a "formal unit" (`details.lean-unit`). How the units are shown is
// decided by the layout, stored in `document.body.dataset.layout`:
//
//   fold    – each unit is folded into a one-line bar that opens in place;
//   switch  – a page-wide switch shows or hides all units ("text only" edition);
//   margin  – units are cards in the right margin, opening to full width;
//   notes   – units leave the text flow; a small marker opens them in a side panel.
//
// The prototype switcher (bottom right) selects the layout; the choice is remembered.

(function () {
  "use strict";

  const LAYOUTS = {
    fold: "A · inline folds",
    switch: "B · text-only switch",
    margin: "C · margin cards",
    notes: "D · side-panel notes",
  };
  const STORE = "roquette-book-layout";
  const STORE_LEAN = "roquette-book-show-lean";

  function load(key, dflt) {
    try { return localStorage.getItem(key) ?? dflt; } catch (e) { return dflt; }
  }
  function save(key, val) {
    try { localStorage.setItem(key, val); } catch (e) { /* private mode */ }
  }

  function chosenLayout() {
    const p = new URLSearchParams(location.search).get("layout");
    if (p && p in LAYOUTS) { save(STORE, p); return p; }
    const s = load(STORE, "fold");
    return s in LAYOUTS ? s : "fold";
  }

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

  function isBlank(el) {
    return el.textContent.trim() === "" && !el.querySelector("img, .math");
  }

  // The declaration names shown by the `#stmt` commands of a code box.
  function namesOf(box) {
    const names = [];
    box.querySelectorAll("code.hl.lean.block").forEach((code) => {
      const kw = code.querySelector(".keyword.token");
      if (kw && kw.textContent.trim() === "#stmt") {
        const c = code.querySelector(".const.token");
        if (c) names.push(c.textContent.trim());
      }
    });
    return names;
  }

  // A label for a unit without `#stmt`: `example`s and the page context.
  function otherLabel(body) {
    const kw = body.querySelector("code.hl.lean.block .keyword.token");
    const k = kw ? kw.textContent.trim() : "";
    if (k === "example") return "a worked example";
    if (k === "universe" || k === "variable") return "the variables of this page";
    return k || "Lean";
  }

  // --- layout C: cards in the margin, next to the last paragraph that introduces them
  function setupMargin(units) {
    const wide = window.matchMedia("(min-width: 1200px)");
    wide.addEventListener("change", () => {
      units.forEach((u) => {
        if (!u._flow) return;
        if (wide.matches && !u.open) u._margin(); else u._flow();
      });
    });
    units.forEach((unit, i) => {
      unit.dataset.order = String(i);
      let prose = unit.previousElementSibling;
      while (prose && (prose.classList.contains("lean-unit") || prose.classList.contains("lean-emptied"))) {
        prose = prose.previousElementSibling;
      }
      if (!isProse(prose)) return;
      let container = prose;
      while (container.lastElementChild && container.lastElementChild.tagName === "SECTION") {
        container = container.lastElementChild;
      }
      const anchor = container.lastElementChild;
      if (!anchor) return;
      const flowNext = unit.nextElementSibling;
      const flowParent = unit.parentElement;
      // the units after the same prose block keep their order
      const place = () => {
        unit.classList.add("in-margin");
        let before = anchor;
        for (const sib of container.querySelectorAll(":scope > details.lean-unit.in-margin")) {
          if (sib !== unit && Number(sib.dataset.order) > Number(unit.dataset.order)) { before = sib; break; }
        }
        container.insertBefore(unit, before);
      };
      unit._flow = () => { unit.classList.remove("in-margin"); flowParent.insertBefore(unit, flowNext); };
      unit._margin = place;
      if (wide.matches) place();
      unit.addEventListener("toggle", () => {
        if (!wide.matches) return;
        if (unit.open && unit.classList.contains("in-margin")) {
          unit._flow();
          unit.scrollIntoView({ block: "nearest" });
        } else if (!unit.open && !unit.classList.contains("in-margin")) {
          unit._margin();
        }
      });
    });
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
      unit.dataset.names = what.textContent;
      units.push(unit);
      child = unit.nextElementSibling;
    }
    return units;
  }

  // --- layout D: markers in the text and a side panel
  function setupNotes(units, content) {
    const panel = document.createElement("aside");
    panel.className = "lean-panel";
    panel.setAttribute("aria-label", "Lean statement");
    panel.innerHTML = '<div class="lean-panel-head"><span class="lean-panel-title"></span>' +
      '<button type="button" class="lean-panel-close" aria-label="Close">×</button></div>' +
      '<div class="lean-panel-content"></div>';
    document.body.appendChild(panel);
    const slot = panel.querySelector(".lean-panel-content");
    let current = null;
    function close() {
      if (current) { current.home.appendChild(current.body); current.marker.classList.remove("active"); }
      current = null;
      panel.classList.remove("open");
    }
    panel.querySelector(".lean-panel-close").addEventListener("click", close);
    document.addEventListener("keydown", (e) => { if (e.key === "Escape") close(); });
    units.forEach((unit) => {
      const marker = document.createElement("button");
      marker.type = "button";
      marker.className = "lean-marker";
      marker.textContent = "Lean";
      marker.title = unit.dataset.names;
      // attach to the last paragraph of the prose before the unit
      let host = null;
      let prev = unit.previousElementSibling;
      while (prev && (prev.classList.contains("lean-unit") || prev.classList.contains("lean-emptied"))) {
        prev = prev.previousElementSibling;
      }
      if (isProse(prev)) {
        const ps = [...prev.querySelectorAll("p, li")].filter((p) => !p.closest("blockquote"));
        host = ps[ps.length - 1] || null;
      }
      if (host) { host.append(" ", marker); }
      else {
        const wrap = document.createElement("div");
        wrap.className = "lean-marker-row";
        wrap.appendChild(marker);
        content.insertBefore(wrap, unit);
      }
      const body = unit.querySelector(".lean-unit-body");
      marker.addEventListener("click", () => {
        if (current && current.unit === unit) { close(); return; }
        close();
        current = { unit, body, home: unit, marker };
        panel.querySelector(".lean-panel-title").textContent = unit.dataset.names;
        slot.appendChild(body);
        marker.classList.add("active");
        panel.classList.add("open");
      });
    });
  }

  // --- toolbar in the title bar
  function setupToolbar(units, layout) {
    const bar = document.querySelector(".title-bar");
    if (!bar) return;
    const tools = document.createElement("div");
    tools.className = "lean-tools";
    if (layout === "fold" || layout === "margin") {
      const open = document.createElement("button");
      open.type = "button";
      open.textContent = "Expand all Lean";
      const shut = document.createElement("button");
      shut.type = "button";
      shut.textContent = "Fold all Lean";
      open.addEventListener("click", () => units.forEach((u) => (u.open = true)));
      shut.addEventListener("click", () => units.forEach((u) => (u.open = false)));
      tools.append(open, shut);
    }
    if (layout === "switch" || layout === "margin") {
      const label = document.createElement("label");
      label.className = "lean-switch";
      const box = document.createElement("input");
      box.type = "checkbox";
      box.checked = load(STORE_LEAN, layout === "margin" ? "1" : "0") === "1";
      const apply = () => {
        document.body.classList.toggle("lean-hidden", !box.checked);
        save(STORE_LEAN, box.checked ? "1" : "0");
      };
      box.addEventListener("change", apply);
      apply();
      label.append(box, document.createTextNode(" Show Lean"));
      tools.appendChild(label);
    }
    bar.appendChild(tools);
  }

  // --- prototype switcher
  function setupSwitcher(layout) {
    const box = document.createElement("div");
    box.className = "layout-switcher";
    box.innerHTML = '<div class="layout-switcher-title">Layout prototype</div>';
    for (const [key, name] of Object.entries(LAYOUTS)) {
      const a = document.createElement("a");
      const url = new URL(location.href);
      url.searchParams.set("layout", key);
      a.href = url.pathname + url.search + url.hash;
      a.textContent = name;
      if (key === layout) a.className = "current";
      box.appendChild(a);
    }
    document.body.appendChild(box);
  }

  document.addEventListener("DOMContentLoaded", () => {
    const layout = chosenLayout();
    document.body.dataset.layout = layout;
    const units = [];
    document.querySelectorAll(".code-content").forEach((c) => units.push(...buildUnits(c)));
    if (layout === "switch") units.forEach((u) => (u.open = true));
    if (layout === "margin") setupMargin(units);
    if (layout === "notes") {
      document.querySelectorAll(".code-content").forEach((c) =>
        setupNotes(units.filter((u) => u.parentElement === c), c));
    }
    setupToolbar(units, layout);
    setupSwitcher(layout);
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
