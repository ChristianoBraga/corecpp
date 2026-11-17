// Theme selection of the Core C++ blueprint.
//
// Loaded synchronously in every page head through `extraHead`, so the stored
// choice applies before the first paint. The reader picks Auto, Light or Dark
// from a selector at the foot of the table of contents. Auto follows the
// system preference. The choice persists in localStorage when it is available.
(function () {
  var KEY = "corecpp-theme";
  var root = document.documentElement;

  function load() {
    try { return localStorage.getItem(KEY) || "auto"; } catch (e) { return "auto"; }
  }

  function store(choice) {
    try { localStorage.setItem(KEY, choice); } catch (e) { /* storage unavailable */ }
  }

  function apply(choice) {
    if (choice === "light" || choice === "dark") {
      root.setAttribute("data-theme", choice);
    } else {
      root.removeAttribute("data-theme");
    }
  }

  var current = load();
  apply(current);

  function mount() {
    var host = document.querySelector("#toc .last");
    if (!host || host.querySelector(".th-theme-switch")) return;
    var group = document.createElement("div");
    group.className = "th-theme-switch";
    group.setAttribute("role", "group");
    group.setAttribute("aria-label", "Colour theme");
    var options = [["auto", "Auto"], ["light", "Light"], ["dark", "Dark"]];
    var buttons = options.map(function (opt) {
      var b = document.createElement("button");
      b.type = "button";
      b.textContent = opt[1];
      b.dataset.choice = opt[0];
      b.addEventListener("click", function () {
        current = opt[0];
        store(current);
        apply(current);
        sync();
      });
      group.appendChild(b);
      return b;
    });
    function sync() {
      buttons.forEach(function (b) {
        b.setAttribute("aria-pressed", b.dataset.choice === current ? "true" : "false");
      });
    }
    sync();
    host.appendChild(group);
  }

  if (document.readyState === "loading") {
    document.addEventListener("DOMContentLoaded", mount);
  } else {
    mount();
  }
})();
