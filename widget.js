/**
 * widget.js — SAC Python Formula Editor
 * SAP Analytics Cloud 2024+ Custom Widget (Web Component)
 *
 * Architecture overview
 * ─────────────────────
 * ┌─ Shadow DOM ──────────────────────────────────────────────────┐
 * │  Toolbar   [select][input][Run][Test][Save][New][badge][●]   │
 * │  Fixtures  Collapsible JSON fixture editor (test mode only)  │
 * │  Editor    Monaco Python editor (1fr)                        │
 * │  Output    Collapsible output panel                          │
 * │  Statusbar Mode + execution time                             │
 * └───────────────────────────────────────────────────────────────┘
 *
 * Vendor bundling — what is and isn't in the ZIP
 * ────────────────────────────────────────────────
 * BUNDLED  vendor/monaco/         (~4.1 MB) — Monaco Editor, zero CDN needed
 *            loader.js, editor/editor.main.js, editor/editor.main.css,
 *            base/worker/workerMain.js
 * BUNDLED  vendor/pyodide/pyodide.js  (14 KB) — no script-src CSP needed
 * NOT ZIP  Pyodide WASM (~10 MB)      — loaded from URL:
 *            • pyodideBaseURL property → your internal server (zero CDN)
 *            • cdn.jsdelivr.net        → default            (needs connect-src CSP)
 *
 * Performance guarantees
 * ──────────────────────
 * • Monaco AMD loader injected once per page (window.__pfeMonacoPromise).
 * • Pyodide Web Worker spawned once per widget instance; never killed between runs.
 * • ResultSet hashes prevent re-serialising unchanged DataFrames to the worker.
 * • Compiled Python code objects cached in worker (LRU-50) to skip re-parsing.
 * • All Pyodide work happens in the worker thread — UI never blocks.
 */

'use strict';

/* ── Constants ──────────────────────────────────────────────────────────────── */
/* Monaco Editor IS bundled in the widget ZIP (SAC limit is 10 MB; Monaco is ~4 MB).
   Loading priority:
     1. this.monacoBaseURL  — if set by admin (custom/internal server override)
     2. MONACO_LOCAL        — vendor/monaco bundled in the ZIP (default, zero CDN)
   Pyodide.js (14 KB) IS bundled locally in vendor/pyodide/pyodide.js.
   The Pyodide WASM binary (~10 MB) is loaded from this.pyodideBaseURL or CDN. */
const MONACO_LOCAL  = 'vendor/monaco';
const PYODIDE_LOCAL = 'vendor/pyodide/pyodide.js';
const BINDING_SLOTS = ['dataBinding1','dataBinding2','dataBinding3','dataBinding4','dataBinding5'];

const DEBOUNCE_COMPILE_MS = 450;
const WORKER_FILE         = 'python_worker.js';

const DEFAULT_SCRIPT = `# SAC Python Formula Editor
# ─────────────────────────────────────────────────────────
# Available objects per bound model slot:
#   dataBinding1  (or your alias)  → pandas DataFrame
#   <variable_name>               → SAC input variable value
#
# Helper functions:
#   filter_scope(df, Region='EMEA')          in-memory filter
#   set_scope('dataBinding1', Region='EMEA') SAC-side filter
#   store_result('key', value)               queue result
#   display(obj)                             print to output
#   debug('label', obj)                      type + shape info
#   df_info(df, 'name')                      DataFrame diagnostics
#   assert_equal('test', actual, expected)   test assertion
#
# Press Ctrl+Enter to run.  Press 🧪 Test to run with fixtures.
# ─────────────────────────────────────────────────────────

display(dataBinding1)
`;

const DEFAULT_FIXTURES = `{
  "dataBinding1": [
    { "Region": "EMEA", "FiscalYear": "2024", "Revenue": 1000000 },
    { "Region": "APJ",  "FiscalYear": "2024", "Revenue":  800000 },
    { "Region": "NA",   "FiscalYear": "2024", "Revenue": 1200000 }
  ],
  "variables": {
    "IV_YEAR":    "2024",
    "IV_COUNTRY": "DE"
  }
}`;

/* ═══════════════════════════════════════════════════════════════════════════════
   Web Component Class
   ═══════════════════════════════════════════════════════════════════════════════ */
class PythonFormulaEditor extends HTMLElement {

  /* ── A: Constructor ──────────────────────────────────────────────────────── */
  constructor() {
    super();
    this.attachShadow({ mode: 'open' });

    /** All mutable runtime state lives here for easy inspection/reset. */
    this._state = {
      /* Infrastructure */
      monacoReady:         false,
      workerReady:         false,
      pyodideReady:        false,
      worker:              null,
      editor:              null,
      editorModel:         null,       /* Python script Monaco model */
      fixturesModel:       null,       /* JSON fixture Monaco model */
      msgCounter:          0,
      pendingMessages:     {},
      _compileTimer:       null,
      _widgetBase:         null,       /* resolved URL of widget.js dir */

      /* Data */
      lastResultHash:      {},
      lastResults:         {},
      lastDurationMs:      0,

      /* UI state */
      outputCollapsed:     false,
      fixturesPanelOpen:   false,
      fixturesEditorMode:  false,      /* true when fixtures JSON is in the editor */
    };
  }

  /* ── B: Lifecycle – Connected ────────────────────────────────────────────── */
  connectedCallback() {
    this._buildShadowDOM();
    this._applyTheme(this.editorTheme || 'vs-dark');
    this._applyToolbarVisibility();
    this._applyOutputVisibility();
    this._syncOutputHeight();
    this._syncScriptSelector();
    this._loadMonaco();       /* async, non-blocking */
    this._spawnWorker();      /* async, non-blocking */
  }

  /* ── C: Lifecycle – Disconnected ─────────────────────────────────────────── */
  disconnectedCallback() {
    if (this._state.editor) {
      try { this._state.editor.dispose(); } catch (_) {}
    }
    if (this._state.fixturesEditor) {
      try { this._state.fixturesEditor.dispose(); } catch (_) {}
    }
    if (this._state.worker) {
      this._state.worker.terminate();
      this._state.worker = null;
    }
    /* Cancel all pending message timeouts */
    for (const p of Object.values(this._state.pendingMessages)) {
      clearTimeout(p.timeout);
      p.reject(new Error('Widget disconnected'));
    }
  }

  /* ── D: SAC Lifecycle – Before update ───────────────────────────────────── */
  onCustomWidgetBeforeUpdate(/* oChangedProperties */) {}

  /* ── E: SAC Lifecycle – After update ────────────────────────────────────── */
  onCustomWidgetAfterUpdate(oChangedProperties) {
    if (oChangedProperties.scriptStorage) {
      this._syncScriptSelector();
    }
    if (oChangedProperties.activeFunctionId) {
      this._loadScriptIntoEditor(this.activeFunctionId);
    }
    if (oChangedProperties.mode) {
      this._applyModeUI(this.mode);
    }
    if (oChangedProperties.editorTheme) {
      this._applyTheme(this.editorTheme);
      if (this._state.monacoReady) {
        window.monaco && monaco.editor.setTheme(this.editorTheme);
      }
    }
    if (oChangedProperties.showToolbar) {
      this._applyToolbarVisibility();
    }
    if (oChangedProperties.showOutputPanel) {
      this._applyOutputVisibility();
    }
    if (oChangedProperties.outputPanelHeight) {
      this._syncOutputHeight();
    }
    if (oChangedProperties.testFixtures && this._state.fixturesModel) {
      /* Sync fixture JSON into the fixture editor model */
      const json = this.testFixtures && this.testFixtures !== '{}' ? this.testFixtures : DEFAULT_FIXTURES;
      this._state.fixturesModel.setValue(json);
    }
    /* Data change — optionally auto-run */
    const dataChanged = BINDING_SLOTS.some(k => oChangedProperties[k]);
    if (dataChanged && this.autoRunOnDataChange && this._state.pyodideReady) {
      this._executeActive();
    }
  }

  /* ── F: SAC Lifecycle – Resize ───────────────────────────────────────────── */
  onCustomWidgetResize() {
    if (this._state.editor) {
      try { this._state.editor.layout(); } catch (_) {}
    }
  }

  /* ── G: SAC Lifecycle – Destroy ─────────────────────────────────────────── */
  onCustomWidgetDestroy() {
    this.disconnectedCallback();
  }

  /* ═══════════════════════════════════════════════════════════════════════════
     SECTION 1 — Shadow DOM Construction
     ═══════════════════════════════════════════════════════════════════════════ */

  _buildShadowDOM() {
    /* Inline CSS instead of external link for SAC-hosted compatibility */
    const style = document.createElement('style');
    style.textContent = `
/* ─────────────────────────────────────────────────────────────────────────────
   widget.css — SAC Python Formula Editor
   Scoped entirely inside the Shadow DOM. Uses CSS Grid for the 4-row layout
   and CSS custom properties for all dynamic values (output height, theme colours).
   ───────────────────────────────────────────────────────────────────────────── */

:host {
  display:     block;
  width:       100%;
  height:      100%;
  font-family: 'Segoe UI', 'SAP 72', -apple-system, BlinkMacSystemFont, sans-serif;
  font-size:   13px;
  box-sizing:  border-box;

  --toolbar-height:    40px;
  --statusbar-height:  22px;
  --output-height:     200px;
  --fixtures-height:   0px;

  --color-bg:          #1e1e1e;
  --color-toolbar:     #252526;
  --color-border:      #3c3c3c;
  --color-text:        #cccccc;
  --color-text-muted:  #858585;
  --color-accent:      #0078d4;
  --color-error:       #f44747;
  --color-warn:        #d7ba7d;
  --color-success:     #4ec9b0;
  --color-info:        #9cdcfe;
  --color-output-bg:   #1a1a1a;
  --color-statusbar:   #007acc;
}

*, *::before, *::after { box-sizing: inherit; }

#pfe-root.theme-light {
  --color-bg:         #ffffff;
  --color-toolbar:    #f3f3f3;
  --color-border:     #e0e0e0;
  --color-text:       #333333;
  --color-text-muted: #888888;
  --color-output-bg:  #f8f8f8;
  --color-statusbar:  #0078d4;
}

#pfe-root.theme-hc-black {
  --color-bg:         #000000;
  --color-toolbar:    #000000;
  --color-border:     #6fc3df;
  --color-text:       #ffffff;
  --color-text-muted: #aaaaaa;
  --color-output-bg:  #000000;
  --color-statusbar:  #000000;
}

#pfe-root {
  display:               grid;
  grid-template-rows:    var(--toolbar-height) var(--fixtures-height) 1fr var(--output-height) var(--statusbar-height);
  grid-template-columns: 1fr;
  grid-template-areas: "toolbar" "fixtures" "editor" "output" "statusbar";
  width:      100%;
  height:     100%;
  background: var(--color-bg);
  color:      var(--color-text);
  overflow:   hidden;
}

#pfe-root.test-active { border-left: 3px solid var(--color-success); }

#pfe-toolbar {
  grid-area:     toolbar;
  display:       flex;
  align-items:   center;
  gap:           5px;
  padding:       0 8px;
  background:    var(--color-toolbar);
  border-bottom: 1px solid var(--color-border);
  overflow:      hidden;
  flex-shrink:   0;
}

#pfe-toolbar[hidden] { display: none; }
#pfe-root:has(#pfe-toolbar[hidden]) {
  grid-template-rows: 0 1fr var(--output-height) var(--statusbar-height);
}

#fn-select, #fn-id-input {
  height:        26px;
  background:    var(--color-border);
  color:         var(--color-text);
  border:        1px solid transparent;
  border-radius: 3px;
  padding:       0 7px;
  font-size:     12px;
  outline:       none;
  transition:    border-color 0.15s;
}
#fn-select:focus, #fn-id-input:focus { border-color: var(--color-accent); }
#fn-select    { min-width: 130px; cursor: pointer; }
#fn-id-input  { width: 150px; }

.pfe-btn {
  height:        26px;
  padding:       0 11px;
  border:        none;
  border-radius: 3px;
  cursor:        pointer;
  font-size:     12px;
  font-weight:   500;
  white-space:   nowrap;
  transition:    opacity 0.15s, background 0.15s;
  color:         #fff;
}
.pfe-btn:hover:not(:disabled)  { opacity: 0.85; }
.pfe-btn:active:not(:disabled) { opacity: 0.70; }
.pfe-btn:disabled              { opacity: 0.40; cursor: not-allowed; }

#btn-run   { background: var(--color-success); color: #1e1e1e; font-weight: 700; }
#btn-save  { background: #6a9955; }
#btn-new   { background: var(--color-border); color: var(--color-text); }
#btn-mode-toggle { background: var(--color-border); color: var(--color-text); font-size: 11px; }

.pfe-badge {
  padding:       2px 8px;
  border-radius: 3px;
  font-size:     10px;
  font-weight:   700;
  letter-spacing: 0.6px;
  text-transform: uppercase;
  user-select:   none;
}
.badge-debug      { background: var(--color-warn); color: #1e1e1e; }
.badge-production { background: var(--color-error); color: #fff; }

#status-indicator {
  width:         10px;
  height:        10px;
  border-radius: 50%;
  margin-left:   auto;
  flex-shrink:   0;
  transition:    background 0.2s;
}

.status-idle    { background: var(--color-success); }
.status-loading { background: var(--color-warn); animation: pfe-pulse 1.2s infinite alternate; }
.status-running { background: var(--color-warn); animation: pfe-pulse 0.7s infinite alternate; }
.status-error   { background: var(--color-error); }

@keyframes pfe-pulse { from { opacity: 1; } to { opacity: 0.25; } }

#pfe-editor-container { grid-area: editor; position: relative; overflow: hidden; background: var(--color-bg); }
#monaco-host { position: absolute; inset: 0; }
#editor-placeholder {
  position: absolute; inset: 0; display: flex; flex-direction: column; align-items: center; justify-content: center; gap: 12px;
  color: var(--color-text-muted); font-size: 13px; background: var(--color-bg);
}

.pfe-spinner {
  width: 28px; height: 28px; border: 3px solid var(--color-border); border-top-color: var(--color-accent); border-radius: 50%;
  animation: pfe-spin 0.8s linear infinite;
}
@keyframes pfe-spin { to { transform: rotate(360deg); } }

#pfe-output-panel {
  grid-area: output; display: grid; grid-template-rows: 28px 1fr; border-top: 2px solid var(--color-border);
  background: var(--color-output-bg); overflow: hidden;
}
#pfe-output-panel[hidden] { display: none; }
#output-header {
  display: flex; align-items: center; padding: 0 8px; gap: 8px; background: var(--color-toolbar);
  border-bottom: 1px solid var(--color-border); font-size: 11px; font-weight: 600; text-transform: uppercase;
  letter-spacing: 0.5px; color: var(--color-text-muted); user-select: none; flex-shrink: 0;
}
.output-title { color: var(--color-text); }
#output-meta { font-size: 10px; font-weight: 400; color: var(--color-text-muted); }
.header-btn {
  height: 20px; padding: 0 7px; font-size: 11px; background: transparent; color: var(--color-text-muted);
  border: 1px solid var(--color-border); border-radius: 2px; cursor: pointer; transition: color 0.15s, border-color 0.15s;
}
.header-btn:hover { color: var(--color-text); border-color: var(--color-text-muted); }
#btn-collapse-output { margin-left: auto; }

#output-content {
  overflow-y: auto; overflow-x: auto; padding: 8px 12px; margin: 0; font-family: 'Cascadia Code', 'Consolas', monospace;
  font-size: 12px; line-height: 1.6; white-space: pre-wrap; word-break: break-all; color: var(--color-text);
}
.out-error { color: var(--color-error); }
.out-warn  { color: var(--color-warn); }
.out-success { color: var(--color-success); }
.out-info { color: var(--color-info); }
.out-muted { color: var(--color-text-muted); font-size: 11px; }

.out-table { width: 100%; border-collapse: collapse; font-size: 11px; margin: 4px 0; }
.out-table th { background: var(--color-toolbar); color: var(--color-info); text-align: left; padding: 3px 8px; border-bottom: 1px solid var(--color-border); font-weight: 600; }
.out-table td { padding: 3px 8px; border-bottom: 1px solid var(--color-border); }

#pfe-status-bar {
  grid-area: statusbar; display: flex; align-items: center; padding: 0 8px; gap: 12px; background: var(--color-statusbar);
  font-size: 11px; color: rgba(255,255,255,0.9); flex-shrink: 0;
}
#execution-time { margin-left: auto; opacity: 0.75; }

#pfe-loading-overlay {
  position: absolute; inset: 0; z-index: 100; display: flex; flex-direction: column; align-items: center; justify-content: center; gap: 10px;
  background: rgba(30, 30, 30, 0.92); color: var(--color-text); font-size: 13px;
}
#pfe-loading-overlay[hidden] { display: none; }
.pfe-loading-text { color: var(--color-text-muted); font-size: 12px; }

[data-tooltip] { position: relative; }
[data-tooltip]::after {
  content: attr(data-tooltip); position: absolute; bottom: calc(100% + 4px); left: 50%; transform: translateX(-50%);
  background: #333; color: #fff; font-size: 11px; padding: 3px 8px; border-radius: 3px; white-space: nowrap;
  pointer-events: none; opacity: 0; transition: opacity 0.15s; z-index: 200;
}
[data-tooltip]:hover::after { opacity: 1; }

@media (max-width: 420px) { #fn-id-input, #btn-mode-toggle, .pfe-badge, [data-tooltip="New script"] { display: none; } #fn-select { min-width: 90px; } }

#btn-test { background: #6a9955; }
#btn-test:hover:not(:disabled) { background: #5a8844; }
#btn-fixtures { background: #3c3c3c; color: var(--color-text); }
#btn-fixtures:hover:not(:disabled) { background: #4a4a4a; }

#pfe-fixtures-panel {
  grid-area: fixtures; display: grid; grid-template-rows: 28px 1fr; border-bottom: 2px solid #6a9955;
  background: #1a2b1a; overflow: hidden;
}
#pfe-fixtures-panel[hidden] { display: none; }
#fixtures-header {
  display: flex; align-items: center; padding: 0 8px; gap: 8px; background: #1e301e; border-bottom: 1px solid #3d6b3d;
  font-size: 11px; font-weight: 600; color: #6a9955; user-select: none; flex-shrink: 0;
}
.fixtures-title { font-size: 12px; font-weight: 700; color: #6a9955; }
#fixtures-editor-host { height: 100%; overflow: hidden; }
#btn-save-fixtures { height: 20px; padding: 0 8px; font-size: 11px; background: #6a9955; color: #fff; border: none; border-radius: 2px; cursor: pointer; margin-left: auto; }
#btn-save-fixtures:hover { background: #5a8844; }
#btn-close-fixtures { height: 20px; padding: 0 7px; font-size: 11px; background: transparent; color: var(--color-text-muted); border: 1px solid var(--color-border); border-radius: 2px; cursor: pointer; }
    `;
    this.shadowRoot.appendChild(style);

    this.shadowRoot.innerHTML += `
      <div id="pfe-root">

        <!-- Toolbar -->
        <div id="pfe-toolbar">
          <select id="fn-select" title="Select stored script"></select>
          <input  id="fn-id-input" type="text" placeholder="Function ID" autocomplete="off" spellcheck="false" />
          <button id="btn-run"  class="pfe-btn" data-tooltip="Run script (Ctrl+Enter)">▶ Run</button>
          <button id="btn-test" class="pfe-btn btn-test" data-tooltip="Run in test mode using fixtures">🧪 Test</button>
          <button id="btn-fixtures" class="pfe-btn btn-fixtures" data-tooltip="Open / edit test fixtures">Fixtures</button>
          <button id="btn-save" class="pfe-btn" data-tooltip="Save script">💾 Save</button>
          <button id="btn-new"  class="pfe-btn" data-tooltip="New script">＋ New</button>
          <span   id="mode-badge" class="pfe-badge badge-debug">DEBUG</span>
          <button id="btn-mode-toggle" class="pfe-btn" data-tooltip="Toggle debug / production mode">Switch Mode</button>
          <span   id="status-indicator" class="status-loading" title="Initialising…"></span>
        </div>

        <!-- Fixtures Panel (collapsible, opens above editor) -->
        <div id="pfe-fixtures-panel" hidden>
          <div id="fixtures-header">
            <span class="fixtures-title">🧪 Test Fixtures</span>
            <span class="out-muted">Define mock DataFrames and variables — used only by the Test button</span>
            <button class="header-btn" id="btn-save-fixtures">Save Fixtures</button>
            <button class="header-btn" id="btn-close-fixtures">✕ Close</button>
          </div>
          <div id="fixtures-editor-host"></div>
        </div>

        <!-- Monaco Editor -->
        <div id="pfe-editor-container">
          <div id="monaco-host"></div>
          <div id="editor-placeholder">
            <div class="pfe-spinner"></div>
            <span id="placeholder-text">Loading editor…</span>
          </div>
        </div>

        <!-- Output Panel -->
        <div id="pfe-output-panel">
          <div id="output-header">
            <span class="output-title">Output</span>
            <span id="output-meta"></span>
            <button class="header-btn" id="btn-clear-output" data-tooltip="Clear output">✕ Clear</button>
            <button class="header-btn" id="btn-collapse-output">▼</button>
          </div>
          <pre id="output-content"></pre>
        </div>

        <!-- Status Bar -->
        <div id="pfe-status-bar">
          <span id="status-text">Initialising Pyodide…</span>
          <span id="execution-time"></span>
        </div>

        <!-- Loading overlay (visible until Pyodide is ready) -->
        <div id="pfe-loading-overlay">
          <div class="pfe-spinner"></div>
          <span>Loading Python runtime (Pyodide)…</span>
          <span class="pfe-loading-text">First load: ~10–20 s · Subsequent runs: instant</span>
        </div>

      </div>
    `;

    this._wireToolbarEvents();
  }

  _wireToolbarEvents() {
    const r = this.shadowRoot;

    r.getElementById('btn-run').addEventListener('click',      () => this._executeActive());
    r.getElementById('btn-test').addEventListener('click',     () => this._executeTest());
    r.getElementById('btn-fixtures').addEventListener('click', () => this._toggleFixturesPanel());
    r.getElementById('btn-save').addEventListener('click',     () => this._saveCurrentScript());
    r.getElementById('btn-new').addEventListener('click',      () => this._newScript());

    r.getElementById('btn-mode-toggle').addEventListener('click', () => {
      this.setMode(this.mode === 'debug' ? 'production' : 'debug');
    });

    r.getElementById('fn-select').addEventListener('change', (e) => {
      this._loadScriptIntoEditor(e.target.value);
    });

    r.getElementById('btn-clear-output').addEventListener('click', () => {
      this.clearResults();
    });

    r.getElementById('btn-collapse-output').addEventListener('click', () => {
      this._toggleOutputCollapse();
    });

    r.getElementById('btn-save-fixtures').addEventListener('click',  () => this._saveFixtures());
    r.getElementById('btn-close-fixtures').addEventListener('click', () => this._toggleFixturesPanel(false));
  }

  /* ═══════════════════════════════════════════════════════════════════════════
     SECTION 2 — Monaco Editor
     ═══════════════════════════════════════════════════════════════════════════ */

  _loadMonaco() {
    /* Singleton per page — multiple widget instances share one loader */
    if (!window.__pfeMonacoPromise) {
      window.__pfeMonacoPromise = new Promise((resolve, reject) => {
        /* Default to jsDelivr CDN for SAC-hosted compatibility (no subfolders in ZIP) */
        const defaultCDN = 'https://cdn.jsdelivr.net/npm/monaco-editor@0.50.0/min/vs';
        const customBase = this.monacoBaseURL && this.monacoBaseURL.trim();
        const base = (customBase || defaultCDN).replace(/\/$/, '');

        const script = document.createElement('script');
        script.src = `${base}/loader.js`;
        script.onload = () => {
          window.require.config({ 
            paths: { vs: base },
            'vs/nls': { availableLanguages: { '*': '' } } /* Patch for SAC: Disable NLS loading */
          });
          window.require(['vs/editor/editor.main'], () => resolve(window.monaco), reject);
        };
        script.onerror = () => reject(new Error(`Monaco failed to load from: ${base}/loader.js`));
        document.head.appendChild(script);
      });
    }

    window.__pfeMonacoPromise.then(() => {
      this._initEditor();
    }).catch(err => {
      this._setPlaceholderText('Failed to load Monaco editor: ' + (err.message || err));
    });
  }

  /** Resolve a path relative to widget.js so vendor/ works when the widget
   *  is served from any URL (SAC CDN, local dev server, etc.). */
  _resolveWidgetUrl(relativePath) {
    if (!this._state._widgetBase) {
      let discoveredSrc = '';

      /* 1. Try standard currentScript */
      if (document.currentScript && document.currentScript.src) {
        discoveredSrc = document.currentScript.src;
      }

      /* 2. Search for the specific script tag in the page */
      if (!discoveredSrc) {
        const scripts = Array.from(document.getElementsByTagName('script'));
        const widgetScript = scripts.find(s => (
          s.src && (s.src.includes('widget.js') || s.src.includes('com.custom.pythoneditor'))
        ));
        if (widgetScript) discoveredSrc = widgetScript.src;
      }

      /* 3. Stack trace fallback (filtering out SAP system domains) */
      if (!discoveredSrc) {
        try {
          const stack = new Error().stack || '';
          const matches = stack.match(/(https?:\/\/[^ ]+\.js)/g) || [];
          discoveredSrc = matches.find(s => (
            s.includes('widget.js') && 
            !s.includes('assets.sapanalytics.cloud') && 
            !s.includes('hcs.cloud.sap')
          )) || '';
        } catch (e) {}
      }

      if (discoveredSrc && discoveredSrc.includes('://')) {
        this._state._widgetBase = discoveredSrc.substring(0, discoveredSrc.lastIndexOf('/') + 1);
        console.log('PFE: Discovered base path:', this._state._widgetBase);
      } else {
        /* Last resort: the story origin */
        this._state._widgetBase = window.location.origin + '/';
      }
    }
    
    try {
      return new URL(relativePath, this._state._widgetBase).href;
    } catch (e) {
      return relativePath;
    }
  }

  _initEditor() {
    const host = this.shadowRoot.getElementById('monaco-host');

    /* Retrieve current script (from active function or default) */
    const initialScript = this._getStoredScript(this.activeFunctionId) || DEFAULT_SCRIPT;

    /* Python model for the main script editor */
    const model = monaco.editor.createModel(initialScript, 'python');

    /* JSON model for the fixtures editor (reused in same Monaco instance) */
    const fixturesJson = this.testFixtures && this.testFixtures !== '{}' ? this.testFixtures : DEFAULT_FIXTURES;
    const fixturesModel = monaco.editor.createModel(fixturesJson, 'json');

    const editor = monaco.editor.create(host, {
      model,
      theme:               this.editorTheme || 'vs-dark',
      language:            'python',
      automaticLayout:     true,
      minimap:             { enabled: false },
      fontSize:            13,
      fontFamily:          "'Cascadia Code','Consolas','Courier New',monospace",
      scrollBeyondLastLine: false,
      wordWrap:            'on',
      renderWhitespace:    'boundary',
      lineNumbers:         'on',
      glyphMargin:         true,
      folding:             true,
      suggestOnTriggerCharacters: true,
    });

    /* Keyboard shortcut: Ctrl+Enter → run */
    editor.addCommand(
      monaco.KeyMod.CtrlCmd | monaco.KeyCode.Enter,
      () => this._executeActive()
    );

    /* Debounced pre-flight compile check on every keystroke */
    editor.onDidChangeModelContent(() => {
      if (this._state.fixturesEditorMode) return;  /* skip compile check for JSON */
      clearTimeout(this._state._compileTimer);
      this._state._compileTimer = setTimeout(() => {
        this._sendPreflightCheck();
      }, DEBOUNCE_COMPILE_MS);
    });

    /* Also create a separate small editor for the fixtures panel */
    const fixturesHost = this.shadowRoot.getElementById('fixtures-editor-host');
    if (fixturesHost) {
      this._state.fixturesEditor = monaco.editor.create(fixturesHost, {
        model:            fixturesModel,
        theme:            this.editorTheme || 'vs-dark',
        language:         'json',
        automaticLayout:  true,
        minimap:          { enabled: false },
        fontSize:         12,
        lineNumbers:      'on',
        scrollBeyondLastLine: false,
        wordWrap:         'on',
        formatOnPaste:    true,
      });
    }

    this._state.editor         = editor;
    this._state.editorModel    = model;
    this._state.fixturesModel  = fixturesModel;
    this._state.monacoReady    = true;

    /* Hide placeholder, show editor */
    this.shadowRoot.getElementById('editor-placeholder').hidden = true;
    host.style.visibility = 'visible';

    /* Populate function ID input with current activeFunctionId */
    if (this.activeFunctionId) {
      this.shadowRoot.getElementById('fn-id-input').value = this.activeFunctionId;
    }
  }

  _getEditorValue() {
    return this._state.editor ? this._state.editor.getValue() : '';
  }

  _setEditorValue(script) {
    if (!this._state.editor) return;
    this._state.editor.setValue(script || '');
    this._state.editor.setScrollPosition({ scrollTop: 0 });
  }

  _setPlaceholderText(text) {
    const el = this.shadowRoot.getElementById('placeholder-text');
    if (el) el.textContent = text;
  }

  /* ═══════════════════════════════════════════════════════════════════════════
     SECTION 3 — Web Worker
     ═══════════════════════════════════════════════════════════════════════════ */

  _spawnWorker() {
    const workerUrl = this._resolveWidgetUrl(WORKER_FILE);

    try {
      /* Create a Blob that imports the worker script. This bypasses the cross-origin
         restriction for the worker constructor, as the Blob itself is same-origin. */
      const blob = new Blob([`importScripts("${workerUrl}");`], { type: 'application/javascript' });
      this._state.worker = new Worker(URL.createObjectURL(blob));
    } catch (err) {
      /* Fallback to direct worker if Blob fails (unlikely) */
      console.warn('PFE: Blob worker failed, falling back to direct:', err);
      this._state.worker = new Worker(workerUrl);
    }

    this._state.worker.onmessage  = (e) => this._onWorkerMessage(e.data);
    this._state.worker.onerror    = (e) => this._appendOutput(
      `[Worker Error] ${e.message}`, 'out-error'
    );
  }

  _nextMsgId() {
    return ++this._state.msgCounter;
  }

  /** Post a message and return a Promise that resolves/rejects on the response. */
  _postWorker(type, payload = {}, timeoutMs = 60000) {
    const id = this._nextMsgId();
    return new Promise((resolve, reject) => {
      const timer = setTimeout(() => {
        delete this._state.pendingMessages[id];
        reject(new Error(`Worker message timeout: ${type} (id=${id})`));
      }, timeoutMs);
      this._state.pendingMessages[id] = { resolve, reject, timeout: timer };
      this._state.worker.postMessage({ id, type, payload });
    });
  }

  _onWorkerMessage(data) {
    const { id, type, payload = {} } = data;

    /* Resolve any pending Promise */
    const pending = this._state.pendingMessages[id];
    if (pending) {
      clearTimeout(pending.timeout);
      delete this._state.pendingMessages[id];
      pending.resolve(data);
    }

    /* Handle broadcast messages (no pending Promise) */
    switch (type) {
      case 'WORKER_READY':
        this._state.workerReady = true;
        this._setStatus('Pyodide loading…');
        /* Default to jsDelivr CDN for SAC-hosted compatibility (no subfolders in ZIP) */
        {
          const defaultCDN = `https://cdn.jsdelivr.net/pyodide/v${this.pyodideVersion || '0.26.4'}/full/`;
          const pyodideIndexURL = (this.pyodideBaseURL && this.pyodideBaseURL.trim())
            ? this.pyodideBaseURL.trim()
            : defaultCDN;
          const pyodideJsUrl = (this.pyodideBaseURL && this.pyodideBaseURL.trim()) 
            ? `${pyodideIndexURL}pyodide.js`
            : `${defaultCDN}pyodide.js`;

          this._state.worker.postMessage({
            id: this._nextMsgId(),
            type: 'INIT',
            payload: { pyodideJsUrl, pyodideIndexURL, pyodideVersion: this.pyodideVersion || '0.26.4' }
          });
        }
        break;

      case 'PYODIDE_READY':
        this._state.pyodideReady = true;
        this._hideLoadingOverlay();
        this._setStatusIndicator('status-idle');
        this._setStatus(`Ready · Pyodide loaded in ${payload.durationMs}ms`);
        this._appendOutput(
          `✓ Pyodide ready (${payload.durationMs}ms). Press Ctrl+Enter to run.\n`,
          'out-success'
        );
        /* Run initial preflight if editor is already loaded */
        if (this._state.monacoReady) this._sendPreflightCheck();
        break;

      case 'PYODIDE_ERROR':
        this._setStatusIndicator('status-error');
        this._setStatus('Pyodide failed to load');
        this._appendOutput(`✗ Pyodide error: ${payload.error}\n`, 'out-error');
        break;

      case 'COMPILE_RESULT':
        this._applyMonacoMarkers(payload.errors || []);
        break;

      case 'EXEC_RESULT':
        this._handleExecResult(payload);
        break;

      case 'EXEC_ERROR':
        this._handleExecError(payload);
        break;

      case 'TEST_EXEC_RESULT':
        this._handleTestResult(payload);
        break;

      case 'TEST_EXEC_ERROR':
        this._handleExecError(payload, '', true);
        break;
    }
  }

  /* ═══════════════════════════════════════════════════════════════════════════
     SECTION 4 — Data Collection
     ═══════════════════════════════════════════════════════════════════════════ */

  /**
   * Iterate all 5 binding slots. For each slot with data, build a binding
   * descriptor. Only mark `changed:true` when the ResultSet hash differs from
   * the cached value — the worker skips DataFrame rebuild on unchanged slots.
   */
  _collectDataBindings() {
    const aliases = this._parseBindingAliases();
    const bindings = [];

    for (const slotName of BINDING_SLOTS) {
      let ds;
      try { ds = this.getDataSource(slotName); } catch (_) { continue; }
      if (!ds || typeof ds.getResultSet !== 'function') continue;

      let resultSet;
      try { resultSet = ds.getResultSet(); } catch (_) { continue; }
      if (!resultSet) continue;

      const rows = this._resultSetToRows(ds, resultSet);
      const hash = this._hashRows(rows);
      const alias = aliases[slotName] || slotName;

      bindings.push({
        slotName,
        alias,
        rows,
        hash,
        changed: hash !== (this._state.lastResultHash[slotName] || '')
      });

      this._state.lastResultHash[slotName] = hash;
    }

    return bindings;
  }

  /**
   * Convert a SAC ResultSet to a plain array of row objects.
   * Extracts rawValue for measures and id/label for dimensions.
   */
  _resultSetToRows(ds, resultSet) {
    const rows = [];
    if (!resultSet || !Array.isArray(resultSet)) return rows;

    /* Try to identify which columns are measures via metadata */
    let measureIds = new Set();
    try {
      const metadata = ds.getMetadata();
      if (metadata) {
        (metadata.getMeasures() || []).forEach(m => {
          const id = m.getId ? m.getId() : (m.id || String(m));
          measureIds.add(id);
        });
      }
    } catch (_) {}

    for (const row of resultSet) {
      if (!row) continue;
      const rowObj = {};

      for (const [k, v] of Object.entries(row)) {
        if (v == null) {
          rowObj[k] = null;
        } else if (typeof v === 'object') {
          /* Cell object: { id, label, rawValue, ... }
             Priority:
             1. If it's a known measure OR has rawValue -> take rawValue
             2. If it has an id -> take id (technical name)
             3. If it has a label -> take label (description)
             4. Fallback to stringified object */
          if (measureIds.has(k) || ('rawValue' in v)) {
            rowObj[k] = v.rawValue != null ? v.rawValue : 0;
          } else {
            rowObj[k] = v.id != null ? v.id : (v.label != null ? v.label : JSON.stringify(v));
          }
        } else {
          /* Flat value */
          rowObj[k] = v;
        }
      }
      rows.push(rowObj);
    }

    return rows;
  }

  /** Fast djb2 hash of JSON-stringified rows for change detection. */
  _hashRows(rows) {
    const str = JSON.stringify(rows);
    let h = 5381;
    const len = str.length;
    
    /* If data is large, sample it to keep hashing fast but representative */
    const maxChars = 16384;
    const step = Math.max(1, Math.floor(len / maxChars));

    for (let i = 0; i < len; i += step) {
      h = ((h << 5) + h) ^ str.charCodeAt(i);
      h |= 0;
    }
    return (h >>> 0).toString(16) + '_' + rows.length;
  }

  /**
   * Collect SAC input variables from all bound data sources.
   * Returns a flat { [variableName]: value } map.
   */
  _collectVariables() {
    const vars = {};
    for (const slotName of BINDING_SLOTS) {
      let ds;
      try { ds = this.getDataSource(slotName); } catch (_) { continue; }
      if (!ds) continue;

      let varInput;
      try { varInput = ds.getVariableInput(); } catch (_) { continue; }
      if (!varInput) continue;

      /* varInput may be an object or array of { name, value } entries */
      if (Array.isArray(varInput)) {
        for (const v of varInput) {
          if (v && v.name) vars[v.name] = v.value != null ? String(v.value) : '';
        }
      } else if (typeof varInput === 'object') {
        for (const [k, v] of Object.entries(varInput)) {
          vars[k] = v != null ? String(v) : '';
        }
      }
    }
    return vars;
  }

  _parseBindingAliases() {
    try { return JSON.parse(this.bindingAliases || '{}'); } catch (_) { return {}; }
  }

  /* ═══════════════════════════════════════════════════════════════════════════
     SECTION 5 — Execution Pipeline
     ═══════════════════════════════════════════════════════════════════════════ */

  async _executeActive(scriptId) {
    if (!this._state.pyodideReady) {
      this._appendOutput('⚠ Pyodide not ready yet. Please wait.\n', 'out-warn');
      return;
    }

    const fnId = scriptId || this.activeFunctionId || '';
    const script = scriptId
      ? (this._getStoredScript(scriptId) || '')
      : this._getEditorValue();

    if (!script.trim()) {
      this._appendOutput('⚠ Script is empty.\n', 'out-warn');
      return;
    }

    /* Pre-flight syntax check */
    const compileErrors = await this._preflightCheck(script);
    if (compileErrors.length > 0) {
      this._applyMonacoMarkers(compileErrors);
      this._appendOutput(
        `✗ Syntax error on line ${compileErrors[0].startLineNumber}: ${compileErrors[0].message}\n`,
        'out-error'
      );
      this._dispatchEvent('onCalculationError', {
        functionId: fnId,
        error:      compileErrors[0].message,
        lineNumber: compileErrors[0].startLineNumber
      });
      return;
    }

    /* Collect data */
    const bindings  = this._collectDataBindings();
    const variables = this._collectVariables();

    /* UI: running state */
    this._setStatusIndicator('status-running');
    this._setStatus(`Running ${fnId || 'script'}…`);
    this._appendOutput(`\n── Run${fnId ? ' [' + fnId + ']' : ''} ──────────────\n`, 'out-muted');
    this.shadowRoot.getElementById('btn-run').disabled = true;

    try {
      const response = await this._postWorker('EXECUTE', { script, bindings, variables }, 120000);

      if (response.type === 'EXEC_RESULT') {
        this._handleExecResult(response.payload, fnId);
      } else {
        this._handleExecError(response.payload, fnId);
      }
    } catch (err) {
      this._appendOutput(`✗ Worker error: ${err.message}\n`, 'out-error');
      this._setStatusIndicator('status-error');
    } finally {
      this.shadowRoot.getElementById('btn-run').disabled = false;
    }
  }

  async _preflightCheck(script) {
    if (!this._state.pyodideReady) return [];
    try {
      const response = await this._postWorker('COMPILE_CHECK', { script }, 10000);
      return (response.payload && response.payload.errors) || [];
    } catch (_) {
      return [];
    }
  }

  _sendPreflightCheck() {
    /* Fire-and-forget; result handled in _onWorkerMessage COMPILE_RESULT */
    if (!this._state.pyodideReady) return;
    const script = this._getEditorValue();
    if (!script) return;
    const id = this._nextMsgId();
    /* Register a lightweight handler (no timeout, we just update markers) */
    this._state.pendingMessages[id] = {
      resolve: () => {},
      reject:  () => {},
      timeout: null
    };
    this._state.worker.postMessage({ id, type: 'COMPILE_CHECK', payload: { script } });
  }

  _handleExecResult(payload, fnId = '') {
    const { results = {}, filterQueue = [], stdout, durationMs } = payload;

    this._state.lastResults     = results;
    this._state.lastDurationMs  = durationMs;

    /* Clear any existing error markers on success */
    this._applyMonacoMarkers([]);

    /* Print captured stdout */
    if (stdout && stdout.trim()) {
      this._appendOutput(stdout + '\n', null);
    }

    const resultCount = Object.keys(results).length;

    if (this.mode === 'production') {
      this._appendOutput(
        `✓ Done in ${durationMs}ms · Writing back ${resultCount} result(s) to planning model…\n`,
        'out-success'
      );
      this._applyWriteback(results);
    } else {
      /* Debug mode: render results in output panel */
      if (resultCount > 0) {
        this._renderResults(results);
      }
      this._appendOutput(`✓ Completed in ${durationMs}ms\n`, 'out-success');
    }

    /* Apply any set_scope() calls queued during execution */
    for (const f of (filterQueue || [])) {
      this._applySACFilter(f.bindingId, f.dim, f.members);
    }

    this._setStatusIndicator('status-idle');
    this._setStatus(`Last run: ${durationMs}ms`);
    this.shadowRoot.getElementById('execution-time').textContent = `${durationMs}ms`;

    this._dispatchEvent('onCalculationComplete', {
      functionId:  fnId || this.activeFunctionId,
      resultCount,
      durationMs
    });
  }

  _handleExecError(payload, fnId = '', isTest = false) {
    const { error, lineNumber, traceback, stdout } = payload;

    if (stdout && stdout.trim()) {
      this._appendOutput(stdout + '\n', null);
    }

    const lineInfo = lineNumber ? ` (line ${lineNumber})` : '';
    const prefix   = isTest ? '[TEST] ' : '';
    this._appendOutput(`${prefix}✗ Error${lineInfo}: ${error}\n`, 'out-error');

    if (traceback && traceback !== error) {
      this._appendOutput(traceback + '\n', 'out-muted');
    }

    if (lineNumber) {
      this._applyMonacoMarkers([{
        startLineNumber: lineNumber,
        startColumn:     1,
        endLineNumber:   lineNumber,
        endColumn:       999,
        message:         error,
        severity:        8
      }]);
    }

    this._setStatusIndicator('status-error');
    this._setStatus(`Error${lineInfo}`);
    this.shadowRoot.getElementById('btn-run').disabled  = false;
    this.shadowRoot.getElementById('btn-test').disabled = false;

    const eventName = isTest ? 'onTestError' : 'onCalculationError';
    this._dispatchEvent(eventName, {
      functionId: fnId || this.activeFunctionId,
      error,
      lineNumber
    });
  }

  /* ═══════════════════════════════════════════════════════════════════════════
     SECTION 5b — Test Mode Execution
     ═══════════════════════════════════════════════════════════════════════════ */

  /**
   * Run the script with testFixtures mock data instead of live SAC bindings.
   * Results are NEVER written to the planning model regardless of `mode`.
   */
  async _executeTest(scriptId) {
    if (!this._state.pyodideReady) {
      this._appendOutput('⚠ Pyodide not ready yet. Please wait.\n', 'out-warn');
      return;
    }

    const fnId   = scriptId || this.activeFunctionId || '';
    const script = scriptId
      ? (this._getStoredScript(scriptId) || '')
      : this._getEditorValue();

    if (!script.trim()) {
      this._appendOutput('⚠ Script is empty.\n', 'out-warn');
      return;
    }

    /* Pre-flight check */
    const compileErrors = await this._preflightCheck(script);
    if (compileErrors.length > 0) {
      this._applyMonacoMarkers(compileErrors);
      this._appendOutput(
        `[TEST] ✗ Syntax error on line ${compileErrors[0].startLineNumber}: ${compileErrors[0].message}\n`,
        'out-error'
      );
      this._dispatchEvent('onTestError', { functionId: fnId, error: compileErrors[0].message, lineNumber: compileErrors[0].startLineNumber });
      return;
    }

    /* Build bindings from testFixtures */
    const aliases  = this._parseBindingAliases();
    const fixtures = this._parseTestFixtures();
    const bindings = [];

    for (const slotName of BINDING_SLOTS) {
      if (!fixtures[slotName]) continue;
      const rows  = fixtures[slotName];
      const alias = aliases[slotName] || slotName;
      const hash  = 'fixture_' + this._hashRows(rows);
      bindings.push({ slotName, alias, rows, hash, changed: true });
    }

    /* Merge fixture variables with any real SAC variables */
    const sacVars      = this._collectVariables();
    const fixtureVars  = fixtures.variables || {};
    const variables    = Object.assign({}, sacVars, fixtureVars);

    /* Mark test mode visually */
    this._setStatusIndicator('status-running');
    this._setStatus(`🧪 Testing ${fnId || 'script'}…`);
    this._appendOutput(`\n── 🧪 Test${fnId ? ' [' + fnId + ']' : ''} ──────────────\n`, 'out-info');
    this.shadowRoot.getElementById('btn-run').disabled  = true;
    this.shadowRoot.getElementById('btn-test').disabled = true;
    this.shadowRoot.getElementById('pfe-root').classList.add('test-active');

    try {
      const response = await this._postWorker('TEST_EXECUTE', { script, bindings, variables }, 120000);
      if (response.type === 'TEST_EXEC_RESULT') {
        this._handleTestResult(response.payload, fnId);
      } else {
        this._handleExecError(response.payload, fnId, true);
      }
    } catch (err) {
      this._appendOutput(`[TEST] ✗ Worker error: ${err.message}\n`, 'out-error');
      this._setStatusIndicator('status-error');
    } finally {
      this.shadowRoot.getElementById('btn-run').disabled  = false;
      this.shadowRoot.getElementById('btn-test').disabled = false;
      this.shadowRoot.getElementById('pfe-root').classList.remove('test-active');
    }
  }

  _handleTestResult(payload, fnId = '') {
    const { results = {}, assertions = [], stdout, durationMs, passed, failCount } = payload;

    this._state.lastResults    = results;
    this._state.lastDurationMs = durationMs;
    this._applyMonacoMarkers([]);

    /* Print captured stdout */
    if (stdout && stdout.trim()) {
      this._appendOutput(stdout + '\n', null);
    }

    /* Render assertion summary */
    if (assertions.length > 0) {
      this._appendOutput(`\n── Assertions (${assertions.length - failCount} passed, ${failCount} failed) ──\n`, 'out-info');
      for (const a of assertions) {
        const cls  = a.passed ? 'out-success' : 'out-error';
        const icon = a.passed ? '✓' : '✗';
        this._appendOutput(`  ${icon} ${a.label}  actual=${a.actual}  expected=${a.expected}\n`, cls);
      }
    }

    /* Render result data */
    const resultCount = Object.keys(results).length;
    if (resultCount > 0) {
      this._appendOutput(`\n── Results (${resultCount}) ──\n`, 'out-info');
      this._renderResults(results);
    }

    const overallStatus = passed ? '✓ All tests passed' : `✗ ${failCount} assertion(s) failed`;
    const statusCss     = passed ? 'out-success' : 'out-error';
    this._appendOutput(`\n🧪 ${overallStatus} · ${durationMs}ms\n`, statusCss);

    this._setStatusIndicator(passed ? 'status-idle' : 'status-error');
    this._setStatus(`Test: ${passed ? 'PASS' : 'FAIL'} · ${durationMs}ms`);
    this.shadowRoot.getElementById('execution-time').textContent = `${durationMs}ms`;

    this._dispatchEvent('onTestComplete', {
      functionId:  fnId || this.activeFunctionId,
      passed,
      failCount,
      resultCount,
      durationMs
    });
  }

  /* ── Fixtures panel ─────────────────────────────────────────────────────── */

  _toggleFixturesPanel(forceOpen) {
    const panel = this.shadowRoot.getElementById('pfe-fixtures-panel');
    if (!panel) return;

    const open = forceOpen !== undefined ? forceOpen : !this._state.fixturesPanelOpen;
    this._state.fixturesPanelOpen = open;
    panel.hidden = !open;

    /* Update grid to show/hide the fixtures row */
    const root    = this.shadowRoot.getElementById('pfe-root');
    const fHeight = open ? '220px' : '0px';
    root.style.setProperty('--fixtures-height', fHeight);

    if (open && this._state.fixturesEditor) {
      /* Refresh editor layout after panel becomes visible */
      setTimeout(() => {
        try { this._state.fixturesEditor.layout(); } catch (_) {}
        /* Load current testFixtures into the fixture editor */
        const json = this.testFixtures && this.testFixtures !== '{}' ? this.testFixtures : DEFAULT_FIXTURES;
        if (this._state.fixturesModel) {
          this._state.fixturesModel.setValue(json);
        }
      }, 50);
    }
  }

  _saveFixtures() {
    if (!this._state.fixturesEditor) return;
    const json = this._state.fixturesEditor.getValue();
    try {
      JSON.parse(json);  /* validate */
      this.testFixtures = json;
      this._appendOutput('✓ Test fixtures saved.\n', 'out-success');
    } catch (err) {
      this._appendOutput(`✗ Invalid JSON in fixtures: ${err.message}\n`, 'out-error');
    }
  }

  _parseTestFixtures() {
    try {
      return JSON.parse(this.testFixtures || '{}');
    } catch (_) {
      return {};
    }
  }

  /* ═══════════════════════════════════════════════════════════════════════════
     SECTION 6 — Writeback (Production Mode)
     ═══════════════════════════════════════════════════════════════════════════ */

  /**
   * Write results back to SAC Planning Model.
   *
   * For scalar numeric results, uses the compound key format:
   *   "{bindingSlot}.{measureId}.{dim1=val1,dim2=val2}"
   * e.g. "dataBinding1.Revenue.Region=EMEA,FiscalYear=2024"
   *
   * Plain (non-compound) keys are shown in the output panel only.
   */
  _applyWriteback(results) {
    /* Group setValue calls by binding so we call submitData() once per model */
    const byBinding = {};

    for (const [key, value] of Object.entries(results)) {
      const parsed = this._parseWritebackKey(key);
      if (!parsed) {
        this._appendOutput(
          `  [skipped] "${key}" — not a compound writeback key\n`,
          'out-muted'
        );
        continue;
      }
      const { bindingId, measureId, coords } = parsed;
      if (!byBinding[bindingId]) byBinding[bindingId] = [];
      byBinding[bindingId].push({ measureId, coords, value });
    }

    for (const [bindingId, entries] of Object.entries(byBinding)) {
      let ds;
      try { ds = this.getDataSource(bindingId); } catch (_) { continue; }
      if (!ds) continue;

      let setCount = 0;
      for (const { measureId, coords, value } of entries) {
        try {
          ds.setValue(measureId, coords, Number(value));
          setCount++;
        } catch (err) {
          this._appendOutput(
            `  ✗ setValue failed for "${measureId}": ${err.message}\n`,
            'out-error'
          );
        }
      }

      if (setCount > 0) {
        try {
          ds.submitData();
          this._appendOutput(
            `  ✓ Submitted ${setCount} value(s) to ${bindingId}\n`,
            'out-success'
          );
        } catch (err) {
          this._appendOutput(`  ✗ submitData failed: ${err.message}\n`, 'out-error');
        }
      }
    }
  }

  /**
   * Parse compound writeback key: "{bindingId}.{measureId}.{dim1=val1,...}"
   * Returns null if key is not in this format.
   */
  _parseWritebackKey(key) {
    const parts = key.split('.');
    if (parts.length < 3) return null;
    const bindingId = parts[0];
    const measureId = parts[1];
    const dimStr    = parts.slice(2).join('.');
    const coords    = {};
    for (const pair of dimStr.split(',')) {
      const eq = pair.indexOf('=');
      if (eq < 1) return null;
      coords[pair.slice(0, eq).trim()] = pair.slice(eq + 1).trim();
    }
    return { bindingId, measureId, coords };
  }

  /* ═══════════════════════════════════════════════════════════════════════════
     SECTION 7 — Monaco Markers
     ═══════════════════════════════════════════════════════════════════════════ */

  _applyMonacoMarkers(errors) {
    if (!this._state.monacoReady || !this._state.editorModel) return;
    const markers = errors.map(e => ({
      ...e,
      owner:    'pfe-python',
      resource: this._state.editorModel.uri
    }));
    monaco.editor.setModelMarkers(this._state.editorModel, 'pfe-python', markers);
  }

  /* ═══════════════════════════════════════════════════════════════════════════
     SECTION 8 — Output Panel Rendering
     ═══════════════════════════════════════════════════════════════════════════ */

  _appendOutput(text, cssClass) {
    const panel = this.shadowRoot.getElementById('output-content');
    if (!panel) return;

    const wasAtBottom = panel.scrollHeight - panel.clientHeight <= panel.scrollTop + 20;

    const span = document.createElement('span');
    if (cssClass) span.className = cssClass;
    span.textContent = text;
    panel.appendChild(span);

    if (wasAtBottom) panel.scrollTop = panel.scrollHeight;
  }

  _renderResults(results) {
    for (const [key, value] of Object.entries(results)) {
      this._appendOutput(`\n[${key}]\n`, 'out-info');
      if (Array.isArray(value) && value.length > 0 && typeof value[0] === 'object') {
        this._renderTable(value);
      } else if (value !== null && typeof value === 'object') {
        this._appendOutput(JSON.stringify(value, null, 2) + '\n', null);
      } else {
        this._appendOutput(String(value) + '\n', null);
      }
    }
  }

  _renderTable(records) {
    const panel = this.shadowRoot.getElementById('output-content');
    if (!panel || !records.length) return;

    const headers = Object.keys(records[0]);
    const table   = document.createElement('table');
    table.className = 'out-table';

    const thead = table.createTHead();
    const hrow  = thead.insertRow();
    for (const h of headers) {
      const th = document.createElement('th');
      th.textContent = h;
      hrow.appendChild(th);
    }

    const tbody = table.createTBody();
    for (const rec of records.slice(0, 200)) {  /* cap at 200 rows for display */
      const tr = tbody.insertRow();
      for (const h of headers) {
        tr.insertCell().textContent = rec[h] != null ? String(rec[h]) : '';
      }
    }

    if (records.length > 200) {
      const note = document.createElement('span');
      note.className   = 'out-muted';
      note.textContent = `\n… ${records.length - 200} more rows not shown\n`;
      panel.appendChild(table);
      panel.appendChild(note);
    } else {
      panel.appendChild(table);
    }
  }

  _toggleOutputCollapse() {
    this._state.outputCollapsed = !this._state.outputCollapsed;
    const root   = this.shadowRoot.getElementById('pfe-root');
    const btn    = this.shadowRoot.getElementById('btn-collapse-output');
    const height = this._state.outputCollapsed
      ? '28px'
      : `${this.outputPanelHeight || 200}px`;
    root.style.setProperty('--output-height', height);
    btn.textContent = this._state.outputCollapsed ? '▲' : '▼';
  }

  /* ═══════════════════════════════════════════════════════════════════════════
     SECTION 9 — Script Storage
     ═══════════════════════════════════════════════════════════════════════════ */

  _parseScriptStorage() {
    try { return JSON.parse(this.scriptStorage || '{}'); } catch (_) { return {}; }
  }

  _persistScriptStorage(library) {
    this.scriptStorage = JSON.stringify(library);
  }

  _getStoredScript(fnId) {
    if (!fnId) return null;
    const lib = this._parseScriptStorage();
    return lib[fnId] ? lib[fnId].script : null;
  }

  _saveCurrentScript() {
    const fnIdEl = this.shadowRoot.getElementById('fn-id-input');
    const fnId   = (fnIdEl ? fnIdEl.value : this.activeFunctionId || '').trim();
    if (!fnId) {
      this._appendOutput('⚠ Enter a Function ID before saving.\n', 'out-warn');
      return;
    }
    const script = this._getEditorValue();
    this.saveScript(fnId, script, '');
    this._appendOutput(`✓ Script saved as "${fnId}"\n`, 'out-success');
  }

  _newScript() {
    this._setEditorValue(DEFAULT_SCRIPT);
    this.shadowRoot.getElementById('fn-id-input').value = '';
    this.activeFunctionId = '';
    this._applyMonacoMarkers([]);
  }

  _loadScriptIntoEditor(fnId) {
    if (!fnId) return;
    const script = this._getStoredScript(fnId);
    if (script != null) {
      this._setEditorValue(script);
      this.shadowRoot.getElementById('fn-id-input').value = fnId;
      this.activeFunctionId = fnId;
    }
  }

  _syncScriptSelector() {
    const sel = this.shadowRoot.getElementById('fn-select');
    if (!sel) return;
    const lib = this._parseScriptStorage();
    const ids = Object.keys(lib);

    sel.innerHTML = '<option value="">— Select script —</option>';
    for (const id of ids) {
      const opt = document.createElement('option');
      opt.value       = id;
      opt.textContent = id;
      if (id === this.activeFunctionId) opt.selected = true;
      sel.appendChild(opt);
    }
  }

  /* ═══════════════════════════════════════════════════════════════════════════
     SECTION 10 — SAC Filters
     ═══════════════════════════════════════════════════════════════════════════ */

  _applySACFilter(bindingId, dim, members) {
    let ds;
    try { ds = this.getDataSource(bindingId); } catch (_) { return; }
    if (!ds || typeof ds.setFilter !== 'function') return;

    try {
      ds.setFilter({
        dimension: dim,
        members:   members.map(m => ({ id: m }))
      });
      /* Invalidate hash so next run rebuilds the DataFrame */
      delete this._state.lastResultHash[bindingId];
      /* Also tell the worker to invalidate its DF cache */
      if (this._state.worker) {
        this._state.worker.postMessage({
          id:      this._nextMsgId(),
          type:    'SET_FILTER',
          payload: { bindingId, dim, members }
        });
      }
    } catch (err) {
      this._appendOutput(`⚠ setFilter failed for ${bindingId}: ${err.message}\n`, 'out-warn');
    }
  }

  /* ═══════════════════════════════════════════════════════════════════════════
     SECTION 11 — UI Helpers
     ═══════════════════════════════════════════════════════════════════════════ */

  _setStatus(text) {
    const el = this.shadowRoot.getElementById('status-text');
    if (el) el.textContent = text;
  }

  _setStatusIndicator(cssClass) {
    const el = this.shadowRoot.getElementById('status-indicator');
    if (!el) return;
    el.className = cssClass;
    const labels = {
      'status-idle':    'Ready',
      'status-loading': 'Loading…',
      'status-running': 'Running…',
      'status-error':   'Error'
    };
    el.title = labels[cssClass] || '';
  }

  _hideLoadingOverlay() {
    const el = this.shadowRoot.getElementById('pfe-loading-overlay');
    if (el) el.hidden = true;
  }

  _applyTheme(theme) {
    const root = this.shadowRoot.getElementById('pfe-root');
    if (!root) return;
    root.classList.remove('theme-light', 'theme-dark', 'theme-hc-black');
    if (theme === 'vs')          root.classList.add('theme-light');
    else if (theme === 'hc-black') root.classList.add('theme-hc-black');
    /* vs-dark is the default — no extra class needed */
  }

  _applyModeUI(mode) {
    const badge  = this.shadowRoot.getElementById('mode-badge');
    const root   = this.shadowRoot.getElementById('pfe-root');
    if (badge) {
      badge.textContent = mode === 'production' ? 'PRODUCTION' : 'DEBUG';
      badge.className   = mode === 'production' ? 'pfe-badge badge-production' : 'pfe-badge badge-debug';
    }
    if (root) {
      root.classList.toggle('mode-production', mode === 'production');
    }
    this._setStatus(`Mode: ${mode}`);
  }

  _applyToolbarVisibility() {
    const el = this.shadowRoot.getElementById('pfe-toolbar');
    if (el) el.hidden = !this.showToolbar;
  }

  _applyOutputVisibility() {
    const el = this.shadowRoot.getElementById('pfe-output-panel');
    if (el) el.hidden = !this.showOutputPanel;
  }

  _syncOutputHeight() {
    const root = this.shadowRoot.getElementById('pfe-root');
    if (root && !this._state.outputCollapsed) {
      root.style.setProperty('--output-height', `${this.outputPanelHeight || 200}px`);
    }
  }

  _dispatchEvent(eventName, detail) {
    this.dispatchEvent(new CustomEvent(eventName, { detail, bubbles: true, composed: true }));
  }

  /* ═══════════════════════════════════════════════════════════════════════════
     SECTION 12 — SAC Scripting API (callable from Story Scripts)
     ═══════════════════════════════════════════════════════════════════════════ */

  /** Returns the stored script string for the given Function ID, or null. */
  getScriptById(id) {
    return this._getStoredScript(id) || null;
  }

  /**
   * Persist a script in the story widget property.
   * @param {string} id          Function ID
   * @param {string} script      Python source
   * @param {string} description Optional description
   */
  saveScript(id, script, description = '') {
    if (!id) return;
    const lib = this._parseScriptStorage();
    lib[id] = {
      script,
      description: description || lib[id]?.description || '',
      lastModified: new Date().toISOString()
    };
    this._persistScriptStorage(lib);
    this._syncScriptSelector();
    this._dispatchEvent('onScriptSaved', { functionId: id });
  }

  /**
   * Execute a stored script by Function ID, or the editor's current script
   * if scriptId is omitted.
   */
  executeScript(scriptId) {
    this._executeActive(scriptId || null);
  }

  /** Returns the last execution result map as a JSON string. */
  getResult() {
    return JSON.stringify(this._state.lastResults || {});
  }

  /**
   * Apply an SAC-side filter on a binding slot.
   * @param {string} bindingId e.g. 'dataBinding1'
   * @param {string} dimension  Dimension ID
   * @param {string} members    Comma-separated member IDs
   */
  setFilter(bindingId, dimension, members) {
    const memberArr = (members || '').split(',').map(m => m.trim()).filter(Boolean);
    this._applySACFilter(bindingId, dimension, memberArr);
  }

  /** Clear the output panel and the last result map. */
  clearResults() {
    const panel = this.shadowRoot.getElementById('output-content');
    if (panel) panel.innerHTML = '';
    this._state.lastResults    = {};
    this._state.lastDurationMs = 0;
    this.shadowRoot.getElementById('execution-time').textContent = '';
    this.shadowRoot.getElementById('output-meta').textContent    = '';
  }

  /**
   * Get the current value of an SAC input variable.
   * @param {string} name  Variable name
   * @returns {string|null}
   */
  getVariable(name) {
    const vars = this._collectVariables();
    return vars[name] != null ? vars[name] : null;
  }

  /**
   * Attempt to set an SAC input variable value.
   * Fires onVariableChanged.
   */
  setVariable(name, value) {
    for (const slotName of BINDING_SLOTS) {
      let ds;
      try { ds = this.getDataSource(slotName); } catch (_) { continue; }
      if (!ds) continue;
      try {
        if (typeof ds.setVariableValue === 'function') {
          ds.setVariableValue(name, value);
        }
      } catch (_) { /* not all bindings expose variables */ }
    }
    this._dispatchEvent('onVariableChanged', { name, value });
  }

  /** Returns a JSON string array of all stored Function IDs. */
  getAllFunctionIds() {
    return JSON.stringify(Object.keys(this._parseScriptStorage()));
  }

  /**
   * Set execution mode.
   * @param {string} mode  'debug' | 'production'
   */
  setMode(mode) {
    if (mode !== 'debug' && mode !== 'production') return;
    this.mode = mode;
    this._applyModeUI(mode);
  }

  /**
   * Run the active script (or specified ID) in test mode using testFixtures.
   * Results are NEVER written to the planning model.
   * @param {string} scriptId  Optional Function ID to run.
   */
  runTest(scriptId) {
    this._executeTest(scriptId || null);
  }

  /** Returns the current testFixtures JSON string. */
  getTestFixtures() {
    return this.testFixtures || '{}';
  }

  /**
   * Set testFixtures from a JSON string.
   * @param {string} json  Fixtures JSON.
   */
  setTestFixtures(json) {
    try {
      JSON.parse(json);  /* validate */
      this.testFixtures = json;
      if (this._state.fixturesModel) {
        this._state.fixturesModel.setValue(json);
      }
    } catch (err) {
      this._appendOutput(`✗ setTestFixtures: invalid JSON — ${err.message}\n`, 'out-error');
    }
  }
}

/* ── Register the custom element ──────────────────────────────────────────── */
customElements.define('com-custom-pythoneditor', PythonFormulaEditor);
