// =============================================================================
// HAROLD BIRKETT'S MANUFACTURING REPORT PROGRAM (VERSION 2.1)
// 100% Client-Side Browser CRT Terminal & 132-Col Line Printer Controller
// =============================================================================

(function () {
  "use strict";

  // DOM References
  const crtScreen = document.getElementById("crt-screen");
  const crtTopRow1 = document.getElementById("crt-top-row1");
  const crtTopRow3 = document.getElementById("crt-top-row3");
  const crtPromptLabel = document.getElementById("crt-prompt-label");
  const crtInputForm = document.getElementById("crt-input-form");
  const crtInput = document.getElementById("crt-input");
  const lblStateBadge = document.getElementById("lbl-state-badge");

  const lblFactory = document.getElementById("lbl-factory");
  const lblCropStart = document.getElementById("lbl-crop-start");
  const lblDisk = document.getElementById("lbl-disk");
  const diskFilesList = document.getElementById("disk-files-list");

  const selTheme = document.getElementById("sel-theme");
  const chkStrictMode = document.getElementById("chk-strict-mode");
  const btnReturnMenu = document.getElementById("btn-return-menu");
  const btnSeedStMary = document.getElementById("btn-seed-stmary");
  const btnSeedRaceland = document.getElementById("btn-seed-raceland");
  const btnExportDisk = document.getElementById("btn-export-disk");
  const btnImportDisk = document.getElementById("btn-import-disk");
  const fileImportDisk = document.getElementById("file-import-disk");

  const selPrinterJob = document.getElementById("sel-printer-job");
  const chkGreenbar = document.getElementById("chk-greenbar");
  const btnBatchDemo = document.getElementById("btn-batch-demo");
  const btnDownloadTxt = document.getElementById("btn-download-txt");
  const btnPrintPaper = document.getElementById("btn-print-paper");
  const btnClearPrinter = document.getElementById("btn-clear-printer");
  const printerTray = document.getElementById("printer-tray");

  const diskModal = document.getElementById("disk-modal");
  const modalTitle = document.getElementById("modal-title");
  const modalBody = document.getElementById("modal-body");
  const btnCloseModal = document.getElementById("btn-close-modal");

  // Instantiate in-browser Wang 2200 / Niakwa BASIC-2 session
  const session = new window.MFREngine.MFRSession();
  window.mfrSession = session;

  // Local client state
  let latestPayload = null;
  let selectedJobId = null;
  let lastPrinterJobCount = 0;

  // ---------------------------------------------------------------------------
  // WebAudio Wang 2200 HEX(07) Terminal Beep (800Hz Square Wave, 150ms)
  // ---------------------------------------------------------------------------
  let audioCtx = null;
  function playTerminalBeep() {
    try {
      if (!audioCtx) {
        const AudioContextClass = window.AudioContext || window.webkitAudioContext;
        if (!AudioContextClass) return;
        audioCtx = new AudioContextClass();
      }
      if (audioCtx.state === "suspended") {
        audioCtx.resume();
      }
      const osc = audioCtx.createOscillator();
      const gain = audioCtx.createGain();
      osc.type = "square";
      osc.frequency.setValueAtTime(800, audioCtx.currentTime);
      gain.gain.setValueAtTime(0.08, audioCtx.currentTime);
      gain.gain.exponentialRampToValueAtTime(0.001, audioCtx.currentTime + 0.15);
      osc.connect(gain);
      gain.connect(audioCtx.destination);
      osc.start();
      osc.stop(audioCtx.currentTime + 0.15);
    } catch (e) {
      // Ignore audio errors if blocked by browser autoplay policy
    }
  }

  // ---------------------------------------------------------------------------
  // State Rendering
  // ---------------------------------------------------------------------------
  function renderState(payload) {
    if (!payload) return;
    latestPayload = payload;

    if (payload.beep) {
      playTerminalBeep();
    }

    // Top status rows
    crtTopRow1.textContent = payload.top_bar_row1 || "";
    crtTopRow3.textContent = payload.top_bar_row3 || "";

    // State badge & prompt
    lblStateBadge.textContent = "STATE: " + (payload.state || "MENU");
    const promptTxt = payload.current_prompt || "INPUT";
    crtPromptLabel.textContent = promptTxt.endsWith("?") ? promptTxt : promptTxt + "?";

    // Strict mode checkbox sync
    if (typeof payload.strict_wang_mode === "boolean") {
      chkStrictMode.checked = payload.strict_wang_mode;
    }

    // Metadata bar
    lblFactory.textContent = payload.factory_name || "---";
    lblCropStart.textContent = payload.crop_start_date || "---";
    lblDisk.textContent = payload.active_disk || "D12";

    // Disk file tags
    renderDiskFiles(payload.disk_files || []);

    // CRT lines
    renderCrtScreen(payload.crt_lines || [], payload.state);

    // Printer jobs
    renderPrinterJobs(payload.printer_jobs || []);

    // Keep focus on input unless user is interacting with a select or modal
    if (
      document.activeElement !== selTheme &&
      document.activeElement !== selPrinterJob &&
      diskModal.classList.contains("hidden")
    ) {
      crtInput.focus();
    }
  }

  function renderDiskFiles(files) {
    diskFilesList.innerHTML = "";

    // Always include MRPARAMS chip first
    const paramsTag = document.createElement("span");
    paramsTag.className = "disk-file-tag";
    paramsTag.textContent = "MRPARAMS";
    paramsTag.title = "Inspect MRPARAMS file on virtual disk";
    paramsTag.addEventListener("click", () => inspectDiskFile("MRPARAMS"));
    diskFilesList.appendChild(paramsTag);

    files.forEach((f) => {
      const fname = typeof f === "object" && f !== null ? f.name : String(f);
      const fdate = typeof f === "object" && f !== null && f.date ? ` (${f.date})` : "";
      const tag = document.createElement("span");
      tag.className = "disk-file-tag";
      tag.textContent = fname + fdate;
      tag.title = "Inspect crop day file " + fname + fdate;
      tag.addEventListener("click", () => inspectDiskFile(fname));
      diskFilesList.appendChild(tag);
    });
  }

  function renderCrtScreen(lines, currentState) {
    crtScreen.innerHTML = "";
    const isMenu = currentState === "MENU";

    lines.forEach((lineText) => {
      const div = document.createElement("div");

      // Make numbered menu rows clickable in MENU state
      if (isMenu) {
        const match = lineText.match(/^\s*(\d{1,2})\.\s+/);
        if (match) {
          const itemNum = match[1];
          div.className = "crt-menu-item-link";
          div.title = "Click to run Menu Item " + itemNum;
          div.addEventListener("click", () => {
            submitUserInput(itemNum);
          });
        }
      }

      div.textContent = lineText;
      crtScreen.appendChild(div);
    });

    crtScreen.scrollTop = crtScreen.scrollHeight;
  }

  function renderPrinterJobs(jobs) {
    // If a new job arrived, auto-select the newest job (first in array)
    if (jobs.length > lastPrinterJobCount && jobs.length > 0) {
      selectedJobId = jobs[0].id;
    }
    lastPrinterJobCount = jobs.length;

    selPrinterJob.innerHTML = "";
    if (jobs.length === 0) {
      const opt = document.createElement("option");
      opt.value = "";
      opt.textContent = "-- No Print Jobs Yet --";
      selPrinterJob.appendChild(opt);
      selectedJobId = null;
      printerTray.innerHTML =
        '<div style="padding:18px;color:#333;">No printer output in tray. Select a report or form from the CRT menu (Items 3, 4, 5, 6, 7, 11, 12, 13) or click <b>Print All Oct 2015 Reports</b> above.</div>';
      return;
    }

    // Ensure selectedJobId exists in jobs
    let activeJob = jobs.find((j) => String(j.id) === String(selectedJobId));
    if (!activeJob) {
      activeJob = jobs[0];
      selectedJobId = activeJob.id;
    }

    jobs.forEach((job) => {
      const opt = document.createElement("option");
      opt.value = String(job.id);
      const pageCount = (job.pages || []).length;
      opt.textContent = `#${job.id} [${job.timestamp || ""}] ${job.title} (${pageCount} pg)`;
      if (String(job.id) === String(selectedJobId)) {
        opt.selected = true;
      }
      selPrinterJob.appendChild(opt);
    });

    renderSelectedPaper(activeJob);
  }

  function renderSelectedPaper(job) {
    printerTray.innerHTML = "";
    if (!job || !job.pages || job.pages.length === 0) {
      printerTray.innerHTML =
        '<div style="padding:18px;color:#333;">Selected print job has no pages.</div>';
      return;
    }

    if (chkGreenbar.checked) {
      printerTray.classList.add("greenbar-on");
    } else {
      printerTray.classList.remove("greenbar-on");
    }

    job.pages.forEach((pageContent, idx) => {
      const sheet = document.createElement("div");
      sheet.className = "paper-sheet";

      const hdr = document.createElement("div");
      hdr.className = "paper-page-header";
      const leftSpan = document.createElement("span");
      leftSpan.textContent = job.title;
      const rightSpan = document.createElement("span");
      rightSpan.textContent = `CONTINUOUS FORM 215(132) — SHEET ${idx + 1} OF ${job.pages.length}`;
      hdr.appendChild(leftSpan);
      hdr.appendChild(rightSpan);
      sheet.appendChild(hdr);

      const contentBox = document.createElement("div");
      contentBox.className = "paper-content";

      const rawLines = Array.isArray(pageContent)
        ? pageContent
        : String(pageContent).replace(/\r\n/g, "\n").split("\n");
      rawLines.forEach((lineStr) => {
        const lineDiv = document.createElement("div");
        lineDiv.className = "paper-line";
        lineDiv.textContent = lineStr.length > 0 ? lineStr : " ";
        contentBox.appendChild(lineDiv);
      });

      sheet.appendChild(contentBox);
      printerTray.appendChild(sheet);
    });
  }

  // ---------------------------------------------------------------------------
  // User Actions (100% Synchronous In-Browser Execution)
  // ---------------------------------------------------------------------------
  function submitUserInput(valueStr) {
    const payload = session.handleInput(valueStr);
    crtInput.value = "";
    renderState(payload);
  }

  function inspectDiskFile(name) {
    const res = session.getDiskFileContent(name);
    modalTitle.textContent = "VIRTUAL DISK INSPECTOR: " + name;
    modalBody.textContent = JSON.stringify(res, null, 2);
    diskModal.classList.remove("hidden");
  }

  // ---------------------------------------------------------------------------
  // Event Listeners
  // ---------------------------------------------------------------------------
  crtInputForm.addEventListener("submit", (e) => {
    e.preventDefault();
    submitUserInput(crtInput.value);
  });

  // Quick-key buttons
  document.querySelectorAll(".qk-btn").forEach((btn) => {
    btn.addEventListener("click", () => {
      const val =
        btn.getAttribute("data-input") !== null
          ? btn.getAttribute("data-input")
          : btn.getAttribute("data-val") || "";
      submitUserInput(val);
    });
  });

  // Theme switcher on document.body
  selTheme.addEventListener("change", () => {
    document.body.classList.remove("theme-green", "theme-amber", "theme-dos", "theme-win95");
    document.body.classList.add(selTheme.value);
  });

  // Strict mode toggle
  chkStrictMode.addEventListener("change", () => {
    const payload = session.handleAction({
      action: "toggle_strict",
      strict: chkStrictMode.checked,
    });
    renderState(payload);
  });

  // Return to main menu
  btnReturnMenu.addEventListener("click", () => {
    const payload = session.handleAction({ action: "reset_menu" });
    renderState(payload);
  });

  // Seed datasets
  btnSeedStMary.addEventListener("click", () => {
    const payload = session.handleAction({ action: "seed_st_mary" });
    renderState(payload);
  });

  btnSeedRaceland.addEventListener("click", () => {
    const payload = session.handleAction({ action: "seed_raceland" });
    renderState(payload);
  });

  // Export virtual disk as .JSON file
  if (btnExportDisk) {
    btnExportDisk.addEventListener("click", () => {
      const bundle = session.exportDiskBundle();
      const blob = new Blob([JSON.stringify(bundle, null, 2)], {
        type: "application/json;charset=utf-8",
      });
      const url = URL.createObjectURL(blob);
      const a = document.createElement("a");
      a.href = url;
      a.download = "Birkett_MFR_Virtual_Disk.json";
      document.body.appendChild(a);
      a.click();
      document.body.removeChild(a);
      URL.revokeObjectURL(url);
    });
  }

  // Import virtual disk from .JSON file
  if (btnImportDisk && fileImportDisk) {
    btnImportDisk.addEventListener("click", () => {
      fileImportDisk.value = "";
      fileImportDisk.click();
    });

    fileImportDisk.addEventListener("change", (e) => {
      const file = e.target.files && e.target.files[0];
      if (!file) return;
      const reader = new FileReader();
      reader.onload = (ev) => {
        try {
          const parsed = JSON.parse(String(ev.target.result));
          const payload = session.importDiskBundle(parsed);
          renderState(payload);
        } catch (err) {
          playTerminalBeep();
          crtTopRow3.textContent = "DISK IMPORT ERROR: " + err.message;
        }
      };
      reader.readAsText(file);
    });
  }

  // Batch print all Oct 2015 sample reports
  btnBatchDemo.addEventListener("click", () => {
    btnBatchDemo.disabled = true;
    btnBatchDemo.textContent = "Generating Reports...";
    try {
      const payload = session.handleAction({
        action: "quick_print_demo_pack",
      });
      renderState(payload);
    } finally {
      btnBatchDemo.disabled = false;
      btnBatchDemo.textContent = "Print All Oct 2015 Reports";
    }
  });

  // Printer job selector
  selPrinterJob.addEventListener("change", () => {
    selectedJobId = selPrinterJob.value;
    if (latestPayload && latestPayload.printer_jobs) {
      const job = latestPayload.printer_jobs.find(
        (j) => String(j.id) === String(selectedJobId)
      );
      if (job) renderSelectedPaper(job);
    }
  });

  // Green-bar toggle
  chkGreenbar.addEventListener("change", () => {
    if (chkGreenbar.checked) {
      printerTray.classList.add("greenbar-on");
    } else {
      printerTray.classList.remove("greenbar-on");
    }
  });

  // Download .TXT with ASCII form-feeds (\f) between pages
  btnDownloadTxt.addEventListener("click", () => {
    if (!latestPayload || !latestPayload.printer_jobs) return;
    const job = latestPayload.printer_jobs.find(
      (j) => String(j.id) === String(selectedJobId)
    );
    if (!job || !job.pages) return;

    const pageStrings = job.pages.map((p) =>
      Array.isArray(p) ? p.join("\n") : String(p)
    );
    const content = pageStrings.join("\n\f\n");
    const blob = new Blob([content], { type: "text/plain;charset=utf-8" });
    const url = URL.createObjectURL(blob);
    const a = document.createElement("a");
    const safeTitle = (job.title || "MFR_REPORT")
      .replace(/[^A-Za-z0-9_\-]+/g, "_")
      .replace(/^_+|_+$/g, "");
    a.href = url;
    a.download = `${safeTitle}_Job${job.id}.txt`;
    document.body.appendChild(a);
    a.click();
    document.body.removeChild(a);
    URL.revokeObjectURL(url);
  });

  // Browser print
  btnPrintPaper.addEventListener("click", () => {
    window.print();
  });

  // Clear printer tray
  btnClearPrinter.addEventListener("click", () => {
    const payload = session.handleAction({ action: "clear_printer" });
    renderState(payload);
  });

  // Close modal
  btnCloseModal.addEventListener("click", () => {
    diskModal.classList.add("hidden");
    crtInput.focus();
  });
  diskModal.addEventListener("click", (e) => {
    if (e.target === diskModal) {
      diskModal.classList.add("hidden");
      crtInput.focus();
    }
  });

  // Initial load directly from in-browser session
  renderState(session.getStatusPayload());
})();
