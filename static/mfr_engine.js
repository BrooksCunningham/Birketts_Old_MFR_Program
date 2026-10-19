// =============================================================================
// HAROLD BIRKETT'S MANUFACTURING REPORT PROGRAM (VERSION 2.1)
// 100% Client-Side JavaScript Wang 2200 / Niakwa BASIC-2 Engine
// Implements:
//   MRSTART, MRDATA, MRDATAWU, MRDATACO, MRDACOWU, MRDATAPR, MRDATAP2,
//   MRCALC, MRREPOPR, MRREPOP2, MRREPOCK, MRSTOCK, MRSTOCKC, MRSTOCKG,
//   MRHELPC, MRHELPS, MRENCROP, MRCUSTOM, MRCUSTPR, MRBLANFM, MRDATAFM,
//   MRSTOKFM, MRCOMPPR.
// =============================================================================

(function (root, factory) {
  if (typeof module === "object" && module.exports) {
    module.exports = factory();
  } else {
    root.MFREngine = factory();
  }
})(typeof self !== "undefined" ? self : this, function () {
  "use strict";

  // ---------------------------------------------------------------------------
  // 1-Indexed Wang BASIC-2 Array Classes
  // ---------------------------------------------------------------------------
  class OneBasedArray1D {
    constructor(size, defaultVal = 0.0) {
      this.size = size;
      this.defaultVal = defaultVal;
      this.data = new Array(size + 1).fill(defaultVal);
    }

    get(idx) {
      const i = Math.round(idx);
      if (i >= 0 && i <= this.size) {
        return this.data[i];
      }
      return this.defaultVal;
    }

    set(idx, val) {
      const i = Math.round(idx);
      if (i >= 0 && i <= this.size) {
        this.data[i] = val;
      }
    }

    toList() {
      return this.data.slice(1);
    }

    fromList(vals) {
      if (!Array.isArray(vals)) return;
      const limit = Math.min(vals.length, this.size);
      for (let i = 0; i < limit; i++) {
        this.data[i + 1] = vals[i];
      }
    }
  }

  class OneBasedArray2D {
    constructor(rows, cols, defaultVal = 0.0) {
      this.rows = rows;
      this.cols = cols;
      this.defaultVal = defaultVal;
      this.data = [];
      for (let r = 0; r <= rows; r++) {
        this.data.push(new Array(cols + 1).fill(defaultVal));
      }
    }

    get(r, c) {
      const ri = Math.round(r);
      const ci = Math.round(c);
      if (ri >= 0 && ri <= this.rows && ci >= 0 && ci <= this.cols) {
        return this.data[ri][ci];
      }
      return this.defaultVal;
    }

    set(r, c, val) {
      const ri = Math.round(r);
      const ci = Math.round(c);
      if (ri >= 0 && ri <= this.rows && ci >= 0 && ci <= this.cols) {
        this.data[ri][ci] = val;
      }
    }

    clear(maxRow = null) {
      const rmax = maxRow !== null ? maxRow : this.rows;
      for (let r = 1; r <= rmax; r++) {
        for (let c = 1; c <= this.cols; c++) {
          this.data[r][c] = this.defaultVal;
        }
      }
    }
  }

  // ---------------------------------------------------------------------------
  // Math & Brix Polynomial Helpers
  // ---------------------------------------------------------------------------
  function safeDiv(num, den) {
    if (Math.abs(den) < 1e-12) return 0.0;
    return num / den;
  }

  function brixDensityPoly5(brix) {
    const k = Number(brix) || 0.0;
    return (
      62.2514 +
      0.240778534 * k +
      0.0007971907 * Math.pow(k, 2) +
      0.00000395521 * Math.pow(k, 3) -
      1.247356e-8 * Math.pow(k, 4) -
      1.94891e-11 * Math.pow(k, 5)
    );
  }

  function brixLbsSolidsPerGal(brix) {
    const b = Number(brix) || 0.0;
    if (Math.abs(b) < 1e-12) return 0.0;
    const k1 = brixDensityPoly5(b);
    return (k1 / 7.48) * (b / 100.0);
  }

  function brixDensityPoly4(brix) {
    const b = Number(brix) || 0.0;
    return (
      62.2511 +
      0.24081 * b +
      0.0007902404 * Math.pow(b, 2) +
      0.00000423954 * Math.pow(b, 3) -
      1.657193e-8 * Math.pow(b, 4)
    );
  }

  // ---------------------------------------------------------------------------
  // Wang 2200 BASIC-2 Date Conversion Subroutines (DEFFN'221 - DEFFN'225)
  // ---------------------------------------------------------------------------
  function pad2(n) {
    return String(n).padStart(2, "0");
  }

  function wangParseMmddyy(dateStr) {
    const s = String(dateStr || "").trim();
    const parts = s.split("/");
    if (parts.length !== 3) return null;
    const p0 = parts[0].trim();
    const p1 = parts[1].trim();
    const p2 = parts[2].trim();
    if (!/^\d+$/.test(p0) || !/^\d+$/.test(p1) || !/^\d+$/.test(p2)) {
      return null;
    }
    const u0 = parseInt(p0, 10);
    const u6 = parseInt(p1, 10);
    const u9 = parseInt(p2, 10);
    if (u0 < 1 || u0 > 12 || u9 < 0 || u9 > 99) return null;

    const daysInMonths = [31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31];
    if (u9 % 4 === 0) daysInMonths[1] = 29;
    if (u6 < 1 || u6 > daysInMonths[u0 - 1]) return null;

    const formattedZero = `${pad2(u0)}/${pad2(u6)}/${pad2(u9)}`;
    let dayOfYear = u6;
    for (let i = 0; i < u0 - 1; i++) {
      dayOfYear += daysInMonths[i];
    }
    const julian = u9 * 1000 + dayOfYear;
    return { month: u0, day: u6, year: u9, formatted: formattedZero, julian };
  }

  function wangNormalizeJulian(q9) {
    const yr = Math.floor(q9 / 1000);
    const ddd = q9 - yr * 1000;
    const u0 = Math.trunc(365.25 * (yr - 1)) + ddd;
    let newYr = Math.trunc(u0 / 365.25);
    const diff = u0 - Math.trunc(365.25 * newYr);
    const sgn = diff > 0 ? 1 : diff < 0 ? -1 : 0;
    newYr = newYr - 1 + sgn;
    const newDdd = u0 - Math.trunc(365.25 * newYr);
    return (newYr + 1) * 1000 + newDdd;
  }

  function wangJulianToMmddyy(u9Input) {
    const u9 = wangNormalizeJulian(Math.round(u9Input));
    const q9 = Math.floor(u9 / 1000);
    const ddd = u9 - q9 * 1000;
    const daysInMonths = [31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31];
    if (q9 % 4 === 0) daysInMonths[1] = 29;
    let cum = 0;
    let u6 = 1;
    let u0 = ddd;
    for (let mIdx = 1; mIdx <= 12; mIdx++) {
      const dim = daysInMonths[mIdx - 1];
      if (cum + dim >= ddd) {
        u6 = mIdx;
        u0 = ddd - cum;
        break;
      }
      cum += dim;
    }
    return {
      formatted: `${pad2(u6)}/${pad2(u0)}/${pad2(q9 % 100)}`,
      julian: u9,
    };
  }

  function wangJulianDiff(u0Start, u6End) {
    const u0 = Math.round(u0Start);
    const u6 = Math.round(u6End);
    const yr6 = Math.floor(u6 / 1000);
    const ddd6 = u6 - yr6 * 1000;
    const yr0 = Math.floor(u0 / 1000);
    const ddd0 = u0 - yr0 * 1000;
    const days6 = Math.trunc(365.25 * (yr6 - 1)) + ddd6;
    const days0 = Math.trunc(365.25 * (yr0 - 1)) + ddd0;
    let u3 = days6 - days0;
    if (u3 < -18000) u3 += 36525;
    return u3;
  }

  function zellerWeekdayIndex(mmDdYy) {
    const m0 = parseInt(String(mmDdYy).slice(0, 2), 10);
    const d = parseInt(String(mmDdYy).slice(3, 5), 10);
    const y0 = parseInt(String(mmDdYy).slice(6, 8), 10);
    if (isNaN(m0) || isNaN(d) || isNaN(y0)) return 0;
    let m = m0;
    let y = y0 < 50 ? y0 + 2000 : y0 + 1900;
    if (m <= 2) {
      m += 12;
      y -= 1;
    }
    let n =
      d +
      Math.trunc((13 * m + 3) / 5) +
      Math.trunc((5 * y) / 4) -
      Math.trunc(y / 100) +
      Math.trunc(y / 400) +
      1;
    n = n - Math.trunc(n / 7) * 7;
    return n;
  }

  // ---------------------------------------------------------------------------
  // Wang 2200 BASIC-2 PRINTUSING Formatter (with BCD Truncation)
  // ---------------------------------------------------------------------------
  function formatWithCommas(intVal) {
    const s = String(Math.trunc(intVal));
    return s.replace(/\B(?=(\d{3})+(?!\d))/g, ",");
  }

  function formatPrintusingNumeric(spec, valInput) {
    const width = spec.length;
    const hasSign = spec.startsWith("-") || spec.startsWith("+");
    const hasCommas = spec.includes(",");
    const decimals = spec.includes(".") ? spec.split(".")[1].length : 0;

    let val = Number(valInput);
    if (!Number.isFinite(val)) val = 0.0;

    // Wang 2200 BASIC-2 PRINTUSING truncates BCD mantissa digits at last '#'
    let isNeg = val < -1e-12;
    const absVal = Math.abs(val);
    const factor = Math.pow(10, decimals);
    const roundedInt = Math.floor(absVal * factor + 1e-7);
    if (roundedInt === 0) isNeg = false;

    let numStr;
    if (decimals > 0) {
      const intPart = Math.floor(roundedInt / factor);
      const fracPart = roundedInt % factor;
      const intStr = hasCommas ? formatWithCommas(intPart) : String(intPart);
      const fracStr = String(fracPart).padStart(decimals, "0");
      numStr = `${intStr}.${fracStr}`;
    } else {
      const intPart = roundedInt;
      numStr = hasCommas ? formatWithCommas(intPart) : String(intPart);
    }

    if (isNeg) {
      if (hasSign) {
        numStr = "-" + numStr;
      } else {
        return "#".repeat(width);
      }
    }

    if (numStr.length > width) {
      return spec.replace(/-/g, "#");
    }

    return numStr.padStart(width, " ");
  }

  function formatPrintusing(imageInput, args) {
    let image = String(imageInput);
    if (image.startsWith("%")) {
      image = image.slice(1);
    }

    const out = [];
    let i = 0;
    const n = image.length;
    let argIdx = 0;

    while (i < n) {
      const ch = image[i];
      if (ch === "-" && i + 1 < n && (image[i + 1] === "#" || image[i + 1] === ".")) {
        let j = i + 1;
        while (j < n && (image[j] === "#" || image[j] === "," || image[j] === ".")) {
          j++;
        }
        const spec = image.slice(i, j);
        const val = argIdx < args.length ? args[argIdx] : 0.0;
        argIdx++;
        if (typeof val === "string") {
          out.push(val.slice(0, spec.length).padEnd(spec.length, " "));
        } else {
          out.push(formatPrintusingNumeric(spec, val));
        }
        i = j;
      } else if (ch === "#") {
        let j = i;
        while (j < n && (image[j] === "#" || image[j] === "," || image[j] === ".")) {
          j++;
        }
        const spec = image.slice(i, j);
        const val = argIdx < args.length ? args[argIdx] : "";
        argIdx++;
        if (typeof val === "string" && !spec.includes(".") && !spec.includes(",")) {
          const w = spec.length;
          out.push(val.slice(0, w).padEnd(w, " "));
        } else {
          const numVal = typeof val === "string" ? 0.0 : Number(val);
          out.push(formatPrintusingNumeric(spec, numVal));
        }
        i = j;
      } else {
        out.push(ch);
        i++;
      }
    }

    return out.join("").replace(/\s+$/, "");
  }

  // ---------------------------------------------------------------------------
  // Daily Input Item Definitions (Items 2..108, 246, 251..254)
  // ---------------------------------------------------------------------------
  function getDailyInputPrompts(J_str, H_str, H_num) {
    const items = [];
    items.push([2, " 2   LBS TRS PURCHASED", null]);
    for (let k = 1; k <= 10; k++) {
      items.push([k + 2, `${String(k + 2).padStart(2, " ")}   HOURS LOST`, J_str.get(k)]);
    }
    items.push([13, "13   TOTAL HOURS AVAILABLE FOR GRINDING TODAY", null]);
    for (let k = 1; k <= 12; k++) {
      items.push([k + 13, `${String(k + 13).padStart(2, " ")}   QUANTITY USED`, H_str.get(k)]);
    }

    items.push([26, "26   CRUSHER JUICE BRIX", null]);
    items.push([27, "27   CRUSHER JUICE POL", null]);
    if (H_num.get(2) !== 0) items.push([28, "28   CRUSHER JUICE GLUCOSE", null]);
    if (H_num.get(3) !== 0) items.push([29, "29   CRUSHER JUICE pH", null]);

    items.push([30, "30   MIXED JUICE BRIX", null]);
    items.push([31, "31   MIXED JUICE POL", null]);
    if (H_num.get(4) !== 0) items.push([32, "32   MIXED JUICE GLUCOSE", null]);
    if (H_num.get(5) !== 0) items.push([33, "33   MIXED JUICE pH", null]);

    items.push([34, "34   LAST ROLL JUICE BRIX", null]);
    items.push([35, "35   LAST ROLL JUICE POL", null]);
    items.push([36, "36   CLARIFIED JUICE BRIX", null]);
    items.push([37, "37   CLARIFIED JUICE POL", null]);
    if (H_num.get(6) !== 0) items.push([38, "38   CLARIFIED JUICE GLUCOSE", null]);
    if (H_num.get(7) !== 0) items.push([39, "39   CLARIFIED JUICE pH", null]);

    if (H_num.get(18) !== 0) {
      items.push([40, "40   FILTRATE JUICE BRIX", null]);
      items.push([41, "41   FILTRATE JUICE POL", null]);
    }

    items.push([42, "42   SYRUP BRIX", null]);
    items.push([43, "43   SYRUP POL", null]);
    if (H_num.get(8) !== 0) items.push([44, "44   SYRUP GLUCOSE", null]);
    if (H_num.get(9) !== 0) items.push([45, "45   SYRUP pH", null]);

    items.push([46, "46   A MASSECUITE BRIX", null]);
    items.push([47, "47   A MASSECUITE POL", null]);
    if (H_num.get(19) !== 0) {
      items.push([48, "48   TOP-OFF A MASSECUITE BRIX", null]);
      items.push([49, "49   TOP-OFF A MASSECUITE POL", null]);
    }

    items.push([50, "50   B MASSECUITE BRIX", null]);
    items.push([51, "51   B MASSECUITE POL", null]);
    items.push([52, "52   C MASSECUITE BRIX", null]);
    items.push([53, "53   C MASSECUITE POL", null]);
    items.push([54, "54   A MOLASSES BRIX", null]);
    items.push([55, "55   A MOLASSES POL", null]);
    if (H_num.get(19) !== 0) {
      items.push([56, "56   TOP-OFF A MOLASSES BRIX", null]);
      items.push([57, "57   TOP-OFF A MOLASSES POL", null]);
    }

    items.push([58, "58   B MOLASSES BRIX", null]);
    items.push([59, "59   B MOLASSES POL", null]);
    items.push([60, "60   GRAIN BRIX", null]);
    items.push([61, "61   GRAIN POL", null]);
    items.push([62, "62   C MAGMA BRIX", null]);
    items.push([63, "63   C MAGMA POL", null]);

    if (H_num.get(20) !== 0) {
      if (H_num.get(22) !== 0) {
        items.push([64, "64   B MAGMA BRIX", null]);
        items.push([65, "65   B MAGMA POL", null]);
      } else {
        items.push([64, "64   C CYCLONE BRIX", null]);
        items.push([65, "65   C CYCLONE POL", null]);
      }
    }

    items.push([66, "66   CU. FT. OF A MASSECUITE MADE", null]);
    if (H_num.get(19) !== 0) {
      items.push([67, "67   CU. FT. OF TOP-OFF A MASSECUITE MADE", null]);
    }
    items.push([68, "68   CU. FT. OF B MASSECUITE MADE", null]);
    items.push([69, "69   CU. FT. OF C MASSECUITE MADE", null]);
    items.push([70, "70   MOISTURE % SUGAR MADE", null]);
    items.push([71, "71   POL OF SUGAR MADE", null]);
    if (H_num.get(10) !== 0) items.push([72, "72   STARCH SUGAR MADE", null]);
    if (H_num.get(11) !== 0) items.push([73, "73   DEXTRAN SUGAR MADE", null]);

    items.push([74, "74   FINAL MOLASSES MADE BRIX", null]);
    items.push([75, "75   FINAL MOLASSES MADE POL", null]);
    if (H_num.get(12) !== 0) items.push([76, "76   FINAL MOLASSES MADE % GLUCOSE", null]);
    if (H_num.get(13) !== 0) items.push([77, "77   FINAL MOLASSES MADE % ASH", null]);
    if (H_num.get(14) !== 0) items.push([78, "78   FINAL MOLASSES MADE CLERGET", null]);

    items.push([79, "79   FINAL MOLASSES SHIPPED BRIX", null]);
    items.push([80, "80   FINAL MOLASSES SHIPPED POL", null]);
    if (H_num.get(15) !== 0) items.push([81, "81   FINAL MOLASSES SHIPPED % GLUCOSE", null]);
    if (H_num.get(16) !== 0) items.push([82, "82   FINAL MOLASSES SHIPPED % ASH", null]);
    if (H_num.get(17) !== 0) items.push([83, "83   FINAL MOLASSES SHIPPED CLERGET", null]);

    items.push([84, "84   POL % FILTER CAKE", null]);
    if (H_num.get(21) !== 0) items.push([85, "85   MOISTURE % FILTER CAKE", null]);

    items.push([86, "86   POL % BAGASSE", null]);
    items.push([87, "87   MOISTURE % BAGASSE", null]);
    items.push([88, "88   TONS CANE PURCHASED", null]);
    items.push([91, "91   TONS CANE GROUND", null]);
    items.push([92, "92   TONS MIXED JUICE", null]);
    items.push([93, "93   TONS IMBIBITION WATER", null]);
    items.push([94, "94   TONS FILTER CAKE MADE", null]);
    items.push([95, "95   LBS SUGAR MADE", null]);
    items.push([96, "96   GALLONS FINAL MOLASSES MADE", null]);
    items.push([97, "97   LBS SUGAR SHIPPED", null]);
    items.push([98, "98   GALLONS FINAL MOLASSES SHIPPED", null]);
    items.push([99, "99   CORE LAB CANE, % POL", null]);
    items.push([100, "100  CORE LAB CANE, % BRIX", null]);
    items.push([101, "101  CORE LAB CANE, % FIBER", null]);
    items.push([102, "102  RAINFALL, INCHES", null]);
    items.push([103, "103  MAXIMUM TEMPERATURE, DEG. F", null]);
    items.push([104, "104  MINIMUM TEMPERATURE, DEG. F", null]);
    items.push([105, "105  LBS SUGAR BRIX IN PROCESS", null]);
    items.push([106, "106  LBS SUGAR POL IN PROCESS", null]);
    items.push([107, "107  LBS FINAL MOLASSES BRIX IN PROCESS", null]);
    items.push([108, "108  LBS FINAL MOLASSES POL IN PROCESS", null]);

    if (H_num.get(27) !== 0) {
      items.push([246, "246  TONS OF METERED IMBIBITON WATER", null]);
      items.push([251, "251  LBS SUGAR IN WAREHOUSE # 1", null]);
      items.push([252, "252  LBS SUGAR IN WAREHOUSE # 2", null]);
      items.push([253, "253  LBS SUGAR IN WAREHOUSE # 3", null]);
      items.push([254, "254  LBS SUGAR IN WAREHOUSE # 4", null]);
    }

    return items;
  }

  // ---------------------------------------------------------------------------
  // Preliminary Workup (MRDATAWU & MRDACOWU)
  // ---------------------------------------------------------------------------
  function runWorkupOnA(A, H_num, isCorrection = false) {
    A.set(247, 1, A.get(246, 1));
    if (isCorrection) {
      A.set(255, 1, A.get(251, 1));
      A.set(256, 1, A.get(252, 1));
      A.set(257, 1, A.get(253, 1));
      A.set(258, 1, A.get(254, 1));
    }

    // Lost time filling routine (0050-0090)
    let sumLost = 0.0;
    for (let j = 1; j <= 10; j++) {
      const v = A.get(j + 2, 1);
      A.set(109 + j, 1, v);
      sumLost += v;
    }
    A.set(120, 1, sumLost);
    A.set(121, 1, A.get(13, 1));

    // Material and supplies filling routine (0110-0130)
    for (let j = 1; j <= 12; j++) {
      A.set(121 + j, 1, A.get(13 + j, 1));
    }

    // Weighting factor (0140-0180)
    if (H_num.get(1) === 0) {
      A.set(109, 1, A.get(91, 1));
    } else {
      A.set(109, 1, 1.0);
    }

    const k = A.get(109, 1);
    for (let idx = 134; idx <= 187; idx++) {
      A.set(idx, 1, 0.0);
    }

    if (A.get(26, 1) !== 0) {
      A.set(134, 1, k);
      A.set(148, 1, k * A.get(26, 1));
      A.set(149, 1, k * A.get(27, 1));
    }
    if (A.get(28, 1) !== 0) {
      A.set(135, 1, k);
      A.set(150, 1, k * A.get(28, 1));
    }
    if (A.get(29, 1) !== 0) {
      A.set(136, 1, k);
      A.set(151, 1, k * A.get(29, 1));
    }
    if (A.get(34, 1) !== 0) {
      A.set(143, 1, k);
      A.set(160, 1, k * A.get(34, 1));
      A.set(161, 1, k * A.get(35, 1));
    }
    if (A.get(36, 1) !== 0) {
      A.set(137, 1, k);
      A.set(152, 1, k * A.get(36, 1));
      A.set(153, 1, k * A.get(37, 1));
    }
    if (A.get(38, 1) !== 0) {
      A.set(138, 1, k);
      A.set(154, 1, k * A.get(38, 1));
    }
    if (A.get(39, 1) !== 0) {
      A.set(139, 1, k);
      A.set(155, 1, k * A.get(39, 1));
    }
    if (A.get(42, 1) !== 0) {
      A.set(140, 1, k);
      A.set(156, 1, k * A.get(42, 1));
      A.set(157, 1, k * A.get(43, 1));
    }
    if (A.get(44, 1) !== 0) {
      A.set(141, 1, k);
      A.set(158, 1, k * A.get(44, 1));
    }
    if (A.get(45, 1) !== 0) {
      A.set(142, 1, k);
      A.set(159, 1, k * A.get(45, 1));
    }
    if (A.get(40, 1) !== 0) {
      A.set(144, 1, k);
      A.set(162, 1, k * A.get(40, 1));
      A.set(163, 1, k * A.get(41, 1));
    }
    if (A.get(60, 1) !== 0) {
      A.set(145, 1, k);
      A.set(164, 1, k * A.get(60, 1));
      A.set(165, 1, k * A.get(61, 1));
    }
    if (A.get(62, 1) !== 0) {
      A.set(146, 1, k);
      A.set(166, 1, k * A.get(62, 1));
      A.set(167, 1, k * A.get(63, 1));
    }
    if (A.get(64, 1) !== 0) {
      A.set(147, 1, k);
      A.set(168, 1, k * A.get(64, 1));
      A.set(169, 1, k * A.get(65, 1));
    }

    // Weighted cubic feet routine (0720-0880)
    for (let j = 1; j <= 4; j++) {
      A.set(183 + j, 1, A.get(65 + j, 1));
    }
    A.set(170, 1, A.get(184, 1) * A.get(46, 1));
    A.set(171, 1, A.get(184, 1) * A.get(47, 1));
    A.set(172, 1, A.get(185, 1) * A.get(48, 1));
    A.set(173, 1, A.get(185, 1) * A.get(49, 1));
    A.set(174, 1, A.get(186, 1) * A.get(50, 1));
    A.set(175, 1, A.get(186, 1) * A.get(51, 1));
    A.set(176, 1, A.get(187, 1) * A.get(52, 1));
    A.set(177, 1, A.get(187, 1) * A.get(53, 1));
    A.set(178, 1, A.get(184, 1) * A.get(54, 1));
    A.set(179, 1, A.get(184, 1) * A.get(55, 1));
    A.set(180, 1, A.get(185, 1) * A.get(56, 1));
    A.set(181, 1, A.get(185, 1) * A.get(57, 1));
    A.set(182, 1, A.get(186, 1) * A.get(58, 1));
    A.set(183, 1, A.get(186, 1) * A.get(59, 1));

    for (let j = 1; j <= 3; j++) {
      A.set(187 + j, 1, A.get(87 + j, 1));
    }
    A.set(191, 1, A.get(91, 1));
    A.set(195, 1, A.get(92, 1));
    A.set(200, 1, A.get(93, 1));
    A.set(201, 1, A.get(94, 1));

    for (let j = 1; j <= 4; j++) {
      A.set(195 + j, 1, (A.get(29 + j, 1) * A.get(195, 1)) / 100.0);
    }
    A.set(199, 1, A.get(199, 1) * 100.0);
    A.set(202, 1, (A.get(201, 1) * A.get(84, 1)) / 100.0);
    A.set(203, 1, (A.get(201, 1) * A.get(85, 1)) / 100.0);
    A.set(204, 1, A.get(95, 1) / 2000.0);
    A.set(205, 1, A.get(204, 1) * (1.0 - A.get(70, 1) / 100.0));
    for (let j = 1; j <= 3; j++) {
      A.set(205 + j, 1, (A.get(204, 1) * A.get(70 + j, 1)) / 100.0);
    }
    A.set(209, 1, A.get(205, 1) + A.get(105, 1) / 2000.0);
    A.set(210, 1, A.get(206, 1) + A.get(106, 1) / 2000.0);

    // Final Molasses Made (1090-1140)
    A.set(211, 1, A.get(96, 1));
    const brixFmMade = A.get(74, 1);
    A.set(212, 1, (A.get(96, 1) * brixDensityPoly5(brixFmMade)) / 7.48 / 2000.0);
    for (let j = 1; j <= 5; j++) {
      A.set(212 + j, 1, (A.get(212, 1) * A.get(73 + j, 1)) / 100.0);
    }

    // Final Molasses Shipped (1150-1200)
    A.set(220, 1, A.get(98, 1));
    const brixFmShip = A.get(79, 1);
    A.set(221, 1, (A.get(98, 1) * brixDensityPoly5(brixFmShip)) / 7.48 / 2000.0);
    for (let j = 1; j <= 5; j++) {
      A.set(221 + j, 1, (A.get(221, 1) * A.get(78 + j, 1)) / 100.0);
    }

    // Bagasse & Cane Balance (1210-1400)
    A.set(227, 1, A.get(91, 1) + A.get(93, 1) - A.get(92, 1));
    A.set(229, 1, (A.get(227, 1) * A.get(86, 1)) / 100.0);
    A.set(228, 1, safeDiv(A.get(229, 1) * A.get(34, 1), A.get(35, 1)));
    A.set(231, 1, (A.get(227, 1) * A.get(87, 1)) / 100.0);
    A.set(230, 1, A.get(227, 1) - A.get(231, 1) - A.get(228, 1));

    A.set(218, 1, A.get(213, 1) + A.get(107, 1) / 2000.0);
    A.set(219, 1, A.get(214, 1) + A.get(108, 1) / 2000.0);
    A.set(235, 1, A.get(2, 1));
    for (let j = 1; j <= 3; j++) {
      A.set(235 + j, 1, (A.get(188, 1) * A.get(98 + j, 1)) / 100.0);
    }

    A.set(239, 1, A.get(102, 1));
    A.set(240, 1, A.get(103, 1));
    A.set(241, 1, A.get(104, 1));
    A.set(242, 1, A.get(97, 1));

    A.set(192, 1, A.get(228, 1) + A.get(196, 1));
    A.set(193, 1, A.get(229, 1) + A.get(197, 1));
    A.set(194, 1, A.get(230, 1));

    A.set(
      232,
      1,
      A.get(195, 1) -
        safeDiv(A.get(195, 1) * (A.get(26, 1) * 0.97 - A.get(30, 1)), A.get(26, 1) * 0.97)
    );
    A.set(233, 1, (A.get(232, 1) * A.get(26, 1) * 0.97) / 100.0);
    A.set(234, 1, safeDiv(A.get(233, 1) * A.get(31, 1), A.get(30, 1)));

    // Filling in Todate Column A(J, 2) (1410-1645)
    for (let j = 1; j <= 109; j++) {
      A.set(j, 2, A.get(j, 1));
    }
    for (let j = 110; j <= 239; j++) {
      A.set(j, 2, A.get(j, 1) + A.get(j, 3));
    }

    A.set(255, 1, A.get(251, 1));
    A.set(256, 1, A.get(252, 1));
    A.set(257, 1, A.get(253, 1));
    A.set(258, 1, A.get(254, 1));
    A.set(251, 2, A.get(251, 1));
    A.set(252, 2, A.get(252, 1));
    A.set(253, 2, A.get(253, 1));
    A.set(254, 2, A.get(254, 1));
    for (let j = 255; j <= 258; j++) {
      A.set(j, 2, A.get(j, 1) + A.get(j, 3));
    }

    A.set(209, 2, A.get(209, 1) + A.get(205, 3));
    A.set(210, 2, A.get(210, 1) + A.get(206, 3));
    A.set(218, 2, A.get(218, 1) + A.get(213, 3));
    A.set(219, 2, A.get(219, 1) + A.get(214, 3));

    A.set(244, 1, A.get(103, 1));
    A.set(245, 1, A.get(104, 1));
    A.set(240, 2, Math.max(A.get(240, 1), A.get(240, 3)));
    if (A.get(1, 3) === 0) {
      A.set(241, 2, A.get(241, 1));
    } else {
      A.set(241, 2, Math.min(A.get(241, 1), A.get(241, 3)));
    }

    A.set(242, 2, A.get(242, 1) + A.get(242, 3));
    A.set(244, 2, A.get(244, 1) + A.get(244, 3));
    A.set(245, 2, A.get(245, 1) + A.get(245, 3));
    A.set(247, 2, A.get(247, 1) + A.get(247, 3));
    A.set(246, 2, A.get(246, 1));
    A.set(243, 2, A.get(243, 1));
    A.set(248, 1, A.get(188, 2) - A.get(191, 2));
    A.set(248, 2, A.get(248, 1) + A.get(248, 3));
  }

  // ---------------------------------------------------------------------------
  // MRCALC: Calculation Module for Daily & Weekly Reports
  // ---------------------------------------------------------------------------
  function runMrcalc(A, B, C, D, E, F, G, H_num, dayFilesRange) {
    B.clear();
    C.clear();
    D.clear();
    E.clear();
    F.clear();
    G.clear();

    for (let j = 1; j <= 258; j++) {
      A.set(j, 1, A.get(j, 2) - A.get(j, 3));
    }

    // Calculating Mill Data Block (0310-0605)
    for (const j of [1, 2]) {
      B.set(1, j, A.get(1, j));
      B.set(2, j, A.get(121, j) - A.get(120, j));
      B.set(3, j, A.get(120, j));
      B.set(4, j, safeDiv(A.get(120, j) * 100.0, A.get(121, j)));
      B.set(5, j, A.get(191, j));
      B.set(6, j, A.get(188, j));
      B.set(8, j, safeDiv(A.get(191, j), A.get(121, j) - A.get(120, j)));
      B.set(9, j, safeDiv(A.get(191, j) * 24.0, A.get(121, j)));
      B.set(10, j, B.get(8, j) * 24.0);
      B.set(11, j, safeDiv(A.get(194, j), A.get(121, j) - A.get(120, j)));
      B.set(12, j, safeDiv(B.get(11, j), H_num.get(29)));
      B.set(13, j, safeDiv(A.get(197, j) * 100.0, A.get(193, j)));
      B.set(15, j, safeDiv(A.get(195, j) * 100.0, A.get(191, j)));
      B.set(
        16,
        j,
        safeDiv(
          A.get(196, j) * 100.0 * (A.get(191, j) - A.get(194, j)),
          A.get(191, j) * A.get(192, j)
        )
      );
      B.set(18, j, safeDiv(A.get(200, j) * 100.0, A.get(191, j)));
      B.set(19, j, safeDiv(A.get(200, j) * 100.0, A.get(194, j)));
      B.set(20, j, B.get(15, j) - B.get(16, j));
      B.set(21, j, safeDiv(A.get(193, j) * 100.0, A.get(191, j)));
      B.set(22, j, safeDiv(A.get(194, j) * 100.0, A.get(191, j)));
      B.set(23, j, safeDiv(A.get(229, j) * 100.0, A.get(227, j)));
      B.set(24, j, safeDiv(A.get(231, j) * 100.0, A.get(227, j)));
      B.set(25, j, safeDiv(A.get(230, j) * 100.0, A.get(227, j)));
      B.set(26, j, safeDiv(A.get(227, j) * 100.0, A.get(191, j)));
      B.set(27, j, safeDiv(A.get(229, j) * 100.0, A.get(230, j)));
      B.set(28, j, safeDiv(A.get(247, j) * 100.0, A.get(191, j)));
      B.set(17, j, safeDiv((100.0 - B.get(13, j)) * (100.0 - B.get(22, j)), B.get(22, j)));
      B.set(14, j, 100.0 - B.get(17, j) / 7.0);
    }

    B.set(7, 1, A.get(188, 2) - A.get(191, 2));
    B.set(7, 2, safeDiv(A.get(248, 2), A.get(1, 2)));

    // Calculating Production Data Block (0610-0950)
    for (const j of [1, 2]) {
      B.set(1, j + 2, (A.get(206, j) * 2000.0) / 0.96);
      B.set(2, j + 2, ((A.get(210, j) - A.get(206, j)) * 2000.0) / 0.96);
      B.set(3, j + 2, (A.get(210, j) * 2000.0) / 0.96);
      B.set(4, j + 2, A.get(204, j) * 2000.0);
      B.set(5, j + 2, safeDiv((A.get(210, j) - A.get(206, j)) * 2000.0 * A.get(204, j), A.get(206, j)));
      B.set(6, j + 2, safeDiv(A.get(210, j) * 2000.0 * A.get(204, j), A.get(206, j)));

      const polPctSug = safeDiv(A.get(206, j) * 100.0, A.get(204, j));
      const rvFactor = ((polPctSug - 92.0) * 1.75 + 93.0) / 100.0;
      B.set(7, j + 2, B.get(6, j + 2) * rvFactor);
      B.set(8, j + 2, safeDiv(B.get(7, j + 2), A.get(191, j)));
      B.set(9, j + 2, safeDiv(B.get(8, j + 2), 20.0));
      B.set(10, j + 2, safeDiv((A.get(210, j) * 2000.0) / 0.96, A.get(191, j)));
      B.set(11, j + 2, A.get(235, j));
      B.set(12, j + 2, safeDiv(A.get(235, j), A.get(188, j)));
      B.set(13, j + 2, safeDiv(B.get(10, j + 2) * 100.0 * A.get(188, j), A.get(235, j)));
      B.set(14, j + 2, A.get(211, j));

      const k1 = brixLbsSolidsPerGal(H_num.get(30));
      B.set(15, j + 2, safeDiv((A.get(218, j) - A.get(213, j)) * 2000.0, k1));
      B.set(16, j + 2, safeDiv(A.get(218, j) * 2000.0, k1));
      B.set(17, j + 2, safeDiv(B.get(16, j + 2), A.get(191, j)));
      B.set(18, j + 2, safeDiv(A.get(206, j) * 100.0, A.get(204, j)));
      B.set(19, j + 2, A.get(201, j));
      B.set(20, j + 2, safeDiv(A.get(201, j) * 2000.0, A.get(191, j)));
      const denomBhe = 1.4 - 0.4 * safeDiv(A.get(196, j), A.get(197, j));
      B.set(21, j + 2, safeDiv(A.get(210, j) * 100.0, A.get(197, j) * denomBhe));
      B.set(23, j + 2, A.get(239, j));
      B.set(24, j + 2, safeDiv(A.get(236, j) * 100.0, A.get(188, j)));
      B.set(25, j + 2, safeDiv(A.get(237, j) * 100.0, A.get(188, j)));
      B.set(26, j + 2, safeDiv(A.get(238, j) * 100.0, A.get(188, j)));
      B.set(27, j + 2, safeDiv(B.get(8, j + 2) * A.get(188, j), A.get(190, j)));
      B.set(28, j + 2, safeDiv(B.get(8, j + 2) * A.get(188, j), A.get(189, j)));
      B.set(
        27,
        3,
        safeDiv(
          B.get(7, 3),
          safeDiv(A.get(191, 2) * A.get(190, 2), A.get(188, 2)) -
            safeDiv(A.get(191, 3) * A.get(190, 3), A.get(188, 3))
        )
      );
      B.set(
        28,
        3,
        safeDiv(
          B.get(7, 3),
          safeDiv(A.get(191, 2) * A.get(189, 2), A.get(188, 2)) -
            safeDiv(A.get(191, 3) * A.get(189, 3), A.get(188, 3))
        )
      );
    }

    // Massecuite Tabulation Block (0980-1110)
    C.set(3, 1, A.get(184, 1));
    C.set(3, 3, A.get(184, 2));
    C.set(4, 1, A.get(185, 1));
    C.set(4, 3, A.get(185, 2));
    C.set(5, 1, A.get(186, 1));
    C.set(5, 3, A.get(186, 2));
    C.set(6, 1, A.get(187, 1));
    C.set(6, 3, A.get(187, 2));
    C.set(8, 1, C.get(3, 1) + C.get(4, 1) + C.get(5, 1) + C.get(6, 1));
    C.set(8, 3, C.get(3, 3) + C.get(4, 3) + C.get(5, 3) + C.get(6, 3));
    for (let j = 3; j <= 8; j++) {
      C.set(j, 2, safeDiv(C.get(j, 1), A.get(191, 1)));
      C.set(j, 4, safeDiv(C.get(j, 3), A.get(191, 2)));
    }

    // Products Shipped Block (1120-1380)
    C.set(1, 5, A.get(242, 1));
    C.set(1, 6, A.get(242, 2));
    C.set(1, 7, A.get(204, 2) * 2000.0 - A.get(242, 2));

    let k = safeDiv(A.get(213, 1) * 100.0, A.get(212, 1));
    let k1 = brixLbsSolidsPerGal(k);
    C.set(2, 5, safeDiv(A.get(222, 1) * 2000.0, k1));

    k = safeDiv(A.get(213, 2) * 100.0, A.get(212, 2));
    k1 = brixLbsSolidsPerGal(k);
    C.set(2, 6, safeDiv(A.get(222, 2) * 2000.0, k1));
    C.set(2, 7, B.get(14, 4) - C.get(2, 6));

    k = safeDiv(A.get(222, 1) * 100.0, A.get(221, 1));
    k1 = brixLbsSolidsPerGal(k);
    C.set(3, 5, safeDiv(A.get(222, 1) * 2000.0, k1));

    k = safeDiv(A.get(222, 2) * 100.0, A.get(221, 2));
    k1 = brixLbsSolidsPerGal(k);
    C.set(3, 6, safeDiv(A.get(222, 2) * 2000.0, k1));
    C.set(3, 7, safeDiv((A.get(213, 2) - A.get(222, 2)) * 2000.0, k1));

    for (const j of [1, 2]) {
      C.set(4, 4 + j, safeDiv((A.get(195, j) - A.get(232, j)) * 100.0, A.get(232, j)));
      C.set(4 + j, 5, safeDiv(A.get(233, j) * 100.0, A.get(232, j)));
      C.set(4 + j, 6, safeDiv(A.get(234, j) * 100.0, A.get(232, j)));
      C.set(4 + j, 7, safeDiv(A.get(234, j) * 100.0, A.get(233, j)));
      C.set(7, 4 + j, A.get(190, j));
      C.set(8, 4 + j, A.get(189, j));
    }

    // Pol Account Block Array D (1390-1590)
    for (const j of [1, 2]) {
      D.set(1, j, A.get(229, j));
      D.set(2, j, A.get(219, j));
      D.set(3, j, A.get(202, j));
      D.set(6, j, A.get(210, j));
      D.set(7, j, A.get(197, j));
      D.set(8, j, A.get(193, j));
      D.set(4, j, D.get(7, j) - D.get(6, j) - D.get(2, j) - D.get(3, j));
      D.set(5, j, D.get(1, j) + D.get(2, j) + D.get(3, j) + D.get(4, j));
      D.set(9, j, D.get(7, j) - D.get(3, j));
      D.set(10, j, D.get(2, j) + D.get(3, j) + D.get(6, j));
    }

    for (let j = 1; j <= 10; j++) {
      D.set(j, 3, safeDiv(D.get(j, 1) * 100.0, D.get(7, 1)));
      D.set(j, 4, safeDiv(D.get(j, 2) * 100.0, D.get(7, 2)));
      D.set(j, 5, safeDiv(D.get(j, 1) * 100.0, A.get(191, 1)));
      D.set(j, 6, safeDiv(D.get(j, 2) * 100.0, A.get(191, 2)));
      D.set(5, 3, D.get(2, 3) + D.get(3, 3) + D.get(4, 3));
      D.set(5, 4, D.get(2, 4) + D.get(3, 4) + D.get(4, 4));
    }

    // Analyses Block Array E (1600-2180)
    for (const j of [1, 2]) {
      const off = (j - 1) * 6;
      E.set(1, 1 + off, safeDiv(A.get(237, j) * 100.0, A.get(188, j) - A.get(238, j)));
      E.set(1, 2 + off, safeDiv(A.get(236, j) * 100.0, A.get(188, j) - A.get(238, j)));
      E.set(2, 1 + off, safeDiv(A.get(148, j), A.get(134, j)));
      E.set(2, 2 + off, safeDiv(A.get(149, j), A.get(134, j)));
      E.set(2, 4 + off, safeDiv(A.get(150, j), A.get(135, j)));
      E.set(2, 5 + off, safeDiv(E.get(2, 4 + off) * 100.0, E.get(2, 2 + off)));
      E.set(2, 6 + off, safeDiv(A.get(151, j), A.get(136, j)));
      E.set(3, 1 + off, safeDiv(A.get(192, j) * 100.0, A.get(191, j) - A.get(194, j)));
      E.set(3, 2 + off, safeDiv(A.get(193, j) * 100.0, A.get(191, j) - A.get(194, j)));
      E.set(4, 1 + off, safeDiv(A.get(196, j) * 100.0, A.get(195, j)));
      E.set(4, 2 + off, safeDiv(A.get(197, j) * 100.0, A.get(195, j)));
      E.set(4, 4 + off, safeDiv(A.get(198, j) * 100.0, A.get(195, j)));
      E.set(4, 5 + off, safeDiv(A.get(198, j) * 100.0, A.get(197, j)));
      E.set(4, 6 + off, safeDiv(A.get(199, j), A.get(195, j)));
      E.set(5, 1 + off, safeDiv(A.get(160, j), A.get(143, j)));
      E.set(5, 2 + off, safeDiv(A.get(161, j), A.get(143, j)));
      E.set(6, 1 + off, safeDiv(A.get(152, j), A.get(137, j)));
      E.set(6, 2 + off, safeDiv(A.get(153, j), A.get(137, j)));
      E.set(6, 4 + off, safeDiv(A.get(154, j), A.get(138, j)));
      E.set(6, 5 + off, safeDiv(E.get(6, 4 + off) * 100.0, E.get(6, 2 + off)));
      E.set(6, 6 + off, safeDiv(A.get(155, j), A.get(139, j)));
      E.set(7, 1 + off, safeDiv(A.get(162, j), A.get(144, j)));
      E.set(7, 2 + off, safeDiv(A.get(163, j), A.get(144, j)));
      E.set(8, 1 + off, safeDiv(A.get(156, j), A.get(140, j)));
      E.set(8, 2 + off, safeDiv(A.get(157, j), A.get(140, j)));
      E.set(8, 4 + off, safeDiv(A.get(158, j), A.get(141, j)));
      E.set(8, 5 + off, safeDiv(E.get(8, 4 + off) * 100.0, E.get(8, 2 + off)));
      E.set(8, 6 + off, safeDiv(A.get(159, j), A.get(142, j)));

      // Massecuites (1910-1980)
      E.set(9, 1 + off, safeDiv(A.get(170, j), A.get(184, j)));
      E.set(9, 2 + off, safeDiv(A.get(171, j), A.get(184, j)));
      E.set(10, 1 + off, safeDiv(A.get(172, j), A.get(185, j)));
      E.set(10, 2 + off, safeDiv(A.get(173, j), A.get(185, j)));
      E.set(11, 1 + off, safeDiv(A.get(174, j), A.get(186, j)));
      E.set(11, 2 + off, safeDiv(A.get(175, j), A.get(186, j)));
      E.set(12, 1 + off, safeDiv(A.get(176, j), A.get(187, j)));
      E.set(12, 2 + off, safeDiv(A.get(177, j), A.get(187, j)));

      // Molasses (2000-2050)
      E.set(13, 1 + off, safeDiv(A.get(178, j), A.get(184, j)));
      E.set(13, 2 + off, safeDiv(A.get(179, j), A.get(184, j)));
      E.set(14, 1 + off, safeDiv(A.get(180, j), A.get(185, j)));
      E.set(14, 2 + off, safeDiv(A.get(181, j), A.get(185, j)));
      E.set(15, 1 + off, safeDiv(A.get(182, j), A.get(186, j)));
      E.set(15, 2 + off, safeDiv(A.get(183, j), A.get(186, j)));

      // Grain and Magmas (2070-2120)
      E.set(16, 1 + off, safeDiv(A.get(164, j), A.get(145, j)));
      E.set(16, 2 + off, safeDiv(A.get(165, j), A.get(145, j)));
      E.set(17, 1 + off, safeDiv(A.get(166, j), A.get(146, j)));
      E.set(17, 2 + off, safeDiv(A.get(167, j), A.get(146, j)));
      E.set(18, 1 + off, safeDiv(A.get(168, j), A.get(147, j)));
      E.set(18, 2 + off, safeDiv(A.get(169, j), A.get(147, j)));
    }

    for (let j = 1; j <= 18; j++) {
      E.set(j, 3, safeDiv(E.get(j, 2) * 100.0, E.get(j, 1)));
      E.set(j, 9, safeDiv(E.get(j, 8) * 100.0, E.get(j, 7)));
    }

    // Analyses of Products Array F (2190-2530)
    for (const j of [1, 2]) {
      F.set(j, 1, safeDiv(A.get(205, j) * 100.0, A.get(204, j)));
      F.set(j, 2, safeDiv(A.get(206, j) * 100.0, A.get(204, j)));
      F.set(j, 4, safeDiv(A.get(207, j) * 100.0, A.get(204, j)));
      F.set(j, 5, safeDiv(A.get(208, j) * 100.0, A.get(204, j)));
      F.set(j, 7, safeDiv((A.get(204, j) - A.get(205, j)) * 100.0, A.get(204, j)));
      F.set(j, 8, safeDiv(F.get(j, 7), 100.0 - F.get(j, 2)));
      F.set(j, 10, F.get(j, 2) + F.get(j, 4));

      // Final Molasses Made (2300-2360)
      F.set(2 + j, 1, safeDiv(A.get(213, j) * 100.0, A.get(212, j)));
      F.set(2 + j, 2, safeDiv(A.get(214, j) * 100.0, A.get(212, j)));
      F.set(2 + j, 4, safeDiv(A.get(215, j) * 100.0, A.get(212, j)));
      F.set(2 + j, 5, safeDiv(A.get(216, j) * 100.0, A.get(212, j)));
      F.set(2 + j, 6, safeDiv(A.get(215, j) * 100.0, A.get(216, j)));
      F.set(2 + j, 9, safeDiv(A.get(217, j) * 100.0, A.get(212, j)));
      F.set(2 + j, 10, safeDiv((A.get(215, j) + A.get(217, j) * 1.052632) * 100.0, A.get(212, j)));

      // Final Molasses Shipped (2380-2440)
      F.set(4 + j, 1, safeDiv(A.get(222, j) * 100.0, A.get(221, j)));
      F.set(4 + j, 2, safeDiv(A.get(223, j) * 100.0, A.get(221, j)));
      F.set(4 + j, 4, safeDiv(A.get(224, j) * 100.0, A.get(221, j)));
      F.set(4 + j, 5, safeDiv(A.get(225, j) * 100.0, A.get(221, j)));
      F.set(4 + j, 6, safeDiv(A.get(224, j) * 100.0, A.get(225, j)));
      F.set(4 + j, 9, safeDiv(A.get(226, j) * 100.0, A.get(221, j)));
      F.set(4 + j, 10, safeDiv((A.get(224, j) + A.get(226, j) * 1.052632) * 100.0, A.get(221, j)));

      // Filter Cake (2450-2480)
      F.set(6 + j, 1, safeDiv((A.get(201, j) - A.get(203, 1)) * 100.0, A.get(201, j)));
      F.set(6 + j, 2, safeDiv(A.get(202, j) * 100.0, A.get(201, j)));
      F.set(6 + j, 7, safeDiv(A.get(203, j) * 100.0, A.get(201, j)));
    }

    for (let j = 1; j <= 8; j++) {
      F.set(j, 3, safeDiv(F.get(j, 2) * 100.0, F.get(j, 1)));
    }

    // Lost Time Hours & Materials/Supplies Array G (2540-2710)
    for (let j = 1; j <= 10; j++) {
      G.set(j, 1, A.get(j + 109, 1));
      G.set(j, 2, A.get(j + 109, 2));
    }
    G.set(12, 1, A.get(120, 1));
    G.set(12, 2, A.get(120, 2));
    for (let j = 1; j <= 12; j++) {
      G.set(j, 3, safeDiv(G.get(j, 1) * 100.0, A.get(121, 1)));
      G.set(j, 4, safeDiv(G.get(j, 2) * 100.0, A.get(121, 2)));
    }

    for (let j = 1; j <= 12; j++) {
      G.set(j, 5, A.get(j + 121, 1));
      G.set(j, 6, A.get(j + 121, 2));
      G.set(j, 7, safeDiv(G.get(j, 5), A.get(191, 1)));
      G.set(j, 8, safeDiv(G.get(j, 6), A.get(191, 2)));
    }

    // Max/Min Temperature scan across range (2770-2960)
    if (Math.round(H_num.get(26) - H_num.get(27)) === 1 || !dayFilesRange || dayFilesRange.length === 0) {
      A.set(240, 1, A.get(103, 2));
      A.set(241, 1, A.get(104, 2));
    } else {
      let maxT = dayFilesRange[0][102];
      let minT = dayFilesRange[0][103];
      for (const xArr of dayFilesRange) {
        if (xArr[102] > maxT) maxT = xArr[102];
        if (xArr[103] < minT) minT = xArr[103];
      }
      A.set(240, 1, maxT);
      A.set(241, 1, minT);
    }
  }

  // ---------------------------------------------------------------------------
  // 132-Column Report & Form Renderers (MRREPOPR, MRREPOP2, MRREPOCK, etc.)
  // ---------------------------------------------------------------------------
  function _cDLabels(H_num, page = 1) {
    const C_s = new OneBasedArray1D(62, "");
    const D_s = new OneBasedArray1D(30, "");

    const cList = [
      "Number of Crop Days",
      "Grinding Time, Hours",
      "Lost Time, Hours",
      "Lost Time, % Total Time",
      "CANE: Tons Ground",
      "      Tons Purchased",
      "      Tons on Yard",
      "Grinding Rate, per Hour",
      "               Crop Day",
      "               24 Hours",
      "Tons Fiber Ground per Hour",
      "Tons Fiber Ground/Hr./Sq. Ft.",
      "EXTRACTION: Pol % Pol in Cane",
      "            Reduced (F=12.5)",
      "            Mixed Juice % Cane",
      "            Abs. Juice % Cane",
      "Absolute Juice Lost % Fiber",
      "IMBIBITION: % Cane",
      "            % Fiber",
      "Dilution % Cane",
      "CANE: Per Cent Pol",
      "      Per Cent Fiber",
      "BAGASSE: Per Cent Pol",
      "         Per Cent Moisture",
      "         Per Cent Fiber",
      "         Per Cent Cane",
      "         Pol % Fiber",
      "Metered Imbibition % Cane",
      "In Bagasse",
      "In Final Molasses",
      "In Filter Cake",
      "Undetermined",
      "Total Losses",
      "Recovered in Sugar",
      "Pol in Juice % Cane",
      "Pol in Cane",
      "Corer Juice",
      "Crusher Juice",
      "Absolute Juice",
      "Mixed Juice",
      "Last Roll Juice",
      "Clarified Juice",
      "Filter Press Juice",
      "Syrup",
      "A Massecuite",
      "Top-Off Massecuite",
      "B Massecuite",
      "C Massecuite",
      "A Molasses",
      "Top-Off A Molasses",
      "B Molasses",
      "Grain",
      "C Magma",
      "B Magma",
      "Sugar Made",
      "Sugar Made",
      "Final Molasses Made",
      "Final Molasses Made",
      "Final Molasses Shipped",
      "Final Molasses Shipped",
      "Filter Cake",
      "Filter Cake",
    ];
    C_s.fromList(cList);
    if (H_num.get(22) === 0) {
      C_s.set(54, "C Cyclone");
    }

    const dList = [
      "SUGAR, Lbs 96 Made",
      "       Lbs 96 in Process",
      "       Lbs 96 Made and Estimated",
      "       Lbs Made",
      "       Lbs in Process",
      "       Lbs Made and Estimated",
      "       Lbs Total Equivalent - RV",
      "       Lbs Sugar/Ton Cane - RV",
      page === 1 ? "       Lbs 96 Sugar/Ton Cane" : "       Yield Sugar, RV % Cane",
      page === 1 ? "       Yield, 96 Sugar % Cane" : "       CRS, Lbs 96 Sugar/Ton Cane",
      "TRS, Total lbs Purchased",
      "TRS, Lbs 96 Sugar/Ton Cane",
      "Liquidation Factor",
      "F. MOL: Gallons Made - As Prod.",
      "        Gallons in Process @",
      "        Total Gals M&E @",
      "        Gals per Ton Cane @",
      "POLARIZATION OF SUGAR",
      "Filter Cake: Tons Made",
      "             Lbs/Ton Cane",
      "BOILING HOUSE EFFICIENCY",
      "Temperature, (Maximum/Minimum), F",
      "Rainfall, Inches",
      "Corer: Per Cent Pol",
      "       Per Cent Brix",
      "       Per Cent Fiber",
      "Boiling House Retention, %",
      "Overall Recovery, %",
      H_num.get(28) === 1 ? "    Run" : "  Today",
      "To Date",
    ];
    D_s.fromList(dList);
    return [C_s, D_s];
  }

  function renderMrrepoprPage1(B_name, A2_s, A, B, C, D, H_num) {
    const lines = [];
    const [C_s, D_s] = _cDLabels(H_num, 1);
    const weekdays = ["SUNDAY", "MONDAY", "TUESDAY", "WEDNESDAY", "THURSDAY", "FRIDAY", "SATURDAY"];
    const nWk = zellerWeekdayIndex(A2_s.get(2));
    const dayName = weekdays[nWk];

    const bTrim = String(B_name || "").trim();
    lines.push(" ".repeat(Math.max(0, Math.trunc(66 - bTrim.length / 2))) + bTrim);
    lines.push("");
    if (H_num.get(28) !== 0) {
      lines.push(" ".repeat(52) + "WEEKLY MANUFACTURING REPORT" + " ".repeat(45) + "Page 1");
      lines.push(" ".repeat(62) + "WEEKLY");
      const img1340 =
        "%Crop Started ########                  Date: ######## to ########                      Weekly Report No. ###";
      lines.push(formatPrintusing(img1340, [A2_s.get(3), A2_s.get(1), A2_s.get(2), H_num.get(31)]));
    } else {
      lines.push(" ".repeat(52) + "DAILY MANUFACTURING REPORT" + " ".repeat(46) + "Page 1");
      lines.push(" ".repeat(Math.max(0, Math.trunc(66 - dayName.length / 2))) + dayName);
      const img1370 =
        "%Crop Started ########                       Date: ########                              Daily Report No. ###";
      lines.push(formatPrintusing(img1370, [A2_s.get(3), A2_s.get(2), A.get(1, 2)]));
    }

    const sep = "-".repeat(131);
    lines.push(sep);
    if (H_num.get(28) !== 0) {
      lines.push(
        "        MILLING DATA                    Run        To Date   !          PRODUCTION DATA                        Run          To Date"
      );
    } else {
      lines.push(
        "        MILLING DATA                  Today        To Date   !          PRODUCTION DATA                      Today          To Date"
      );
    }
    lines.push(sep);

    const img1460 =
      "%############################## -#,###,###.## -#,###,###.##  !  ################################ -###,###,###.## -###,###,###.##";
    const img1500 =
      "%############################## -#,###,###.### -#,###,###.### ! ################################ -###,###,###.## -###,###,###.##";
    const img1570 =
      "%############################## -#,###,###.## -#,###,###.##  !  ################################# -##,###,###.## -###,###,###.##";
    const img1670 =
      "%############################## -#,###,###.## -#,###,###.##  !  ############################ ##.## -#,###,###.## -###,###,###.##";
    const img1700 =
      "%############################## -#,###,###.## -#,###,###.##  !  ######################## ##.##   -###,###,###.## -###,###,###.##";
    const img1730 =
      "%############################## -#,###,###.## -#,###,###.##  !  ########################### ##.## -##,###,###.## -###,###,###.##";
    const img1790 =
      "%############################## -#,###,###.## -#,###,###.##  !  ##################################     -###/-###       -###/-###";

    for (let j = 1; j <= 4; j++) {
      lines.push(
        formatPrintusing(img1460, [C_s.get(j), B.get(j, 1), B.get(j, 2), D_s.get(j), B.get(j, 3), B.get(j, 4)])
      );
    }
    for (let j = 5; j <= 7; j++) {
      lines.push(
        formatPrintusing(img1500, [C_s.get(j), B.get(j, 1), B.get(j, 2), D_s.get(j), B.get(j, 3), B.get(j, 4)])
      );
    }
    let j = 8;
    lines.push(
      formatPrintusing(img1460, [C_s.get(j), B.get(j, 1), B.get(j, 2), D_s.get(j), B.get(j, 3), B.get(j, 4)])
    );
    j = 9;
    lines.push(
      formatPrintusing(img1460, [C_s.get(j), B.get(j, 1), B.get(j, 2), D_s.get(j), B.get(j + 1, 3), B.get(j + 1, 4)])
    );
    j = 10;
    lines.push(
      formatPrintusing(img1570, [
        C_s.get(j),
        B.get(j, 1),
        B.get(j, 2),
        D_s.get(j),
        B.get(j, 3) / 20.0,
        B.get(j, 4) / 20.0,
      ])
    );
    j = 11;
    lines.push(
      formatPrintusing(img1460, [C_s.get(j), B.get(j, 1), B.get(j, 2), D_s.get(j), B.get(j, 3), B.get(j, 4)])
    );
    j = 12;
    lines.push(
      formatPrintusing(img1500, [C_s.get(j), B.get(j, 1), B.get(j, 2), D_s.get(j), B.get(j, 3), B.get(j, 4)])
    );
    for (const jj of [13, 14]) {
      lines.push(
        formatPrintusing(img1460, [
          C_s.get(jj),
          B.get(jj, 1),
          B.get(jj, 2),
          D_s.get(jj),
          B.get(jj, 3),
          B.get(jj, 4),
        ])
      );
    }
    j = 15;
    lines.push(
      formatPrintusing(img1670, [
        C_s.get(j),
        B.get(j, 1),
        B.get(j, 2),
        D_s.get(j),
        H_num.get(30),
        B.get(j, 3),
        B.get(j, 4),
      ])
    );
    j = 16;
    lines.push(
      formatPrintusing(img1700, [
        C_s.get(j),
        B.get(j, 1),
        B.get(j, 2),
        D_s.get(j),
        H_num.get(30),
        B.get(j, 3),
        B.get(j, 4),
      ])
    );
    j = 17;
    lines.push(
      formatPrintusing(img1730, [
        C_s.get(j),
        B.get(j, 1),
        B.get(j, 2),
        D_s.get(j),
        H_num.get(30),
        B.get(j, 3),
        B.get(j, 4),
      ])
    );
    for (let jj = 18; jj <= 21; jj++) {
      lines.push(
        formatPrintusing(img1460, [
          C_s.get(jj),
          B.get(jj, 1),
          B.get(jj, 2),
          D_s.get(jj),
          B.get(jj, 3),
          B.get(jj, 4),
        ])
      );
    }
    j = 22;
    lines.push(
      formatPrintusing(img1790, [
        C_s.get(j),
        B.get(j, 1),
        B.get(j, 2),
        D_s.get(j),
        A.get(240, 1),
        A.get(241, 1),
        A.get(240, 2),
        A.get(241, 2),
      ])
    );
    for (let jj = 23; jj <= 26; jj++) {
      lines.push(
        formatPrintusing(img1460, [
          C_s.get(jj),
          B.get(jj, 1),
          B.get(jj, 2),
          D_s.get(jj),
          B.get(jj, 3),
          B.get(jj, 4),
        ])
      );
    }
    j = 27;
    lines.push(
      formatPrintusing(img1460, [C_s.get(j), B.get(j, 1), B.get(j, 2), D_s.get(j), D.get(6, 3), D.get(6, 4)])
    );
    j = 28;
    lines.push(
      formatPrintusing(img1460, [
        C_s.get(j),
        B.get(j, 1),
        B.get(j, 2),
        D_s.get(j),
        (D.get(6, 3) * B.get(13, 1)) / 100.0,
        (D.get(6, 4) * B.get(13, 2)) / 100.0,
      ])
    );

    lines.push(sep);
    if (H_num.get(28) !== 0) {
      lines.push(
        "MASSECUITE                RUN             TO DATE        !  PRODUCTS SHIPPED            RUN         TO DATE         ON HAND"
      );
    } else {
      lines.push(
        "MASSECUITE              TODAY             TO DATE        !  PRODUCTS SHIPPED          TODAY         TO DATE         ON HAND"
      );
    }
    lines.push(sep);

    const img1910 =
      "%Massecuite         Cu. Ft.    /Ton     Cu. Ft.    /Ton  !  Sugar, Lbs             -###,###,###    -###,###,###    -###,###,###";
    const img1940 =
      "%----------         -------    ----     -------    ----  !  F. Mol, Gals (As Made) -###,###,###    -###,###,###    -###,###,###";
    const img1970 =
      "%A Massecuite  -###,###,### -###.## -###,###,### -###.## !  F. Mol, Gals (Shipped) -###,###,###    -###,###,###    -###,###,###";
    const img2000 =
      "%Top-Off A Mass.   -###,###,### -###.## -###,###,### -###.## !  W/H 1, Lbs Sugar   -###,###,###,### -#,###,###,###";
    const img2030 =
      "%B Massecuite  -###,###,### -###.## -###,###,### -###.## !  W/H 2, Lbs Sugar   -###,###,###,### -#,###,###,###";
    const img2060 =
      "%C Massecuite  -###,###,### -###.## -###,###,### -###.## !  W/H 3, Lbs Sugar   -###,###,###,### -#,###,###,###";
    const img2090 =
      "%                   -------    ----     -------    ----  !  W/H 4, Lbs Sugar   -###,###,###,### -#,###,###,###";
    const img2120 =
      "%     TOTAL    -###,###,### -###.## -###,###,### -###.## !  TOTAL, Lbs Sugar   -###,###,###,### -#,###,###,###";

    lines.push(formatPrintusing(img1910, [C.get(1, 5), C.get(1, 6), C.get(1, 7)]));
    lines.push(formatPrintusing(img1940, [C.get(2, 5), C.get(2, 6), C.get(2, 7)]));
    lines.push(
      formatPrintusing(img1970, [
        C.get(3, 1),
        C.get(3, 2),
        C.get(3, 3),
        C.get(3, 4),
        C.get(3, 5),
        C.get(3, 6),
        C.get(3, 7),
      ])
    );
    lines.push(
      formatPrintusing(img2000, [
        C.get(4, 1),
        C.get(4, 2),
        C.get(4, 3),
        C.get(4, 4),
        A.get(255, 1),
        A.get(255, 2),
      ])
    );
    lines.push(
      formatPrintusing(img2030, [
        C.get(5, 1),
        C.get(5, 2),
        C.get(5, 3),
        C.get(5, 4),
        A.get(256, 1),
        A.get(256, 2),
      ])
    );
    lines.push(
      formatPrintusing(img2060, [
        C.get(6, 1),
        C.get(6, 2),
        C.get(6, 3),
        C.get(6, 4),
        A.get(257, 1),
        A.get(257, 2),
      ])
    );
    lines.push(formatPrintusing(img2090, [A.get(258, 1), A.get(258, 2)]));
    const totWh1 = A.get(255, 1) + A.get(256, 1) + A.get(257, 1) + A.get(258, 1);
    const totWh2 = A.get(255, 2) + A.get(256, 2) + A.get(257, 2) + A.get(258, 2);
    lines.push(formatPrintusing(img2120, [C.get(8, 1), C.get(8, 2), C.get(8, 3), C.get(8, 4), totWh1, totWh2]));

    lines.push(sep);
    lines.push(
      "                                              POL - TONS                      PER CENT POL EXTRACTED                    PER CENT CANE"
    );
    lines.push(
      "POL ACCOUNT                            ------------------------               ----------------------                 -------------------"
    );
    if (H_num.get(28) !== 0) {
      lines.push(
        "-----------                                Run          To Date                  Run         To Date                    Run      To Date"
      );
    } else {
      lines.push(
        "-----------                              Today          To Date                Today         To Date                  Today      To Date"
      );
    }
    lines.push(
      "                                      --------         --------              -------         -------                -------      -------"
    );

    const img2230 =
      "%####################         -###,###,###.###  -#,###,###.###                   ---             ---           -###,###.### -##,###.###";
    const img2260 =
      "%####################         -###,###,###.###  -#,###,###.###       -###,###,###.##     -###,###.##           -###,###.### -##,###.###";

    lines.push(formatPrintusing(img2230, [C_s.get(29), D.get(1, 1), D.get(1, 2), D.get(1, 5), D.get(1, 6)]));
    for (let jj = 2; jj <= 7; jj++) {
      lines.push(
        formatPrintusing(img2260, [
          C_s.get(jj + 28),
          D.get(jj, 1),
          D.get(jj, 2),
          D.get(jj, 3),
          D.get(jj, 4),
          D.get(jj, 5),
          D.get(jj, 6),
        ])
      );
    }
    lines.push(formatPrintusing(img2230, [C_s.get(36), D.get(8, 1), D.get(8, 2), D.get(8, 5), D.get(8, 6)]));
    lines.push(sep);
    return lines;
  }

  function renderMrrepop2Page2(B_name, B1_s, A2_s, A, E, F, G, J_s, H_s, H_num) {
    const lines = [];
    const [C_s, D_s] = _cDLabels(H_num, 2);
    const bTrim = String(B_name || "").trim();

    const title =
      H_num.get(28) !== 0
        ? `${bTrim} WEEKLY MANUFACTURING REPORT (Cont'd)`
        : `${bTrim} DAILY MANUFACTURING REPORT (Cont'd)`;
    const pad = Math.max(0, Math.trunc(66 - title.length / 2));
    lines.push((" ".repeat(pad) + title).padEnd(124, " ") + "Page 2");

    if (H_num.get(28) !== 0) {
      const img2380 =
        "%Date: ######## to ########                               ANALYTICAL DATA                               Weekly Report No. ###";
      lines.push(formatPrintusing(img2380, [A2_s.get(1), A2_s.get(2), H_num.get(31)]));
    } else {
      const img2410 =
        "%Date: ########                                           ANALYTICAL DATA                               Daily Report No.  ###";
      lines.push(formatPrintusing(img2410, [A2_s.get(2), A.get(1, 2)]));
    }

    const sep = "-".repeat(131);
    lines.push(sep);
    if (H_num.get(28) !== 0) {
      lines.push(
        "ANALYSIS OF                                     RUN                        !                        TO DATE"
      );
    } else {
      lines.push(
        "ANALYSIS OF                                   TODAY                        !                        TO DATE"
      );
    }
    lines.push(sep);
    lines.push(
      "                       Brix     Pol    Purity  Glucose  G. Rat.     pH     !    Brix     Pol    Purity  Glucose  G. Rat.     pH"
    );
    lines.push(
      "                      ------   -----   ------  -------  -------   -----    !   ------   -----   ------  -------  -------   -----"
    );

    const img2740 =
      "%#################### -###.##  -###.##  -###.##                            !  -###.##  -###.##  -###.##";
    const img2780 =
      "%#################### -###.##  -###.##  -###.##  -###.##  -###.##  -###.## !  -###.##  -###.##  -###.##  -###.##  -###.##  -###.##";

    for (let j = 1; j <= 18; j++) {
      if (j === 2 || j === 4 || j === 6 || j === 8) {
        lines.push(
          formatPrintusing(img2780, [
            C_s.get(j + 36),
            E.get(j, 1),
            E.get(j, 2),
            E.get(j, 3),
            E.get(j, 4),
            E.get(j, 5),
            E.get(j, 6),
            E.get(j, 7),
            E.get(j, 8),
            E.get(j, 9),
            E.get(j, 10),
            E.get(j, 11),
            E.get(j, 12),
          ])
        );
      } else {
        lines.push(
          formatPrintusing(img2740, [
            C_s.get(j + 36),
            E.get(j, 1),
            E.get(j, 2),
            E.get(j, 3),
            E.get(j, 7),
            E.get(j, 8),
            E.get(j, 9),
          ])
        );
      }
    }

    lines.push(sep);
    lines.push(
      "ANALYSIS OF                       Brix     Pol    Purity  Glu/Dex  Ash/Str   RS/Ash  Moisture  Safety Fac.  Clerget  T. Sugars"
    );
    lines.push(
      "-----------                      -----    -----   ------  -------  -------   ------  --------  -----------  -------  ---------"
    );

    const img2850 =
      "%###################### ####### -###.##  -###.##  -###.##  -###.##   -###.##           -###.##     -###.##                     -###.##";
    const img2900 =
      "%###################### ####### -###.##  -###.##  -###.##  -###.##   -###.##  -###.##                                 -###.##   -###.##";
    const img2990 =
      "%###################### #######          -###.##                                       -###.##";

    for (const j of [1, 2]) {
      const lbl = j === 1 ? D_s.get(29) : D_s.get(30);
      lines.push(
        formatPrintusing(img2850, [
          C_s.get(j + 54),
          lbl,
          F.get(j, 1),
          F.get(j, 2),
          F.get(j, 3),
          F.get(j, 4),
          F.get(j, 5),
          F.get(j, 7),
          F.get(j, 8),
          F.get(j, 10),
        ])
      );
    }
    for (const j of [3, 4, 5, 6]) {
      const lbl = j % 2 === 1 ? D_s.get(29) : D_s.get(30);
      lines.push(
        formatPrintusing(img2900, [
          C_s.get(j + 54),
          lbl,
          F.get(j, 1),
          F.get(j, 2),
          F.get(j, 3),
          F.get(j, 4),
          F.get(j, 5),
          F.get(j, 6),
          F.get(j, 9),
          F.get(j, 10),
        ])
      );
    }
    for (const j of [7, 8]) {
      const lbl = j === 7 ? D_s.get(29) : D_s.get(30);
      lines.push(formatPrintusing(img2990, [C_s.get(j + 54), lbl, F.get(j, 2), F.get(j, 7)]));
    }

    lines.push(sep);
    lines.push(
      "                     ANALYSIS OF MILL LOST TIME                   !                      MATERIALS AND SUPPLIES USED"
    );
    lines.push(sep);
    lines.push(
      "                           HOURS               PER CENT           !                              TOTAL AMOUNT          PER TON CANE"
    );
    lines.push(
      "                    -------------------    -----------------      !                          --------------------    ----------------"
    );
    if (H_num.get(28) !== 0) {
      lines.push(
        "Category              For Run   To Date     For Run  To Date      !  Item                      For Run    To Date     For Run  To Date"
      );
    } else {
      lines.push(
        "Category                Today   To Date       Today  To Date      !  Item                        Today    To Date       Today  To Date"
      );
    }
    lines.push(
      "--------              -------   -------     -------  -------      !  -------------             -------    -------     -------  -------"
    );

    const img3140 =
      "%################ -##,###.### -##,###.###   -###.### -###.###     !  ##################### -#,###,### -###,###,###    -###.### -###.###";
    const img3180 =
      "%                     -------   -------     -------  -------      !  ##################### -#,###,### -###,###,###    -###.### -###.###";

    for (let j = 1; j <= 10; j++) {
      lines.push(
        formatPrintusing(img3140, [
          J_s.get(j),
          G.get(j, 1),
          G.get(j, 2),
          G.get(j, 3),
          G.get(j, 4),
          H_s.get(j),
          G.get(j, 5),
          G.get(j, 6),
          G.get(j, 7),
          G.get(j, 8),
        ])
      );
    }
    let j = 11;
    lines.push(formatPrintusing(img3180, [H_s.get(j), G.get(j, 5), G.get(j, 6), G.get(j, 7), G.get(j, 8)]));
    j = 12;
    lines.push(
      formatPrintusing(img3140, [
        "      TOTAL",
        G.get(j, 1),
        G.get(j, 2),
        G.get(j, 3),
        G.get(j, 4),
        H_s.get(j),
        G.get(j, 5),
        G.get(j, 6),
        G.get(j, 7),
        G.get(j, 8),
      ])
    );
    lines.push(sep);
    lines.push(`REMARKS: ${String(B1_s.get(1)).replace(/\s+$/, "")}${String(B1_s.get(2)).replace(/\s+$/, "")}`);
    lines.push(`         ${String(B1_s.get(3)).replace(/\s+$/, "")}${String(B1_s.get(4)).replace(/\s+$/, "")}`);
    lines.push(`         ${String(B1_s.get(5)).replace(/\s+$/, "")}${String(B1_s.get(6)).replace(/\s+$/, "")}`);
    lines.push("");
    lines.push("      Chief Chemist:                                                  Fabrication Superintendent:");
    return lines;
  }

  function renderMrrepockPage3(B_name, A2_s, A, B, C, D, E, F, H_num) {
    const K = new OneBasedArray2D(24, 6, 0.0);
    const C_lbl = new OneBasedArray1D(2, "");
    C_lbl.set(1, H_num.get(28) !== 0 ? "Run" : "Today");
    C_lbl.set(2, "To Date");

    let f33 = F.get(3, 3);
    if (f33 === 0) f33 = safeDiv(A.get(219, 1) * 100.0, A.get(218, 1));
    let f43 = F.get(4, 3);
    if (f43 === 0) f43 = safeDiv(A.get(219, 2) * 100.0, A.get(218, 2));

    // Solids Balance (4100-4390)
    K.set(1, 1, safeDiv(D.get(1, 1) * 100.0, E.get(5, 3)));
    K.set(1, 2, safeDiv(D.get(1, 2) * 100.0, E.get(5, 9)));
    K.set(2, 1, D.get(2, 1) + A.get(218, 1) - A.get(219, 1));
    K.set(2, 2, D.get(2, 2) + A.get(218, 2) - A.get(219, 2));
    if (f33 !== 0) K.set(2, 1, safeDiv(D.get(2, 1) * 100.0, f33));
    if (f43 !== 0) K.set(2, 2, safeDiv(D.get(2, 2) * 100.0, f43));
    K.set(6, 1, safeDiv(D.get(6, 1) * 100.0, F.get(1, 3)));
    K.set(6, 2, safeDiv(D.get(6, 2) * 100.0, F.get(2, 3)));
    K.set(7, 1, safeDiv(D.get(7, 1) * 100.0, E.get(4, 3)));
    K.set(7, 2, safeDiv(D.get(7, 2) * 100.0, E.get(4, 9)));
    K.set(9, 1, safeDiv(D.get(9, 1) * 100.0, E.get(6, 3)));
    K.set(9, 2, safeDiv(D.get(9, 2) * 100.0, E.get(6, 9)));

    for (const j of [1, 2]) {
      K.set(8, j, K.get(1, j) + K.get(7, j));
      K.set(3, j, K.get(7, j) - K.get(9, j));
      K.set(4, j, K.get(7, j) - K.get(6, j) - K.get(2, j) - K.get(3, j));
      K.set(5, j, K.get(1, j) + K.get(2, j) + K.get(3, j) + K.get(4, j));
      K.set(10, j, K.get(2, j) + K.get(3, j) + K.get(6, j));
    }

    for (let j = 1; j <= 10; j++) {
      K.set(j, 3, safeDiv(K.get(j, 1) * 100.0, K.get(7, 1)));
      K.set(j, 4, safeDiv(K.get(j, 2) * 100.0, K.get(7, 2)));
      K.set(j, 5, safeDiv(K.get(j, 1) * 100.0, A.get(191, 1)));
      K.set(j, 6, safeDiv(K.get(j, 2) * 100.0, A.get(191, 2)));
    }

    K.set(5, 3, K.get(2, 3) + K.get(3, 3) + K.get(4, 3));
    K.set(5, 4, K.get(2, 4) + K.get(3, 4) + K.get(4, 4));

    // Purities Compared to Mixed Juice (4400-4520)
    K.set(11, 1, F.get(1, 3));
    K.set(11, 2, f33);
    K.set(11, 3, safeDiv(D.get(3, 1) * 100.0, K.get(3, 1)));
    K.set(11, 4, safeDiv(D.get(10, 1) * 100.0, K.get(10, 1)));
    K.set(11, 5, E.get(4, 3));
    K.set(11, 6, K.get(11, 5) - K.get(11, 4));

    K.set(12, 1, F.get(2, 3));
    K.set(12, 2, f43);
    K.set(12, 3, safeDiv(D.get(3, 2) * 100.0, K.get(3, 2)));
    K.set(12, 4, safeDiv(D.get(10, 2) * 100.0, K.get(10, 2)));
    K.set(12, 5, E.get(4, 9));
    K.set(12, 6, K.get(12, 5) - K.get(12, 4));

    // Purities Compared to Syrup (4530-4630)
    K.set(13, 1, F.get(1, 3));
    K.set(13, 2, f33);
    K.set(13, 3, safeDiv((D.get(6, 1) + D.get(2, 1)) * 100.0, K.get(6, 1) + K.get(2, 1)));
    K.set(13, 4, E.get(8, 3));
    K.set(13, 5, E.get(8, 3) - K.get(13, 3));

    K.set(14, 1, F.get(2, 3));
    K.set(14, 2, f43);
    K.set(14, 3, safeDiv((D.get(6, 2) + D.get(2, 2)) * 100.0, K.get(6, 2) + K.get(2, 2)));
    K.set(14, 4, E.get(8, 9));
    K.set(14, 5, E.get(8, 9) - K.get(14, 3));

    // Theoretical Yields (4640-4740)
    K.set(15, 1, safeDiv(F.get(1, 3) * (E.get(4, 3) - f33) * 100.0, E.get(4, 3) * (F.get(1, 3) - f33)));
    K.set(15, 2, D.get(3, 3));
    K.set(15, 3, K.get(15, 1) - K.get(15, 2));
    K.set(15, 4, D.get(6, 3));
    K.set(15, 5, K.get(15, 3) - K.get(15, 4));

    K.set(16, 1, safeDiv(F.get(2, 3) * (E.get(4, 9) - f43) * 100.0, E.get(4, 9) * (F.get(2, 3) - f43)));
    K.set(16, 2, D.get(3, 4));
    K.set(16, 3, K.get(16, 1) - K.get(16, 2));
    K.set(16, 4, D.get(6, 4));
    K.set(16, 5, K.get(16, 3) - K.get(16, 4));

    // Solids in Final Molasses (4750-4850)
    K.set(17, 1, safeDiv((F.get(1, 3) - E.get(4, 3)) * 100.0, F.get(1, 3) - f33));
    K.set(17, 2, K.get(3, 3));
    K.set(17, 3, K.get(17, 1) - K.get(17, 2));
    K.set(17, 4, K.get(2, 3));
    K.set(17, 5, K.get(17, 3) - K.get(17, 4));

    K.set(18, 1, safeDiv((F.get(2, 3) - E.get(4, 9)) * 100.0, F.get(2, 3) - f43));
    K.set(18, 2, K.get(3, 4));
    K.set(18, 3, K.get(18, 1) - K.get(18, 2));
    K.set(18, 4, K.get(2, 4));
    K.set(18, 5, K.get(18, 3) - K.get(18, 4));

    // Crystal Yields (4860-4940)
    K.set(19, 1, safeDiv((E.get(9, 3) - E.get(13, 3)) * 100.0, 100.0 - E.get(13, 3)));
    K.set(19, 2, safeDiv((E.get(10, 3) - E.get(14, 3)) * 100.0, 100.0 - E.get(14, 3)));
    K.set(19, 3, safeDiv((E.get(11, 3) - E.get(15, 3)) * 100.0, 100.0 - E.get(15, 3)));
    K.set(19, 4, safeDiv((E.get(12, 3) - f33) * 100.0, 100.0 - f33));

    K.set(20, 1, safeDiv((E.get(9, 9) - E.get(13, 9)) * 100.0, 100.0 - E.get(13, 9)));
    K.set(20, 2, safeDiv((E.get(10, 9) - E.get(14, 9)) * 100.0, 100.0 - E.get(14, 9)));
    K.set(20, 3, safeDiv((E.get(11, 9) - E.get(15, 9)) * 100.0, 100.0 - E.get(15, 9)));
    K.set(20, 4, safeDiv((E.get(12, 9) - f43) * 100.0, 100.0 - f43));

    // Sugar Based on Cu. Ft. (4950-5130 & DEFFN'4 at 7101-7105)
    function deffn4(aP, bP, cP, dBrix, eMoist, fCuft) {
      if (Math.abs(dBrix) < 1e-9 || Math.abs(fCuft) < 1e-9) return 0.0;
      const k1 = (brixDensityPoly5(dBrix) * dBrix) / 100.0;
      return safeDiv((bP - cP) * k1 * fCuft * 100.0, (aP - cP) * (100.0 - eMoist));
    }

    K.set(21, 1, deffn4(F.get(1, 3), E.get(9, 3), E.get(13, 3), E.get(9, 1), F.get(1, 7), C.get(3, 1)));
    K.set(21, 2, deffn4(F.get(1, 3), E.get(10, 3), E.get(14, 3), E.get(10, 1), F.get(1, 7), C.get(4, 1)));
    K.set(21, 3, deffn4(F.get(1, 3), E.get(11, 3), E.get(15, 3), E.get(11, 1), F.get(1, 7), C.get(5, 1)));
    // Historical line 5020: K(21,4) = K(21,1) + K(21,2)
    K.set(21, 4, K.get(21, 1) + K.get(21, 2));
    K.set(21, 5, B.get(4, 3));
    K.set(21, 6, safeDiv((K.get(21, 4) - K.get(21, 5)) * 100.0, K.get(21, 4)));

    K.set(22, 1, deffn4(F.get(2, 3), E.get(9, 9), E.get(13, 9), E.get(9, 7), F.get(2, 7), C.get(3, 3)));
    K.set(22, 2, deffn4(F.get(2, 3), E.get(10, 9), E.get(14, 9), E.get(10, 7), F.get(2, 7), C.get(4, 3)));
    K.set(22, 3, deffn4(F.get(2, 3), E.get(11, 9), E.get(15, 9), E.get(11, 7), F.get(2, 7), C.get(5, 3)));
    K.set(22, 4, K.get(22, 1) + K.get(22, 2));
    K.set(22, 5, B.get(4, 4));
    K.set(22, 6, safeDiv((K.get(22, 4) - K.get(22, 5)) * 100.0, K.get(22, 4)));

    // Final Molasses Recycled in C Sugar (5140-5160)
    K.set(
      23,
      1,
      safeDiv((E.get(12, 3) - f33) * (100.0 - E.get(17, 3)) * 100.0, (E.get(17, 3) - f33) * (100.0 - E.get(12, 3)))
    );
    K.set(
      24,
      1,
      safeDiv((E.get(12, 9) - f43) * (100.0 - E.get(17, 9)) * 100.0, (E.get(17, 9) - f43) * (100.0 - E.get(12, 9)))
    );

    const lines = [];
    const bTrim = String(B_name || "").trim();
    const hdrLeft = H_num.get(28) !== 0 ? `Date: ${A2_s.get(1)} to ${A2_s.get(2)}` : `Date: ${A2_s.get(2)}`;
    const centerPos = Math.max(hdrLeft.length + 2, Math.trunc(66 - bTrim.length / 2));
    const hdrLine = hdrLeft.padEnd(centerPos, " ") + bTrim;
    lines.push(hdrLine.padEnd(124, " ") + "Page 3");
    lines.push("");
    lines.push(
      "                                         BRIX - TONS                    PER CENT BRIX EXTRACTED                    PER CENT CANE"
    );
    lines.push(
      "BRIX ACCOUNT                      ------------------------              -----------------------                 -------------------"
    );
    if (H_num.get(28) !== 0) {
      lines.push(
        "------------                           Run         To Date                   Run        To Date                     Run     To Date"
      );
    } else {
      lines.push(
        "------------                         Today         To Date                 Today        To Date                   Today     To Date"
      );
    }
    lines.push(
      "                                  --------        --------               -------        -------                 -------     -------"
    );

    const img5370 =
      "%####################      -###,###,###.###  -#,###,###.###                   ---            ---            -###,###.### -##,###.###";
    const img5440 =
      "%####################      -###,###,###.###  -#,###,###.###       -###,###,###.##    -###,###.##            -###,###.### -##,###.###";

    const brixLabels = [
      "In Bagasse",
      "In Final Molasses",
      "In Filter Cake",
      "Undetermined",
      "Total Losses",
      "Recovered in Sugars",
      "Brix in Juice % Cane",
      "Brix in Cane",
    ];
    lines.push(formatPrintusing(img5370, [brixLabels[0], K.get(1, 1), K.get(1, 2), K.get(1, 5), K.get(1, 6)]));
    for (let j = 2; j <= 7; j++) {
      lines.push(
        formatPrintusing(img5440, [
          brixLabels[j - 1],
          K.get(j, 1),
          K.get(j, 2),
          K.get(j, 3),
          K.get(j, 4),
          K.get(j, 5),
          K.get(j, 6),
        ])
      );
    }
    lines.push(formatPrintusing(img5370, [brixLabels[7], K.get(8, 1), K.get(8, 2), K.get(8, 5), K.get(8, 6)]));

    const dash85 = " ".repeat(31) + "-".repeat(85);
    lines.push("");
    lines.push(" ".repeat(57) + "PURITIES - COMPARED TO MIXED JUICE");
    lines.push(dash85);
    lines.push(
      "                               Sugar     Final Molasses    Filter Cake    All Products    Mixed Juice     Difference"
    );
    lines.push(
      "                               -----     --------------    -----------    ------------    -----------     ----------"
    );
    const img5530 =
      "%############                 -###.##    -###,###.##  -###,###,###.## -##,###,###.##  -#,###,###.##   -#,###,###.##";
    for (const j of [11, 12]) {
      lines.push(
        formatPrintusing(img5530, [
          C_lbl.get(j - 10),
          K.get(j, 1),
          K.get(j, 2),
          K.get(j, 3),
          K.get(j, 4),
          K.get(j, 5),
          K.get(j, 6),
        ])
      );
    }

    lines.push("");
    lines.push(" ".repeat(60) + "PURITIES - COMPARED TO SYRUP");
    lines.push(dash85);
    lines.push(
      "                               Sugar       Final Molasses        Sugar & Final Molasses        Syrup      Difference"
    );
    lines.push(
      "                               -----       --------------        ----------------------        -----      ----------"
    );
    const img5620 =
      "%############              -##,###.##      -###,###.##            -##,###,###.##          -###,###.##   -###,###.##";
    for (const j of [13, 14]) {
      lines.push(
        formatPrintusing(img5620, [
          C_lbl.get(j - 12),
          K.get(j, 1),
          K.get(j, 2),
          K.get(j, 3),
          K.get(j, 4),
          K.get(j, 5),
        ])
      );
    }

    lines.push("");
    lines.push(" ".repeat(54) + "THEORETICAL YIELDS % POL IN MIXED JUICE");
    lines.push(dash85);
    lines.push(
      "                                SJM      Filter Loss     Theoretical Recovery     Reported Recovery       Difference"
    );
    lines.push(
      "                               -----     -----------     --------------------     -----------------       ----------"
    );
    const img5710 =
      "%###############      -###,###,###.##   -##,###.##      -###,###,###.##        -###,###,###.##      -###,###,###.##";
    for (const j of [15, 16]) {
      lines.push(
        formatPrintusing(img5710, [
          C_lbl.get(j - 14),
          K.get(j, 1),
          K.get(j, 2),
          K.get(j, 3),
          K.get(j, 4),
          K.get(j, 5),
        ])
      );
    }

    lines.push("");
    lines.push(" ".repeat(47) + "BRIX SOLIDS IN FINAL MOLASSES % SOLIDS IN MIXED JUICE");
    lines.push(dash85);
    lines.push(
      "                               (S-J)/(S-M)       Filter Cake Solids       Theoretical       Reported      Difference"
    );
    lines.push(
      "                               -----------       ------------------       -----------       --------      ----------"
    );
    const img5800 =
      "%################         -##,###,###.##         -##,###,###.##       -#,###,###.##    -#,###,###.##    -###,###.##";
    for (const j of [17, 18]) {
      lines.push(
        formatPrintusing(img5800, [
          C_lbl.get(j - 16),
          K.get(j, 1),
          K.get(j, 2),
          K.get(j, 3),
          K.get(j, 4),
          K.get(j, 5),
        ])
      );
    }

    lines.push("");
    lines.push(" ".repeat(46) + "MASSECUITE CRYSTAL YIELDS (CRYSTALS % MASSECUITE SOLIDS");
    lines.push(dash85);
    lines.push(
      "                               A Massecuite         Top-Off A Massecuite          B Massecuite          C Massecuite"
    );
    lines.push(
      "                               ------------         --------------------          ------------          ------------"
    );
    const img5890 =
      "%#################        -###,###,###.##       -#,###,###,###.##             -##,###,###.##       -###,###,###.##";
    for (const j of [19, 20]) {
      lines.push(
        formatPrintusing(img5890, [C_lbl.get(j - 18), K.get(j, 1), K.get(j, 2), K.get(j, 3), K.get(j, 4)])
      );
    }

    lines.push("");
    lines.push(" ".repeat(43) + "COMPARISON OF SUGAR YIELD BY STRIKES WITH REPORTED SUGAR MADE");
    lines.push(dash85);
    lines.push(
      "                               A Sugar     T-O A Sugar      B Sugar     Total Sugar     Reported Sugar    % Diff'nce"
    );
    lines.push(
      "                               -------     -----------    -----------   -----------     --------------    ----------"
    );
    const img5980 =
      "%###############   -###,###,###,###,### -##,###,###,###   -###,###,###  -###,###,### -#,###,###,###,###  -###,###.##";
    for (const j of [21, 22]) {
      lines.push(
        formatPrintusing(img5980, [
          C_lbl.get(j - 20),
          K.get(j, 1),
          K.get(j, 2),
          K.get(j, 3),
          K.get(j, 4),
          K.get(j, 5),
          K.get(j, 6),
        ])
      );
    }

    lines.push("");
    lines.push(" ".repeat(41) + "FINAL MOLASSES RECYCLED IN MAGMA % FINAL MOLASSES IN C MASSECUITE");
    lines.push(dash85);
    const img6050 = "%##########################                                   -#,###,###,###.##";
    for (const j of [23, 24]) {
      lines.push(formatPrintusing(img6050, [C_lbl.get(j - 22), K.get(j, 1)]));
    }

    return lines;
  }

  function renderMrcomppr(B_name, A2_s, A, B, D, E, F, G, H_num) {
    const C_s = new OneBasedArray1D(82, "");
    const I_arr = new OneBasedArray2D(82, 2, 0.0);

    const cLabels = [
      "             Factory Name",
      "   2.        Run Report Number",
      "             Report Date",
      "             Date Checked",
      "             Dry Milling Factor",
      "   3.        Crop Days",
      "             Hours Grinding",
      "             Minutes Grinding",
      "             Hours Lost",
      "             Minutes Lost",
      "             Mixed Juice % Cane",
      "   7.        Imbibition % Cane",
      "  13.        Pol % Bagasse",
      "  13a.       Moisture % Bagasse",
      "   5.        Gross (Short) Tons Cane Ground",
      "             Crusher Juice Brix",
      "             Crusher Juice Purity",
      "             Mixed Juice Brix",
      "             Mixed Juice Purity",
      "             Last Roll Juice Brix",
      "             Last Roll Juice Purity",
      "             Clarified Juice Brix",
      "             Clarified Juice Purity",
      "             Syrup Brix",
      "             Syrup Purity",
      "  22d.       Final Molasses Brix",
      "  22e.       Final Molasses Purity",
      "             A Massecuite Purity",
      "             B Massecuite Purity",
      "             C Massecuite Purity",
      "             A Molasses Purity",
      "             B Molasses Purity",
      "             Magma Purity",
      "  35.        Trash % Cane",
      "  16.        Lbs Sugar Made and Estimated",
      "  18.        Pol of Sugar as Made and Estimated",
      "  18.        Pol of Sugar as Produced",
      "  22b.       Gals (US) of Final Molasses M & E",
      "             Brix of Final Molasses as M & E",
      "  14.        Tons Filter Cake Produced",
      "  14a.       Pol % Filter Cake Produced",
      "             Moisture % Sugar",
      "   1.        Beginning Date",
      "   2.        Ending Date",
      "   4.        Lost Time % Total Time",
      "   6.        Tons Ground per Hour",
      "   8.        Extraction, Absolute Juice % Cane",
      "   9.        Dilution % Cane",
      "  10.        Pol % Pol in Cane",
      "  11.        Pol % Cane",
      "  12.        Fiber % Cane",
      "  13b.       Bagasse % Fiber",
      "  13c.       Bagasse % Cane",
      "  13d.       Bagasse, Pol % Fiber",
      "  13e.       Tons Fiber Ground/Hour/Sq. Ft.",
      "  15.        Absolute Juice Brix",
      "  15a.       Absolute Juice Pol",
      "  15b.       Absolute Juice Purity",
      "  17.        Sugar: 96 (M&E) Lbs",
      "  19.        Sugar: Lbs 96 per Ton Cane",
      "  20.        Yield 96 Sugar, %",
      "  21.        Yield 96 Sugar, Lbs per Net Ton",
      "  22.        Gallons Molasses Made",
      "  22a.       Gals Molasses in Proc. @ 79.5 Brix",
      "  22b.       Gallons Molasses M&E @ 79.5 Brix",
      "  22c.       Gals Mol. per Ton Cane @ 79.5 Brix",
      "  23.        Pol Retention - %",
      "  24.        Loss in Bagasse",
      "  25.        Loss in Final Molasses",
      "  26.        Loss in Mud",
      "  27.        Loss Undetermined",
      "  28.        Total Losses",
      "  29.        Recovered in Sugar",
      "  30.        Recovered in Com'l Molasses",
      "  31.        Pol in Juice % Cane",
      "  32.        Pol in Cane",
      "  33.        Gas, MCF/Ton Cane",
      "  34.        Oil, Gals/Ton Cane",
      "  36.        Boiling House Efficiency Number",
      "  37.        Corer TRS (Lbs R.V./Std. Ton Cane)",
      "  38.        Liquidation Factor (Std. Tons Cane)",
      "   *         Factory Number",
    ];
    C_s.fromList(cLabels);

    I_arr.set(2, 1, H_num.get(31));
    I_arr.set(5, 1, 0.97);
    for (const j of [1, 2]) {
      I_arr.set(6, j, B.get(1, j));
      I_arr.set(7, j, B.get(2, j));
      I_arr.set(9, j, B.get(3, j));
      I_arr.set(11, j, B.get(15, j));
      I_arr.set(12, j, B.get(18, j));
      I_arr.set(13, j, B.get(23, j));
      I_arr.set(14, j, B.get(24, j));
      I_arr.set(15, j, B.get(5, j));
    }

    I_arr.set(16, 1, E.get(2, 1));
    I_arr.set(16, 2, E.get(2, 7));
    I_arr.set(17, 1, E.get(2, 3));
    I_arr.set(17, 2, E.get(2, 9));
    I_arr.set(18, 1, E.get(4, 1));
    I_arr.set(18, 2, E.get(4, 7));
    I_arr.set(19, 1, E.get(4, 3));
    I_arr.set(19, 2, E.get(4, 9));
    I_arr.set(20, 1, E.get(5, 1));
    I_arr.set(20, 2, E.get(5, 7));
    I_arr.set(21, 1, E.get(5, 3));
    I_arr.set(21, 2, E.get(5, 9));
    I_arr.set(22, 1, E.get(6, 1));
    I_arr.set(22, 2, E.get(6, 7));
    I_arr.set(23, 1, E.get(6, 3));
    I_arr.set(23, 2, E.get(6, 9));
    I_arr.set(24, 1, E.get(8, 1));
    I_arr.set(24, 2, E.get(8, 7));
    I_arr.set(25, 1, E.get(8, 3));
    I_arr.set(25, 2, E.get(8, 9));
    I_arr.set(26, 1, F.get(3, 1));
    I_arr.set(26, 2, F.get(4, 1));
    I_arr.set(27, 1, F.get(3, 3));
    I_arr.set(27, 2, F.get(4, 3));
    I_arr.set(28, 1, E.get(9, 3));
    I_arr.set(28, 2, E.get(9, 9));
    I_arr.set(29, 1, E.get(11, 3));
    I_arr.set(29, 2, E.get(11, 9));
    I_arr.set(30, 1, E.get(12, 3));
    I_arr.set(30, 2, E.get(12, 9));
    I_arr.set(31, 1, E.get(13, 3));
    I_arr.set(31, 2, E.get(13, 9));
    I_arr.set(32, 1, E.get(15, 3));
    I_arr.set(32, 2, E.get(15, 9));
    I_arr.set(33, 1, E.get(17, 3));
    I_arr.set(33, 2, E.get(17, 9));
    I_arr.set(34, 1, 0.0);
    I_arr.set(34, 2, 0.0);
    I_arr.set(35, 1, B.get(6, 3));
    I_arr.set(35, 2, B.get(6, 4));
    I_arr.set(36, 1, B.get(18, 3));
    I_arr.set(36, 2, B.get(18, 4));
    I_arr.set(37, 1, B.get(18, 3));
    I_arr.set(37, 2, B.get(18, 4));
    I_arr.set(38, 1, B.get(16, 3));
    I_arr.set(38, 2, B.get(16, 4));
    I_arr.set(39, 1, H_num.get(30));
    I_arr.set(39, 2, H_num.get(30));
    I_arr.set(40, 1, B.get(19, 3));
    I_arr.set(40, 2, B.get(19, 4));
    I_arr.set(41, 1, F.get(7, 2));
    I_arr.set(41, 2, F.get(8, 2));
    I_arr.set(42, 1, F.get(1, 7));
    I_arr.set(42, 2, F.get(2, 7));

    for (const j of [1, 2]) {
      I_arr.set(45, j, B.get(4, j));
      I_arr.set(46, j, B.get(8, j));
      I_arr.set(47, j, B.get(16, j));
      I_arr.set(48, j, B.get(20, j));
      I_arr.set(49, j, B.get(13, j));
      I_arr.set(50, j, B.get(21, j));
      I_arr.set(51, j, B.get(22, j));
      I_arr.set(52, j, B.get(25, j));
      I_arr.set(53, j, B.get(26, j));
      I_arr.set(54, j, B.get(27, j));
      I_arr.set(55, j, B.get(12, j));
    }

    I_arr.set(56, 1, E.get(3, 1));
    I_arr.set(56, 2, E.get(3, 7));
    I_arr.set(57, 1, E.get(3, 2));
    I_arr.set(57, 2, E.get(3, 8));
    I_arr.set(58, 1, E.get(3, 3));
    I_arr.set(58, 2, E.get(3, 9));
    I_arr.set(59, 1, B.get(3, 3));
    I_arr.set(59, 2, B.get(3, 4));
    I_arr.set(60, 1, B.get(10, 3));
    I_arr.set(60, 2, B.get(10, 4));
    I_arr.set(61, 1, B.get(10, 3) / 20.0);
    I_arr.set(61, 2, B.get(10, 4) / 20.0);
    I_arr.set(62, 1, 0.0);
    I_arr.set(62, 2, 0.0);
    I_arr.set(63, 1, B.get(14, 3));
    I_arr.set(63, 2, B.get(14, 4));
    I_arr.set(64, 1, B.get(15, 3));
    I_arr.set(64, 2, B.get(15, 4));
    I_arr.set(65, 1, B.get(16, 3));
    I_arr.set(65, 2, B.get(16, 4));
    I_arr.set(66, 1, safeDiv((A.get(218, 1) * 2000.0) / 9.338, A.get(191, 1)));
    I_arr.set(66, 2, safeDiv((A.get(218, 2) * 2000.0) / 9.338, A.get(191, 2)));
    I_arr.set(67, 1, D.get(6, 3));
    I_arr.set(67, 2, D.get(6, 4));
    I_arr.set(68, 1, D.get(1, 5));
    I_arr.set(68, 2, D.get(1, 6));
    I_arr.set(69, 1, D.get(2, 5));
    I_arr.set(69, 2, D.get(2, 6));
    I_arr.set(70, 1, D.get(3, 5));
    I_arr.set(70, 2, D.get(3, 6));
    I_arr.set(71, 1, D.get(4, 5));
    I_arr.set(71, 2, D.get(4, 6));
    I_arr.set(72, 1, D.get(5, 5));
    I_arr.set(72, 2, D.get(5, 6));
    I_arr.set(73, 1, D.get(6, 5));
    I_arr.set(73, 2, D.get(6, 6));
    I_arr.set(75, 1, D.get(7, 5));
    I_arr.set(75, 2, D.get(7, 6));
    I_arr.set(76, 1, D.get(8, 5));
    I_arr.set(76, 2, D.get(8, 6));
    I_arr.set(77, 1, G.get(1, 7));
    I_arr.set(77, 2, G.get(1, 8));
    I_arr.set(79, 1, B.get(21, 3));
    I_arr.set(79, 2, B.get(21, 4));
    I_arr.set(80, 1, B.get(12, 3));
    I_arr.set(80, 2, B.get(12, 4));
    I_arr.set(81, 1, B.get(13, 3));
    I_arr.set(81, 2, B.get(13, 4));

    const img2210 = "%##############################################  ##############################################";
    const img2260 = "%############################################## -###,###,###.## -###,###,###.##";
    const img2280 = "%############################################## -##,###,###.### -##,###,###.###";
    const img2290 = "%##############################################        ########        ########";

    const p1 = [];
    p1.push(" ".repeat(21) + "DATA FORM FOR WEEKLY COMPARATIVE REPORT");
    p1.push("");
    p1.push(" ".repeat(36) + "Page 1");
    p1.push("");
    p1.push("Item");
    p1.push("Number       Item                                     Run          To Date");
    p1.push("------       --------------------------------        -----        ---------");
    p1.push(formatPrintusing(img2210, [C_s.get(1), String(B_name || "").trim()]));
    p1.push(
      formatPrintusing(img2290, [C_s.get(2), String(Math.round(I_arr.get(2, 1))).padStart(8, " "), "XXXXXXXX"])
    );
    p1.push(formatPrintusing(img2290, [C_s.get(3), A2_s.get(2), "XXXXXXXX"]));
    p1.push(formatPrintusing(img2290, [C_s.get(4), "  /  /  ", "XXXXXXXX"]));

    for (const [x, y] of [
      [6, 10],
      [11, 15],
      [16, 25],
      [26, 33],
      [35, 42],
    ]) {
      for (let j = x; j <= y; j++) {
        p1.push(formatPrintusing(img2260, [C_s.get(j), I_arr.get(j, 1), I_arr.get(j, 2)]));
      }
      p1.push("");
    }

    const p2 = [];
    p2.push(" ".repeat(21) + "DATA FORM FOR WEEKLY COMPARATIVE REPORT");
    p2.push("");
    p2.push(" ".repeat(36) + "Page 2");
    p2.push("");
    p2.push("Item");
    p2.push("Number       Item                                     Run          To Date");
    p2.push("------       --------------------------------        -----        ---------");
    p2.push(formatPrintusing(img2290, [C_s.get(43), A2_s.get(1), A2_s.get(3)]));
    p2.push(formatPrintusing(img2290, [C_s.get(44), A2_s.get(2), "XXXXXXXX"]));

    for (let j = 45; j <= 51; j++) {
      p2.push(formatPrintusing(img2260, [C_s.get(j), I_arr.get(j, 1), I_arr.get(j, 2)]));
    }
    p2.push("");
    for (let j = 52; j <= 54; j++) {
      p2.push(formatPrintusing(img2260, [C_s.get(j), I_arr.get(j, 1), I_arr.get(j, 2)]));
    }
    p2.push(formatPrintusing(img2280, [C_s.get(55), I_arr.get(55, 1), I_arr.get(55, 2)]));
    for (let j = 56; j <= 58; j++) {
      p2.push(formatPrintusing(img2260, [C_s.get(j), I_arr.get(j, 1), I_arr.get(j, 2)]));
    }
    p2.push("");
    for (let j = 59; j <= 61; j++) {
      p2.push(formatPrintusing(img2260, [C_s.get(j), I_arr.get(j, 1), I_arr.get(j, 2)]));
    }
    for (let j = 63; j <= 67; j++) {
      p2.push(formatPrintusing(img2260, [C_s.get(j), I_arr.get(j, 1), I_arr.get(j, 2)]));
    }
    p2.push("");
    for (let j = 68; j <= 76; j++) {
      p2.push(formatPrintusing(img2280, [C_s.get(j), I_arr.get(j, 1), I_arr.get(j, 2)]));
    }
    p2.push("");
    p2.push(formatPrintusing(img2280, [C_s.get(77), I_arr.get(77, 1), I_arr.get(77, 2)]));
    for (let j = 79; j <= 81; j++) {
      p2.push(formatPrintusing(img2260, [C_s.get(j), I_arr.get(j, 1), I_arr.get(j, 2)]));
    }
    p2.push("");
    p2.push(formatPrintusing(img2290, [C_s.get(82), "        ", "XXXXXXXX"]));

    return [p1, p2];
  }

  function renderMrcustpr(B_name, A1_s, J_s, H_s, I_s, H_num) {
    I_s.set(1, H_num.get(1) === 1 ? "D" : "W");
    for (let j = 2; j <= 23; j++) {
      I_s.set(j, H_num.get(j) === 0 ? "N" : "Y");
    }
    I_s.set(24, H_num.get(27) === 0 ? "N" : "Y");

    const bLabels = ["FACTORY NAME ON REPORT", "GREGORIAN DATE CROP STARTED"];
    for (let i = 1; i <= 10; i++) bLabels.push(`LOST TIME CATEGORY NO. ${i}`);
    for (let i = 1; i <= 12; i++) bLabels.push(`MATERIALS AND SUPPLIES CATEGORY NO. ${i}`);
    bLabels.push(
      "TOTAL ROLL SURFACE OF ALL MILL ROLLS",
      "BRIX DESIRED FOR REPORTING FINAL MOLASSES M&E/TON CANE",
      "WILL ANALYSES BE AVERAGED BY CROP DAY (D) OR CANE WEIGHTING (W)",
      "WILL CRUSHER JUICE GLUCOSE BE REPORTED (Y OR N)",
      "WILL CRUSHER JUICE pH BE REPORTED (Y OR N)",
      "WILL MIXED JUICE GLUCOSE BE REPORTED (Y OR N)",
      "WILL MIXED JUICE pH BE REPORTED (Y OR N)",
      "WILL CLARIFIED JUICE GLUCOSE BE REPORTED (Y OR N)",
      "WILL CLARIFIED JUICE pH BE REPORTED (Y OR N)",
      "WILL SYRUP GLUCOSE BE REPORTED (Y OR N)",
      "WILL SYRUP pH BE REPORTED (Y OR N)",
      "WILL SUGAR MADE STARCH BE REPORTED (Y OR N)",
      "WILL SUGAR MADE DEXTRAN BE REPORTED (Y OR N)",
      "WILL FINAL MOLASSES MADE GLUCOSE BE REPORTED (Y OR N)",
      "WILL FINAL MOLASSES MADE ASH BE REPORTED (Y OR N)",
      "WILL FINAL MOLASSES MADE CLERGET BE REPORTED (Y OR N)",
      "WILL FINAL MOLASSES SHIPPED GLUCOSE BE REPORTED (Y OR N)",
      "WILL FINAL MOLASSES SHIPPED ASH BE REPORTED (Y OR N)",
      "WILL FINAL MOLASSES SHIPPED CLERGET BE REPORTED (Y OR N)",
      "WILL FILTRATE JUICE BRIX AND POL BE REPORTED (Y OR N)",
      "WILL TOP-OFF A STRIKES BRIX AND POL BE REPORTED (Y OR N)",
      "WILL EITHER B MAGMA OR C CYCLONES BE REPORTED (Y OR N)",
      "WILL FILTER CAKE MOISTURES BE REPORTED (Y OR N)",
      "WILL B MAGMA (Y) OR C CYCLONE (N) ANALYSES BE REPORTED",
      "DOES REPORT PRINTER HAVE EXPANDED PRINT CAPABILITY (Y OR N)",
      "WILL METERED IMBIBITION WATER BE REPORTED (Y OR N)",
      "JULIAN DATE CROP STARTED"
    );

    const img650 = "%################################################################   ####################";
    const img660 =
      "%################################################################   ################################################################";

    const p1 = [];
    p1.push(" ".repeat(34) + "CUSTOM PARAMETERS");
    p1.push("");
    p1.push(formatPrintusing(img660, [bLabels[0], String(B_name || "").trim()]));
    p1.push(formatPrintusing(img650, [bLabels[1], String(A1_s || "").trim()]));
    p1.push("");
    p1.push("LOST TIME CATEGORIES");
    p1.push("--------------------");
    p1.push("");
    for (let j = 1; j <= 10; j++) {
      p1.push(formatPrintusing(img650, [bLabels[j + 1], J_s.get(j)]));
    }
    p1.push("");
    p1.push("MATERIALS AND SUPPLIES CATEGORIES");
    p1.push("---------------------------------");
    p1.push("");
    for (let j = 1; j <= 12; j++) {
      p1.push(formatPrintusing(img650, [bLabels[j + 11], H_s.get(j)]));
    }
    p1.push("");
    for (const j of [1, 2]) {
      p1.push(formatPrintusing(img650, [bLabels[j + 23], H_s.get(j + 12)]));
    }

    const p2 = [];
    p2.push("SUPPRESSION OF DATA INPUT FOR ITEMS NOT REPORTED");
    p2.push("------------------------------------------------");
    p2.push("");
    for (let j = 1; j <= 24; j++) {
      p2.push(formatPrintusing(img650, [bLabels[j + 25], I_s.get(j)]));
    }
    p2.push("");
    p2.push("PRINTER AND DATA DISK SELECTIONS");
    p2.push("--------------------------------");
    p2.push("");
    p2.push(`PRINTER SELECTED (0 = SYSTEM, 1 = TERMINAL) IS NO. ${Math.round(H_num.get(36))}`);
    p2.push(
      `DATA DISK SELECTED (0=SAME AS PROGRAM,1=310,2=D11,3=D12,4=D13,5=D14,6=D20,7=D21,8=D22,9=D23,10=D24,11=D25) IS NO. ${Math.round(
        H_num.get(37)
      )}`
    );
    return [p1, p2];
  }

  function renderMrdatafm(B_name, J_s, H_s, H_num) {
    const C_s = new OneBasedArray1D(110, "");
    C_s.set(1, "Crop Day Number");
    C_s.set(2, "Lbs TRS Purchased");
    for (let j = 1; j <= 10; j++) C_s.set(j + 2, J_s.get(j));
    C_s.set(13, "Total Hours Available");
    for (let j = 1; j <= 12; j++) C_s.set(j + 13, H_s.get(j));

    const fixed = {
      26: "Crusher Juice Brix",
      27: "Crusher Juice Pol",
      28: "Crusher Juice Glucose",
      29: "Crusher Juice pH",
      30: "Mixed Juice Brix",
      31: "Mixed Juice Pol",
      32: "Mixed Juice Glucose",
      33: "Mixed Juice pH",
      34: "Last Roll Juice Brix",
      35: "Last Roll Juice Pol",
      36: "Clarified Juice Brix",
      37: "Clarified Juice Pol",
      38: "Clarified Juice Glucose",
      39: "Clarified Juice pH",
      40: "Filter Press Juice Brix",
      41: "Filter Press Juice Pol",
      42: "Syrup Brix",
      43: "Syrup Pol",
      44: "Syrup Glucose",
      45: "Syrup pH",
      46: "A Massecuite Brix",
      47: "A Massecuite Pol",
      48: "Top-Off A Massecuite Brix",
      49: "Top-Off A Massecuite Pol",
      50: "B Massecuite Brix",
      51: "B Massecuite Pol",
      52: "C Massecuite Brix",
      53: "C Massecuite Pol",
      54: "A Molasses Brix",
      55: "A Molasses Pol",
      56: "Top-Off A Molasses Brix",
      57: "Top-Off A Molasses Pol",
      58: "B Molasses Brix",
      59: "B Molasses Pol",
      60: "Grain Brix",
      61: "Grain Pol",
      62: "C Magma Brix",
      63: "C Magma Pol",
      64: H_num.get(22) === 1 ? "B Magma Brix" : "C Cyclone Brix",
      65: H_num.get(22) === 1 ? "B Magma Pol" : "C Cyclone Pol",
      66: "Cu. Ft. of A Massecuite Made",
      67: "Cu. Ft. of Top-Off A Massecuite Made",
      68: "Cu. Ft. of B Massecuite Made",
      69: "Cu. Ft. of C Massecuite Made",
      70: "Sugar Made, % Moisture",
      71: "Sugar Made, % Pol",
      72: "Sugar Made, % Starch",
      73: "Sugar Made, Dextran",
      74: "Final Molasses Made Brix",
      75: "Final Molasses Made Pol",
      76: "Final Molasses Made Glucose",
      77: "Final Molasses Made Ash",
      78: "Final Molasses Made Clerget",
      79: "Final Molasses Shipped Brix",
      80: "Final Molasses Shipped Pol",
      81: "Final Molasses Shipped Glucose",
      82: "Final Molasses Shipped Ash",
      83: "Final Molasses Shipped Clerget",
      84: "Filter Cake Pol",
      85: "Filter Cake Moisture",
      86: "Bagasse Pol",
      87: "Bagasse Moisture",
      88: "Tons Cane Purchased",
      89: "Net Tons Cane Purchased",
      90: "Standard Tons Cane Purchased",
      91: "Tons Cane Ground",
      92: "Tons Mixed Juice",
      93: "Tons Imbibition Water",
      94: "Tons Filter Cake Made",
      95: "Lbs Sugar Made",
      96: "Gallons Final Molasses Made",
      97: "Lbs Sugar Shipped",
      98: "Gallons Final Molasses Shipped",
      99: "Core Lab Cane, % Pol",
      100: "Core Lab Cane, % Brix",
      101: "Core Lab Cane, % Fiber",
      102: "Rainfall, Inches",
      103: "Temperature, Maximum, deg. F",
      104: "Temperature, Minimum, deg. F",
      105: "Lbs Sugar Brix in Process",
      106: "Lbs Sugar Pol in Process",
      107: "Lbs Final Molasses Brix in Process",
      108: "Lbs Final Molasses Pol in Process",
      109: "Weighting Factor",
      110: "Tons Metered Imbibition Water",
    };
    for (const [k, v] of Object.entries(fixed)) {
      C_s.set(Number(k), v);
    }

    const bTrim = String(B_name || "").trim();
    const centerB = " ".repeat(Math.max(0, Math.trunc(40 - bTrim.length / 2))) + bTrim;

    function fmtItem(idx, label, suppressed = false) {
      const idxStr = String(idx).padStart(3, " ");
      const lblPad = String(label || "").padEnd(40, " ");
      if (suppressed) {
        return `${idxStr}     ${lblPad}      XXXXXXXXXX`;
      }
      return `${idxStr}     ${lblPad}`;
    }

    const p1 = [
      centerB,
      "",
      " ".repeat(25) + "DAILY REPORT DATA INPUT FORM" + " ".repeat(16) + "Page 1",
      "",
      "",
      fmtItem("   ", "Report Date", false),
      fmtItem(1, C_s.get(1), true),
      fmtItem(2, C_s.get(2), false),
      "",
    ];
    for (let j = 3; j <= 13; j++) p1.push(fmtItem(j, C_s.get(j), false));
    p1.push("");
    for (let j = 14; j <= 25; j++) p1.push(fmtItem(j, C_s.get(j), false));
    p1.push("");
    p1.push(fmtItem(26, C_s.get(26), false));
    p1.push(fmtItem(27, C_s.get(27), false));
    p1.push(fmtItem(28, C_s.get(28), H_num.get(2) === 0));
    p1.push(fmtItem(29, C_s.get(29), H_num.get(3) === 0));
    p1.push("");
    p1.push(fmtItem(30, C_s.get(30), false));
    p1.push(fmtItem(31, C_s.get(31), false));
    p1.push(fmtItem(32, C_s.get(32), H_num.get(4) === 0));
    p1.push(fmtItem(33, C_s.get(33), H_num.get(5) === 0));
    p1.push("");
    p1.push(fmtItem(34, C_s.get(34), false));
    p1.push(fmtItem(35, C_s.get(35), false));
    p1.push("");
    p1.push(fmtItem(36, C_s.get(36), false));
    p1.push(fmtItem(37, C_s.get(37), false));
    p1.push(fmtItem(38, C_s.get(38), H_num.get(6) === 0));
    p1.push(fmtItem(39, C_s.get(39), H_num.get(7) === 0));

    const p2 = [
      centerB,
      "",
      " ".repeat(22) + "DAILY REPORT DATA INPUT FORM (Cont'd)" + " ".repeat(10) + "Page 2",
      "",
      "",
      fmtItem(40, C_s.get(40), H_num.get(18) === 0),
      fmtItem(41, C_s.get(41), H_num.get(18) === 0),
      "",
      fmtItem(42, C_s.get(42), false),
      fmtItem(43, C_s.get(43), false),
      fmtItem(44, C_s.get(44), H_num.get(8) === 0),
      fmtItem(45, C_s.get(45), H_num.get(9) === 0),
      "",
      fmtItem(46, C_s.get(46), false),
      fmtItem(47, C_s.get(47), false),
      "",
      fmtItem(48, C_s.get(48), H_num.get(19) === 0),
      fmtItem(49, C_s.get(49), H_num.get(19) === 0),
      "",
      fmtItem(50, C_s.get(50), false),
      fmtItem(51, C_s.get(51), false),
      "",
      fmtItem(52, C_s.get(52), false),
      fmtItem(53, C_s.get(53), false),
      "",
      fmtItem(54, C_s.get(54), false),
      fmtItem(55, C_s.get(55), false),
      "",
      fmtItem(56, C_s.get(56), H_num.get(19) === 0),
      fmtItem(57, C_s.get(57), H_num.get(19) === 0),
      "",
      fmtItem(58, C_s.get(58), false),
      fmtItem(59, C_s.get(59), false),
      "",
      fmtItem(60, C_s.get(60), false),
      fmtItem(61, C_s.get(61), false),
      "",
      fmtItem(62, C_s.get(62), false),
      fmtItem(63, C_s.get(63), false),
      "",
      fmtItem(64, C_s.get(64), H_num.get(20) === 0),
      fmtItem(65, C_s.get(65), H_num.get(20) === 0),
      "",
      fmtItem(66, C_s.get(66), false),
      fmtItem(67, C_s.get(67), H_num.get(19) === 0),
      fmtItem(68, C_s.get(68), false),
      fmtItem(69, C_s.get(69), false),
      "",
      fmtItem(70, C_s.get(70), false),
      fmtItem(71, C_s.get(71), false),
      fmtItem(72, C_s.get(72), H_num.get(10) === 0),
      fmtItem(73, C_s.get(73), H_num.get(11) === 0),
    ];

    const p3 = [
      centerB,
      "",
      " ".repeat(22) + "DAILY REPORT DATA INPUT FORM (Cont'd)" + " ".repeat(10) + "Page 3",
      "",
      fmtItem(74, C_s.get(74), false),
      fmtItem(75, C_s.get(75), false),
      fmtItem(76, C_s.get(76), H_num.get(12) === 0),
      fmtItem(77, C_s.get(77), H_num.get(13) === 0),
      fmtItem(78, C_s.get(78), H_num.get(14) === 0),
      "",
      fmtItem(79, C_s.get(79), false),
      fmtItem(80, C_s.get(80), false),
      fmtItem(81, C_s.get(81), H_num.get(15) === 0),
      fmtItem(82, C_s.get(82), H_num.get(16) === 0),
      fmtItem(83, C_s.get(83), H_num.get(17) === 0),
      "",
      fmtItem(84, C_s.get(84), false),
      fmtItem(85, C_s.get(85), H_num.get(21) === 0),
      "",
      fmtItem(86, C_s.get(86), false),
      fmtItem(87, C_s.get(87), false),
      "",
      fmtItem(88, C_s.get(88), false),
      "",
    ];
    for (let j = 91; j <= 96; j++) p3.push(fmtItem(j, C_s.get(j), false));
    p3.push("");
    for (const j of [97, 98]) p3.push(fmtItem(j, C_s.get(j), false));
    p3.push("");
    for (let j = 99; j <= 101; j++) p3.push(fmtItem(j, C_s.get(j), false));
    p3.push("");
    p3.push(fmtItem(102, C_s.get(102), false));
    p3.push("");
    for (const j of [103, 104]) p3.push(fmtItem(j, C_s.get(j), false));
    p3.push("");
    for (const j of [105, 106]) p3.push(fmtItem(j, C_s.get(j), false));
    p3.push("");
    for (const j of [107, 108]) p3.push(fmtItem(j, C_s.get(j), false));
    p3.push("");
    p3.push(fmtItem(109, C_s.get(109), true));
    p3.push("");
    p3.push(fmtItem(246, C_s.get(110), H_num.get(27) === 0));
    p3.push("");
    for (let wh = 1; wh <= 4; wh++) {
      p3.push(fmtItem(250 + wh, `Lbs Sugar in W/H #${wh}`, false));
    }

    const p4 = [
      "REMARKS - LINE 1A:    ------------------------------------------------------------",
      "REMARKS - LINE 1B:    ------------------------------------------------------------",
      "REMARKS - LINE 2A:    ------------------------------------------------------------",
      "REMARKS - LINE 2B:    ------------------------------------------------------------",
      "REMARKS - LINE 3A:    ------------------------------------------------------------",
      "REMARKS - LINE 3B:    ------------------------------------------------------------",
    ];
    return [p1, p2, p3, p4];
  }

  function renderMrstokfm(B_name) {
    const bTrim = String(B_name || "").trim();
    const centerB = " ".repeat(Math.max(0, Math.trunc(40 - bTrim.length / 2))) + bTrim;
    const streams = [
      "Juice",
      "Syrup",
      "A Massecuite",
      "Top-Off A Massecuite",
      "B Massecuite",
      "C Massecuite",
      "A Molasses",
      "Top-Off A Molasses",
      "B Molasses",
      "Grain",
      "B Magma",
      "C Magma",
      "Other Material",
    ];
    const pages = [];
    for (const unitLbl of ["Gallons", "Cu. Ft."]) {
      const p = [
        centerB,
        "",
        " ".repeat(22) + "DATA FORM FOR STOCK CALCULATIONS",
        "",
        "        Date",
        "",
      ];
      let idx = 1;
      for (const st of streams) {
        p.push(`${String(idx).padStart(2, " ")}      ${st}, ${unitLbl}`);
        p.push(`${String(idx + 1).padStart(2, " ")}      ${st}, Brix`);
        p.push(`${String(idx + 2).padStart(2, " ")}      ${st}, Pol`);
        idx += 3;
      }
      p.push("");
      p.push("40      Final Molasses Purity for Run");
      p.push("41      Sugar Purity for Run");
      pages.push(p);
    }
    return pages;
  }

  function renderMrdatapr(B_name, reportDate, X_arr, B1_s, J_s, H_s, H_num, includeTodateWorkup = false) {
    const bTrim = String(B_name || "").trim();
    const centerB = " ".repeat(Math.max(0, Math.trunc(40 - bTrim.length / 2))) + bTrim;
    const imgItem = "%###   ######################################## -###,###,###,###,###.####";
    const imgItem4 = "%####  ######################################## -###,###,###,###,###.####";

    function xVal(idx1Based) {
      if (idx1Based >= 1 && idx1Based <= X_arr.length) {
        return Number(X_arr[idx1Based - 1]) || 0.0;
      }
      return 0.0;
    }

    const kLabels = {
      1: "Crop Day No.",
      2: "Lbs TRS Purchased",
      26: "Crusher Juice Brix",
      27: "Crusher Juice Pol",
      28: "Crusher Juice Glucose",
      29: "Crusher Juice pH",
      30: "Mixed Juice Brix",
      31: "Mixed Juice Pol",
      32: "Mixed Juice Glucose",
      33: "Mixed Juice pH",
      34: "Last Roll Juice Brix",
      35: "Last Roll Juice Pol",
      36: "Clarified Juice Brix",
      37: "Clarified Juice Pol",
      38: "Clarified Juice Glucose",
      39: "Clarified Juice pH",
      40: "Filtrate Juice Brix",
      41: "Filtrate Juice Pol",
      42: "Syrup Brix",
      43: "Syrup Pol",
      44: "Syrup Glucose",
      45: "Syrup pH",
      46: "A Massecuite Brix",
      47: "A Massecuite Pol",
      48: "Top-Off A Massecuite Brix",
      49: "Top-Off A Massecuite Pol",
      50: "B Massecuite Brix",
      51: "B Massecuite Pol",
      52: "C Massecuite Brix",
      53: "C Massecuite Pol",
      54: "A Molasses Brix",
      55: "A Molasses Pol",
      56: "Top-Off A Molasses Brix",
      57: "Top-Off A Molasses Pol",
      58: "B Molasses Brix",
      59: "B Molasses Pol",
      60: "Grain Brix",
      61: "Grain Pol",
      62: "C Magma Brix",
      63: "C Magma Pol",
      64: H_num.get(22) === 1 ? "B Magma Brix" : "C Cyclone Brix",
      65: H_num.get(22) === 1 ? "B Magma Pol" : "C Cyclone Pol",
      66: "Cu. Ft. of A Massecuite Made",
      67: "Cu. Ft. of Top-Off A Mass. Made",
      68: "Cu. Ft. of B Massecuite Made",
      69: "Cu. Ft. of C Massecuite Made",
      70: "Moisture % Sugar Made",
      71: "Pol of Sugar Made",
      72: "Starch in Sugar Made",
      73: "Dextran in Sugar Made",
      74: "Final Molasses Made Brix",
      75: "Final Molasses Made Pol",
      76: "Final Molasses Made % Glucose",
      77: "Final Molasses Made % Ash",
      78: "Final Molasses Made Clerget",
      79: "Final Molasses Shipped Brix",
      80: "Final Molasses Shipped Pol",
      81: "Final Molasses Shipped % Glucose",
      82: "Final Molasses Shipped % Ash",
      83: "Final Molasses Shipped Clerget",
      84: "Pol % Filter Cake",
      85: "Moisture % Filter Cake",
      86: "Pol % Bagasse",
      87: "Moisture % Bagasse",
      88: "Tons Cane Purchased",
      89: "Net Tons Cane Purchased",
      90: "Standard Tons Cane Purchased",
      91: "Tons Cane Ground",
      92: "Tons Mixed Juice",
      93: "Tons Imbibition Water",
      94: "Tons Filter Cake Made",
      95: "Lbs Sugar Made",
      96: "Gallons Final Molasses Made",
      97: "Lbs Sugar Shipped",
      98: "Gallons Final Molasses Shipped",
      99: "Core Lab Cane, % Pol",
      100: "Core Lab Cane, % Brix",
      101: "Core Lab Cane, % Fiber",
      102: "Rainfall, Inches",
      103: "Maximum Temperature, Deg. F",
      104: "Minimum Temperature, Deg. F",
      105: "Lbs Sugar Brix in Process",
      106: "Lbs Sugar Pol in Process",
      107: "Lbs F. Mol. Brix in Process",
      108: "Lbs F. Mol. Pol in Process",
      109: "Weighting Factor",
      246: "Metered Imbibition Water, Tons",
      251: "Lbs Sugar in Warehouse #1",
      252: "Lbs Sugar in Warehouse #2",
      253: "Lbs Sugar in Warehouse #3",
      254: "Lbs Sugar in Warehouse #4",
    };

    const pages = [];
    if (!includeTodateWorkup) {
      const p1 = [
        centerB,
        "",
        " ".repeat(30) + "DAILY REPORT DATA" + " ".repeat(26) + "Page 1",
        "",
        `      Report Date                                                       ${reportDate}`,
        "",
      ];
      for (const j of [1, 2]) p1.push(formatPrintusing(imgItem, [j, kLabels[j], xVal(j)]));
      p1.push("");
      for (let j = 3; j <= 12; j++) p1.push(formatPrintusing(imgItem, [j, J_s.get(j - 2), xVal(j)]));
      p1.push(formatPrintusing(imgItem, [13, "Total Hours Available", xVal(13)]));
      p1.push("");
      for (let j = 14; j <= 25; j++) p1.push(formatPrintusing(imgItem, [j, H_s.get(j - 13), xVal(j)]));
      p1.push("");
      for (const [r0, r1] of [
        [26, 29],
        [30, 33],
        [34, 35],
        [36, 39],
      ]) {
        for (let j = r0; j <= r1; j++) p1.push(formatPrintusing(imgItem, [j, kLabels[j], xVal(j)]));
        p1.push("");
      }
      pages.push(p1);

      const p2 = [" ".repeat(26) + "DAILY REPORT DATA (Cont'd)" + " ".repeat(21) + "Page 2", ""];
      for (const [r0, r1] of [
        [40, 41],
        [42, 45],
        [46, 47],
        [48, 49],
        [50, 51],
        [52, 53],
        [54, 55],
        [56, 57],
        [58, 59],
        [60, 61],
        [62, 63],
        [64, 65],
        [66, 69],
        [70, 73],
      ]) {
        for (let j = r0; j <= r1; j++) p2.push(formatPrintusing(imgItem, [j, kLabels[j], xVal(j)]));
        p2.push("");
      }
      pages.push(p2);

      const p3 = [" ".repeat(26) + "DAILY REPORT DATA (Cont'd)" + " ".repeat(21) + "Page 3", ""];
      for (const [r0, r1] of [
        [74, 78],
        [79, 83],
        [84, 85],
        [86, 87],
        [88, 88],
        [91, 96],
        [97, 98],
        [99, 101],
        [102, 102],
        [103, 104],
        [105, 106],
        [107, 108],
      ]) {
        for (let j = r0; j <= r1; j++) p3.push(formatPrintusing(imgItem, [j, kLabels[j], xVal(j)]));
        p3.push("");
      }
      p3.push(formatPrintusing(imgItem, [109, kLabels[109], xVal(109)]));
      p3.push(formatPrintusing(imgItem, [246, kLabels[246], xVal(246)]));
      for (let wh = 251; wh <= 254; wh++) p3.push(formatPrintusing(imgItem, [wh, kLabels[wh], xVal(wh)]));
      p3.push("");
      const rLabels = ["1A", "1B", "2A", "2B", "3A", "3B"];
      for (let rIdx = 1; rIdx <= 6; rIdx++) {
        p3.push(`REMARKS - LINE ${rLabels[rIdx - 1]}   ${String(B1_s.get(rIdx)).replace(/\s+$/, "")}`);
      }
      pages.push(p3);
      return pages;
    }

    // Item 4: Print Todate Data File on Disk (MRDATAP2 lines 2920-3860)
    const tdLabels = {
      134: "Crusher Juice Brix and Pol",
      135: "Crusher Juice Glucose",
      136: "Crusher Juice pH",
      137: "Clarified Juice Brix and Pol",
      138: "Clarified Juice Glucose",
      139: "Clarified Juice pH",
      140: "Syrup Brix and Pol",
      141: "Syrup Glucose",
      142: "Syrup pH",
      143: "Last Roll Juice Brix and Pol",
      144: "Filter Juice Brix and Pol",
      145: "Grain Brix and Pol",
      146: "C Magma Brix and Pol",
      147: H_num.get(22) === 1 ? "B Magma Brix and Pol" : "C Cyclone Brix and Pol",
      148: "Crusher Juice Brix",
      149: "Crusher Juice Pol",
      150: "Crusher Juice Glucose",
      151: "Crusher Juice pH",
      152: "Clarified Juice Brix",
      153: "Clarified Juice Pol",
      154: "Clarified Juice Glucose",
      155: "Clarified Juice pH",
      156: "Syrup Brix",
      157: "Syrup Pol",
      158: "Syrup Glucose",
      159: "Syrup pH",
      160: "Last Roll Juice Brix",
      161: "Last Roll Juice Pol",
      162: "Filter Press Juice Brix",
      163: "Filter Press Juice Pol",
      164: "Grain Brix",
      165: "Grain Pol",
      166: "C Magma Brix",
      167: "C Magma Pol",
      168: H_num.get(22) === 1 ? "B Magma Brix" : "C Cyclone Brix",
      169: H_num.get(22) === 1 ? "B Magma Pol" : "C Cyclone Pol",
      170: "A Massecuite Brix",
      171: "A Massecuite Pol",
      172: "Top-Off A Massecuite Brix",
      173: "Top-Off A Massecuite Pol",
      174: "B Massecuite Brix",
      175: "B Massecuite Pol",
      176: "C Massecuite Brix",
      177: "C Massecuite Pol",
      178: "A Molasses Brix",
      179: "A Molasses Pol",
      180: "Top-Off A Molasses Brix",
      181: "Top-Off A Molasses Pol",
      182: "B Molasses Brix",
      183: "B Molasses Pol",
      184: "Total Cu. Ft. of A Mass.",
      185: "Total Cu. Ft. of T-O A Mass.",
      186: "Total Cu. Ft. of B Mass.",
      187: "Total Cu. Ft. of C Mass.",
      188: "Tons Cane Purchased",
      189: "Tons Net Cane Purchased",
      190: "Standard Tons Cane Purchased",
      191: "Tons Cane Ground",
      192: "Tons Brix in Cane Ground",
      193: "Tons Pol in Cane Ground",
      194: "Tons Fiber in Cane Ground",
      195: "Tons Mixed Juice",
      196: "Tons Brix in Mixed Juice",
      197: "Tons Pol in Mixed Juice",
      198: "Tons Glucose in Mixed Juice",
      199: "Tons pH in Mixed Juice",
      200: "Tons Imbibition Water",
      201: "Tons Filter Cake",
      202: "Tons Pol in Filter Cake",
      203: "Tons Moisture in Filter Cake",
      204: "Tons Sugar Made",
      205: "Tons Brix in Sugar Made",
      206: "Tons Pol in Sugar Made",
      207: "Tons Starch in Sugar Made",
      208: "Tons Dextran in Sugar Made",
      209: "Tons Brix in Sugar M&E",
      210: "Tons Pol in Sugar M&E",
      211: "Gallons Final Molasses Made",
      212: "Tons Final Molasses Made",
      213: "Tons Brix in F. Mol. Made",
      214: "Tons Pol in F. Mol. Made",
      215: "Tons Glucose in F. Mol. Made",
      216: "Tons Ash in F. Mol. Made",
      217: "Tons Clerget in FM Made",
      218: "Tons Brix in FM M&E",
      219: "Tons Pol in FM M&E",
      220: "Gallons FM Shipped",
      221: "Tons Final Molasses Shipped",
      222: "Tons Brix in FM Shipped",
      223: "Tons Pol in FM Shipped",
      224: "Tons Glucose in FM Shipped",
      225: "Tons Ash in FM Shipped",
      226: "Tons Clerget in FM Shipped",
      227: "Tons Bagasse",
      228: "Tons Brix in Bagasse",
      229: "Tons Pol in Bagasse",
      230: "Tons Fiber in Bagasse",
      231: "Tons Moisture in Bagasse",
      232: "Tons Normal Juice",
      233: "Tons Brix in Normal Juice",
      234: "Tons Pol in Normal Juice",
      235: "Corer, Lbs TRS in Cane Purch.",
      236: "Corer, Tons Pol in Cane Sam",
      237: "Corer, Tons Brix in Cane Sam",
      238: "Corer, Tons Fiber Cane Sam",
      239: "Rainfall, Inches",
      240: "Todate Max. Temp., deg. F",
      241: "Todate Min. Temp., deg. F",
      242: "Lbs Sugar Shipped",
      243: "Julian Date",
      244: "Todate Avg. Max. T, deg. F",
      245: "Todate Avg. Min. T, deg. F",
      247: "Metered Imb. Water, Tons",
    };

    const tp1 = [
      centerB,
      "",
      " ".repeat(25) + "DAILY REPORT TODATE RESULTS" + " ".repeat(21) + "Page 1",
      "",
      `      Report Date                                                       ${reportDate}`,
      "",
      "Lost Time",
      "---------",
      "",
    ];
    for (let j = 110; j <= 119; j++) tp1.push(formatPrintusing(imgItem4, [j, J_s.get(j - 109), xVal(j)]));
    tp1.push(formatPrintusing(imgItem4, [120, "Total Hours Lost", xVal(120)]));
    tp1.push(formatPrintusing(imgItem4, [121, "Total Hours Available", xVal(121)]));
    tp1.push("");
    tp1.push("Chemicals and Supplies");
    tp1.push("----------------------");
    tp1.push("");
    for (let j = 122; j <= 133; j++) tp1.push(formatPrintusing(imgItem4, [j, H_s.get(j - 121), xVal(j)]));
    tp1.push("");
    tp1.push("Weighting Factors");
    tp1.push("-----------------");
    tp1.push("");
    for (let j = 134; j <= 147; j++) tp1.push(formatPrintusing(imgItem4, [j, tdLabels[j], xVal(j)]));
    pages.push(tp1);

    const tp2 = [
      " ".repeat(21) + "DAILY REPORT TODATE RESULTS (Cont'd)" + " ".repeat(16) + "Page 2",
      "",
      "Weight x Analysis",
      "-----------------",
      "",
    ];
    for (let j = 148; j <= 169; j++) tp2.push(formatPrintusing(imgItem4, [j, tdLabels[j], xVal(j)]));
    pages.push(tp2);

    const tp3 = [
      " ".repeat(21) + "DAILY REPORT TODATE RESULTS (Cont'd)" + " ".repeat(16) + "Page 3",
      "",
      "Cu. Ft. x Analysis",
      "------------------",
      "",
    ];
    for (let j = 170; j <= 187; j++) tp3.push(formatPrintusing(imgItem4, [j, tdLabels[j], xVal(j)]));
    tp3.push("");
    tp3.push("Tons Account");
    tp3.push("------------");
    tp3.push("");
    for (let j = 188; j <= 203; j++) tp3.push(formatPrintusing(imgItem4, [j, tdLabels[j], xVal(j)]));
    pages.push(tp3);

    const tp4 = [" ".repeat(21) + "DAILY REPORT TODATE RESULTS (Cont'd)" + " ".repeat(16) + "Page 4", ""];
    for (let j = 204; j <= 245; j++) {
      if (tdLabels[j]) tp4.push(formatPrintusing(imgItem4, [j, tdLabels[j], xVal(j)]));
    }
    tp4.push(formatPrintusing(imgItem4, [247, tdLabels[247], xVal(247)]));
    pages.push(tp4);

    return pages;
  }

  function calculateAndRenderStock(B_name, stockDate, unitMode, inputs41, H_num) {
    const E_st = new OneBasedArray2D(18, 12, 0.0);
    const names = [
      "Juice",
      "Syrup",
      "A Massecuite",
      "Top-Off A Mass.",
      "B Massecuite",
      "C Massecuite",
      "A Molasses",
      "Top-Off A Mol.",
      "B Molasses",
      "Grain",
      "B Magma",
      "C Magma",
      "Other",
      "TOTAL",
      "Final Molasses Purity",
      "Sugar Purity",
      "Sugar in Stock",
      "Final Molasses in Stock",
    ];
    for (let idxS = 0; idxS < 13; idxS++) {
      E_st.set(idxS + 1, 1, inputs41[idxS * 3]);
      E_st.set(idxS + 1, 2, inputs41[idxS * 3 + 1]);
      E_st.set(idxS + 1, 3, inputs41[idxS * 3 + 2]);
    }
    E_st.set(15, 1, inputs41[39]);
    E_st.set(16, 1, inputs41[40]);

    const isCf = String(unitMode).toUpperCase() === "CF";

    for (let j = 1; j <= 13; j++) {
      if (E_st.get(j, 2) !== 0) {
        E_st.set(j, 4, safeDiv(E_st.get(j, 3) * 100.0, E_st.get(j, 2)));
        const dens = brixDensityPoly4(E_st.get(j, 2));
        E_st.set(j, 5, isCf ? dens : dens / 7.48);
        E_st.set(j, 6, (E_st.get(j, 1) * E_st.get(j, 5)) / 2000.0);
        E_st.set(j, 7, (E_st.get(j, 6) * E_st.get(j, 2)) / 100.0);
        E_st.set(j, 8, (E_st.get(j, 6) * E_st.get(j, 3)) / 100.0);
      }
    }

    for (let col = 1; col <= 8; col++) {
      let s = 0.0;
      for (let r = 1; r <= 13; r++) s += E_st.get(r, col);
      E_st.set(14, col, s);
    }

    E_st.set(14, 2, safeDiv(E_st.get(14, 7) * 100.0, E_st.get(14, 6)));
    E_st.set(14, 3, safeDiv(E_st.get(14, 8) * 100.0, E_st.get(14, 6)));
    E_st.set(14, 4, safeDiv(E_st.get(14, 3) * 100.0, E_st.get(14, 2)));
    E_st.set(14, 5, safeDiv(E_st.get(14, 6) * 2000.0, E_st.get(14, 1)));

    E_st.set(17, 1, safeDiv(E_st.get(14, 7) * (E_st.get(14, 4) - E_st.get(15, 1)), E_st.get(16, 1) - E_st.get(15, 1)));
    E_st.set(17, 2, (E_st.get(17, 1) * E_st.get(16, 1)) / 100.0);
    E_st.set(18, 1, E_st.get(14, 7) - E_st.get(17, 1));
    E_st.set(18, 2, E_st.get(14, 8) - E_st.get(17, 2));
    E_st.set(17, 3, (E_st.get(17, 2) * 2000.0) / 0.96);

    const k1 = (brixDensityPoly4(H_num.get(30)) * H_num.get(30)) / 748.0;
    E_st.set(18, 3, safeDiv(E_st.get(18, 1) * 2000.0, k1));

    const bTrim = String(B_name || "").trim();
    const lines = [];
    lines.push(" ".repeat(Math.max(0, Math.trunc(66 - bTrim.length / 2))) + bTrim);
    lines.push("");
    lines.push(" ".repeat(56) + "STOCK CALCULATIONS");
    lines.push("");
    lines.push(`Date: ${stockDate}`);
    lines.push("--------------");
    lines.push("");

    let imgRow;
    if (isCf) {
      lines.push(
        "Material in Stock   Cu. Ft. Measured   Brix     Pol   Purity   Pounds per Cu. Ft.   Tons Material   Tons Brix    Tons Pol"
      );
      lines.push(
        "-----------------   ----------------  -----   -----   ------   ------------------   -------------   ---------    --------"
      );
      imgRow =
        "%#################   -###,###,###.## -###.## -###.##  -###.##           -#,###.###  -##,###,###.### -#,###,###.### -###,###.###";
    } else {
      lines.push(
        "Material in Stock   Gallons Measured   Brix     Pol   Purity   Pounds per Gallon    Tons Material   Tons Brix    Tons Pol"
      );
      lines.push(
        "-----------------   ----------------  -----   -----   ------   -----------------    -------------   ---------    --------"
      );
      imgRow =
        "%#################    -##,###,###.## -###.## -###.##  -###.##           -#,###.###       -#,###.###    -#,###.###   -#,###.###";
    }

    for (let j = 1; j <= 13; j++) {
      lines.push(
        formatPrintusing(imgRow, [
          names[j - 1],
          E_st.get(j, 1),
          E_st.get(j, 2),
          E_st.get(j, 3),
          E_st.get(j, 4),
          E_st.get(j, 5),
          E_st.get(j, 6),
          E_st.get(j, 7),
          E_st.get(j, 8),
        ])
      );
    }
    const sepSt =
      "-------------             ----------  -----   -----   ------               ------        --------     -------     -------";
    lines.push(sepSt);
    const j14 = 14;
    lines.push(
      formatPrintusing(imgRow, [
        names[j14 - 1],
        E_st.get(j14, 1),
        E_st.get(j14, 2),
        E_st.get(j14, 3),
        E_st.get(j14, 4),
        E_st.get(j14, 5),
        E_st.get(j14, 6),
        E_st.get(j14, 7),
        E_st.get(j14, 8),
      ])
    );
    lines.push(sepSt);
    lines.push("");
    lines.push("");
    lines.push("Assumptions");
    lines.push("-----------");
    lines.push("");
    const imgAssump = "%################################      -###.##";
    for (const j of [15, 16]) {
      lines.push(formatPrintusing(imgAssump, [names[j - 1], E_st.get(j, 1)]));
    }
    lines.push("");
    lines.push("");
    lines.push("                                  SUGAR AND MOLASSES IN PROCESS");
    lines.push("                                  -----------------------------");
    lines.push("");
    lines.push("                                    Lbs Brix            Lbs Pol");
    lines.push("                                    --------            -------");

    const img1290 =
      "%########################    -###,###,###,###   -###,###,###,###        (Lbs. 96 Sugar in Stock = -##,###,###.##)";
    const img1320 =
      "%########################    -###,###,###,###   -###,###,###,###        (Final Molasses in Stock - Gals. @ ##.## Brix =-#,###,###.##)";
    const img1350 = "%TOTAL                       -###,###,###,###   -###,###,###,###";

    lines.push(formatPrintusing(img1290, [names[16], E_st.get(17, 1) * 2000.0, E_st.get(17, 2) * 2000.0, E_st.get(17, 3)]));
    lines.push("");
    lines.push(
      formatPrintusing(img1320, [
        names[17],
        E_st.get(18, 1) * 2000.0,
        E_st.get(18, 2) * 2000.0,
        H_num.get(30),
        E_st.get(18, 3),
      ])
    );
    lines.push("                                   ---------           --------");
    lines.push(formatPrintusing(img1350, [E_st.get(14, 7) * 2000.0, E_st.get(14, 8) * 2000.0]));
    lines.push("                                   ---------           --------");

    const summary = {
      sugar_lbs_brix: E_st.get(17, 1) * 2000.0,
      sugar_lbs_pol: E_st.get(17, 2) * 2000.0,
      sugar_lbs_96: E_st.get(17, 3),
      molasses_lbs_brix: E_st.get(18, 1) * 2000.0,
      molasses_lbs_pol: E_st.get(18, 2) * 2000.0,
      molasses_gals_at_brix: E_st.get(18, 3),
    };
    return [lines, summary];
  }

  // ---------------------------------------------------------------------------
  // Historical Presets & Oct 2015 St. Mary Sugar Co-op Dataset
  // ---------------------------------------------------------------------------
  function getStMaryOct2015Params() {
    const jList = [
      "Cleco",
      "Electrical",
      "No Cane on Yard",
      "Misc. Uncontrol",
      "Total Machinery",
      "Chokes",
      "Instrumentation",
      "Full House",
      "Low Steam",
      "Misc. Control",
    ];
    const hStrList = [
      "Gas, M. Cu. Ft.",
      "Mill Biocide Lbs.",
      "Floculent Lbs.",
      "Pan Surfactant Lbs.",
      "Caustic Soda, Lbs",
      "Muriatic Acid Lbs,",
      "Stabrex",
      "Lime (Hydrate Lbs.)",
      "Phosphoric Acid Lbs.",
      "Amylase, Lbs.",
      "Dextranase, Lbs.",
      "Bleach, Lbs",
      "1262",
      "79.50",
      "",
      "",
      "",
      "",
      "",
      "",
    ];
    const iStrList = [
      "W",
      "Y",
      "N",
      "Y",
      "N",
      "Y",
      "Y",
      "N",
      "Y",
      "Y",
      "N",
      "Y",
      "Y",
      "Y",
      "N",
      "N",
      "N",
      "Y",
      "N",
      "Y",
      "N",
      "Y",
      "N",
      "Y",
      "",
      "",
      "",
      "",
      "",
      "",
    ];
    const hNum = new Array(37).fill(0.0);
    hNum[0] = 0.0;
    for (let idx = 2; idx <= 23; idx++) {
      hNum[idx - 1] = iStrList[idx - 1] === "N" ? 0.0 : 1.0;
    }
    hNum[24] = 15279.0; // H(25): Julian date for 10/06/15
    hNum[25] = 6.0; // H(26): Last day number
    hNum[26] = 1.0; // H(27): Metered imbibition flag
    hNum[28] = 1262.0; // H(29): Total Roll Surface of All Mill Rolls
    hNum[29] = 79.5; // H(30): Brix Desired for Molasses M&E
    hNum[35] = 0.0; // H(36): Printer Selection Code
    hNum[36] = 3.0; // H(37): Disk Selection Code (3 = D12)
    return {
      "B$": "ST. MARY SUGAR COOPERATIVE, INC.",
      "A1$": "10/06/15",
      "J$": jList,
      "H$": hStrList,
      "I$": iStrList,
      H: hNum,
    };
  }

  function getRacelandPlatterParams() {
    const jList = [
      "Scheduled Maint.",
      "Instrumentation",
      "No Cane on Yard",
      "Total Machinery",
      "Chokes",
      "Full House",
      "Low Steam",
      "Plant Electrical",
      "Miscellaneous",
      "Rain",
    ];
    const hStrList = [
      "Gas, M. Cu. Ft.",
      "Lime, Lbs. - Process",
      "Lime, Lbs. Cane Wash",
      "HCl Acid, Gals.",
      "Caustic Soda, Gals.",
      "Flocculant, Lbs.",
      "Pan Surfactant, Gal.",
      "Bleach, Gals.",
      "Amylase, Gals.",
      "Dextranase, Gals.",
      "Antifoam, Gals.",
      "Biocide, Lbs.",
      "1644",
      "79.50",
      "",
      "",
      "",
      "",
      "",
      "",
    ];
    const iStrList = [
      "W",
      "N",
      "Y",
      "N",
      "Y",
      "N",
      "Y",
      "N",
      "Y",
      "Y",
      "Y",
      "N",
      "N",
      "N",
      "N",
      "N",
      "N",
      "Y",
      "N",
      "Y",
      "N",
      "Y",
      "N",
      "Y",
      "",
      "",
      "",
      "",
      "",
      "",
    ];
    const hNum = new Array(37).fill(0.0);
    hNum[0] = 0.0;
    for (let idx = 2; idx <= 23; idx++) {
      hNum[idx - 1] = iStrList[idx - 1] === "N" ? 0.0 : 1.0;
    }
    hNum[24] = 22265.0;
    hNum[26] = 1.0;
    hNum[28] = 1644.0;
    hNum[29] = 79.5;
    hNum[35] = 0.0;
    hNum[36] = 3.0;
    return {
      "B$": "RACELAND RAW SUGAR, L.L.C.",
      "A1$": "09/22/22",
      "J$": jList,
      "H$": hStrList,
      "I$": iStrList,
      H: hNum,
    };
  }

  function getStMaryOct2015DailyInputs() {
    return [
      {
        day: 1,
        date: "10/06/15",
        julian: 15279,
        inputs: {
          2: 1806422.36,
          13: 17.5,
          14: 666.0,
          16: 110.0,
          21: 10838.0,
          26: 19.5,
          27: 16.9,
          30: 15.1,
          31: 12.92,
          34: 2.6,
          35: 1.98,
          36: 14.7,
          37: 12.98,
          39: 6.05,
          40: 19.28,
          41: 16.67,
          42: 14.7,
          66: 9987.0,
          68: 1604.0,
          70: 0.0,
          71: 99.0,
          84: 2.3,
          86: 2.23,
          87: 50.0,
          88: 8336.79,
          91: 6436.79,
          92: 6472.585,
          93: 1935.48,
          94: 300.0,
          95: 275596.0,
          99: 13.65,
          100: 16.54,
          101: 18.06,
          102: 0.0,
          103: 86.0,
          104: 70.0,
          105: 827113.0,
          106: 818842.0,
          107: 237564.0,
          108: 78396.0,
          246: 0.0,
        },
        remarks: [
          "SUGAR DETECTED IN INJECTION WATER AT 8.63 POL",
          "SUGAR IN STOCK BASED ON ASSUMPTIONS, MISSING LAB DATA",
          "FILTER CAKE AMOUNT ASSUMED BASED ON PREV REPORTS",
          "SUGAR MADE PURITY ASSUMED AT 99, NO LAB DATA",
          "",
          "",
        ],
      },
      {
        day: 2,
        date: "10/07/15",
        julian: 15280,
        inputs: {
          2: 2112997.66,
          13: 24.0,
          15: 24.0,
          16: 551.0,
          21: 12449.0,
          25: 17.0,
          26: 19.3,
          27: 16.53,
          28: 0.83,
          30: 15.83,
          31: 13.5,
          32: 0.57,
          34: 2.75,
          35: 2.04,
          36: 15.4,
          37: 13.23,
          38: 0.39,
          39: 6.04,
          40: 19.28,
          41: 16.67,
          42: 44.0,
          43: 38.3,
          45: 5.84,
          46: 91.25,
          47: 79.08,
          50: 90.6,
          51: 69.75,
          54: 80.8,
          55: 60.86,
          58: 79.6,
          59: 49.32,
          66: 33823.0,
          68: 5213.0,
          70: 0.67,
          71: 98.1,
          72: 0.8,
          84: 5.19,
          86: 2.5,
          87: 47.47,
          88: 9583.31,
          91: 10976.7,
          92: 12976.53,
          93: 5180.25,
          94: 400.0,
          95: 1653526.0,
          99: 16.68,
          100: 13.79,
          101: 18.52,
          102: 0.0,
          103: 94.0,
          104: 66.0,
          105: 1252930.0,
          106: 1240401.0,
          107: 522519.0,
          108: 172436.0,
          246: 1909.95,
        },
        remarks: ["NO LAB DATA FOR C MASSECUITE", "", "", "", "", ""],
      },
      {
        day: 3,
        date: "10/08/15",
        julian: 15281,
        inputs: {
          2: 2511930.5,
          13: 24.0,
          15: 24.0,
          16: 881.0,
          21: 14671.0,
          25: 17.0,
          26: 20.0,
          27: 17.37,
          28: 0.82,
          30: 16.6,
          31: 14.31,
          32: 0.56,
          34: 3.88,
          35: 3.07,
          36: 16.13,
          37: 14.07,
          38: 0.61,
          39: 6.87,
          42: 60.58,
          43: 52.57,
          45: 6.59,
          46: 92.03,
          47: 80.66,
          50: 92.2,
          51: 69.06,
          52: 92.6,
          53: 53.91,
          54: 80.05,
          55: 60.55,
          58: 82.45,
          59: 46.72,
          60: 92.2,
          61: 58.08,
          62: 93.4,
          63: 81.79,
          64: 93.33,
          65: 85.07,
          66: 51604.0,
          68: 17780.0,
          69: 8556.0,
          70: 0.47,
          71: 98.54,
          72: 1.05,
          74: 76.99,
          75: 34.07,
          84: 5.1,
          86: 2.51,
          87: 49.89,
          88: 11285.44,
          91: 11530.44,
          92: 10569.27,
          93: 2547.27,
          94: 400.0,
          95: 2324038.0,
          96: 12431.0,
          99: 13.88,
          100: 16.74,
          101: 18.57,
          102: 0.0,
          103: 94.0,
          104: 52.0,
          105: 1303447.0,
          106: 1289239.0,
          107: 834292.0,
          108: 275333.0,
          246: 2179.25,
        },
        remarks: ["RAW COLOR 2264", "", "", "", "", ""],
      },
      {
        day: 4,
        date: "10/09/15",
        julian: 15282,
        inputs: {
          2: 2925200.47,
          13: 24.0,
          15: 864.0,
          16: 716.0,
          21: 16833.0,
          25: 17.0,
          26: 19.48,
          27: 16.71,
          28: 0.84,
          30: 15.78,
          31: 13.71,
          32: 0.56,
          34: 3.48,
          35: 2.67,
          36: 15.7,
          37: 13.76,
          38: 0.6,
          39: 6.49,
          42: 62.3,
          43: 53.69,
          45: 6.09,
          46: 91.87,
          47: 81.06,
          50: 93.2,
          51: 71.25,
          52: 92.6,
          53: 53.91,
          54: 79.72,
          55: 61.38,
          58: 80.64,
          59: 48.62,
          60: 90.67,
          61: 63.24,
          62: 93.9,
          63: 81.66,
          64: 93.9,
          65: 86.57,
          66: 51337.0,
          68: 15508.0,
          69: 8556.0,
          70: 0.15,
          71: 99.31,
          72: 1.05,
          74: 72.74,
          75: 32.39,
          84: 4.56,
          86: 2.57,
          87: 49.95,
          88: 12948.67,
          91: 10983.73,
          92: 10683.36,
          93: 3035.53,
          94: 400.0,
          95: 2395498.0,
          96: 124310.0,
          99: 14.11,
          100: 16.89,
          101: 18.44,
          102: 0.0,
          103: 94.0,
          104: 68.0,
          105: 1835856.0,
          106: 1825953.0,
          107: 1179482.0,
          108: 389408.0,
          246: 2109.97,
        },
        remarks: ["", "", "", "", "", ""],
      },
      {
        day: 5,
        date: "10/10/15",
        julian: 15283,
        inputs: {
          2: 2479568.42,
          13: 24.0,
          15: 240.0,
          16: 660.0,
          21: 14043.0,
          25: 17.0,
          26: 19.63,
          27: 16.97,
          28: 0.82,
          30: 15.99,
          31: 14.04,
          32: 0.0,
          34: 3.5,
          35: 2.74,
          36: 15.53,
          37: 13.81,
          38: 0.53,
          39: 7.01,
          40: 19.28,
          41: 16.67,
          42: 60.7,
          43: 53.15,
          45: 6.78,
          46: 92.51,
          47: 82.53,
          50: 93.53,
          51: 71.97,
          52: 95.78,
          53: 56.5,
          54: 80.9,
          55: 62.92,
          58: 81.25,
          59: 46.92,
          60: 91.9,
          61: 65.68,
          62: 94.47,
          63: 83.49,
          64: 94.2,
          65: 86.01,
          66: 50935.0,
          68: 23395.0,
          69: 10227.0,
          70: 0.35,
          71: 98.81,
          72: 1.3,
          74: 69.0,
          75: 31.47,
          76: 12.87,
          77: 13.86,
          84: 7.04,
          86: 2.66,
          87: 48.79,
          88: 10802.77,
          91: 11702.77,
          92: 11224.17,
          93: 2928.98,
          94: 350.0,
          95: 2614862.0,
          96: 80801.7,
          99: 14.24,
          100: 17.01,
          101: 18.1,
          102: 0.0,
          103: 82.0,
          104: 58.0,
          105: 1734092.0,
          106: 1719252.0,
          107: 1175831.0,
          108: 388202.0,
          246: 2139.27,
        },
        remarks: [
          "RAW COLOR 2251",
          "MOIST .35",
          "SAFETY FACTOR .22",
          "SPECIAL COLOR 3875",
          "SUGAR DETECTED IN INJECTION WATER 8 POL",
          "",
        ],
      },
      {
        day: 6,
        date: "10/11/15",
        julian: 15284,
        inputs: {
          2: 2849001.62,
          13: 24.0,
          15: 240.0,
          16: 660.0,
          21: 16213.0,
          25: 17.0,
          26: 19.43,
          27: 16.93,
          28: 0.64,
          30: 15.3,
          31: 13.26,
          32: 0.44,
          34: 4.38,
          35: 3.45,
          36: 16.2,
          37: 14.22,
          38: 0.43,
          39: 6.87,
          40: 19.28,
          41: 16.67,
          42: 59.83,
          43: 53.24,
          45: 6.55,
          46: 92.73,
          47: 83.18,
          50: 94.52,
          51: 73.58,
          52: 94.77,
          53: 59.37,
          54: 78.0,
          55: 59.79,
          58: 76.63,
          59: 45.41,
          60: 91.2,
          61: 62.12,
          62: 94.27,
          63: 83.31,
          64: 93.77,
          65: 96.56,
          66: 51069.0,
          68: 17780.0,
          69: 15641.0,
          70: 0.26,
          71: 99.05,
          72: 2.65,
          74: 77.21,
          75: 32.68,
          84: 4.38,
          86: 2.51,
          87: 49.0,
          88: 12471.96,
          91: 11271.96,
          92: 11419.09,
          93: 3451.78,
          94: 400.0,
          95: 2513672.0,
          96: 74586.18,
          99: 14.17,
          100: 16.91,
          101: 18.22,
          102: 0.0,
          103: 86.0,
          104: 56.0,
          105: 1914562.0,
          106: 1898016.0,
          107: 1062831.0,
          108: 350926.0,
          246: 2074.04,
        },
        remarks: [
          "RAW COLOR 2175   ",
          "RAW COLOR BIG PILE 2116",
          "RAW COLOR OUT OF PROD 2341",
          "",
          "",
          "",
        ],
      },
    ];
  }

  // ---------------------------------------------------------------------------
  // Virtual Disk & Interactive Session State Machine (MRSTART + All 17 Options)
  // ---------------------------------------------------------------------------
  const DISK_CODE_MAP = {
    0: "D12",
    1: "310",
    2: "D11",
    3: "D12",
    4: "D13",
    5: "D14",
    6: "D20",
    7: "D21",
    8: "D22",
    9: "D23",
    10: "D24",
    11: "D25",
  };

  const VFS_STORAGE_KEY = "birkett_mfr_vfs_v1";

  function formatNumberGeneral(val) {
    const n = Number(val);
    if (!Number.isFinite(n)) return "0";
    if (Math.abs(n) < 1e-12) return "0";
    // Emulate Python's {:g} formatting cleanly
    return String(Number(n.toPrecision(12)));
  }

  class MFRSession {
    constructor(options = {}) {
      this.storageKey = options.storageKey || VFS_STORAGE_KEY;
      this.useLocalStorage =
        options.useLocalStorage !== undefined
          ? Boolean(options.useLocalStorage)
          : typeof window !== "undefined" && typeof window.localStorage !== "undefined";

      this.vfs = {
        MRPARAMS: null,
        disks: {},
      };

      // COMMON block variables
      this.B_str = "ST. MARY SUGAR COOPERATIVE, INC.";
      this.B1_str = new OneBasedArray1D(6, " ");
      this.A1_str = "10/06/15";
      this.A2_str = new OneBasedArray1D(3, " ");
      this.A = new OneBasedArray2D(258, 3, 0.0);
      this.J_str = new OneBasedArray1D(10, " ");
      this.H_str = new OneBasedArray1D(20, " ");
      this.I_str = new OneBasedArray1D(30, " ");
      this.H_num = new OneBasedArray1D(37, 0.0);
      this.B = new OneBasedArray2D(28, 4, 0.0);
      this.C = new OneBasedArray2D(8, 7, 0.0);
      this.D = new OneBasedArray2D(10, 6, 0.0);
      this.E = new OneBasedArray2D(18, 12, 0.0);
      this.F = new OneBasedArray2D(8, 10, 0.0);
      this.G = new OneBasedArray2D(12, 8, 0.0);

      // Terminal & Printer State
      this.crt_lines = [];
      this.top_bar_row1 = "";
      this.top_bar_row3 = "";
      this.current_prompt = "";
      this.beep_flag = false;
      this.strict_wang_mode = false;

      this.printer_jobs = [];
      this.state = "MENU";
      this.ctx = {};

      // Load VFS from localStorage if available
      const loadedFromStorage = this._loadVfsFromStorage();
      if (!loadedFromStorage || !this.vfs.MRPARAMS) {
        this.seedStMaryOct2015();
      } else {
        this.loadMrparams();
        this.showMainMenu();
      }

      // Pre-print Daily Report #6 (10/11/15) on initial launch if printer tray is empty
      if (options.autoPrintInitial !== false && this.printer_jobs.length === 0 && this.dayFileExists(6)) {
        this.handleInput("5");
        this.handleInput("Y");
        this.handleInput("10/11/15");
        this.handleInput("Y");
        this.handleInput("1");
        this.showMainMenu();
        this.top_bar_row1 = "READY - OCT 2015 ST. MARY SUGAR CO-OP DATA LOADED ON DISK D12";
      }
    }

    // -------------------------------------------------------------------------
    // Browser Virtual Disk Persistence (localStorage + JSON Export/Import)
    // -------------------------------------------------------------------------
    _loadVfsFromStorage() {
      if (!this.useLocalStorage) return false;
      try {
        const raw = window.localStorage.getItem(this.storageKey);
        if (!raw) return false;
        const parsed = JSON.parse(raw);
        if (parsed && typeof parsed === "object" && parsed.MRPARAMS && parsed.disks) {
          this.vfs = parsed;
          return true;
        }
      } catch (e) {
        // Ignore storage read errors
      }
      return false;
    }

    _saveVfsToStorage() {
      if (!this.useLocalStorage) return;
      try {
        window.localStorage.setItem(this.storageKey, JSON.stringify(this.vfs));
      } catch (e) {
        // Ignore storage quota/security errors
      }
    }

    exportDiskBundle() {
      return JSON.parse(
        JSON.stringify({
          program: "Harold Birkett Manufacturing Report Program v2.1",
          exported_at: new Date().toISOString(),
          MRPARAMS: this.vfs.MRPARAMS,
          disks: this.vfs.disks,
        })
      );
    }

    importDiskBundle(bundleObj) {
      if (!bundleObj || typeof bundleObj !== "object" || !bundleObj.MRPARAMS || !bundleObj.disks) {
        throw new Error("Invalid Virtual Disk JSON bundle.");
      }
      this.vfs = {
        MRPARAMS: JSON.parse(JSON.stringify(bundleObj.MRPARAMS)),
        disks: JSON.parse(JSON.stringify(bundleObj.disks)),
      };
      this._saveVfsToStorage();
      this.loadMrparams();
      this.showMainMenu();
      this.top_bar_row1 = `IMPORTED VIRTUAL DISK BUNDLE (${this.B_str.trim()})`;
      return this.getStatusPayload();
    }

    getDiskName(code = null) {
      const c = code === null ? Math.round(this.H_num.get(37)) : Math.round(code);
      return DISK_CODE_MAP[c] || "D12";
    }

    _getDiskMap(code = null) {
      const dName = this.getDiskName(code);
      if (!this.vfs.disks[dName]) {
        this.vfs.disks[dName] = {};
      }
      return this.vfs.disks[dName];
    }

    loadMrparams() {
      const obj = this.vfs.MRPARAMS;
      if (!obj) return;
      this.B_str = obj["B$"] || "ST. MARY SUGAR COOPERATIVE, INC.";
      this.A1_str = obj["A1$"] || "10/06/15";
      this.J_str.fromList(obj["J$"] || []);
      this.H_str.fromList(obj["H$"] || []);
      this.I_str.fromList(obj["I$"] || []);
      this.H_num.fromList(obj["H"] || []);
    }

    saveMrparams() {
      this.vfs.MRPARAMS = {
        "B$": this.B_str,
        "A1$": this.A1_str,
        "J$": this.J_str.toList(),
        "H$": this.H_str.toList(),
        "I$": this.I_str.toList(),
        H: this.H_num.toList(),
      };
      this._saveVfsToStorage();
    }

    _dayFileKey(dayNum) {
      return String(Math.round(dayNum)).padStart(3, "0");
    }

    dayFileExists(dayNum, diskCode = null) {
      const disk = this._getDiskMap(diskCode);
      const key = this._dayFileKey(dayNum);
      return Object.prototype.hasOwnProperty.call(disk, key);
    }

    saveDayFile(dayNum, a1Date, xArr, b1Remarks, diskCode = null) {
      const disk = this._getDiskMap(diskCode);
      const key = this._dayFileKey(dayNum);
      disk[key] = {
        day: Math.round(dayNum),
        "A1$": String(a1Date),
        X: xArr.slice(0, 258).map((v) => Number(v) || 0.0),
        "B1$": b1Remarks.slice(0, 6).map((s) => String(s)),
      };
      this._saveVfsToStorage();
    }

    loadDayFile(dayNum, diskCode = null) {
      const disk = this._getDiskMap(diskCode);
      const key = this._dayFileKey(dayNum);
      const obj = disk[key] || {};
      const a1 = obj["A1$"] || "  /  /  ";
      let xList = Array.isArray(obj.X) ? obj.X.slice() : new Array(258).fill(0.0);
      while (xList.length < 258) xList.push(0.0);
      let b1List = Array.isArray(obj["B1$"]) ? obj["B1$"].slice() : new Array(6).fill(" ");
      while (b1List.length < 6) b1List.push(" ");
      return [a1, xList, b1List];
    }

    listDiskFiles(diskCode = null) {
      const disk = this._getDiskMap(diskCode);
      const keys = Object.keys(disk).sort();
      return keys.map((k) => {
        const meta = disk[k] || {};
        const xArr = Array.isArray(meta.X) ? meta.X : [];
        return {
          name: k,
          date: meta["A1$"] || "",
          crop_day: xArr.length > 0 ? Math.round(xArr[0]) : 0,
        };
      });
    }

    getDiskFileContent(fname) {
      const clean = String(fname || "").trim();
      if (clean.toUpperCase() === "MRPARAMS") {
        return { name: "MRPARAMS", content: this.vfs.MRPARAMS };
      }
      const disk = this._getDiskMap();
      if (Object.prototype.hasOwnProperty.call(disk, clean)) {
        return { name: clean, disk: this.getDiskName(), content: disk[clean] };
      }
      return { error: `File ${clean} not found on ${this.getDiskName()}` };
    }

    // -------------------------------------------------------------------------
    // Seeding Demo Data (St. Mary Oct 2015 / Raceland PLATTER1.BS2)
    // -------------------------------------------------------------------------
    seedStMaryOct2015() {
      this.vfs.MRPARAMS = getStMaryOct2015Params();
      this.loadMrparams();

      // Clear D12
      this.vfs.disks["D12"] = {};

      // Create file "000" (day before crop started: 10/05/15, Julian 15278)
      const x0 = new Array(258).fill(0.0);
      x0[0] = 0.0;
      x0[242] = 15278.0; // X(243)
      this.saveDayFile(0, "10/05/15", x0, new Array(6).fill(" "), 3);

      // Run MRDATAWU for Days 1..6 sequentially
      const daysData = getStMaryOct2015DailyInputs();
      for (const dInfo of daysData) {
        const dayNum = dInfo.day;
        const dtStr = dInfo.date;
        const jul = dInfo.julian;
        const [, prevX] = this.loadDayFile(dayNum - 1, 3);

        this.A.clear();
        for (let j = 1; j <= 258; j++) {
          this.A.set(j, 3, prevX[j - 1]);
        }
        this.A.set(1, 1, Number(dayNum));
        this.A.set(243, 1, Number(jul));
        for (const [kIdx, val] of Object.entries(dInfo.inputs)) {
          this.A.set(Number(kIdx), 1, Number(val));
        }

        runWorkupOnA(this.A, this.H_num, false);
        const xNew = [];
        for (let j = 1; j <= 258; j++) {
          xNew.push(this.A.get(j, 2));
        }
        this.saveDayFile(dayNum, dtStr, xNew, dInfo.remarks, 3);
      }

      // Copy D12 to D13 backup
      this.vfs.disks["D13"] = JSON.parse(JSON.stringify(this.vfs.disks["D12"]));
      this._saveVfsToStorage();
      this.showMainMenu();
    }

    seedRacelandPlatter() {
      this.vfs.MRPARAMS = getRacelandPlatterParams();
      this.loadMrparams();
      this.vfs.disks["D12"] = {};
      this._saveVfsToStorage();
      this.showMainMenu();
    }

    // -------------------------------------------------------------------------
    // CRT Screen & Menu Helpers (MRSTART lines 0060-0530)
    // -------------------------------------------------------------------------
    clearCrt() {
      this.crt_lines = [];
      this.top_bar_row1 = "";
      this.top_bar_row3 = "";
    }

    printCrt(text = "") {
      for (const line of String(text).split("\n")) {
        this.crt_lines.push(line);
      }
    }

    addPrinterJob(title, pages) {
      const jobId = this.printer_jobs.length + 1;
      const now = new Date();
      const ts = [now.getHours(), now.getMinutes(), now.getSeconds()]
        .map((n) => String(n).padStart(2, "0"))
        .join(":");
      this.printer_jobs.unshift({
        id: jobId,
        timestamp: ts,
        title,
        pages,
      });
    }

    showMainMenu() {
      this.A.clear();
      for (let j = 1; j <= 35; j++) {
        this.H_num.set(j, 0.0);
      }
      this.loadMrparams();
      this.clearCrt();
      const bTrim = this.B_str.trim();
      this.printCrt(" ".repeat(26) + "MANUFACTURING REPORT MENU");
      this.printCrt(" ".repeat(33) + "VERSION 2.1");
      this.printCrt(" ".repeat(Math.max(0, Math.trunc(40 - bTrim.length / 2))) + bTrim);
      this.printCrt("");
      this.printCrt(" 1.   Input Data for Daily Report");
      this.printCrt(" 2.   Correct Data for Daily Report");
      this.printCrt(" 3.   Print Data for Daily Report");
      this.printCrt(" 4.   Print Todate Data File on Disk");
      this.printCrt(" 5.   Print Daily Report");
      this.printCrt(" 6.   Print Weekly Report");
      this.printCrt(" 7.   Perform Stock in Process Calculations");
      this.printCrt(" 8.   Help Routine for Daily Report");
      this.printCrt(" 9.   End of Crop Correction Routine");
      this.printCrt("10.   Customize Program");
      this.printCrt("11.   Print Customized File");
      this.printCrt("12.   Print up Data Forms");
      this.printCrt("13.   Print Weekly Comparative Report Form");
      this.printCrt("14.   Back-up Data to Hard Disk (D13)");
      this.printCrt("16.   END");
      this.printCrt("17.   Delete Data Files at Start of Crop");
      this.printCrt("");
      this.current_prompt = "WHICH ITEM NUMBER DO YOU WANT";
      this.state = "MENU";
      this.ctx = {};
    }

    _askDate(promptText, nextState) {
      this.top_bar_row1 = promptText;
      this.top_bar_row3 = "";
      this.current_prompt = promptText;
      this.ctx.date_prompt = promptText;
      this.ctx.date_next_state = nextState;
      this.state = "DATE_ENTRY";
    }

    _triggerReenter(msg = "RE-ENTER") {
      this.beep_flag = true;
      this.top_bar_row3 = msg;
      this.printCrt(`*** ${msg} ***`);
    }

    // -------------------------------------------------------------------------
    // High-Level Action & Input Dispatchers
    // -------------------------------------------------------------------------
    handleAction(data = {}) {
      const act = String(data.action || "");
      this.beep_flag = false;
      if (act === "reset_menu" || act === "reset_to_menu") {
        this.showMainMenu();
        this.top_bar_row1 = "LOADED MODULE: MRSTART (MAIN MENU)";
      } else if (act === "toggle_strict" || act === "toggle_strict_mode") {
        const strictVal =
          data.strict !== undefined
            ? data.strict
            : data.strict_mode !== undefined
            ? data.strict_mode
            : !this.strict_wang_mode;
        this.strict_wang_mode = Boolean(strictVal);
        const modeLbl = this.strict_wang_mode
          ? "STRICT WANG BASIC-2 MODE"
          : "ENTER-TO-KEEP CONVENIENCE MODE";
        this.top_bar_row1 = `INPUT MODE SET TO: ${modeLbl}`;
      } else if (act === "seed_st_mary") {
        this.seedStMaryOct2015();
        this.top_bar_row1 = "RESTORED OCT 2015 ST. MARY SUGAR CO-OP DEMO DATA (DAYS 1-6)";
      } else if (act === "seed_raceland") {
        this.seedRacelandPlatter();
        this.top_bar_row1 = "LOADED RACELAND RAW SUGAR (PLATTER1.BS2) PARAMETERS";
      } else if (act === "clear_printer") {
        this.printer_jobs = [];
        this.top_bar_row1 = "CLEARED LINE PRINTER (215) OUTPUT TRAY";
      } else if (act === "quick_print_demo_pack" || act === "run_all_sample_reports") {
        if (!this.dayFileExists(6)) {
          this.seedStMaryOct2015();
        }
        for (const dtS of ["10/06/15", "10/07/15", "10/08/15", "10/09/15", "10/10/15", "10/11/15"]) {
          this.showMainMenu();
          this.handleInput("5");
          this.handleInput("Y");
          this.handleInput(dtS);
          this.handleInput("Y");
          this.handleInput("1");
        }
        this.showMainMenu();
        this.handleInput("6");
        this.handleInput("Y");
        this.handleInput("10/10/15");
        this.handleInput("Y");
        this.handleInput("10/06/15");
        this.handleInput("Y");
        this.handleInput("1");
        this.handleInput("1");
        this.handleInput("Y");
        this.handleInput("RAW COLOR 2348");
        this.handleInput("ASH  0.31");
        this.handleInput("SAFETY FACTOR .32        MOIST .41");
        this.handleInput("");
        this.handleInput("DEX 0.99%");
        this.handleInput("");
        this.showMainMenu();
        this.top_bar_row1 = "BATCH PRINTED ALL 6 DAILY REPORTS + WEEKLY REPORT #1 TO LINE PRINTER";
      }
      return this.getStatusPayload();
    }

    handleInput(rawInput = "") {
      const rawStr = String(rawInput);
      this.beep_flag = false;
      this.top_bar_row3 = "";
      const valStr = rawStr.trim();
      this.printCrt(`${this.current_prompt}? ${rawStr}`);

      switch (this.state) {
        case "MENU":
          this._handleMenuChoice(valStr);
          break;
        case "DATE_ENTRY":
          this._handleDateEntry(valStr);
          break;
        case "DATE_CONFIRM":
          this._handleDateConfirm(valStr);
          break;
        case "WAIT_RETURN_MENU":
          this.showMainMenu();
          break;
        case "ITEM1_ALREADY_ENTERED":
          this._handleItem1AlreadyEntered(valStr);
          break;
        case "ITEM1_NO_DATA_START_CROP":
          this._handleItem1StartCropYn(valStr);
          break;
        case "MRDATA_INPUT":
          this._handleMrdataStep(rawStr);
          break;
        case "MRDATACO_INPUT":
          this._handleMrdatacoStep(rawStr);
          break;
        case "REPORT_CHECK_PAGE_YN":
          this._handleReportCheckYn(valStr);
          break;
        case "DAILY_REPORT_COPIES":
          this._handleDailyReportCopies(valStr);
          break;
        case "WEEKLY_REPORT_NUM":
          this._handleWeeklyReportNum(valStr);
          break;
        case "WEEKLY_REPORT_COPIES":
          this._handleWeeklyReportCopies(valStr);
          break;
        case "WEEKLY_REPORT_OK":
          this._handleWeeklyReportOk(valStr);
          break;
        case "WEEKLY_REMARKS":
          this._handleWeeklyRemarks(rawStr);
          break;
        case "MRSTOCK_UNIT":
          this._handleMrstockUnit(valStr);
          break;
        case "MRSTOCK_INPUT":
          this._handleMrstockStep(valStr);
          break;
        case "MRSTOCK_OK":
          this._handleMrstockOk(valStr);
          break;
        case "MRHELP_MODE":
          this._handleMrhelpMode(valStr);
          break;
        case "MRHELPC_INPUT":
          this._handleMrhelpcStep(valStr);
          break;
        case "MRHELPS_INPUT":
          this._handleMrhelpsStep(valStr);
          break;
        case "MRHELP_OK":
          this._handleMrhelpOk(valStr);
          break;
        case "MRENCROP_INPUT":
          this._handleMrencropStep(rawStr);
          break;
        case "MRCUSTOM_INPUT":
          this._handleMrcustomStep(rawStr);
          break;
        case "MRBLANFM_CHOICE":
          this._handleMrblanfmChoice(valStr);
          break;
        case "ITEM17_CONFIRM":
          this._handleItem17Confirm(valStr);
          break;
        case "HALTED":
          this.showMainMenu();
          break;
        default:
          this.showMainMenu();
          break;
      }

      return this.getStatusPayload();
    }

    getStatusPayload() {
      return {
        state: this.state,
        crt_lines: this.crt_lines.slice(-200),
        top_bar_row1: this.top_bar_row1,
        top_bar_row3: this.top_bar_row3,
        current_prompt: this.current_prompt,
        beep: this.beep_flag,
        strict_wang_mode: this.strict_wang_mode,
        factory_name: this.B_str.trim(),
        crop_start_date: this.A1_str.trim(),
        active_disk: this.getDiskName(),
        disk_files: this.listDiskFiles(),
        printer_jobs: this.printer_jobs,
      };
    }

    // -------------------------------------------------------------------------
    // Menu Choice & Date Subroutines
    // -------------------------------------------------------------------------
    _handleMenuChoice(valStr) {
      const num = Number(valStr);
      if (valStr === "" || !Number.isFinite(num)) {
        this._triggerReenter();
        this.showMainMenu();
        return;
      }
      const x = Math.trunc(num);

      if (x === 1) {
        this.clearCrt();
        this.printCrt("DAILY DATA INPUT ROUTINE");
        if (!this.dayFileExists(0)) {
          this.current_prompt = "NO DATA FILES ON DISK - DO YOU WANT TO START THE CROP (Y OR N)";
          this.state = "ITEM1_NO_DATA_START_CROP";
        } else {
          this._askDate("REPORT DATE (MM/DD/YY)?", "ITEM1_AFTER_DATE");
        }
      } else if (x === 2) {
        this.clearCrt();
        this.printCrt("CORRECT DAILY REPORT DATA ROUTINE");
        this._askDate("ENTER DATE OF REPORT TO BE CORRECTED (MM/DD/YY)?", "ITEM2_AFTER_DATE");
      } else if (x === 3 || x === 4) {
        this.clearCrt();
        this.printCrt("PRINT DAILY REPORT DATA ROUTINE");
        this.ctx.menu_x = x;
        this._askDate("DATE OF REPORT DATA TO BE PRINTED (MM/DD/YY)?", "ITEM34_AFTER_DATE");
      } else if (x === 5 || x === 6) {
        this.ctx.menu_x = x;
        this.H_num.set(34, 0.0);
        this.H_num.set(35, 0.0);
        this.A2_str.set(3, this.A1_str);
        this.current_prompt = "DO YOU WANT REPORT CHECKING PAGE PRINTED (Y OR N)";
        this.state = "REPORT_CHECK_PAGE_YN";
      } else if (x === 7) {
        this.clearCrt();
        this._askDate("DATE OF STOCK REPORT (MM/DD/YY)?", "ITEM7_AFTER_DATE");
      } else if (x === 8) {
        this.clearCrt();
        this.printCrt("HELP ROUTINE");
        this.printCrt("");
        this.printCrt("1. Core Sampler Factory Help (MRHELPC)");
        this.printCrt("2. Standard Ton Factory Help (MRHELPS)");
        this.current_prompt = "SELECT HELP ROUTINE (1 OR 2, RETURN=1)";
        this.state = "MRHELP_MODE";
      } else if (x === 9) {
        this.clearCrt();
        this.printCrt("END OF CROP CORRECTION ROUTINE");
        this._askDate("DATE OF LAST CROP DAY (MM/DD/YY)?", "ITEM9_AFTER_DATE");
      } else if (x === 10) {
        this.clearCrt();
        this.printCrt("CUSTOMIZE ROUTINE");
        this._startMrcustom();
      } else if (x === 11) {
        this.clearCrt();
        this.printCrt("PRINT CUSTOMIZED FILE");
        const pages = renderMrcustpr(
          this.B_str,
          this.A1_str,
          this.J_str,
          this.H_str,
          this.I_str,
          this.H_num
        );
        this.addPrinterJob("CUSTOM PARAMETERS (MRCUSTPR)", pages);
        this.showMainMenu();
      } else if (x === 12) {
        this.clearCrt();
        this.printCrt("1    DAILY REPORT DATA FORMS");
        this.printCrt("2    STOCK REPORT DATA FORMS");
        this.printCrt("");
        this.current_prompt = "WHICH FORMS DO YOU WANT PRINTED";
        this.state = "MRBLANFM_CHOICE";
      } else if (x === 13) {
        this.ctx.menu_x = 6;
        this.H_num.set(34, 1.0);
        this.H_num.set(35, 0.0);
        this.A2_str.set(3, this.A1_str);
        this.current_prompt = "DO YOU WANT REPORT CHECKING PAGE PRINTED (Y OR N)";
        this.state = "REPORT_CHECK_PAGE_YN";
      } else if (x === 14) {
        const d12 = this._getDiskMap(3);
        this.vfs.disks["D13"] = JSON.parse(JSON.stringify(d12));
        this._saveVfsToStorage();
        this.showMainMenu();
        this.top_bar_row1 = "BACK-UP COMPLETED: COPIED D12 TO HARD DISK (D13)";
      } else if (x === 15) {
        this.H_num.set(37, 4.0);
        this.saveMrparams();
        this.showMainMenu();
      } else if (x === 16) {
        this.clearCrt();
        this.printCrt("$END - PROGRAM TERMINATED");
        this.current_prompt = "KEY RETURN TO RESTART MRSTART";
        this.state = "HALTED";
      } else if (x === 17) {
        this.current_prompt = "DO YOU WANT TO DELETE ALL DATA FILES TO START CROP (Y OR N)";
        this.state = "ITEM17_CONFIRM";
      } else {
        this.showMainMenu();
      }
    }

    _handleDateEntry(valStr) {
      const parsed = wangParseMmddyy(valStr);
      if (!parsed) {
        this._triggerReenter("INVALID DATE (MM/DD/YY) - RE-ENTER");
        return;
      }
      const norm = wangJulianToMmddyy(parsed.julian);
      this.ctx.u9_str = norm.formatted;
      this.ctx.u9_num = norm.julian;
      this.top_bar_row1 = `IS DATE OK?   (Y/N)   ${norm.formatted}   ${norm.julian}`;
      this.current_prompt = `IS DATE OK? (Y/N) ${norm.formatted} (${norm.julian})`;
      this.state = "DATE_CONFIRM";
    }

    _handleDateConfirm(valStr) {
      const ans = valStr.toUpperCase();
      if (ans === "N") {
        this._askDate(this.ctx.date_prompt, this.ctx.date_next_state);
        return;
      }
      if (ans !== "Y") {
        this._triggerReenter("ENTER Y OR N");
        return;
      }
      this.top_bar_row1 = "";
      const u9Str = this.ctx.u9_str;
      const u9Num = this.ctx.u9_num;
      const nextSt = this.ctx.date_next_state;

      if (nextSt === "ITEM1_AFTER_DATE") {
        this.A2_str.set(2, u9Str);
        const u3 = wangJulianDiff(this.H_num.get(25), u9Num);
        this.H_num.set(27, Number(u9Num));
        this.H_num.set(26, Number(u3));
        if (this.dayFileExists(u3 + 1)) {
          this.current_prompt = "REPORT DATA ALREADY ENTERED - DO YOU WANT TO CORRECT IT? (Y OR N)";
          this.state = "ITEM1_ALREADY_ENTERED";
        } else if (this.dayFileExists(u3)) {
          this._startMrdata();
        } else {
          this.current_prompt = "MUST DO PREVIOUS DAY FIRST (KEY RETURN TO CONTINUE)";
          this.state = "WAIT_RETURN_MENU";
        }
      } else if (nextSt === "ITEM1_START_CROP_DATE") {
        this.loadMrparams();
        this.A1_str = u9Str;
        this.H_num.set(25, Number(u9Num));
        this.H_num.set(26, 0.0);
        this.A2_str.set(2, u9Str);
        this.saveMrparams();

        const prevNorm = wangJulianToMmddyy(u9Num - 1);
        const x0 = new Array(258).fill(0.0);
        x0[0] = 0.0;
        x0[242] = Number(prevNorm.julian);
        this.saveDayFile(0, prevNorm.formatted, x0, new Array(6).fill(" "));
        this.H_num.set(27, this.H_num.get(25));
        this._startMrdata();
      } else if (nextSt === "ITEM2_AFTER_DATE") {
        const u3 = wangJulianDiff(this.H_num.get(25), u9Num);
        if (u3 < 0 || !this.dayFileExists(u3 + 1)) {
          this.current_prompt = "THIS REPORT NOT ON FILE - KEY RETURN TO CONTINUE";
          this.state = "WAIT_RETURN_MENU";
        } else {
          this.H_num.set(26, Number(u3 + 1));
          this._startMrdataco();
        }
      } else if (nextSt === "ITEM34_AFTER_DATE") {
        const u3 = wangJulianDiff(this.H_num.get(25), u9Num);
        const dayIdx = u3 + 1;
        if (u3 < 0 || !this.dayFileExists(dayIdx)) {
          this.current_prompt = "THIS REPORT NOT ON FILE - KEY RETURN TO CONTINUE";
          this.state = "WAIT_RETURN_MENU";
        } else {
          this.H_num.set(28, Number(this.ctx.menu_x || 3));
          this.H_num.set(26, Number(dayIdx));
          const [a1Dt, xArr, b1Rem] = this.loadDayFile(dayIdx);
          const b1Obj = new OneBasedArray1D(6, " ");
          b1Obj.fromList(b1Rem);
          const isTodate = Math.round(this.H_num.get(28)) === 4;
          const pages = renderMrdatapr(
            this.B_str,
            a1Dt,
            xArr,
            b1Obj,
            this.J_str,
            this.H_str,
            this.H_num,
            isTodate
          );
          const title = `${isTodate ? "TODATE FILE" : "DAILY REPORT DATA"} - ${a1Dt} (Day ${dayIdx})`;
          this.addPrinterJob(title, pages);
          this.showMainMenu();
        }
      } else if (nextSt === "ITEM5_AFTER_DATE") {
        this.ctx.daily_rep_u9_str = u9Str;
        this.ctx.daily_rep_u9_num = u9Num;
        this.current_prompt = "NUMBER OF REPORT COPIES REQUIRED";
        this.state = "DAILY_REPORT_COPIES";
      } else if (nextSt === "ITEM6_LAST_DAY") {
        const u3 = wangJulianDiff(this.H_num.get(25), u9Num);
        this.H_num.set(26, Number(u3 + 1));
        this.A2_str.set(2, u9Str);
        this._askDate("FIRST DAY INCLUDED IN THIS WEEKLY REPORT (MM/DD/YY)?", "ITEM6_FIRST_DAY");
      } else if (nextSt === "ITEM6_FIRST_DAY") {
        this.A2_str.set(1, u9Str);
        const u3 = wangJulianDiff(this.H_num.get(25), u9Num);
        this.H_num.set(27, Number(u3));
        this.current_prompt = "NUMBER OF THIS WEEKLY REPORT";
        this.state = "WEEKLY_REPORT_NUM";
      } else if (nextSt === "ITEM7_AFTER_DATE") {
        this.A1_str = u9Str;
        this.ctx.stock_date = u9Str;
        this.clearCrt();
        this.printCrt("STOCK CALCULATIONS");
        this.printCrt("");
        this.current_prompt =
          "WILL MATERIALS IN PROCESS BE REPORTED IN GALLONS OR CUBIC FEET (G OR CF)";
        this.state = "MRSTOCK_UNIT";
      } else if (nextSt === "ITEM9_AFTER_DATE") {
        const u3 = wangJulianDiff(this.H_num.get(25), u9Num);
        this.H_num.set(26, Number(u3));
        if (this.dayFileExists(u3 + 2)) {
          this.current_prompt = "THIS IS NOT LAST CROP DAY, KEY RETURN TO CONTINUE";
          this.state = "WAIT_RETURN_MENU";
        } else if (!this.dayFileExists(u3 + 1)) {
          this.current_prompt = "THIS REPORT NOT ON FILE - KEY RETURN TO CONTINUE";
          this.state = "WAIT_RETURN_MENU";
        } else {
          this._startMrencrop();
        }
      }
    }

    // -------------------------------------------------------------------------
    // Item 1: MRDATA (Daily Input) & MRDATAWU
    // -------------------------------------------------------------------------
    _handleItem1AlreadyEntered(valStr) {
      const ans = valStr.toUpperCase();
      if (ans === "Y") {
        const u3 = wangJulianDiff(this.H_num.get(25), this.ctx.u9_num);
        this.H_num.set(26, Number(u3 + 1));
        this._startMrdataco();
      } else if (ans === "N") {
        this.showMainMenu();
      } else {
        this._triggerReenter("ENTER Y OR N");
      }
    }

    _handleItem1StartCropYn(valStr) {
      const ans = valStr.toUpperCase();
      if (ans === "N") {
        this.showMainMenu();
      } else if (ans === "Y") {
        this._askDate("DATE THAT CROP STARTED (MM/DD/YY)?", "ITEM1_START_CROP_DATE");
      } else {
        this._triggerReenter("ENTER Y OR N");
      }
    }

    _startMrdata() {
      this.A.clear();
      const prevDay = Math.round(this.H_num.get(26));
      this.A.set(1, 1, Number(prevDay + 1));
      this.A.set(243, 1, this.H_num.get(27));
      const [, prevX] = this.loadDayFile(prevDay);
      for (let j = 1; j <= 258; j++) {
        this.A.set(j, 3, prevX[j - 1]);
      }
      for (let j = 1; j <= 6; j++) {
        this.B1_str.set(j, " ");
      }

      this.clearCrt();
      this.printCrt(`DAILY DATA INPUT - CROP DAY ${Math.round(this.A.get(1, 1))} (${this.A2_str.get(2)})`);
      const prompts = getDailyInputPrompts(this.J_str, this.H_str, this.H_num);
      this.ctx.mrdata_prompts = prompts;
      this.ctx.mrdata_idx = 0;
      this.ctx.mrdata_remark_idx = 0;
      this._promptNextMrdata();
    }

    _promptNextMrdata() {
      const prompts = this.ctx.mrdata_prompts;
      const idx = this.ctx.mrdata_idx;
      if (idx < prompts.length) {
        const [, label, preHdr] = prompts[idx];
        if (preHdr) this.printCrt(preHdr);
        this.current_prompt = label;
        this.state = "MRDATA_INPUT";
      } else {
        const remIdx = this.ctx.mrdata_remark_idx;
        const remLabels = ["1A", "1B", "2A", "2B", "3A", "3B"];
        if (remIdx < 6) {
          this.current_prompt = `REMARKS - LINE ${remLabels[remIdx]}`;
          this.state = "MRDATA_INPUT";
        } else {
          runWorkupOnA(this.A, this.H_num, false);
          const dayNum = Math.round(this.A.get(1, 2));
          const xNew = [];
          for (let j = 1; j <= 258; j++) xNew.push(this.A.get(j, 2));
          this.saveDayFile(dayNum, this.A2_str.get(2), xNew, this.B1_str.toList());
          this.showMainMenu();
          this.top_bar_row1 = `SAVED DAILY REPORT NO. ${dayNum} (${this.A2_str.get(2)}) TO DISK ${this.getDiskName()}`;
        }
      }
    }

    _handleMrdataStep(rawInput) {
      const prompts = this.ctx.mrdata_prompts;
      const idx = this.ctx.mrdata_idx;
      if (idx < prompts.length) {
        const [itemNo] = prompts[idx];
        const valS = rawInput.trim();
        let val;
        if (valS === "" && !this.strict_wang_mode) {
          val = 0.0;
        } else {
          const parsed = Number(valS);
          if (valS === "" || !Number.isFinite(parsed)) {
            this._triggerReenter("NUMERIC INPUT REQUIRED - RE-ENTER");
            return;
          }
          val = parsed;
        }
        this.A.set(itemNo, 1, val);
        this.ctx.mrdata_idx += 1;
        this._promptNextMrdata();
      } else {
        const remIdx = this.ctx.mrdata_remark_idx;
        this.B1_str.set(remIdx + 1, rawInput.slice(0, 60));
        this.ctx.mrdata_remark_idx += 1;
        this._promptNextMrdata();
      }
    }

    // -------------------------------------------------------------------------
    // Item 2: MRDATACO (Correct Data) & MRDACOWU (Cascading Recalculation)
    // -------------------------------------------------------------------------
    _startMrdataco() {
      this.A.clear();
      const targetDay = Math.round(this.H_num.get(26));
      const [, prevX] = this.loadDayFile(targetDay - 1);
      for (let j = 1; j <= 258; j++) {
        this.A.set(j, 3, prevX[j - 1]);
      }
      const [a1Dt, curX, curB1] = this.loadDayFile(targetDay);
      this.A1_str = a1Dt;
      for (let j = 1; j <= 258; j++) {
        this.A.set(j, 1, curX[j - 1]);
      }
      this.B1_str.fromList(curB1);

      this.clearCrt();
      this.printCrt("DATA CORRECTION ROUTINE");
      this.printCrt(`FOR CROP DAY  ${Math.round(this.A.get(1, 1))}`);
      this.printCrt(`REPORT FOR DAY ${this.A1_str}`);
      this.printCrt("");

      const prompts = getDailyInputPrompts(this.J_str, this.H_str, this.H_num);
      this.ctx.mrdataco_prompts = prompts;
      this.ctx.mrdataco_idx = 0;
      this.ctx.mrdataco_remark_idx = 0;
      this._promptNextMrdataco();
    }

    _promptNextMrdataco() {
      const prompts = this.ctx.mrdataco_prompts;
      const idx = this.ctx.mrdataco_idx;
      if (idx < prompts.length) {
        const [itemNo, label, preHdr] = prompts[idx];
        if (preHdr) this.printCrt(preHdr);
        const curVal = this.A.get(itemNo, 1);
        this.printCrt(`${label}  ${formatNumberGeneral(curVal)}`);
        this.current_prompt = label;
        this.state = "MRDATACO_INPUT";
      } else {
        const remIdx = this.ctx.mrdataco_remark_idx;
        const remLabels = ["1A", "1B", "2A", "2B", "3A", "3B"];
        if (remIdx < 6) {
          const curRem = String(this.B1_str.get(remIdx + 1)).replace(/\s+$/, "");
          this.printCrt(`CURRENT REMARKS - LINE ${remLabels[remIdx]}: ${curRem}`);
          this.current_prompt = `REMARKS - LINE ${remLabels[remIdx]}`;
          this.state = "MRDATACO_INPUT";
        } else {
          this._runMrdacowuCascade();
        }
      }
    }

    _handleMrdatacoStep(rawInput) {
      const prompts = this.ctx.mrdataco_prompts;
      const idx = this.ctx.mrdataco_idx;
      if (idx < prompts.length) {
        const [itemNo] = prompts[idx];
        const valS = rawInput.trim();
        let val;
        if (valS === "") {
          if (this.strict_wang_mode) {
            this._triggerReenter("STRICT WANG BASIC MODE: MUST TYPE VALUE");
            return;
          }
          val = this.A.get(itemNo, 1);
        } else {
          const parsed = Number(valS);
          if (!Number.isFinite(parsed)) {
            this._triggerReenter("NUMERIC INPUT REQUIRED - RE-ENTER");
            return;
          }
          val = parsed;
        }
        this.A.set(itemNo, 1, val);
        this.printCrt("");
        this.ctx.mrdataco_idx += 1;
        this._promptNextMrdataco();
      } else {
        const remIdx = this.ctx.mrdataco_remark_idx;
        if (rawInput !== "" || this.strict_wang_mode) {
          this.B1_str.set(remIdx + 1, rawInput.slice(0, 60));
        }
        this.ctx.mrdataco_remark_idx += 1;
        this._promptNextMrdataco();
      }
    }

    _runMrdacowuCascade() {
      const cascadedDays = [];
      while (true) {
        runWorkupOnA(this.A, this.H_num, true);
        const dayNum = Math.round(this.A.get(1, 2));
        const xNew = [];
        for (let j = 1; j <= 258; j++) xNew.push(this.A.get(j, 2));
        this.saveDayFile(dayNum, this.A1_str, xNew, this.B1_str.toList());
        cascadedDays.push([dayNum, this.A1_str]);

        for (let j = 1; j <= 258; j++) {
          this.A.set(j, 3, this.A.get(j, 2));
        }

        this.H_num.set(26, this.H_num.get(26) + 1.0);
        const nextDay = Math.round(this.H_num.get(26));
        if (!this.dayFileExists(nextDay)) break;
        const [a1Next, xNext, b1Next] = this.loadDayFile(nextDay);
        this.A1_str = a1Next;
        this.B1_str.fromList(b1Next);
        for (let j = 1; j <= 109; j++) {
          this.A.set(j, 1, xNext[j - 1]);
        }
        for (const j of [243, 246, 251, 252, 253, 254]) {
          this.A.set(j, 1, xNext[j - 1]);
        }
      }

      this.showMainMenu();
      for (const [dNo, dDt] of cascadedDays) {
        this.printCrt(`CORRECTED TODATE FIGURES ON REPORT NO. ${dNo} FOR ${dDt}`);
      }
      this.top_bar_row1 = `CASCADE COMPLETE: UPDATED ${cascadedDays.length} CROP DAY FILE(S)`;
    }

    // -------------------------------------------------------------------------
    // Items 5, 6, 13: Daily Report, Weekly Report, Weekly Comparative Form
    // -------------------------------------------------------------------------
    _handleReportCheckYn(valStr) {
      const ans = valStr.toUpperCase();
      if (ans === "Y") {
        this.H_num.set(35, 1.0);
      } else if (ans === "N") {
        this.H_num.set(35, 0.0);
      } else {
        this._triggerReenter("ENTER Y OR N");
        return;
      }

      if (Math.round(this.ctx.menu_x || 5) === 6) {
        this.clearCrt();
        this.printCrt("PRINT WEEKLY REPORT ROUTINE");
        this._askDate("LAST DAY INCLUDED IN THIS WEEKLY REPORT (MM/DD/YY)?", "ITEM6_LAST_DAY");
      } else {
        this.clearCrt();
        this.printCrt("PRINT DAILY REPORT ROUTINE");
        this._askDate("REPORT FOR CROP DAY (MM/DD/YY)?", "ITEM5_AFTER_DATE");
      }
    }

    _handleDailyReportCopies(valStr) {
      const num = Number(valStr);
      if (valStr === "" || !Number.isFinite(num)) {
        this._triggerReenter("ENTER NUMBER OF COPIES");
        return;
      }
      const copies = Math.max(1, Math.trunc(num));
      this.H_num.set(32, Number(copies));
      const u9Str = this.ctx.daily_rep_u9_str;
      const u9Num = this.ctx.daily_rep_u9_num;
      this.A2_str.set(2, u9Str);
      const u3 = wangJulianDiff(this.H_num.get(25), u9Num);
      this.H_num.set(26, Number(u3 + 1));
      this.H_num.set(27, Number(u3));
      if (u3 < 0 || !this.dayFileExists(u3 + 1)) {
        this.current_prompt = "THIS REPORT NOT ON FILE - KEY RETURN TO CONTINUE";
        this.state = "WAIT_RETURN_MENU";
        return;
      }
      this.H_num.set(28, 0.0);
      this._executeReportGeneration();
    }

    _handleWeeklyReportNum(valStr) {
      const num = Number(valStr);
      if (valStr === "" || !Number.isFinite(num)) {
        this._triggerReenter("ENTER WEEKLY REPORT NUMBER");
        return;
      }
      this.H_num.set(31, Number(Math.trunc(num)));
      if (Math.round(this.H_num.get(34)) === 1) {
        this.current_prompt = "IS THIS OKAY (Y OR N)";
        this.state = "WEEKLY_REPORT_OK";
      } else {
        this.current_prompt = "NUMBER OF REPORT COPIES REQUIRED";
        this.state = "WEEKLY_REPORT_COPIES";
      }
    }

    _handleWeeklyReportCopies(valStr) {
      const num = Number(valStr);
      if (valStr === "" || !Number.isFinite(num)) {
        this._triggerReenter("ENTER NUMBER OF COPIES");
        return;
      }
      this.H_num.set(32, Number(Math.max(1, Math.trunc(num))));
      this.current_prompt = "IS THIS OKAY (Y OR N)";
      this.state = "WEEKLY_REPORT_OK";
    }

    _handleWeeklyReportOk(valStr) {
      const ans = valStr.toUpperCase();
      if (ans === "N") {
        this.clearCrt();
        this.printCrt("PRINT WEEKLY REPORT ROUTINE");
        this._askDate("LAST DAY INCLUDED IN THIS WEEKLY REPORT (MM/DD/YY)?", "ITEM6_LAST_DAY");
        return;
      }
      if (ans !== "Y") {
        this._triggerReenter("ENTER Y OR N");
        return;
      }

      const endDay = Math.round(this.H_num.get(26));
      const baseDay = Math.round(this.H_num.get(27));
      if (endDay < 1 || baseDay < 0 || !this.dayFileExists(endDay) || !this.dayFileExists(baseDay)) {
        this.current_prompt = "THIS REPORT NOT ON FILE - KEY RETURN TO CONTINUE";
        this.state = "WAIT_RETURN_MENU";
        return;
      }

      this.H_num.set(28, 1.0);
      if (Math.round(this.H_num.get(34)) === 0) {
        for (let j = 1; j <= 6; j++) this.B1_str.set(j, " ");
        this.ctx.weekly_rem_idx = 0;
        this.current_prompt = "REMARKS: LINE 1A";
        this.state = "WEEKLY_REMARKS";
      } else {
        this._executeReportGeneration();
      }
    }

    _handleWeeklyRemarks(rawInput) {
      let idx = this.ctx.weekly_rem_idx;
      this.B1_str.set(idx + 1, rawInput.slice(0, 60));
      idx += 1;
      this.ctx.weekly_rem_idx = idx;
      const remLabels = ["1A", "1B", "2A", "2B", "3A", "3B"];
      if (idx < 6) {
        this.current_prompt = `REMARKS: LINE ${remLabels[idx]}`;
      } else {
        this._executeReportGeneration();
      }
    }

    _executeReportGeneration() {
      const endDay = Math.round(this.H_num.get(26));
      const baseDay = Math.round(this.H_num.get(27));

      const [, xEnd, b1End] = this.loadDayFile(endDay);
      const [, xBase] = this.loadDayFile(baseDay);

      this.A.clear();
      for (let j = 1; j <= 258; j++) {
        this.A.set(j, 2, xEnd[j - 1]);
        this.A.set(j, 3, xBase[j - 1]);
      }

      if (Math.round(this.H_num.get(28)) === 0) {
        this.B1_str.fromList(b1End);
      }

      const dayFilesRange = [];
      const startScan = Math.max(1, baseDay > 0 ? baseDay : 1);
      for (let dIdx = startScan; dIdx <= endDay; dIdx++) {
        if (this.dayFileExists(dIdx)) {
          const [, xD] = this.loadDayFile(dIdx);
          dayFilesRange.push(xD);
        }
      }

      const savedH27 = this.H_num.get(27);
      runMrcalc(this.A, this.B, this.C, this.D, this.E, this.F, this.G, this.H_num, dayFilesRange);
      this.H_num.set(27, savedH27);

      if (Math.round(this.H_num.get(34)) === 1) {
        const pages = renderMrcomppr(
          this.B_str,
          this.A2_str,
          this.A,
          this.B,
          this.D,
          this.E,
          this.F,
          this.G,
          this.H_num
        );
        const title = `WEEKLY COMPARATIVE REPORT FORM - ${this.A2_str.get(1)} to ${this.A2_str.get(2)}`;
        this.addPrinterJob(title, pages);
        this.showMainMenu();
        this.top_bar_row1 = `PRINTED ${title} TO LINE PRINTER (215)`;
        return;
      }

      const p1 = renderMrrepoprPage1(
        this.B_str,
        this.A2_str,
        this.A,
        this.B,
        this.C,
        this.D,
        this.H_num
      );
      const p2 = renderMrrepop2Page2(
        this.B_str,
        this.B1_str,
        this.A2_str,
        this.A,
        this.E,
        this.F,
        this.G,
        this.J_str,
        this.H_str,
        this.H_num
      );
      const pages = [p1, p2];
      if (Math.round(this.H_num.get(35)) === 1) {
        const p3 = renderMrrepockPage3(
          this.B_str,
          this.A2_str,
          this.A,
          this.B,
          this.C,
          this.D,
          this.E,
          this.F,
          this.H_num
        );
        pages.push(p3);
      }

      const title =
        Math.round(this.H_num.get(28)) === 1
          ? `WEEKLY MANUFACTURING REPORT NO. ${Math.round(this.H_num.get(31))} (${this.A2_str.get(1)} to ${this.A2_str.get(2)})`
          : `DAILY MANUFACTURING REPORT NO. ${Math.round(this.A.get(1, 2))} (${this.A2_str.get(2)})`;

      this.addPrinterJob(title, pages);
      this.showMainMenu();
      this.top_bar_row1 = `PRINTED ${title} (${pages.length} PAGES) TO LINE PRINTER (215)`;
    }

    // -------------------------------------------------------------------------
    // Item 7: Stock in Process Calculations (MRSTOCK -> MRSTOCKG / MRSTOCKC)
    // -------------------------------------------------------------------------
    _handleMrstockUnit(valStr) {
      const ans = valStr.toUpperCase();
      if (ans !== "G" && ans !== "CF") {
        this._triggerReenter("ENTER G OR CF");
        return;
      }
      this.ctx.stock_unit = ans;
      const unitWord = ans === "G" ? "GALLONS" : "CU. FT.";
      const streams = [
        "JUICE",
        "SYRUP",
        "A MASSECUITE",
        "TOP-OFF A MASSECUITE",
        "B MASSECUITE",
        "C MASSECUITE",
        "A MOLASSES",
        "TOP-OFF A MOLASSES",
        "B MOLASSES",
        "GRAIN",
        "B MAGMA",
        "C MAGMA",
        "OTHER MATERIAL",
      ];
      const prompts = [];
      let idx = 1;
      for (const st of streams) {
        if (st === "B MAGMA") {
          idx += 3;
          continue;
        }
        prompts.push([idx, `${String(idx).padStart(2, " ")}   ${st}, ${unitWord}`]);
        prompts.push([idx + 1, `${String(idx + 1).padStart(2, " ")}   ${st}, BRIX`]);
        prompts.push([idx + 2, `${String(idx + 2).padStart(2, " ")}   ${st}, POL`]);
        idx += 3;
      }
      prompts.push([40, "40   FINAL MOLASSES PURITY FOR RUN"]);
      prompts.push([41, "41   SUGAR PURITY FOR RUN"]);

      this.ctx.stock_prompts = prompts;
      this.ctx.stock_vals = new Array(41).fill(0.0);
      this.ctx.stock_idx = 0;
      this.current_prompt = prompts[0][1];
      this.state = "MRSTOCK_INPUT";
    }

    _handleMrstockStep(valStr) {
      const prompts = this.ctx.stock_prompts;
      let idx = this.ctx.stock_idx;
      const [itemNo] = prompts[idx];
      let v;
      if (valStr === "" && !this.strict_wang_mode) {
        v = 0.0;
      } else {
        const parsed = Number(valStr);
        if (valStr === "" || !Number.isFinite(parsed)) {
          this._triggerReenter("NUMERIC INPUT REQUIRED - RE-ENTER");
          return;
        }
        v = parsed;
      }
      this.ctx.stock_vals[itemNo - 1] = v;
      idx += 1;
      this.ctx.stock_idx = idx;
      if (idx < prompts.length) {
        this.current_prompt = prompts[idx][1];
      } else {
        const [lines, summary] = calculateAndRenderStock(
          this.B_str,
          this.ctx.stock_date || this.A1_str,
          this.ctx.stock_unit,
          this.ctx.stock_vals,
          this.H_num
        );
        const title = `STOCK CALCULATIONS (${this.ctx.stock_unit}) - ${this.ctx.stock_date || this.A1_str}`;
        this.addPrinterJob(title, [lines]);
        this.printCrt("");
        this.printCrt(
          `SUGAR IN STOCK:    ${formatWithCommas(Math.round(summary.sugar_lbs_brix))} Lbs Brix | ${formatWithCommas(
            Math.round(summary.sugar_lbs_pol)
          )} Lbs Pol`
        );
        this.printCrt(
          `MOLASSES IN STOCK: ${formatWithCommas(Math.round(summary.molasses_lbs_brix))} Lbs Brix | ${formatWithCommas(
            Math.round(summary.molasses_lbs_pol)
          )} Lbs Pol`
        );
        this.current_prompt = "IS DATA OKAY (Y OR N)";
        this.state = "MRSTOCK_OK";
      }
    }

    _handleMrstockOk(valStr) {
      const ans = valStr.toUpperCase();
      if (ans === "Y") {
        this.showMainMenu();
      } else if (ans === "N") {
        this._handleMrstockUnit(this.ctx.stock_unit);
      } else {
        this._triggerReenter("ENTER Y OR N");
      }
    }

    // -------------------------------------------------------------------------
    // Item 8: Help Routine for Daily Report (MRHELPC & MRHELPS)
    // -------------------------------------------------------------------------
    _handleMrhelpMode(valStr) {
      if (valStr === "" || valStr === "1") {
        const prompts = [
          "TOTAL LBS TRS PURCHASED",
          "LIQUIDATION FACTOR",
          "POL % MIXED JUICE",
          "BRIX % MIXED JUICE",
          "BOILING HOUSE EFFICIENCY",
          "TONS CANE GROUND TODAY",
          "TONS CANE PURCHASED TODAY",
          "FIBER % BAGASSE",
          "FIBER % CANE DESIRED",
        ];
        this.ctx.help_prompts = prompts;
        this.ctx.help_vals = [];
        this.ctx.help_mode = "C";
        this.current_prompt = prompts[0];
        this.state = "MRHELPC_INPUT";
      } else if (valStr === "2") {
        const prompts = [
          "TONS CANE GROUND",
          "MIXED JUICE BRIX",
          "NORMAL JUICE BRIX",
          "DESIRED NORMAL JUICE EXTRACTION",
          "FIBER % BAGASSE",
          "DESIRED FIBER % CANE",
        ];
        this.ctx.help_prompts = prompts;
        this.ctx.help_vals = [];
        this.ctx.help_mode = "S";
        this.current_prompt = prompts[0];
        this.state = "MRHELPS_INPUT";
      } else {
        this._triggerReenter("ENTER 1 OR 2");
      }
    }

    _handleMrhelpcStep(valStr) {
      const v = Number(valStr);
      if (valStr === "" || !Number.isFinite(v)) {
        this._triggerReenter("NUMERIC INPUT REQUIRED");
        return;
      }
      this.ctx.help_vals.push(v);
      const prompts = this.ctx.help_prompts;
      if (this.ctx.help_vals.length < prompts.length) {
        this.current_prompt = prompts[this.ctx.help_vals.length];
      } else {
        const [a, b, c, d, e, f, g, h, i] = this.ctx.help_vals;
        const denom = c * (1.4 - 0.4 * safeDiv(d, c)) * e * g;
        const m = safeDiv(a * b * 0.048 * f, denom);
        const b1 = safeDiv(f * i, h);
        const i1 = m + b1 - f;
        this.printCrt("");
        this.printCrt(`TONS MIXED JUICE=  ${m.toFixed(4)}`);
        this.printCrt(`TONS IMBIBITION=   ${i1.toFixed(4)}`);
        this.printCrt("");
        this.current_prompt = "IS THIS OKAY (Y OR N)";
        this.state = "MRHELP_OK";
      }
    }

    _handleMrhelpsStep(valStr) {
      const v = Number(valStr);
      if (valStr === "" || !Number.isFinite(v)) {
        this._triggerReenter("NUMERIC INPUT REQUIRED");
        return;
      }
      this.ctx.help_vals.push(v);
      const prompts = this.ctx.help_prompts;
      if (this.ctx.help_vals.length < prompts.length) {
        this.current_prompt = prompts[this.ctx.help_vals.length];
      } else {
        const [c, m, n, e, b, f] = this.ctx.help_vals;
        const d = safeDiv((n - m) * 100.0, m);
        const j = e + d;
        const m1 = (c * j) / 100.0;
        const a = safeDiv(f * c, b);
        const i = m1 + a - c;
        this.printCrt("");
        this.printCrt(`TONS MIXED JUICE=  ${m1.toFixed(4)}`);
        this.printCrt(`TONS IMBIBITION=   ${i.toFixed(4)}`);
        this.printCrt("");
        this.current_prompt = "IS THIS OKAY (Y OR N)";
        this.state = "MRHELP_OK";
      }
    }

    _handleMrhelpOk(valStr) {
      const ans = valStr.toUpperCase();
      if (ans === "Y") {
        this.showMainMenu();
      } else if (ans === "N") {
        const mode = this.ctx.help_mode === "C" ? "1" : "2";
        this._handleMrhelpMode(mode);
      } else {
        this._triggerReenter("ENTER Y OR N");
      }
    }

    // -------------------------------------------------------------------------
    // Item 9: End of Crop Correction Routine (MRENCROP -> MRDACOWU)
    // -------------------------------------------------------------------------
    _startMrencrop() {
      const prevDay = Math.round(this.H_num.get(26));
      const lastDay = prevDay + 1;
      const [, xPrev] = this.loadDayFile(prevDay);
      const [a1Last, xLast, b1Last] = this.loadDayFile(lastDay);
      this.A1_str = a1Last;
      this.B1_str.fromList(b1Last);

      this.A.clear();
      for (let j = 1; j <= 258; j++) {
        this.A.set(j, 2, xPrev[j - 1]);
        this.A.set(j, 3, xLast[j - 1]);
      }
      this.H_num.set(26, Number(lastDay));

      const bVals = new Array(19).fill(0.0);
      bVals[1] = this.A.get(204, 3) * 2000.0;
      bVals[2] = safeDiv((this.A.get(204, 3) - this.A.get(205, 3)) * 100.0, this.A.get(204, 3));
      bVals[3] = safeDiv(this.A.get(206, 3) * 100.0, this.A.get(204, 3));
      bVals[4] = safeDiv(this.A.get(207, 3) * 100.0, this.A.get(204, 3));
      bVals[5] = safeDiv(this.A.get(208, 3) * 100.0, this.A.get(204, 3));
      bVals[6] = this.A.get(211, 3);
      bVals[7] = safeDiv(this.A.get(213, 3) * 100.0, this.A.get(212, 3));
      bVals[8] = safeDiv(this.A.get(214, 3) * 100.0, this.A.get(212, 3));
      bVals[9] = safeDiv(this.A.get(215, 3) * 100.0, this.A.get(212, 3));
      bVals[10] = safeDiv(this.A.get(216, 3) * 100.0, this.A.get(212, 3));
      bVals[11] = safeDiv(this.A.get(217, 3) * 100.0, this.A.get(212, 3));
      bVals[12] = this.A.get(220, 3);
      bVals[13] = safeDiv(this.A.get(222, 3) * 100.0, this.A.get(221, 3));
      bVals[14] = safeDiv(this.A.get(223, 3) * 100.0, this.A.get(221, 3));
      bVals[15] = safeDiv(this.A.get(224, 3) * 100.0, this.A.get(221, 3));
      bVals[16] = safeDiv(this.A.get(225, 3) * 100.0, this.A.get(221, 3));
      bVals[17] = safeDiv(this.A.get(226, 3) * 100.0, this.A.get(221, 3));
      bVals[18] = this.A.get(242, 3);

      const encPrompts = [
        [1, "TODATE LBS SUGAR MADE"],
        [2, "TODATE MOISTURE % SUGAR"],
        [3, "TODATE POL % SUGAR"],
        [4, "TODATE STARCH % SUGAR"],
        [5, "TODATE GRAIN SUGAR"],
        [18, "TODATE LBS SUGAR SHIPPED"],
        [6, "TODATE GALLONS FINAL MOLASSES MADE"],
        [7, "TODATE BRIX OF FINAL MOLASSES MADE"],
        [8, "TODATE POL OF FINAL MOLASSES MADE"],
        [9, "TODATE GLUCOSE % FINAL MOLASSES MADE"],
        [10, "TODATE ASH % FINAL MOLASSES MADE"],
        [11, "TODATE CLERGET OF FINAL MOLASSES MADE"],
        [12, "TODATE GALLONS OF FINAL MOLASSES SHIPPED"],
        [13, "TODATE BRIX OF FINAL MOLASSES SHIPPED"],
        [14, "TODATE POL OF FINAL MOLASSES SHIPPED"],
        [15, "TODATE GLUCOSE % FINAL MOLASSES SHIPPED"],
        [16, "TODATE ASH % FINAL MOLASSES SHIPPED"],
        [17, "TODATE CLERGET % FINAL MOLASSES SHIPPED"],
      ];
      this.printCrt("");
      this.printCrt(`REPORT FOR DAY ${this.A1_str}`);
      this.printCrt(`FOR CROP DAY ${Math.round(this.A.get(1, 3))}`);
      this.printCrt("");

      this.ctx.enc_b = bVals;
      this.ctx.enc_prompts = encPrompts;
      this.ctx.enc_idx = 0;
      const [bIdx, lbl] = encPrompts[0];
      this.printCrt(`${lbl}  ${formatNumberGeneral(bVals[bIdx])}`);
      this.current_prompt = `CORRECT ${lbl}`;
      this.state = "MRENCROP_INPUT";
    }

    _handleMrencropStep(rawInput) {
      const encPrompts = this.ctx.enc_prompts;
      let idx = this.ctx.enc_idx;
      const [bIdx] = encPrompts[idx];
      const valS = rawInput.trim();
      let v;
      if (valS === "" && !this.strict_wang_mode) {
        v = this.ctx.enc_b[bIdx];
      } else {
        const parsed = Number(valS);
        if (valS === "" || !Number.isFinite(parsed)) {
          this._triggerReenter("NUMERIC INPUT REQUIRED");
          return;
        }
        v = parsed;
      }
      this.ctx.enc_b[bIdx] = v;
      idx += 1;
      this.ctx.enc_idx = idx;
      if (idx < encPrompts.length) {
        const [nextBIdx, nextLbl] = encPrompts[idx];
        this.printCrt("");
        this.printCrt(`${nextLbl}  ${formatNumberGeneral(this.ctx.enc_b[nextBIdx])}`);
        this.current_prompt = `CORRECT ${nextLbl}`;
      } else {
        const bv = this.ctx.enc_b;
        this.A.set(204, 1, bv[1] / 2000.0);
        this.A.set(205, 1, ((100.0 - bv[2]) / 100.0) * this.A.get(204, 1));
        this.A.set(206, 1, (bv[3] / 100.0) * this.A.get(204, 1));
        this.A.set(207, 1, (bv[4] / 100.0) * this.A.get(204, 1));
        this.A.set(208, 1, (bv[5] / 100.0) * this.A.get(204, 1));
        this.A.set(211, 1, bv[6]);
        const k = bv[7];
        const k1 = brixDensityPoly5(k) / 7.48;
        this.A.set(212, 1, (this.A.get(211, 1) * k1) / 2000.0);
        this.A.set(213, 1, (this.A.get(212, 1) * k) / 100.0);
        this.A.set(214, 1, (this.A.get(212, 1) * bv[8]) / 100.0);
        this.A.set(215, 1, (this.A.get(212, 1) * bv[9]) / 100.0);
        this.A.set(216, 1, (this.A.get(212, 1) * bv[10]) / 100.0);
        this.A.set(217, 1, (this.A.get(212, 1) * bv[11]) / 100.0);
        this.A.set(220, 1, bv[12]);
        const kS = bv[13];
        const k1S = brixDensityPoly5(kS) / 7.48;
        this.A.set(221, 1, (this.A.get(220, 1) * k1S) / 2000.0);
        this.A.set(222, 1, (this.A.get(221, 1) * kS) / 100.0);
        this.A.set(223, 1, (this.A.get(221, 1) * bv[14]) / 100.0);
        this.A.set(224, 1, (this.A.get(221, 1) * bv[15]) / 100.0);
        this.A.set(225, 1, (this.A.get(221, 1) * bv[16]) / 100.0);
        this.A.set(226, 1, (this.A.get(221, 1) * bv[17]) / 100.0);
        this.A.set(242, 1, bv[18]);

        this.A.set(95, 1, (this.A.get(204, 1) - this.A.get(204, 2)) * 2000.0);
        const dSug = this.A.get(204, 1) - this.A.get(204, 2);
        this.A.set(
          70,
          1,
          safeDiv(
            (this.A.get(204, 1) - this.A.get(205, 1) - this.A.get(204, 2) + this.A.get(205, 2)) * 100.0,
            dSug
          )
        );
        this.A.set(71, 1, safeDiv((this.A.get(206, 1) - this.A.get(206, 2)) * 100.0, dSug));
        this.A.set(72, 1, safeDiv((this.A.get(207, 1) - this.A.get(207, 2)) * 100.0, dSug));
        this.A.set(73, 1, safeDiv((this.A.get(208, 1) - this.A.get(208, 2)) * 100.0, dSug));

        this.A.set(96, 1, this.A.get(211, 1) - this.A.get(211, 2));
        this.A.set(97, 1, this.A.get(242, 1) - this.A.get(242, 2));
        this.A.set(98, 1, this.A.get(220, 1) - this.A.get(220, 2));

        const dFm = this.A.get(212, 1) - this.A.get(212, 2);
        for (let offsetI = 0; offsetI < 5; offsetI++) {
          this.A.set(
            74 + offsetI,
            1,
            safeDiv((this.A.get(213 + offsetI, 1) - this.A.get(213 + offsetI, 2)) * 100.0, dFm)
          );
        }
        const dFms = this.A.get(221, 1) - this.A.get(221, 2);
        for (let offsetI = 0; offsetI < 5; offsetI++) {
          this.A.set(
            79 + offsetI,
            1,
            safeDiv((this.A.get(222 + offsetI, 1) - this.A.get(222 + offsetI, 2)) * 100.0, dFms)
          );
        }

        for (const [r0, r1] of [
          [70, 83],
          [95, 98],
          [204, 208],
          [211, 217],
          [220, 226],
          [242, 242],
        ]) {
          for (let j = r0; j <= r1; j++) {
            this.A.set(j, 3, this.A.get(j, 1));
          }
        }

        for (let j = 1; j <= 258; j++) {
          this.A.set(j, 1, this.A.get(j, 3));
          this.A.set(j, 3, this.A.get(j, 2));
        }

        this._runMrdacowuCascade();
      }
    }

    // -------------------------------------------------------------------------
    // Item 10: Customize Program (MRCUSTOM)
    // -------------------------------------------------------------------------
    _startMrcustom() {
      this.loadMrparams();
      const steps = [["B$", "FACTORY NAME ON REPORT", this.B_str.trim()]];
      for (let j = 1; j <= 10; j++) {
        steps.push([`J$_${j}`, `LOST TIME CATEGORY NO. ${j}`, String(this.J_str.get(j)).trim()]);
      }
      this.H_str.set(1, "Gas, M. Cu. Ft.");
      for (let j = 2; j <= 12; j++) {
        steps.push([
          `H$_${j}`,
          `MATERIALS AND SUPPLIES CATEGORY NO. ${j}`,
          String(this.H_str.get(j)).trim(),
        ]);
      }
      steps.push(["H$_13", "TOTAL ROLL SURFACE OF ALL MILL ROLLS", String(this.H_str.get(13)).trim()]);
      steps.push([
        "H$_14",
        "BRIX DESIRED FOR REPORTING FINAL MOLASSES M&E/TON CANE",
        String(this.H_str.get(14)).trim(),
      ]);

      const iQuestions = [
        [1, "WILL ANALYSES BE AVERAGED BY CROP DAY (D) OR CANE WEIGHTING (W)"],
        [2, "WILL CRUSHER JUICE GLUCOSE BE REPORTED (Y OR N)"],
        [3, "WILL CRUSHER JUICE pH BE REPORTED (Y OR N)"],
        [4, "WILL MIXED JUICE GLUCOSE BE REPORTED (Y OR N)"],
        [5, "WILL MIXED JUICE pH BE REPORTED (Y OR N)"],
        [6, "WILL CLARIFIED JUICE GLUCOSE BE REPORTED (Y OR N)"],
        [7, "WILL CLARIFIED JUICE pH BE REPORTED (Y OR N)"],
        [8, "WILL SYRUP GLUCOSE BE REPORTED (Y OR N)"],
        [9, "WILL SYRUP pH BE REPORTED (Y OR N)"],
        [10, "WILL SUGAR MADE STARCH BE REPORTED (Y OR N)"],
        [11, "WILL SUGAR MADE DEXTRAN BE REPORTED (Y OR N)"],
        [12, "WILL FINAL MOLASSES MADE GLUCOSE BE REPORTED (Y OR N)"],
        [13, "WILL FINAL MOLASSES MADE ASH BE REPORTED (Y OR N)"],
        [14, "WILL FINAL MOLASSES MADE CLERGET BE REPORTED (Y OR N)"],
        [15, "WILL FINAL MOLASSES SHIPPED GLUCOSE BE REPORTED (Y OR N)"],
        [16, "WILL FINAL MOLASSES SHIPPED ASH BE REPORTED (Y OR N)"],
        [17, "WILL FINAL MOLASSES SHIPPED CLERGET BE REPORTED (Y OR N)"],
        [18, "WILL FILTRATE JUICE BRIX AND POL BE REPORTED (Y OR N)"],
        [19, "WILL TOP-OFF A STRIKES BRIX AND POL BE REPORTED (Y OR N)"],
        [20, "WILL EITHER B MAGMA OR C CYCLONES BE REPORTED (Y OR N)"],
        [21, "WILL FILTER CAKE MOISTURES BE REPORTED (Y OR N)"],
        [22, "WILL B MAGMA (Y) OR C CYCLONE (N) ANALYSES BE REPORTED"],
        [23, "DOES REPORT PRINTER HAVE EXPANDED PRINT CAPABILITY (Y OR N)"],
        [24, "WILL METERED IMBIBITION WATER BE REPORTED (Y OR N)"],
      ];
      for (const [idxQ, qText] of iQuestions) {
        steps.push([`I$_${idxQ}`, qText, String(this.I_str.get(idxQ)).trim()]);
      }

      steps.push([
        "H_36",
        "PRINTER SELECTION CODE: 0 = SYSTEM (215), 1 = TERMINAL (204)",
        String(Math.round(this.H_num.get(36))),
      ]);
      steps.push([
        "H_37",
        "CODE FOR DATA DISK (0=SAME, 1=310, 2=D11, 3=D12, 4=D13, ETC.)",
        String(Math.round(this.H_num.get(37))),
      ]);

      this.ctx.cust_steps = steps;
      this.ctx.cust_idx = 0;
      const [, lbl, cur] = steps[0];
      this.printCrt(`[Current: ${cur}]`);
      this.current_prompt = lbl;
      this.state = "MRCUSTOM_INPUT";
    }

    _handleMrcustomStep(rawInput) {
      const steps = this.ctx.cust_steps;
      let idx = this.ctx.cust_idx;
      const [key, , curDefault] = steps[idx];
      let valS = rawInput.trim();
      if (valS === "") valS = curDefault;

      if (key === "B$") {
        this.B_str = valS.slice(0, 64);
      } else if (key.startsWith("J$_")) {
        const jIdx = parseInt(key.split("_")[1], 10);
        this.J_str.set(jIdx, valS.slice(0, 16));
      } else if (key.startsWith("H$_")) {
        const hIdx = parseInt(key.split("_")[1], 10);
        if (hIdx === 13 || hIdx === 14) {
          const numV = Number(valS);
          if (valS === "" || !Number.isFinite(numV)) {
            this._triggerReenter("NOT NUMERIC, ENTER AGAIN");
            return;
          }
          this.H_str.set(hIdx, valS.slice(0, 20));
          this.H_num.set(16 + hIdx, numV);
        } else {
          this.H_str.set(hIdx, valS.slice(0, 20));
        }
      } else if (key.startsWith("I$_")) {
        const iIdx = parseInt(key.split("_")[1], 10);
        this.I_str.set(iIdx, valS.toUpperCase().slice(0, 16));
      } else if (key === "H_36") {
        const n = parseInt(valS, 10);
        if (isNaN(n)) {
          this._triggerReenter("ENTER 0 OR 1");
          return;
        }
        this.H_num.set(36, Number(n));
      } else if (key === "H_37") {
        const n = parseInt(valS, 10);
        if (isNaN(n)) {
          this._triggerReenter("ENTER DISK CODE 0..11");
          return;
        }
        this.H_num.set(37, Number(n));
      }

      idx += 1;
      this.ctx.cust_idx = idx;
      if (idx < steps.length) {
        const [, nextLbl, nextCur] = steps[idx];
        this.printCrt(`[Current: ${nextCur}]`);
        this.current_prompt = nextLbl;
      } else {
        this.H_num.set(1, String(this.I_str.get(1)).trim().toUpperCase() === "D" ? 1.0 : 0.0);
        for (let j = 2; j <= 23; j++) {
          this.H_num.set(j, String(this.I_str.get(j)).trim().toUpperCase() === "N" ? 0.0 : 1.0);
        }
        this.H_num.set(27, String(this.I_str.get(24)).trim().toUpperCase() === "N" ? 0.0 : 1.0);
        this.saveMrparams();
        this.showMainMenu();
        this.top_bar_row1 = "SAVED CUSTOMIZED PARAMETERS TO MRPARAMS";
      }
    }

    // -------------------------------------------------------------------------
    // Item 12: Print Blank Data Forms (MRBLANFM) & Item 17: Scratch Disk
    // -------------------------------------------------------------------------
    _handleMrblanfmChoice(valStr) {
      if (valStr === "1") {
        const pages = renderMrdatafm(this.B_str, this.J_str, this.H_str, this.H_num);
        this.addPrinterJob("BLANK DAILY REPORT DATA INPUT FORMS (MRDATAFM)", pages);
        this.showMainMenu();
        this.top_bar_row1 = "PRINTED DAILY REPORT DATA INPUT FORMS TO LINE PRINTER (215)";
      } else if (valStr === "2") {
        const pages = renderMrstokfm(this.B_str);
        this.addPrinterJob("BLANK STOCK REPORT DATA FORMS (MRSTOKFM)", pages);
        this.showMainMenu();
        this.top_bar_row1 = "PRINTED STOCK REPORT DATA FORMS TO LINE PRINTER (215)";
      } else {
        this._triggerReenter("ENTER 1 OR 2");
      }
    }

    _handleItem17Confirm(valStr) {
      const ans = valStr.toUpperCase();
      if (ans === "Y") {
        const dName = this.getDiskName();
        this.vfs.disks[dName] = {};
        this._saveVfsToStorage();
        this.showMainMenu();
        this.top_bar_row1 = `SCRATCHED ALL DATA FILES ON DISK ${dName}`;
      } else if (ans === "N") {
        this.showMainMenu();
      } else {
        this._triggerReenter("ENTER Y OR N");
      }
    }
  }

  return {
    OneBasedArray1D,
    OneBasedArray2D,
    safeDiv,
    brixDensityPoly5,
    brixLbsSolidsPerGal,
    brixDensityPoly4,
    wangParseMmddyy,
    wangNormalizeJulian,
    wangJulianToMmddyy,
    wangJulianDiff,
    zellerWeekdayIndex,
    formatPrintusingNumeric,
    formatPrintusing,
    getDailyInputPrompts,
    runWorkupOnA,
    runMrcalc,
    renderMrrepoprPage1,
    renderMrrepop2Page2,
    renderMrrepockPage3,
    renderMrcomppr,
    renderMrcustpr,
    renderMrdatafm,
    renderMrstokfm,
    renderMrdatapr,
    calculateAndRenderStock,
    getStMaryOct2015Params,
    getRacelandPlatterParams,
    getStMaryOct2015DailyInputs,
    MFRSession,
  };
});
