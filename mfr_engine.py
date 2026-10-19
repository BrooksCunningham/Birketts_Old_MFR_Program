"""
Core engine for Harold Birkett's Manufacturing Report Program (Version 2.1).
Faithfully implements the Wang 2200 / Niakwa BASIC-2 COMMON block, Julian date subroutines,
PRINTUSING formatting, virtual disk persistence, and all chained modules:
  MRSTART, MRDATA, MRDATAWU, MRDATACO, MRDACOWU, MRDATAPR, MRDATAP2,
  MRCALC, MRREPOPR, MRREPOP2, MRREPOCK, MRSTOCK, MRSTOCKC, MRSTOCKG,
  MRHELPC, MRHELPS, MRENCROP, MRCUSTOM, MRCUSTPR, MRBLANFM, MRDATAFM,
  MRSTOKFM, MRCOMPPR.
"""
from __future__ import annotations

import copy
import json
import math
import shutil
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple


ROOT_DIR = Path(__file__).resolve().parent
DATA_ROOT = ROOT_DIR / "data"


class OneBasedArray1D:
    """1-indexed 1D array emulating Wang BASIC-2 DIM X(N)."""

    def __init__(self, size: int, default: Any = 0.0):
        self.size = size
        self.default = default
        self.data: List[Any] = [copy.deepcopy(default) for _ in range(size + 1)]

    def __getitem__(self, idx: int) -> Any:
        idx = int(round(idx))
        if 0 <= idx <= self.size:
            return self.data[idx]
        return self.default

    def __setitem__(self, idx: int, val: Any) -> None:
        idx = int(round(idx))
        if 0 <= idx <= self.size:
            self.data[idx] = val

    def to_list(self) -> List[Any]:
        return self.data[1:]

    def from_list(self, vals: List[Any]) -> None:
        for i, v in enumerate(vals[: self.size], start=1):
            self.data[i] = v


class OneBasedArray2D:
    """1-indexed 2D array emulating Wang BASIC-2 DIM A(R, C)."""

    def __init__(self, rows: int, cols: int, default: Any = 0.0):
        self.rows = rows
        self.cols = cols
        self.default = default
        self.data: List[List[Any]] = [
            [copy.deepcopy(default) for _ in range(cols + 1)] for _ in range(rows + 1)
        ]

    def __getitem__(self, key: Tuple[int, int]) -> Any:
        r, c = int(round(key[0])), int(round(key[1]))
        if 0 <= r <= self.rows and 0 <= c <= self.cols:
            return self.data[r][c]
        return self.default

    def __setitem__(self, key: Tuple[int, int], val: Any) -> None:
        r, c = int(round(key[0])), int(round(key[1]))
        if 0 <= r <= self.rows and 0 <= c <= self.cols:
            self.data[r][c] = val

    def clear(self, max_row: Optional[int] = None) -> None:
        rmax = max_row if max_row is not None else self.rows
        for r in range(1, rmax + 1):
            for c in range(1, self.cols + 1):
                self.data[r][c] = copy.deepcopy(self.default)


def safe_div(num: float, den: float) -> float:
    """Wang BASIC-2 division with zero-denominator guard."""
    if abs(den) < 1e-12:
        return 0.0
    return num / den


def brix_density_poly_5(brix: float) -> float:
    """
    5th-order polynomial used in MRDATAWU, MRCALC (line 2740), MRENCROP, MRREPOCK:
    Returns pounds total weight per cubic foot of solution at given Brix.
    """
    k = float(brix)
    return (
        62.2514
        + 0.240778534 * k
        + 0.0007971907 * (k ** 2)
        + 0.00000395521 * (k ** 3)
        - 1.247356e-8 * (k ** 4)
        - 1.94891e-11 * (k ** 5)
    )


def brix_lbs_solids_per_gal(brix: float) -> float:
    """MRCALC subroutine 2740-2750: Lbs Brix solids per gallon from Brix."""
    if abs(brix) < 1e-12:
        return 0.0
    k1 = brix_density_poly_5(brix)
    return (k1 / 7.48) * (brix / 100.0)


def brix_density_poly_4(brix: float) -> float:
    """4th-order polynomial used in MRSTOCKC (line 700) and MRSTOCKG (line 580)."""
    b = float(brix)
    return (
        62.2511
        + 0.24081 * b
        + 0.0007902404 * (b ** 2)
        + 0.00000423954 * (b ** 3)
        - 1.657193e-8 * (b ** 4)
    )


# ==============================================================================
# Wang 2200 BASIC-2 Date Conversion Subroutines (DEFFN'221 - DEFFN'225)
# ==============================================================================

def wang_parse_mmddyy(date_str: str) -> Optional[Tuple[int, int, int, str, int]]:
    """
    Emulates DEFFN'221(U9$):
    Parses MM/DD/YY (or M/D/YY), validates calendar date, and returns:
    (month, day, year_2d, formatted_mm_dd_yy, julian_yyddd)
    """
    s = date_str.strip()
    parts = s.split("/")
    if len(parts) != 3:
        return None
    try:
        u0 = int(parts[0].strip())
        u6 = int(parts[1].strip())
        u9 = int(parts[2].strip())
    except ValueError:
        return None

    if u0 < 1 or u0 > 12 or u9 < 0 or u9 > 99:
        return None

    days_in_months = [31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31]
    if u9 % 4 == 0:
        days_in_months[1] = 29

    if u6 < 1 or u6 > days_in_months[u0 - 1]:
        return None

    formatted = f"{u0:2d}/{u6:2d}/{u9:2d}"
    # Note: on scanned outputs, leading zero is printed when typed or formatted, e.g. 10/06/15
    # In Wang BASIC-2 DEFFN'223, XOR HEX(00001F00001F0000) turns '0' (0x30) into '/' (0x2F)
    # on a zero-padded 8-digit integer MM0DD0YY, preserving leading zeros!
    formatted_zero = f"{u0:02d}/{u6:02d}/{u9:02d}"
    day_of_year = sum(days_in_months[: u0 - 1]) + u6
    julian = u9 * 1000 + day_of_year
    return (u0, u6, u9, formatted_zero, julian)


def wang_normalize_julian(q9: int) -> int:
    """Emulates DEFFN'224(Q9): Normalizes a YYDDD Julian date across year/day boundaries."""
    yr = int(q9 // 1000)
    ddd = q9 - yr * 1000
    u0 = int(365.25 * (yr - 1)) + ddd
    new_yr = int(u0 / 365.25)
    diff = u0 - int(365.25 * new_yr)
    sgn = 1 if diff > 0 else (-1 if diff < 0 else 0)
    new_yr = new_yr - 1 + sgn
    new_ddd = u0 - int(365.25 * new_yr)
    return (new_yr + 1) * 1000 + new_ddd


def wang_julian_to_mmddyy(u9: int) -> Tuple[str, int]:
    """Emulates DEFFN'223(U9): Normalizes YYDDD and formats as MM/DD/YY."""
    u9 = wang_normalize_julian(int(round(u9)))
    q9 = int(u9 // 1000)
    ddd = int(u9 - q9 * 1000)
    days_in_months = [31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31]
    if q9 % 4 == 0:
        days_in_months[1] = 29
    cum = 0
    u6 = 1
    u0 = ddd
    for m_idx, dim in enumerate(days_in_months, start=1):
        if cum + dim >= ddd:
            u6 = m_idx
            u0 = ddd - cum
            break
        cum += dim
    return f"{u6:02d}/{u0:02d}/{q9 % 100:02d}", u9


def wang_julian_diff(u0_start: int, u6_end: int) -> int:
    """Emulates DEFFN'225(U0, U6): Returns number of days U3 = U6 - U0."""
    u0 = int(round(u0_start))
    u6 = int(round(u6_end))
    yr6 = int(u6 // 1000)
    ddd6 = u6 - yr6 * 1000
    yr0 = int(u0 // 1000)
    ddd0 = u0 - yr0 * 1000
    days6 = int(365.25 * (yr6 - 1)) + ddd6
    days0 = int(365.25 * (yr0 - 1)) + ddd0
    u3 = days6 - days0
    if u3 < -18000:
        u3 += 36525
    return u3


def zeller_weekday_index(mm_dd_yy: str) -> int:
    """
    Emulates MRREPOPR lines 0060-0140:
    Returns N in 0..6 where K$(N+1) is SUNDAY(1)..SATURDAY(7).
    """
    try:
        m = int(mm_dd_yy[0:2])
        d = int(mm_dd_yy[3:5])
        y = int(mm_dd_yy[6:8])
    except ValueError:
        return 0
    if y < 50:
        y += 100
    y += 1900
    if m <= 2:
        m += 12
        y -= 1
    n = d + int((13 * m + 3) / 5) + int(5 * y / 4) - int(y / 100) + int(y / 400) + 1
    n = n - int(n / 7) * 7
    return n


# ==============================================================================
# Wang 2200 BASIC-2 PRINTUSING Formatter
# ==============================================================================

def format_printusing_numeric(spec: str, val: float) -> str:
    """
    Formats a numeric value according to a Wang BASIC-2 PRINTUSING numeric mask,
    such as '-#,###,###.##', '-###.##', '##.##', '-###', etc.
    """
    width = len(spec)
    has_sign = spec.startswith("-") or spec.startswith("+")
    has_commas = "," in spec
    if "." in spec:
        dec_part = spec.split(".")[1]
        decimals = len(dec_part)
    else:
        decimals = 0

    if math.isnan(val) or math.isinf(val):
        val = 0.0

    # Wang 2200 BASIC-2 PRINTUSING truncates BCD mantissa digits at the last '#' position
    is_neg = val < -1e-12
    abs_val = abs(val)
    factor = 10 ** decimals
    rounded_int = int(math.floor(abs_val * factor + 1e-7))
    if rounded_int == 0:
        is_neg = False

    if decimals > 0:
        int_part = rounded_int // factor
        frac_part = rounded_int % factor
        int_str = f"{int_part:,}" if has_commas else f"{int_part}"
        num_str = f"{int_str}.{frac_part:0{decimals}d}"
    else:
        int_part = rounded_int
        num_str = f"{int_part:,}" if has_commas else f"{int_part}"

    if is_neg:
        if has_sign:
            num_str = "-" + num_str
        else:
            # Overflow / negative without sign position fills with '#'
            return "#" * width

    if len(num_str) > width:
        # Try without commas if Wang BASIC-2 strips commas before overflowing, else fill with '#'
        return spec.replace("-", "#")

    return num_str.rjust(width)


def format_printusing(image: str, args: List[Any]) -> str:
    """
    Emulates Wang BASIC-2 PRINTUSING line formatting.
    Matches '#' / '-#' fields in `image` sequentially with `args`.
    """
    if image.startswith("%"):
        image = image[1:]

    out = []
    i = 0
    n = len(image)
    arg_idx = 0

    while i < n:
        ch = image[i]
        # Check for numeric field starting with '-' followed by '#' or '.'
        if ch == "-" and i + 1 < n and image[i + 1] in ("#", "."):
            j = i + 1
            while j < n and image[j] in ("#", ",", "."):
                j += 1
            spec = image[i:j]
            val = args[arg_idx] if arg_idx < len(args) else 0.0
            arg_idx += 1
            if isinstance(val, str):
                out.append(val[: len(spec)].ljust(len(spec)))
            else:
                out.append(format_printusing_numeric(spec, float(val)))
            i = j
        elif ch == "#":
            # Could be string field (all '#') or unsigned numeric field ('##.##')
            j = i
            while j < n and image[j] in ("#", ",", "."):
                j += 1
            spec = image[i:j]
            val = args[arg_idx] if arg_idx < len(args) else ""
            arg_idx += 1
            if isinstance(val, str) and "." not in spec and "," not in spec:
                w = len(spec)
                out.append(val[:w].ljust(w))
            else:
                num_val = float(val) if not isinstance(val, str) else 0.0
                out.append(format_printusing_numeric(spec, num_val))
            i = j
        else:
            out.append(ch)
            i += 1

    return "".join(out).rstrip()


# ==============================================================================
# Daily Input Item Definitions (Items 2..108, 246, 251..254)
# ==============================================================================

def get_daily_input_prompts(J_str: OneBasedArray1D, H_str: OneBasedArray1D, H_num: OneBasedArray1D) -> List[Tuple[int, str, Optional[str]]]:
    """
    Returns ordered list of (item_index_in_A, prompt_label, pre_header_line)
    matching MRDATA (lines 0190-1754) and MRDATACO (lines 0260-4018),
    respecting the suppression flags H(2)..H(22) and H(27).
    """
    items: List[Tuple[int, str, Optional[str]]] = []
    items.append((2, " 2   LBS TRS PURCHASED", None))
    for k in range(1, 11):
        items.append((k + 2, f"{k+2:2d}   HOURS LOST", J_str[k]))
    items.append((13, "13   TOTAL HOURS AVAILABLE FOR GRINDING TODAY", None))
    for k in range(1, 13):
        items.append((k + 13, f"{k+13:2d}   QUANTITY USED", H_str[k]))

    items.append((26, "26   CRUSHER JUICE BRIX", None))
    items.append((27, "27   CRUSHER JUICE POL", None))
    if H_num[2] != 0:
        items.append((28, "28   CRUSHER JUICE GLUCOSE", None))
    if H_num[3] != 0:
        items.append((29, "29   CRUSHER JUICE pH", None))

    items.append((30, "30   MIXED JUICE BRIX", None))
    items.append((31, "31   MIXED JUICE POL", None))
    if H_num[4] != 0:
        items.append((32, "32   MIXED JUICE GLUCOSE", None))
    if H_num[5] != 0:
        items.append((33, "33   MIXED JUICE pH", None))

    items.append((34, "34   LAST ROLL JUICE BRIX", None))
    items.append((35, "35   LAST ROLL JUICE POL", None))
    items.append((36, "36   CLARIFIED JUICE BRIX", None))
    items.append((37, "37   CLARIFIED JUICE POL", None))
    if H_num[6] != 0:
        items.append((38, "38   CLARIFIED JUICE GLUCOSE", None))
    if H_num[7] != 0:
        items.append((39, "39   CLARIFIED JUICE pH", None))

    if H_num[18] != 0:
        items.append((40, "40   FILTRATE JUICE BRIX", None))
        items.append((41, "41   FILTRATE JUICE POL", None))

    items.append((42, "42   SYRUP BRIX", None))
    items.append((43, "43   SYRUP POL", None))
    if H_num[8] != 0:
        items.append((44, "44   SYRUP GLUCOSE", None))
    if H_num[9] != 0:
        items.append((45, "45   SYRUP pH", None))

    items.append((46, "46   A MASSECUITE BRIX", None))
    items.append((47, "47   A MASSECUITE POL", None))
    if H_num[19] != 0:
        items.append((48, "48   TOP-OFF A MASSECUITE BRIX", None))
        items.append((49, "49   TOP-OFF A MASSECUITE POL", None))

    items.append((50, "50   B MASSECUITE BRIX", None))
    items.append((51, "51   B MASSECUITE POL", None))
    items.append((52, "52   C MASSECUITE BRIX", None))
    items.append((53, "53   C MASSECUITE POL", None))
    items.append((54, "54   A MOLASSES BRIX", None))
    items.append((55, "55   A MOLASSES POL", None))
    if H_num[19] != 0:
        items.append((56, "56   TOP-OFF A MOLASSES BRIX", None))
        items.append((57, "57   TOP-OFF A MOLASSES POL", None))

    items.append((58, "58   B MOLASSES BRIX", None))
    items.append((59, "59   B MOLASSES POL", None))
    items.append((60, "60   GRAIN BRIX", None))
    items.append((61, "61   GRAIN POL", None))
    items.append((62, "62   C MAGMA BRIX", None))
    items.append((63, "63   C MAGMA POL", None))

    if H_num[20] != 0:
        if H_num[22] != 0:
            items.append((64, "64   B MAGMA BRIX", None))
            items.append((65, "65   B MAGMA POL", None))
        else:
            items.append((64, "64   C CYCLONE BRIX", None))
            items.append((65, "65   C CYCLONE POL", None))

    items.append((66, "66   CU. FT. OF A MASSECUITE MADE", None))
    if H_num[19] != 0:
        items.append((67, "67   CU. FT. OF TOP-OFF A MASSECUITE MADE", None))
    items.append((68, "68   CU. FT. OF B MASSECUITE MADE", None))
    items.append((69, "69   CU. FT. OF C MASSECUITE MADE", None))
    items.append((70, "70   MOISTURE % SUGAR MADE", None))
    items.append((71, "71   POL OF SUGAR MADE", None))
    if H_num[10] != 0:
        items.append((72, "72   STARCH SUGAR MADE", None))
    if H_num[11] != 0:
        items.append((73, "73   DEXTRAN SUGAR MADE", None))

    items.append((74, "74   FINAL MOLASSES MADE BRIX", None))
    items.append((75, "75   FINAL MOLASSES MADE POL", None))
    if H_num[12] != 0:
        items.append((76, "76   FINAL MOLASSES MADE % GLUCOSE", None))
    if H_num[13] != 0:
        items.append((77, "77   FINAL MOLASSES MADE % ASH", None))
    if H_num[14] != 0:
        items.append((78, "78   FINAL MOLASSES MADE CLERGET", None))

    items.append((79, "79   FINAL MOLASSES SHIPPED BRIX", None))
    items.append((80, "80   FINAL MOLASSES SHIPPED POL", None))
    if H_num[15] != 0:
        items.append((81, "81   FINAL MOLASSES SHIPPED % GLUCOSE", None))
    if H_num[16] != 0:
        items.append((82, "82   FINAL MOLASSES SHIPPED % ASH", None))
    if H_num[17] != 0:
        items.append((83, "83   FINAL MOLASSES SHIPPED CLERGET", None))

    items.append((84, "84   POL % FILTER CAKE", None))
    if H_num[21] != 0:
        items.append((85, "85   MOISTURE % FILTER CAKE", None))

    items.append((86, "86   POL % BAGASSE", None))
    items.append((87, "87   MOISTURE % BAGASSE", None))
    items.append((88, "88   TONS CANE PURCHASED", None))
    items.append((91, "91   TONS CANE GROUND", None))
    items.append((92, "92   TONS MIXED JUICE", None))
    items.append((93, "93   TONS IMBIBITION WATER", None))
    items.append((94, "94   TONS FILTER CAKE MADE", None))
    items.append((95, "95   LBS SUGAR MADE", None))
    items.append((96, "96   GALLONS FINAL MOLASSES MADE", None))
    items.append((97, "97   LBS SUGAR SHIPPED", None))
    items.append((98, "98   GALLONS FINAL MOLASSES SHIPPED", None))
    items.append((99, "99   CORE LAB CANE, % POL", None))
    items.append((100, "100  CORE LAB CANE, % BRIX", None))
    items.append((101, "101  CORE LAB CANE, % FIBER", None))
    items.append((102, "102  RAINFALL, INCHES", None))
    items.append((103, "103  MAXIMUM TEMPERATURE, DEG. F", None))
    items.append((104, "104  MINIMUM TEMPERATURE, DEG. F", None))
    items.append((105, "105  LBS SUGAR BRIX IN PROCESS", None))
    items.append((106, "106  LBS SUGAR POL IN PROCESS", None))
    items.append((107, "107  LBS FINAL MOLASSES BRIX IN PROCESS", None))
    items.append((108, "108  LBS FINAL MOLASSES POL IN PROCESS", None))

    if H_num[27] != 0:
        items.append((246, "246  TONS OF METERED IMBIBITON WATER", None))
        items.append((251, "251  LBS SUGAR IN WAREHOUSE # 1", None))
        items.append((252, "252  LBS SUGAR IN WAREHOUSE # 2", None))
        items.append((253, "253  LBS SUGAR IN WAREHOUSE # 3", None))
        items.append((254, "254  LBS SUGAR IN WAREHOUSE # 4", None))

    return items


# ==============================================================================
# Preliminary Workup (MRDATAWU & MRDACOWU)
# ==============================================================================

def run_workup_on_A(A: OneBasedArray2D, H_num: OneBasedArray1D, is_correction: bool = False) -> None:
    """
    Executes the exact equations of MRDATAWU (lines 0030-1645) and MRDACOWU (lines 0030-1645)
    given A(J, 1) [Today's inputs] and A(J, 3) [Previous day's To-Date X()].
    Populates A(J, 2) [Today's To-Date].
    """
    A[247, 1] = A[246, 1]
    if is_correction:
        A[255, 1] = A[251, 1]
        A[256, 1] = A[252, 1]
        A[257, 1] = A[253, 1]
        A[258, 1] = A[254, 1]

    # Lost time filling routine (0050-0090)
    for j in range(1, 11):
        A[109 + j, 1] = A[j + 2, 1]
    A[120, 1] = sum(A[109 + j, 1] for j in range(1, 11))
    A[121, 1] = A[13, 1]

    # Material and supplies filling routine (0110-0130)
    for j in range(1, 13):
        A[121 + j, 1] = A[13 + j, 1]

    # Weighting factor (0140-0180)
    if H_num[1] == 0:
        A[109, 1] = A[91, 1]
    else:
        A[109, 1] = 1.0

    # Data workup (0200-0700)
    k = A[109, 1]
    # Clear weighted slots first in case a value was changed to 0 during correction
    for idx in range(134, 188):
        A[idx, 1] = 0.0

    if A[26, 1] != 0:
        A[134, 1] = k
        A[148, 1] = k * A[26, 1]
        A[149, 1] = k * A[27, 1]
    if A[28, 1] != 0:
        A[135, 1] = k
        A[150, 1] = k * A[28, 1]
    if A[29, 1] != 0:
        A[136, 1] = k
        A[151, 1] = k * A[29, 1]
    if A[34, 1] != 0:
        A[143, 1] = k
        A[160, 1] = k * A[34, 1]
        A[161, 1] = k * A[35, 1]
    if A[36, 1] != 0:
        A[137, 1] = k
        A[152, 1] = k * A[36, 1]
        A[153, 1] = k * A[37, 1]
    if A[38, 1] != 0:
        A[138, 1] = k
        A[154, 1] = k * A[38, 1]
    if A[39, 1] != 0:
        A[139, 1] = k
        A[155, 1] = k * A[39, 1]
    if A[42, 1] != 0:
        A[140, 1] = k
        A[156, 1] = k * A[42, 1]
        A[157, 1] = k * A[43, 1]
    if A[44, 1] != 0:
        A[141, 1] = k
        A[158, 1] = k * A[44, 1]
    if A[45, 1] != 0:
        A[142, 1] = k
        A[159, 1] = k * A[45, 1]
    if A[40, 1] != 0:
        A[144, 1] = k
        A[162, 1] = k * A[40, 1]
        A[163, 1] = k * A[41, 1]
    if A[60, 1] != 0:
        A[145, 1] = k
        A[164, 1] = k * A[60, 1]
        A[165, 1] = k * A[61, 1]
    if A[62, 1] != 0:
        A[146, 1] = k
        A[166, 1] = k * A[62, 1]
        A[167, 1] = k * A[63, 1]
    if A[64, 1] != 0:
        A[147, 1] = k
        A[168, 1] = k * A[64, 1]
        A[169, 1] = k * A[65, 1]

    # Weighted cubic feet routine (0720-0880)
    for j in range(1, 5):
        A[183 + j, 1] = A[65 + j, 1]
    A[170, 1] = A[184, 1] * A[46, 1]
    A[171, 1] = A[184, 1] * A[47, 1]
    A[172, 1] = A[185, 1] * A[48, 1]
    A[173, 1] = A[185, 1] * A[49, 1]
    A[174, 1] = A[186, 1] * A[50, 1]
    A[175, 1] = A[186, 1] * A[51, 1]
    A[176, 1] = A[187, 1] * A[52, 1]
    A[177, 1] = A[187, 1] * A[53, 1]
    A[178, 1] = A[184, 1] * A[54, 1]
    A[179, 1] = A[184, 1] * A[55, 1]
    A[180, 1] = A[185, 1] * A[56, 1]
    A[181, 1] = A[185, 1] * A[57, 1]
    A[182, 1] = A[186, 1] * A[58, 1]
    A[183, 1] = A[186, 1] * A[59, 1]

    for j in range(1, 4):
        A[187 + j, 1] = A[87 + j, 1]
    A[191, 1] = A[91, 1]
    A[195, 1] = A[92, 1]
    A[200, 1] = A[93, 1]
    A[201, 1] = A[94, 1]

    for j in range(1, 5):
        A[195 + j, 1] = A[29 + j, 1] * A[195, 1] / 100.0
    A[199, 1] = A[199, 1] * 100.0
    A[202, 1] = A[201, 1] * A[84, 1] / 100.0
    A[203, 1] = A[201, 1] * A[85, 1] / 100.0
    A[204, 1] = A[95, 1] / 2000.0
    A[205, 1] = A[204, 1] * (1.0 - A[70, 1] / 100.0)
    for j in range(1, 4):
        A[205 + j, 1] = A[204, 1] * A[70 + j, 1] / 100.0
    A[209, 1] = A[205, 1] + A[105, 1] / 2000.0
    A[210, 1] = A[206, 1] + A[106, 1] / 2000.0

    # Final Molasses Made (1090-1140)
    A[211, 1] = A[96, 1]
    brix_fm_made = A[74, 1]
    A[212, 1] = A[96, 1] * brix_density_poly_5(brix_fm_made) / 7.48 / 2000.0
    for j in range(1, 6):
        A[212 + j, 1] = A[212, 1] * A[73 + j, 1] / 100.0

    # Final Molasses Shipped (1150-1200)
    A[220, 1] = A[98, 1]
    brix_fm_ship = A[79, 1]
    A[221, 1] = A[98, 1] * brix_density_poly_5(brix_fm_ship) / 7.48 / 2000.0
    for j in range(1, 6):
        A[221 + j, 1] = A[221, 1] * A[78 + j, 1] / 100.0

    # Bagasse & Cane Balance (1210-1400)
    A[227, 1] = A[91, 1] + A[93, 1] - A[92, 1]
    A[229, 1] = A[227, 1] * A[86, 1] / 100.0
    A[228, 1] = safe_div(A[229, 1] * A[34, 1], A[35, 1])
    A[231, 1] = A[227, 1] * A[87, 1] / 100.0
    A[230, 1] = A[227, 1] - A[231, 1] - A[228, 1]

    A[218, 1] = A[213, 1] + A[107, 1] / 2000.0
    A[219, 1] = A[214, 1] + A[108, 1] / 2000.0
    A[235, 1] = A[2, 1]
    for j in range(1, 4):
        A[235 + j, 1] = A[188, 1] * A[98 + j, 1] / 100.0

    A[239, 1] = A[102, 1]
    A[240, 1] = A[103, 1]
    A[241, 1] = A[104, 1]
    A[242, 1] = A[97, 1]

    A[192, 1] = A[228, 1] + A[196, 1]
    A[193, 1] = A[229, 1] + A[197, 1]
    A[194, 1] = A[230, 1]

    A[232, 1] = A[195, 1] - safe_div(
        A[195, 1] * (A[26, 1] * 0.97 - A[30, 1]), A[26, 1] * 0.97
    )
    A[233, 1] = A[232, 1] * A[26, 1] * 0.97 / 100.0
    A[234, 1] = safe_div(A[233, 1] * A[31, 1], A[30, 1])

    # Filling in Todate Column A(J, 2) (1410-1645)
    for j in range(1, 110):
        A[j, 2] = A[j, 1]
    for j in range(110, 240):
        A[j, 2] = A[j, 1] + A[j, 3]

    A[255, 1] = A[251, 1]
    A[256, 1] = A[252, 1]
    A[257, 1] = A[253, 1]
    A[258, 1] = A[254, 1]
    A[251, 2] = A[251, 1]
    A[252, 2] = A[252, 1]
    A[253, 2] = A[253, 1]
    A[254, 2] = A[254, 1]
    for j in range(255, 259):
        A[j, 2] = A[j, 1] + A[j, 3]

    A[209, 2] = A[209, 1] + A[205, 3]
    A[210, 2] = A[210, 1] + A[206, 3]
    A[218, 2] = A[218, 1] + A[213, 3]
    A[219, 2] = A[219, 1] + A[214, 3]

    A[244, 1] = A[103, 1]
    A[245, 1] = A[104, 1]
    A[240, 2] = max(A[240, 1], A[240, 3])
    if A[1, 3] == 0:
        A[241, 2] = A[241, 1]
    else:
        A[241, 2] = min(A[241, 1], A[241, 3])

    A[242, 2] = A[242, 1] + A[242, 3]
    A[244, 2] = A[244, 1] + A[244, 3]
    A[245, 2] = A[245, 1] + A[245, 3]
    A[247, 2] = A[247, 1] + A[247, 3]
    A[246, 2] = A[246, 1]
    A[243, 2] = A[243, 1]
    A[248, 1] = A[188, 2] - A[191, 2]
    A[248, 2] = A[248, 1] + A[248, 3]


# ==============================================================================
# MRCALC: Calculation Module for Daily & Weekly Reports
# ==============================================================================

def run_mrcalc(
    A: OneBasedArray2D,
    B: OneBasedArray2D,
    C: OneBasedArray2D,
    D: OneBasedArray2D,
    E: OneBasedArray2D,
    F: OneBasedArray2D,
    G: OneBasedArray2D,
    H_num: OneBasedArray1D,
    day_files_range: List[List[float]],
) -> None:
    """
    Executes MRCALC (lines 0230-2960) assuming A(J, 2) is loaded from end day H(26)
    and A(J, 3) is loaded from baseline day H(27).
    `day_files_range` contains the X(1..258) arrays for days max(1, H(27)+1)..H(26)
    for computing max/min temperatures across Weekly runs (lines 2770-2960).
    """
    B.clear()
    C.clear()
    D.clear()
    E.clear()
    F.clear()
    G.clear()

    for j in range(1, 259):
        A[j, 1] = A[j, 2] - A[j, 3]

    # Calculating Mill Data Block (0310-0605)
    for j in (1, 2):
        B[1, j] = A[1, j]
        B[2, j] = A[121, j] - A[120, j]
        B[3, j] = A[120, j]
        B[4, j] = safe_div(A[120, j] * 100.0, A[121, j])
        B[5, j] = A[191, j]
        B[6, j] = A[188, j]
        B[8, j] = safe_div(A[191, j], A[121, j] - A[120, j])
        B[9, j] = safe_div(A[191, j] * 24.0, A[121, j])
        B[10, j] = B[8, j] * 24.0
        B[11, j] = safe_div(A[194, j], A[121, j] - A[120, j])
        B[12, j] = safe_div(B[11, j], H_num[29])
        B[13, j] = safe_div(A[197, j] * 100.0, A[193, j])
        B[15, j] = safe_div(A[195, j] * 100.0, A[191, j])
        B[16, j] = safe_div(
            A[196, j] * 100.0 * (A[191, j] - A[194, j]), A[191, j] * A[192, j]
        )
        B[18, j] = safe_div(A[200, j] * 100.0, A[191, j])
        B[19, j] = safe_div(A[200, j] * 100.0, A[194, j])
        B[20, j] = B[15, j] - B[16, j]
        B[21, j] = safe_div(A[193, j] * 100.0, A[191, j])
        B[22, j] = safe_div(A[194, j] * 100.0, A[191, j])
        B[23, j] = safe_div(A[229, j] * 100.0, A[227, j])
        B[24, j] = safe_div(A[231, j] * 100.0, A[227, j])
        B[25, j] = safe_div(A[230, j] * 100.0, A[227, j])
        B[26, j] = safe_div(A[227, j] * 100.0, A[191, j])
        B[27, j] = safe_div(A[229, j] * 100.0, A[230, j])
        B[28, j] = safe_div(A[247, j] * 100.0, A[191, j])
        B[17, j] = safe_div((100.0 - B[13, j]) * (100.0 - B[22, j]), B[22, j])
        B[14, j] = 100.0 - B[17, j] / 7.0

    B[7, 1] = A[188, 2] - A[191, 2]
    B[7, 2] = safe_div(A[248, 2], A[1, 2])

    # Calculating Production Data Block (0610-0950)
    for j in (1, 2):
        B[1, j + 2] = A[206, j] * 2000.0 / 0.96
        B[2, j + 2] = (A[210, j] - A[206, j]) * 2000.0 / 0.96
        B[3, j + 2] = A[210, j] * 2000.0 / 0.96
        B[4, j + 2] = A[204, j] * 2000.0
        B[5, j + 2] = safe_div(
            (A[210, j] - A[206, j]) * 2000.0 * A[204, j], A[206, j]
        )
        B[6, j + 2] = safe_div(A[210, j] * 2000.0 * A[204, j], A[206, j])

        pol_pct_sug = safe_div(A[206, j] * 100.0, A[204, j])
        rv_factor = ((pol_pct_sug - 92.0) * 1.75 + 93.0) / 100.0
        B[7, j + 2] = B[6, j + 2] * rv_factor
        B[8, j + 2] = safe_div(B[7, j + 2], A[191, j])
        B[9, j + 2] = safe_div(B[8, j + 2], 20.0)
        B[10, j + 2] = safe_div(A[210, j] * 2000.0 / 0.96, A[191, j])
        B[11, j + 2] = A[235, j]
        B[12, j + 2] = safe_div(A[235, j], A[188, j])
        B[13, j + 2] = safe_div(
            B[10, j + 2] * 100.0 * A[188, j], A[235, j]
        )
        B[14, j + 2] = A[211, j]

        k1 = brix_lbs_solids_per_gal(H_num[30])
        B[15, j + 2] = safe_div((A[218, j] - A[213, j]) * 2000.0, k1)
        B[16, j + 2] = safe_div(A[218, j] * 2000.0, k1)
        B[17, j + 2] = safe_div(B[16, j + 2], A[191, j])
        B[18, j + 2] = safe_div(A[206, j] * 100.0, A[204, j])
        B[19, j + 2] = A[201, j]
        B[20, j + 2] = safe_div(A[201, j] * 2000.0, A[191, j])
        denom_bhe = 1.4 - 0.4 * safe_div(A[196, j], A[197, j])
        B[21, j + 2] = safe_div(A[210, j] * 100.0, A[197, j] * denom_bhe)
        B[23, j + 2] = A[239, j]
        B[24, j + 2] = safe_div(A[236, j] * 100.0, A[188, j])
        B[25, j + 2] = safe_div(A[237, j] * 100.0, A[188, j])
        B[26, j + 2] = safe_div(A[238, j] * 100.0, A[188, j])
        B[27, j + 2] = safe_div(B[8, j + 2] * A[188, j], A[190, j])
        B[28, j + 2] = safe_div(B[8, j + 2] * A[188, j], A[189, j])
        B[27, 3] = safe_div(
            B[7, 3],
            safe_div(A[191, 2] * A[190, 2], A[188, 2])
            - safe_div(A[191, 3] * A[190, 3], A[188, 3]),
        )
        B[28, 3] = safe_div(
            B[7, 3],
            safe_div(A[191, 2] * A[189, 2], A[188, 2])
            - safe_div(A[191, 3] * A[189, 3], A[188, 3]),
        )

    # Massecuite Tabulation Block (0980-1110)
    C[3, 1] = A[184, 1]
    C[3, 3] = A[184, 2]
    C[4, 1] = A[185, 1]
    C[4, 3] = A[185, 2]
    C[5, 1] = A[186, 1]
    C[5, 3] = A[186, 2]
    C[6, 1] = A[187, 1]
    C[6, 3] = A[187, 2]
    C[8, 1] = C[3, 1] + C[4, 1] + C[5, 1] + C[6, 1]
    C[8, 3] = C[3, 3] + C[4, 3] + C[5, 3] + C[6, 3]
    for j in range(3, 9):
        C[j, 2] = safe_div(C[j, 1], A[191, 1])
        C[j, 4] = safe_div(C[j, 3], A[191, 2])

    # Products Shipped Block (1120-1380)
    C[1, 5] = A[242, 1]
    C[1, 6] = A[242, 2]
    C[1, 7] = A[204, 2] * 2000.0 - A[242, 2]

    k = safe_div(A[213, 1] * 100.0, A[212, 1])
    k1 = brix_lbs_solids_per_gal(k)
    C[2, 5] = safe_div(A[222, 1] * 2000.0, k1)

    k = safe_div(A[213, 2] * 100.0, A[212, 2])
    k1 = brix_lbs_solids_per_gal(k)
    C[2, 6] = safe_div(A[222, 2] * 2000.0, k1)
    C[2, 7] = B[14, 4] - C[2, 6]

    k = safe_div(A[222, 1] * 100.0, A[221, 1])
    k1 = brix_lbs_solids_per_gal(k)
    C[3, 5] = safe_div(A[222, 1] * 2000.0, k1)

    k = safe_div(A[222, 2] * 100.0, A[221, 2])
    k1 = brix_lbs_solids_per_gal(k)
    C[3, 6] = safe_div(A[222, 2] * 2000.0, k1)
    C[3, 7] = safe_div((A[213, 2] - A[222, 2]) * 2000.0, k1)

    for j in (1, 2):
        C[4, 4 + j] = safe_div((A[195, j] - A[232, j]) * 100.0, A[232, j])
        C[4 + j, 5] = safe_div(A[233, j] * 100.0, A[232, j])
        C[4 + j, 6] = safe_div(A[234, j] * 100.0, A[232, j])
        C[4 + j, 7] = safe_div(A[234, j] * 100.0, A[233, j])
        C[7, 4 + j] = A[190, j]
        C[8, 4 + j] = A[189, j]

    # Pol Account Block Array D (1390-1590)
    for j in (1, 2):
        D[1, j] = A[229, j]
        D[2, j] = A[219, j]
        D[3, j] = A[202, j]
        D[6, j] = A[210, j]
        D[7, j] = A[197, j]
        D[8, j] = A[193, j]
        D[4, j] = D[7, j] - D[6, j] - D[2, j] - D[3, j]
        D[5, j] = D[1, j] + D[2, j] + D[3, j] + D[4, j]
        D[9, j] = D[7, j] - D[3, j]
        D[10, j] = D[2, j] + D[3, j] + D[6, j]

    for j in range(1, 11):
        D[j, 3] = safe_div(D[j, 1] * 100.0, D[7, 1])
        D[j, 4] = safe_div(D[j, 2] * 100.0, D[7, 2])
        D[j, 5] = safe_div(D[j, 1] * 100.0, A[191, 1])
        D[j, 6] = safe_div(D[j, 2] * 100.0, A[191, 2])
        D[5, 3] = D[2, 3] + D[3, 3] + D[4, 3]
        D[5, 4] = D[2, 4] + D[3, 4] + D[4, 4]

    # Analyses Block Array E (1600-2180)
    for j in (1, 2):
        off = (j - 1) * 6
        E[1, 1 + off] = safe_div(A[237, j] * 100.0, A[188, j] - A[238, j])
        E[1, 2 + off] = safe_div(A[236, j] * 100.0, A[188, j] - A[238, j])
        E[2, 1 + off] = safe_div(A[148, j], A[134, j])
        E[2, 2 + off] = safe_div(A[149, j], A[134, j])
        E[2, 4 + off] = safe_div(A[150, j], A[135, j])
        E[2, 5 + off] = safe_div(E[2, 4 + off] * 100.0, E[2, 2 + off])
        E[2, 6 + off] = safe_div(A[151, j], A[136, j])
        E[3, 1 + off] = safe_div(A[192, j] * 100.0, A[191, j] - A[194, j])
        E[3, 2 + off] = safe_div(A[193, j] * 100.0, A[191, j] - A[194, j])
        E[4, 1 + off] = safe_div(A[196, j] * 100.0, A[195, j])
        E[4, 2 + off] = safe_div(A[197, j] * 100.0, A[195, j])
        E[4, 4 + off] = safe_div(A[198, j] * 100.0, A[195, j])
        E[4, 5 + off] = safe_div(A[198, j] * 100.0, A[197, j])
        E[4, 6 + off] = safe_div(A[199, j], A[195, j])
        E[5, 1 + off] = safe_div(A[160, j], A[143, j])
        E[5, 2 + off] = safe_div(A[161, j], A[143, j])
        E[6, 1 + off] = safe_div(A[152, j], A[137, j])
        E[6, 2 + off] = safe_div(A[153, j], A[137, j])
        E[6, 4 + off] = safe_div(A[154, j], A[138, j])
        E[6, 5 + off] = safe_div(E[6, 4 + off] * 100.0, E[6, 2 + off])
        E[6, 6 + off] = safe_div(A[155, j], A[139, j])
        E[7, 1 + off] = safe_div(A[162, j], A[144, j])
        E[7, 2 + off] = safe_div(A[163, j], A[144, j])
        E[8, 1 + off] = safe_div(A[156, j], A[140, j])
        E[8, 2 + off] = safe_div(A[157, j], A[140, j])
        E[8, 4 + off] = safe_div(A[158, j], A[141, j])
        E[8, 5 + off] = safe_div(E[8, 4 + off] * 100.0, E[8, 2 + off])
        E[8, 6 + off] = safe_div(A[159, j], A[142, j])

        # Massecuites (1910-1980)
        E[9, 1 + off] = safe_div(A[170, j], A[184, j])
        E[9, 2 + off] = safe_div(A[171, j], A[184, j])
        E[10, 1 + off] = safe_div(A[172, j], A[185, j])
        E[10, 2 + off] = safe_div(A[173, j], A[185, j])
        E[11, 1 + off] = safe_div(A[174, j], A[186, j])
        E[11, 2 + off] = safe_div(A[175, j], A[186, j])
        E[12, 1 + off] = safe_div(A[176, j], A[187, j])
        E[12, 2 + off] = safe_div(A[177, j], A[187, j])

        # Molasses (2000-2050)
        E[13, 1 + off] = safe_div(A[178, j], A[184, j])
        E[13, 2 + off] = safe_div(A[179, j], A[184, j])
        E[14, 1 + off] = safe_div(A[180, j], A[185, j])
        E[14, 2 + off] = safe_div(A[181, j], A[185, j])
        E[15, 1 + off] = safe_div(A[182, j], A[186, j])
        E[15, 2 + off] = safe_div(A[183, j], A[186, j])

        # Grain and Magmas (2070-2120)
        E[16, 1 + off] = safe_div(A[164, j], A[145, j])
        E[16, 2 + off] = safe_div(A[165, j], A[145, j])
        E[17, 1 + off] = safe_div(A[166, j], A[146, j])
        E[17, 2 + off] = safe_div(A[167, j], A[146, j])
        E[18, 1 + off] = safe_div(A[168, j], A[147, j])
        E[18, 2 + off] = safe_div(A[169, j], A[147, j])

    for j in range(1, 19):
        E[j, 3] = safe_div(E[j, 2] * 100.0, E[j, 1])
        E[j, 9] = safe_div(E[j, 8] * 100.0, E[j, 7])

    # Analyses of Products Array F (2190-2530)
    for j in (1, 2):
        F[j, 1] = safe_div(A[205, j] * 100.0, A[204, j])
        F[j, 2] = safe_div(A[206, j] * 100.0, A[204, j])
        F[j, 4] = safe_div(A[207, j] * 100.0, A[204, j])
        F[j, 5] = safe_div(A[208, j] * 100.0, A[204, j])
        F[j, 7] = safe_div((A[204, j] - A[205, j]) * 100.0, A[204, j])
        F[j, 8] = safe_div(F[j, 7], 100.0 - F[j, 2])
        F[j, 10] = F[j, 2] + F[j, 4]

        # Final Molasses Made (2300-2360)
        F[2 + j, 1] = safe_div(A[213, j] * 100.0, A[212, j])
        F[2 + j, 2] = safe_div(A[214, j] * 100.0, A[212, j])
        F[2 + j, 4] = safe_div(A[215, j] * 100.0, A[212, j])
        F[2 + j, 5] = safe_div(A[216, j] * 100.0, A[212, j])
        F[2 + j, 6] = safe_div(A[215, j] * 100.0, A[216, j])
        F[2 + j, 9] = safe_div(A[217, j] * 100.0, A[212, j])
        F[2 + j, 10] = safe_div(
            (A[215, j] + A[217, j] * 1.052632) * 100.0, A[212, j]
        )

        # Final Molasses Shipped (2380-2440)
        F[4 + j, 1] = safe_div(A[222, j] * 100.0, A[221, j])
        F[4 + j, 2] = safe_div(A[223, j] * 100.0, A[221, j])
        F[4 + j, 4] = safe_div(A[224, j] * 100.0, A[221, j])
        F[4 + j, 5] = safe_div(A[225, j] * 100.0, A[221, j])
        F[4 + j, 6] = safe_div(A[224, j] * 100.0, A[225, j])
        F[4 + j, 9] = safe_div(A[226, j] * 100.0, A[221, j])
        F[4 + j, 10] = safe_div(
            (A[224, j] + A[226, j] * 1.052632) * 100.0, A[221, j]
        )

        # Filter Cake (2450-2480)
        F[6 + j, 1] = safe_div((A[201, j] - A[203, 1]) * 100.0, A[201, j])
        F[6 + j, 2] = safe_div(A[202, j] * 100.0, A[201, j])
        F[6 + j, 7] = safe_div(A[203, j] * 100.0, A[201, j])

    for j in range(1, 9):
        F[j, 3] = safe_div(F[j, 2] * 100.0, F[j, 1])

    # Lost Time Hours & Materials/Supplies Array G (2540-2710)
    for j in range(1, 11):
        G[j, 1] = A[j + 109, 1]
        G[j, 2] = A[j + 109, 2]
    G[12, 1] = A[120, 1]
    G[12, 2] = A[120, 2]
    for j in range(1, 13):
        G[j, 3] = safe_div(G[j, 1] * 100.0, A[121, 1])
        G[j, 4] = safe_div(G[j, 2] * 100.0, A[121, 2])

    for j in range(1, 13):
        G[j, 5] = A[j + 121, 1]
        G[j, 6] = A[j + 121, 2]
        G[j, 7] = safe_div(G[j, 5], A[191, 1])
        G[j, 8] = safe_div(G[j, 6], A[191, 2])

    # Max/Min Temperature scan across range (2770-2960)
    if round(H_num[26] - H_num[27]) == 1 or not day_files_range:
        A[240, 1] = A[103, 2]
        A[241, 1] = A[104, 2]
    else:
        max_t = day_files_range[0][102]  # 0-based index 102 is X(103)
        min_t = day_files_range[0][103]  # 0-based index 103 is X(104)
        for x_arr in day_files_range:
            max_t = max(max_t, x_arr[102])
            min_t = min(min_t, x_arr[103])
        A[240, 1] = max_t
        A[241, 1] = min_t


# ==============================================================================
# 132-Column Report & Form Renderers (MRREPOPR, MRREPOP2, MRREPOCK, etc.)
# ==============================================================================

def _c_d_labels(H_num: OneBasedArray1D, page: int = 1) -> Tuple[OneBasedArray1D, OneBasedArray1D]:
    """Builds C$(1..62) and D$(1..30) label arrays for MRREPOPR and MRREPOP2."""
    C_s = OneBasedArray1D(62, "")
    D_s = OneBasedArray1D(30, "")

    c_list = [
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
    ]
    C_s.from_list(c_list)
    if H_num[22] == 0:
        C_s[54] = "C Cyclone"

    d_list = [
        "SUGAR, Lbs 96 Made",
        "       Lbs 96 in Process",
        "       Lbs 96 Made and Estimated",
        "       Lbs Made",
        "       Lbs in Process",
        "       Lbs Made and Estimated",
        "       Lbs Total Equivalent - RV",
        "       Lbs Sugar/Ton Cane - RV",
        "       Lbs 96 Sugar/Ton Cane" if page == 1 else "       Yield Sugar, RV % Cane",
        "       Yield, 96 Sugar % Cane" if page == 1 else "       CRS, Lbs 96 Sugar/Ton Cane",
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
        "    Run" if H_num[28] == 1 else "  Today",
        "To Date",
    ]
    D_s.from_list(d_list)
    return C_s, D_s


def render_mrrepopr_page1(
    B_name: str,
    A2_s: OneBasedArray1D,
    A: OneBasedArray2D,
    B: OneBasedArray2D,
    C: OneBasedArray2D,
    D: OneBasedArray2D,
    H_num: OneBasedArray1D,
) -> List[str]:
    """Renders Page 1 of the Daily or Weekly Manufacturing Report (MRREPOPR)."""
    lines: List[str] = []
    C_s, D_s = _c_d_labels(H_num, page=1)
    weekdays = ["SUNDAY", "MONDAY", "TUESDAY", "WEDNESDAY", "THURSDAY", "FRIDAY", "SATURDAY"]
    n_wk = zeller_weekday_index(A2_s[2])
    day_name = weekdays[n_wk]

    b_trim = B_name.strip()
    lines.append(" " * max(0, int(66 - len(b_trim) / 2)) + b_trim)
    lines.append("")
    if H_num[28] != 0:
        lines.append(" " * 52 + "WEEKLY MANUFACTURING REPORT" + " " * 45 + "Page 1")
        lines.append(" " * 62 + "WEEKLY")
        img_1340 = "%Crop Started ########                  Date: ######## to ########                      Weekly Report No. ###"
        lines.append(format_printusing(img_1340, [A2_s[3], A2_s[1], A2_s[2], H_num[31]]))
    else:
        lines.append(" " * 52 + "DAILY MANUFACTURING REPORT" + " " * 46 + "Page 1")
        lines.append(" " * max(0, int(66 - len(day_name) / 2)) + day_name)
        img_1370 = "%Crop Started ########                       Date: ########                              Daily Report No. ###"
        lines.append(format_printusing(img_1370, [A2_s[3], A2_s[2], A[1, 2]]))

    sep = "-" * 131
    lines.append(sep)
    if H_num[28] != 0:
        lines.append(
            "        MILLING DATA                    Run        To Date   !          PRODUCTION DATA                        Run          To Date"
        )
    else:
        lines.append(
            "        MILLING DATA                  Today        To Date   !          PRODUCTION DATA                      Today          To Date"
        )
    lines.append(sep)

    img_1460 = "%############################## -#,###,###.## -#,###,###.##  !  ################################ -###,###,###.## -###,###,###.##"
    img_1500 = "%############################## -#,###,###.### -#,###,###.### ! ################################ -###,###,###.## -###,###,###.##"
    img_1570 = "%############################## -#,###,###.## -#,###,###.##  !  ################################# -##,###,###.## -###,###,###.##"
    img_1670 = "%############################## -#,###,###.## -#,###,###.##  !  ############################ ##.## -#,###,###.## -###,###,###.##"
    img_1700 = "%############################## -#,###,###.## -#,###,###.##  !  ######################## ##.##   -###,###,###.## -###,###,###.##"
    img_1730 = "%############################## -#,###,###.## -#,###,###.##  !  ########################### ##.## -##,###,###.## -###,###,###.##"
    img_1790 = "%############################## -#,###,###.## -#,###,###.##  !  ##################################     -###/-###       -###/-###"

    for j in range(1, 5):
        lines.append(format_printusing(img_1460, [C_s[j], B[j, 1], B[j, 2], D_s[j], B[j, 3], B[j, 4]]))
    for j in range(5, 8):
        lines.append(format_printusing(img_1500, [C_s[j], B[j, 1], B[j, 2], D_s[j], B[j, 3], B[j, 4]]))
    j = 8
    lines.append(format_printusing(img_1460, [C_s[j], B[j, 1], B[j, 2], D_s[j], B[j, 3], B[j, 4]]))
    j = 9
    lines.append(format_printusing(img_1460, [C_s[j], B[j, 1], B[j, 2], D_s[j], B[j + 1, 3], B[j + 1, 4]]))
    j = 10
    lines.append(format_printusing(img_1570, [C_s[j], B[j, 1], B[j, 2], D_s[j], B[j, 3] / 20.0, B[j, 4] / 20.0]))
    j = 11
    lines.append(format_printusing(img_1460, [C_s[j], B[j, 1], B[j, 2], D_s[j], B[j, 3], B[j, 4]]))
    j = 12
    lines.append(format_printusing(img_1500, [C_s[j], B[j, 1], B[j, 2], D_s[j], B[j, 3], B[j, 4]]))
    for j in (13, 14):
        lines.append(format_printusing(img_1460, [C_s[j], B[j, 1], B[j, 2], D_s[j], B[j, 3], B[j, 4]]))
    j = 15
    lines.append(format_printusing(img_1670, [C_s[j], B[j, 1], B[j, 2], D_s[j], H_num[30], B[j, 3], B[j, 4]]))
    j = 16
    lines.append(format_printusing(img_1700, [C_s[j], B[j, 1], B[j, 2], D_s[j], H_num[30], B[j, 3], B[j, 4]]))
    j = 17
    lines.append(format_printusing(img_1730, [C_s[j], B[j, 1], B[j, 2], D_s[j], H_num[30], B[j, 3], B[j, 4]]))
    for j in range(18, 22):
        lines.append(format_printusing(img_1460, [C_s[j], B[j, 1], B[j, 2], D_s[j], B[j, 3], B[j, 4]]))
    j = 22
    lines.append(format_printusing(img_1790, [C_s[j], B[j, 1], B[j, 2], D_s[j], A[240, 1], A[241, 1], A[240, 2], A[241, 2]]))
    for j in range(23, 27):
        lines.append(format_printusing(img_1460, [C_s[j], B[j, 1], B[j, 2], D_s[j], B[j, 3], B[j, 4]]))
    j = 27
    lines.append(format_printusing(img_1460, [C_s[j], B[j, 1], B[j, 2], D_s[j], D[6, 3], D[6, 4]]))
    j = 28
    lines.append(format_printusing(img_1460, [C_s[j], B[j, 1], B[j, 2], D_s[j], D[6, 3] * B[13, 1] / 100.0, D[6, 4] * B[13, 2] / 100.0]))

    lines.append(sep)
    if H_num[28] != 0:
        lines.append(
            "MASSECUITE                RUN             TO DATE        !  PRODUCTS SHIPPED            RUN         TO DATE         ON HAND"
        )
    else:
        lines.append(
            "MASSECUITE              TODAY             TO DATE        !  PRODUCTS SHIPPED          TODAY         TO DATE         ON HAND"
        )
    lines.append(sep)

    img_1910 = "%Massecuite         Cu. Ft.    /Ton     Cu. Ft.    /Ton  !  Sugar, Lbs             -###,###,###    -###,###,###    -###,###,###"
    img_1940 = "%----------         -------    ----     -------    ----  !  F. Mol, Gals (As Made) -###,###,###    -###,###,###    -###,###,###"
    img_1970 = "%A Massecuite  -###,###,### -###.## -###,###,### -###.## !  F. Mol, Gals (Shipped) -###,###,###    -###,###,###    -###,###,###"
    img_2000 = "%Top-Off A Mass.   -###,###,### -###.## -###,###,### -###.## !  W/H 1, Lbs Sugar   -###,###,###,### -#,###,###,###"
    img_2030 = "%B Massecuite  -###,###,### -###.## -###,###,### -###.## !  W/H 2, Lbs Sugar   -###,###,###,### -#,###,###,###"
    img_2060 = "%C Massecuite  -###,###,### -###.## -###,###,### -###.## !  W/H 3, Lbs Sugar   -###,###,###,### -#,###,###,###"
    img_2090 = "%                   -------    ----     -------    ----  !  W/H 4, Lbs Sugar   -###,###,###,### -#,###,###,###"
    img_2120 = "%     TOTAL    -###,###,### -###.## -###,###,### -###.## !  TOTAL, Lbs Sugar   -###,###,###,### -#,###,###,###"

    lines.append(format_printusing(img_1910, [C[1, 5], C[1, 6], C[1, 7]]))
    lines.append(format_printusing(img_1940, [C[2, 5], C[2, 6], C[2, 7]]))
    lines.append(format_printusing(img_1970, [C[3, 1], C[3, 2], C[3, 3], C[3, 4], C[3, 5], C[3, 6], C[3, 7]]))
    lines.append(format_printusing(img_2000, [C[4, 1], C[4, 2], C[4, 3], C[4, 4], A[255, 1], A[255, 2]]))
    lines.append(format_printusing(img_2030, [C[5, 1], C[5, 2], C[5, 3], C[5, 4], A[256, 1], A[256, 2]]))
    lines.append(format_printusing(img_2060, [C[6, 1], C[6, 2], C[6, 3], C[6, 4], A[257, 1], A[257, 2]]))
    lines.append(format_printusing(img_2090, [A[258, 1], A[258, 2]]))
    tot_wh_1 = A[255, 1] + A[256, 1] + A[257, 1] + A[258, 1]
    tot_wh_2 = A[255, 2] + A[256, 2] + A[257, 2] + A[258, 2]
    lines.append(format_printusing(img_2120, [C[8, 1], C[8, 2], C[8, 3], C[8, 4], tot_wh_1, tot_wh_2]))

    lines.append(sep)
    lines.append(
        "                                              POL - TONS                      PER CENT POL EXTRACTED                    PER CENT CANE"
    )
    lines.append(
        "POL ACCOUNT                            ------------------------               ----------------------                 -------------------"
    )
    if H_num[28] != 0:
        lines.append(
            "-----------                                Run          To Date                  Run         To Date                    Run      To Date"
        )
    else:
        lines.append(
            "-----------                              Today          To Date                Today         To Date                  Today      To Date"
        )
    lines.append(
        "                                      --------         --------              -------         -------                -------      -------"
    )

    img_2230 = "%####################         -###,###,###.###  -#,###,###.###                   ---             ---           -###,###.### -##,###.###"
    img_2260 = "%####################         -###,###,###.###  -#,###,###.###       -###,###,###.##     -###,###.##           -###,###.### -##,###.###"

    lines.append(format_printusing(img_2230, [C_s[29], D[1, 1], D[1, 2], D[1, 5], D[1, 6]]))
    for j in range(2, 8):
        lines.append(format_printusing(img_2260, [C_s[j + 28], D[j, 1], D[j, 2], D[j, 3], D[j, 4], D[j, 5], D[j, 6]]))
    lines.append(format_printusing(img_2230, [C_s[36], D[8, 1], D[8, 2], D[8, 5], D[8, 6]]))
    lines.append(sep)
    return lines


def render_mrrepop2_page2(
    B_name: str,
    B1_s: OneBasedArray1D,
    A2_s: OneBasedArray1D,
    A: OneBasedArray2D,
    E: OneBasedArray2D,
    F: OneBasedArray2D,
    G: OneBasedArray2D,
    J_s: OneBasedArray1D,
    H_s: OneBasedArray1D,
    H_num: OneBasedArray1D,
) -> List[str]:
    """Renders Page 2 of the Daily or Weekly Manufacturing Report (MRREPOP2)."""
    lines: List[str] = []
    C_s, D_s = _c_d_labels(H_num, page=2)
    b_trim = B_name.strip()

    if H_num[28] != 0:
        title = f"{b_trim} WEEKLY MANUFACTURING REPORT (Cont'd)"
    else:
        title = f"{b_trim} DAILY MANUFACTURING REPORT (Cont'd)"
    pad = max(0, int(66 - len(title) / 2))
    lines.append((" " * pad + title).ljust(124) + "Page 2")

    if H_num[28] != 0:
        img_2380 = "%Date: ######## to ########                               ANALYTICAL DATA                               Weekly Report No. ###"
        lines.append(format_printusing(img_2380, [A2_s[1], A2_s[2], H_num[31]]))
    else:
        img_2410 = "%Date: ########                                           ANALYTICAL DATA                               Daily Report No.  ###"
        lines.append(format_printusing(img_2410, [A2_s[2], A[1, 2]]))

    sep = "-" * 131
    lines.append(sep)
    if H_num[28] != 0:
        lines.append(
            "ANALYSIS OF                                     RUN                        !                        TO DATE"
        )
    else:
        lines.append(
            "ANALYSIS OF                                   TODAY                        !                        TO DATE"
        )
    lines.append(sep)
    lines.append(
        "                       Brix     Pol    Purity  Glucose  G. Rat.     pH     !    Brix     Pol    Purity  Glucose  G. Rat.     pH"
    )
    lines.append(
        "                      ------   -----   ------  -------  -------   -----    !   ------   -----   ------  -------  -------   -----"
    )

    img_2740 = "%#################### -###.##  -###.##  -###.##                            !  -###.##  -###.##  -###.##"
    img_2780 = "%#################### -###.##  -###.##  -###.##  -###.##  -###.##  -###.## !  -###.##  -###.##  -###.##  -###.##  -###.##  -###.##"

    for j in range(1, 19):
        if j in (2, 4, 6, 8):
            lines.append(
                format_printusing(
                    img_2780,
                    [
                        C_s[j + 36],
                        E[j, 1],
                        E[j, 2],
                        E[j, 3],
                        E[j, 4],
                        E[j, 5],
                        E[j, 6],
                        E[j, 7],
                        E[j, 8],
                        E[j, 9],
                        E[j, 10],
                        E[j, 11],
                        E[j, 12],
                    ],
                )
            )
        else:
            lines.append(
                format_printusing(
                    img_2740,
                    [C_s[j + 36], E[j, 1], E[j, 2], E[j, 3], E[j, 7], E[j, 8], E[j, 9]],
                )
            )

    lines.append(sep)
    lines.append(
        "ANALYSIS OF                       Brix     Pol    Purity  Glu/Dex  Ash/Str   RS/Ash  Moisture  Safety Fac.  Clerget  T. Sugars"
    )
    lines.append(
        "-----------                      -----    -----   ------  -------  -------   ------  --------  -----------  -------  ---------"
    )

    img_2850 = "%###################### ####### -###.##  -###.##  -###.##  -###.##   -###.##           -###.##     -###.##                     -###.##"
    img_2900 = "%###################### ####### -###.##  -###.##  -###.##  -###.##   -###.##  -###.##                                 -###.##   -###.##"
    img_2990 = "%###################### #######          -###.##                                       -###.##"

    for j in (1, 2):
        lbl = D_s[29] if j == 1 else D_s[30]
        lines.append(
            format_printusing(
                img_2850,
                [C_s[j + 54], lbl, F[j, 1], F[j, 2], F[j, 3], F[j, 4], F[j, 5], F[j, 7], F[j, 8], F[j, 10]],
            )
        )
    for j in (3, 4, 5, 6):
        lbl = D_s[29] if j % 2 == 1 else D_s[30]
        lines.append(
            format_printusing(
                img_2900,
                [C_s[j + 54], lbl, F[j, 1], F[j, 2], F[j, 3], F[j, 4], F[j, 5], F[j, 6], F[j, 9], F[j, 10]],
            )
        )
    for j in (7, 8):
        lbl = D_s[29] if j == 7 else D_s[30]
        lines.append(format_printusing(img_2990, [C_s[j + 54], lbl, F[j, 2], F[j, 7]]))

    lines.append(sep)
    lines.append(
        "                     ANALYSIS OF MILL LOST TIME                   !                      MATERIALS AND SUPPLIES USED"
    )
    lines.append(sep)
    lines.append(
        "                           HOURS               PER CENT           !                              TOTAL AMOUNT          PER TON CANE"
    )
    lines.append(
        "                    -------------------    -----------------      !                          --------------------    ----------------"
    )
    if H_num[28] != 0:
        lines.append(
            "Category              For Run   To Date     For Run  To Date      !  Item                      For Run    To Date     For Run  To Date"
        )
    else:
        lines.append(
            "Category                Today   To Date       Today  To Date      !  Item                        Today    To Date       Today  To Date"
        )
    lines.append(
        "--------              -------   -------     -------  -------      !  -------------             -------    -------     -------  -------"
    )

    img_3140 = "%################ -##,###.### -##,###.###   -###.### -###.###     !  ##################### -#,###,### -###,###,###    -###.### -###.###"
    img_3180 = "%                     -------   -------     -------  -------      !  ##################### -#,###,### -###,###,###    -###.### -###.###"

    for j in range(1, 11):
        lines.append(
            format_printusing(
                img_3140,
                [J_s[j], G[j, 1], G[j, 2], G[j, 3], G[j, 4], H_s[j], G[j, 5], G[j, 6], G[j, 7], G[j, 8]],
            )
        )
    j = 11
    lines.append(format_printusing(img_3180, [H_s[j], G[j, 5], G[j, 6], G[j, 7], G[j, 8]]))
    j = 12
    lines.append(
        format_printusing(
            img_3140,
            ["      TOTAL", G[j, 1], G[j, 2], G[j, 3], G[j, 4], H_s[j], G[j, 5], G[j, 6], G[j, 7], G[j, 8]],
        )
    )
    lines.append(sep)
    lines.append(f"REMARKS: {B1_s[1].rstrip()}{B1_s[2].rstrip()}")
    lines.append(f"         {B1_s[3].rstrip()}{B1_s[4].rstrip()}")
    lines.append(f"         {B1_s[5].rstrip()}{B1_s[6].rstrip()}")
    lines.append("")
    lines.append("      Chief Chemist:                                                  Fabrication Superintendent:")
    return lines


def render_mrrepock_page3(
    B_name: str,
    A2_s: OneBasedArray1D,
    A: OneBasedArray2D,
    B: OneBasedArray2D,
    C: OneBasedArray2D,
    D: OneBasedArray2D,
    E: OneBasedArray2D,
    F: OneBasedArray2D,
    H_num: OneBasedArray1D,
) -> List[str]:
    """
    Renders Page 3 of the Daily or Weekly Manufacturing Report (MRREPOCK, lines 4000-7105),
    detokenized directly from PLATTER1.BS2.
    """
    K = OneBasedArray2D(24, 6, 0.0)
    C_lbl = OneBasedArray1D(2, "")
    C_lbl[1] = "Run" if H_num[28] != 0 else "Today"
    C_lbl[2] = "To Date"

    f33 = F[3, 3]
    if f33 == 0:
        f33 = safe_div(A[219, 1] * 100.0, A[218, 1])
    f43 = F[4, 3]
    if f43 == 0:
        f43 = safe_div(A[219, 2] * 100.0, A[218, 2])

    # Solids Balance (4100-4390)
    K[1, 1] = safe_div(D[1, 1] * 100.0, E[5, 3])
    K[1, 2] = safe_div(D[1, 2] * 100.0, E[5, 9])
    K[2, 1] = D[2, 1] + A[218, 1] - A[219, 1]
    K[2, 2] = D[2, 2] + A[218, 2] - A[219, 2]
    if f33 != 0:
        K[2, 1] = safe_div(D[2, 1] * 100.0, f33)
    if f43 != 0:
        K[2, 2] = safe_div(D[2, 2] * 100.0, f43)
    K[6, 1] = safe_div(D[6, 1] * 100.0, F[1, 3])
    K[6, 2] = safe_div(D[6, 2] * 100.0, F[2, 3])
    K[7, 1] = safe_div(D[7, 1] * 100.0, E[4, 3])
    K[7, 2] = safe_div(D[7, 2] * 100.0, E[4, 9])
    K[9, 1] = safe_div(D[9, 1] * 100.0, E[6, 3])
    K[9, 2] = safe_div(D[9, 2] * 100.0, E[6, 9])

    for j in (1, 2):
        K[8, j] = K[1, j] + K[7, j]
        K[3, j] = K[7, j] - K[9, j]
        K[4, j] = K[7, j] - K[6, j] - K[2, j] - K[3, j]
        K[5, j] = K[1, j] + K[2, j] + K[3, j] + K[4, j]
        K[10, j] = K[2, j] + K[3, j] + K[6, j]

    for j in range(1, 11):
        K[j, 3] = safe_div(K[j, 1] * 100.0, K[7, 1])
        K[j, 4] = safe_div(K[j, 2] * 100.0, K[7, 2])
        K[j, 5] = safe_div(K[j, 1] * 100.0, A[191, 1])
        K[j, 6] = safe_div(K[j, 2] * 100.0, A[191, 2])

    K[5, 3] = K[2, 3] + K[3, 3] + K[4, 3]
    K[5, 4] = K[2, 4] + K[3, 4] + K[4, 4]

    # Purities Compared to Mixed Juice (4400-4520)
    K[11, 1] = F[1, 3]
    K[11, 2] = f33
    K[11, 3] = safe_div(D[3, 1] * 100.0, K[3, 1])
    K[11, 4] = safe_div(D[10, 1] * 100.0, K[10, 1])
    K[11, 5] = E[4, 3]
    K[11, 6] = K[11, 5] - K[11, 4]

    K[12, 1] = F[2, 3]
    K[12, 2] = f43
    K[12, 3] = safe_div(D[3, 2] * 100.0, K[3, 2])
    K[12, 4] = safe_div(D[10, 2] * 100.0, K[10, 2])
    K[12, 5] = E[4, 9]
    K[12, 6] = K[12, 5] - K[12, 4]

    # Purities Compared to Syrup (4530-4630)
    K[13, 1] = F[1, 3]
    K[13, 2] = f33
    K[13, 3] = safe_div((D[6, 1] + D[2, 1]) * 100.0, K[6, 1] + K[2, 1])
    K[13, 4] = E[8, 3]
    K[13, 5] = E[8, 3] - K[13, 3]

    K[14, 1] = F[2, 3]
    K[14, 2] = f43
    K[14, 3] = safe_div((D[6, 2] + D[2, 2]) * 100.0, K[6, 2] + K[2, 2])
    K[14, 4] = E[8, 9]
    K[14, 5] = E[8, 9] - K[14, 3]

    # Theoretical Yields (4640-4740)
    K[15, 1] = safe_div(
        F[1, 3] * (E[4, 3] - f33) * 100.0, E[4, 3] * (F[1, 3] - f33)
    )
    K[15, 2] = D[3, 3]
    K[15, 3] = K[15, 1] - K[15, 2]
    K[15, 4] = D[6, 3]
    K[15, 5] = K[15, 3] - K[15, 4]

    K[16, 1] = safe_div(
        F[2, 3] * (E[4, 9] - f43) * 100.0, E[4, 9] * (F[2, 3] - f43)
    )
    K[16, 2] = D[3, 4]
    K[16, 3] = K[16, 1] - K[16, 2]
    K[16, 4] = D[6, 4]
    K[16, 5] = K[16, 3] - K[16, 4]

    # Solids in Final Molasses (4750-4850)
    K[17, 1] = safe_div((F[1, 3] - E[4, 3]) * 100.0, F[1, 3] - f33)
    K[17, 2] = K[3, 3]
    K[17, 3] = K[17, 1] - K[17, 2]
    K[17, 4] = K[2, 3]
    K[17, 5] = K[17, 3] - K[17, 4]

    K[18, 1] = safe_div((F[2, 3] - E[4, 9]) * 100.0, F[2, 3] - f43)
    K[18, 2] = K[3, 4]
    K[18, 3] = K[18, 1] - K[18, 2]
    K[18, 4] = K[2, 4]
    K[18, 5] = K[18, 3] - K[18, 4]

    # Crystal Yields (4860-4940)
    K[19, 1] = safe_div((E[9, 3] - E[13, 3]) * 100.0, 100.0 - E[13, 3])
    K[19, 2] = safe_div((E[10, 3] - E[14, 3]) * 100.0, 100.0 - E[14, 3])
    K[19, 3] = safe_div((E[11, 3] - E[15, 3]) * 100.0, 100.0 - E[15, 3])
    K[19, 4] = safe_div((E[12, 3] - f33) * 100.0, 100.0 - f33)

    K[20, 1] = safe_div((E[9, 9] - E[13, 9]) * 100.0, 100.0 - E[13, 9])
    K[20, 2] = safe_div((E[10, 9] - E[14, 9]) * 100.0, 100.0 - E[14, 9])
    K[20, 3] = safe_div((E[11, 9] - E[15, 9]) * 100.0, 100.0 - E[15, 9])
    K[20, 4] = safe_div((E[12, 9] - f43) * 100.0, 100.0 - f43)

    # Sugar Based on Cu. Ft. (4950-5130 & DEFFN'4 at 7101-7105)
    def deffn_4(a_p: float, b_p: float, c_p: float, d_brix: float, e_moist: float, f_cuft: float) -> float:
        if abs(d_brix) < 1e-9 or abs(f_cuft) < 1e-9:
            return 0.0
        k1 = brix_density_poly_5(d_brix) * d_brix / 100.0
        return safe_div((b_p - c_p) * k1 * f_cuft * 100.0, (a_p - c_p) * (100.0 - e_moist))

    K[21, 1] = deffn_4(F[1, 3], E[9, 3], E[13, 3], E[9, 1], F[1, 7], C[3, 1])
    K[21, 2] = deffn_4(F[1, 3], E[10, 3], E[14, 3], E[10, 1], F[1, 7], C[4, 1])
    K[21, 3] = deffn_4(F[1, 3], E[11, 3], E[15, 3], E[11, 1], F[1, 7], C[5, 1])
    # Historical line 5020: K(21,4) = K(21,1) + K(21,2)
    K[21, 4] = K[21, 1] + K[21, 2]
    K[21, 5] = B[4, 3]
    K[21, 6] = safe_div((K[21, 4] - K[21, 5]) * 100.0, K[21, 4])

    K[22, 1] = deffn_4(F[2, 3], E[9, 9], E[13, 9], E[9, 7], F[2, 7], C[3, 3])
    K[22, 2] = deffn_4(F[2, 3], E[10, 9], E[14, 9], E[10, 7], F[2, 7], C[4, 3])
    K[22, 3] = deffn_4(F[2, 3], E[11, 9], E[15, 9], E[11, 7], F[2, 7], C[5, 3])
    K[22, 4] = K[22, 1] + K[22, 2]
    K[22, 5] = B[4, 4]
    K[22, 6] = safe_div((K[22, 4] - K[22, 5]) * 100.0, K[22, 4])

    # Final Molasses Recycled in C Sugar (5140-5160)
    K[23, 1] = safe_div(
        (E[12, 3] - f33) * (100.0 - E[17, 3]) * 100.0,
        (E[17, 3] - f33) * (100.0 - E[12, 3]),
    )
    K[24, 1] = safe_div(
        (E[12, 9] - f43) * (100.0 - E[17, 9]) * 100.0,
        (E[17, 9] - f43) * (100.0 - E[12, 9]),
    )

    # Print Statements (5230-6070)
    lines: List[str] = []
    b_trim = B_name.strip()
    if H_num[28] != 0:
        hdr_left = f"Date: {A2_s[1]} to {A2_s[2]}"
    else:
        hdr_left = f"Date: {A2_s[2]}"
    center_pos = max(len(hdr_left) + 2, int(66 - len(b_trim) / 2))
    hdr_line = hdr_left.ljust(center_pos) + b_trim
    lines.append(hdr_line.ljust(124) + "Page 3")
    lines.append("")
    lines.append(
        "                                         BRIX - TONS                    PER CENT BRIX EXTRACTED                    PER CENT CANE"
    )
    lines.append(
        "BRIX ACCOUNT                      ------------------------              -----------------------                 -------------------"
    )
    if H_num[28] != 0:
        lines.append(
            "------------                           Run         To Date                   Run        To Date                     Run     To Date"
        )
    else:
        lines.append(
            "------------                         Today         To Date                 Today        To Date                   Today     To Date"
        )
    lines.append(
        "                                  --------        --------               -------        -------                 -------     -------"
    )

    img_5370 = "%####################      -###,###,###.###  -#,###,###.###                   ---            ---            -###,###.### -##,###.###"
    img_5440 = "%####################      -###,###,###.###  -#,###,###.###       -###,###,###.##    -###,###.##            -###,###.### -##,###.###"

    brix_labels = [
        "In Bagasse",
        "In Final Molasses",
        "In Filter Cake",
        "Undetermined",
        "Total Losses",
        "Recovered in Sugars",
        "Brix in Juice % Cane",
        "Brix in Cane",
    ]
    lines.append(format_printusing(img_5370, [brix_labels[0], K[1, 1], K[1, 2], K[1, 5], K[1, 6]]))
    for j in range(2, 8):
        lines.append(
            format_printusing(
                img_5440,
                [brix_labels[j - 1], K[j, 1], K[j, 2], K[j, 3], K[j, 4], K[j, 5], K[j, 6]],
            )
        )
    lines.append(format_printusing(img_5370, [brix_labels[7], K[8, 1], K[8, 2], K[8, 5], K[8, 6]]))

    dash_85 = " " * 31 + "-" * 85
    lines.append("")
    lines.append(" " * 57 + "PURITIES - COMPARED TO MIXED JUICE")
    lines.append(dash_85)
    lines.append(
        "                               Sugar     Final Molasses    Filter Cake    All Products    Mixed Juice     Difference"
    )
    lines.append(
        "                               -----     --------------    -----------    ------------    -----------     ----------"
    )
    img_5530 = "%############                 -###.##    -###,###.##  -###,###,###.## -##,###,###.##  -#,###,###.##   -#,###,###.##"
    for j in (11, 12):
        lines.append(
            format_printusing(
                img_5530,
                [C_lbl[j - 10], K[j, 1], K[j, 2], K[j, 3], K[j, 4], K[j, 5], K[j, 6]],
            )
        )

    lines.append("")
    lines.append(" " * 60 + "PURITIES - COMPARED TO SYRUP")
    lines.append(dash_85)
    lines.append(
        "                               Sugar       Final Molasses        Sugar & Final Molasses        Syrup      Difference"
    )
    lines.append(
        "                               -----       --------------        ----------------------        -----      ----------"
    )
    img_5620 = "%############              -##,###.##      -###,###.##            -##,###,###.##          -###,###.##   -###,###.##"
    for j in (13, 14):
        lines.append(
            format_printusing(
                img_5620,
                [C_lbl[j - 12], K[j, 1], K[j, 2], K[j, 3], K[j, 4], K[j, 5]],
            )
        )

    lines.append("")
    lines.append(" " * 54 + "THEORETICAL YIELDS % POL IN MIXED JUICE")
    lines.append(dash_85)
    lines.append(
        "                                SJM      Filter Loss     Theoretical Recovery     Reported Recovery       Difference"
    )
    lines.append(
        "                               -----     -----------     --------------------     -----------------       ----------"
    )
    img_5710 = "%###############      -###,###,###.##   -##,###.##      -###,###,###.##        -###,###,###.##      -###,###,###.##"
    for j in (15, 16):
        lines.append(
            format_printusing(
                img_5710,
                [C_lbl[j - 14], K[j, 1], K[j, 2], K[j, 3], K[j, 4], K[j, 5]],
            )
        )

    lines.append("")
    lines.append(" " * 47 + "BRIX SOLIDS IN FINAL MOLASSES % SOLIDS IN MIXED JUICE")
    lines.append(dash_85)
    lines.append(
        "                               (S-J)/(S-M)       Filter Cake Solids       Theoretical       Reported      Difference"
    )
    lines.append(
        "                               -----------       ------------------       -----------       --------      ----------"
    )
    img_5800 = "%################         -##,###,###.##         -##,###,###.##       -#,###,###.##    -#,###,###.##    -###,###.##"
    for j in (17, 18):
        lines.append(
            format_printusing(
                img_5800,
                [C_lbl[j - 16], K[j, 1], K[j, 2], K[j, 3], K[j, 4], K[j, 5]],
            )
        )

    lines.append("")
    lines.append(" " * 46 + "MASSECUITE CRYSTAL YIELDS (CRYSTALS % MASSECUITE SOLIDS")
    lines.append(dash_85)
    lines.append(
        "                               A Massecuite         Top-Off A Massecuite          B Massecuite          C Massecuite"
    )
    lines.append(
        "                               ------------         --------------------          ------------          ------------"
    )
    img_5890 = "%#################        -###,###,###.##       -#,###,###,###.##             -##,###,###.##       -###,###,###.##"
    for j in (19, 20):
        lines.append(
            format_printusing(
                img_5890,
                [C_lbl[j - 18], K[j, 1], K[j, 2], K[j, 3], K[j, 4]],
            )
        )

    lines.append("")
    lines.append(" " * 43 + "COMPARISON OF SUGAR YIELD BY STRIKES WITH REPORTED SUGAR MADE")
    lines.append(dash_85)
    lines.append(
        "                               A Sugar     T-O A Sugar      B Sugar     Total Sugar     Reported Sugar    % Diff'nce"
    )
    lines.append(
        "                               -------     -----------    -----------   -----------     --------------    ----------"
    )
    img_5980 = "%###############   -###,###,###,###,### -##,###,###,###   -###,###,###  -###,###,### -#,###,###,###,###  -###,###.##"
    for j in (21, 22):
        lines.append(
            format_printusing(
                img_5980,
                [C_lbl[j - 20], K[j, 1], K[j, 2], K[j, 3], K[j, 4], K[j, 5], K[j, 6]],
            )
        )

    lines.append("")
    lines.append(" " * 41 + "FINAL MOLASSES RECYCLED IN MAGMA % FINAL MOLASSES IN C MASSECUITE")
    lines.append(dash_85)
    img_6050 = "%##########################                                   -#,###,###,###.##"
    for j in (23, 24):
        lines.append(format_printusing(img_6050, [C_lbl[j - 22], K[j, 1]]))

    return lines


def render_mrcomppr(
    B_name: str,
    A2_s: OneBasedArray1D,
    A: OneBasedArray2D,
    B: OneBasedArray2D,
    D: OneBasedArray2D,
    E: OneBasedArray2D,
    F: OneBasedArray2D,
    G: OneBasedArray2D,
    H_num: OneBasedArray1D,
) -> List[List[str]]:
    """Renders the 2-page Weekly Comparative Report Form (MRCOMPPR)."""
    C_s = OneBasedArray1D(82, "")
    I_arr = OneBasedArray2D(82, 2, 0.0)

    c_labels = [
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
    ]
    C_s.from_list(c_labels)

    I_arr[2, 1] = H_num[31]
    I_arr[5, 1] = 0.97
    for j in (1, 2):
        I_arr[6, j] = B[1, j]
        I_arr[7, j] = B[2, j]
        I_arr[9, j] = B[3, j]
        I_arr[11, j] = B[15, j]
        I_arr[12, j] = B[18, j]
        I_arr[13, j] = B[23, j]
        I_arr[14, j] = B[24, j]
        I_arr[15, j] = B[5, j]

    I_arr[16, 1], I_arr[16, 2] = E[2, 1], E[2, 7]
    I_arr[17, 1], I_arr[17, 2] = E[2, 3], E[2, 9]
    I_arr[18, 1], I_arr[18, 2] = E[4, 1], E[4, 7]
    I_arr[19, 1], I_arr[19, 2] = E[4, 3], E[4, 9]
    I_arr[20, 1], I_arr[20, 2] = E[5, 1], E[5, 7]
    I_arr[21, 1], I_arr[21, 2] = E[5, 3], E[5, 9]
    I_arr[22, 1], I_arr[22, 2] = E[6, 1], E[6, 7]
    I_arr[23, 1], I_arr[23, 2] = E[6, 3], E[6, 9]
    I_arr[24, 1], I_arr[24, 2] = E[8, 1], E[8, 7]
    I_arr[25, 1], I_arr[25, 2] = E[8, 3], E[8, 9]
    I_arr[26, 1], I_arr[26, 2] = F[3, 1], F[4, 1]
    I_arr[27, 1], I_arr[27, 2] = F[3, 3], F[4, 3]
    I_arr[28, 1], I_arr[28, 2] = E[9, 3], E[9, 9]
    I_arr[29, 1], I_arr[29, 2] = E[11, 3], E[11, 9]
    I_arr[30, 1], I_arr[30, 2] = E[12, 3], E[12, 9]
    I_arr[31, 1], I_arr[31, 2] = E[13, 3], E[13, 9]
    I_arr[32, 1], I_arr[32, 2] = E[15, 3], E[15, 9]
    I_arr[33, 1], I_arr[33, 2] = E[17, 3], E[17, 9]
    I_arr[34, 1], I_arr[34, 2] = 0.0, 0.0
    I_arr[35, 1], I_arr[35, 2] = B[6, 3], B[6, 4]
    I_arr[36, 1], I_arr[36, 2] = B[18, 3], B[18, 4]
    I_arr[37, 1], I_arr[37, 2] = B[18, 3], B[18, 4]
    I_arr[38, 1], I_arr[38, 2] = B[16, 3], B[16, 4]
    I_arr[39, 1], I_arr[39, 2] = H_num[30], H_num[30]
    I_arr[40, 1], I_arr[40, 2] = B[19, 3], B[19, 4]
    I_arr[41, 1], I_arr[41, 2] = F[7, 2], F[8, 2]
    I_arr[42, 1], I_arr[42, 2] = F[1, 7], F[2, 7]

    for j in (1, 2):
        I_arr[45, j] = B[4, j]
        I_arr[46, j] = B[8, j]
        I_arr[47, j] = B[16, j]
        I_arr[48, j] = B[20, j]
        I_arr[49, j] = B[13, j]
        I_arr[50, j] = B[21, j]
        I_arr[51, j] = B[22, j]
        I_arr[52, j] = B[25, j]
        I_arr[53, j] = B[26, j]
        I_arr[54, j] = B[27, j]
        I_arr[55, j] = B[12, j]

    I_arr[56, 1], I_arr[56, 2] = E[3, 1], E[3, 7]
    I_arr[57, 1], I_arr[57, 2] = E[3, 2], E[3, 8]
    I_arr[58, 1], I_arr[58, 2] = E[3, 3], E[3, 9]
    I_arr[59, 1], I_arr[59, 2] = B[3, 3], B[3, 4]
    I_arr[60, 1], I_arr[60, 2] = B[10, 3], B[10, 4]
    I_arr[61, 1], I_arr[61, 2] = B[10, 3] / 20.0, B[10, 4] / 20.0
    I_arr[62, 1], I_arr[62, 2] = 0.0, 0.0
    I_arr[63, 1], I_arr[63, 2] = B[14, 3], B[14, 4]
    I_arr[64, 1], I_arr[64, 2] = B[15, 3], B[15, 4]
    I_arr[65, 1], I_arr[65, 2] = B[16, 3], B[16, 4]
    I_arr[66, 1] = safe_div(A[218, 1] * 2000.0 / 9.338, A[191, 1])
    I_arr[66, 2] = safe_div(A[218, 2] * 2000.0 / 9.338, A[191, 2])
    I_arr[67, 1], I_arr[67, 2] = D[6, 3], D[6, 4]
    I_arr[68, 1], I_arr[68, 2] = D[1, 5], D[1, 6]
    I_arr[69, 1], I_arr[69, 2] = D[2, 5], D[2, 6]
    I_arr[70, 1], I_arr[70, 2] = D[3, 5], D[3, 6]
    I_arr[71, 1], I_arr[71, 2] = D[4, 5], D[4, 6]
    I_arr[72, 1], I_arr[72, 2] = D[5, 5], D[5, 6]
    I_arr[73, 1], I_arr[73, 2] = D[6, 5], D[6, 6]
    I_arr[75, 1], I_arr[75, 2] = D[7, 5], D[7, 6]
    I_arr[76, 1], I_arr[76, 2] = D[8, 5], D[8, 6]
    I_arr[77, 1], I_arr[77, 2] = G[1, 7], G[1, 8]
    I_arr[79, 1], I_arr[79, 2] = B[21, 3], B[21, 4]
    I_arr[80, 1], I_arr[80, 2] = B[12, 3], B[12, 4]
    I_arr[81, 1], I_arr[81, 2] = B[13, 3], B[13, 4]

    img_2210 = "%##############################################  ##############################################"
    img_2260 = "%############################################## -###,###,###.## -###,###,###.##"
    img_2280 = "%############################################## -##,###,###.### -##,###,###.###"
    img_2290 = "%##############################################        ########        ########"

    p1: List[str] = []
    p1.append(" " * 21 + "DATA FORM FOR WEEKLY COMPARATIVE REPORT")
    p1.append("")
    p1.append(" " * 36 + "Page 1")
    p1.append("")
    p1.append("Item")
    p1.append("Number       Item                                     Run          To Date")
    p1.append("------       --------------------------------        -----        ---------")
    p1.append(format_printusing(img_2210, [C_s[1], B_name.strip()]))
    p1.append(format_printusing(img_2290, [C_s[2], f"{int(round(I_arr[2, 1])):8d}", "XXXXXXXX"]))
    p1.append(format_printusing(img_2290, [C_s[3], A2_s[2], "XXXXXXXX"]))
    p1.append(format_printusing(img_2290, [C_s[4], "  /  /  ", "XXXXXXXX"]))

    for x, y in ((6, 10), (11, 15), (16, 25), (26, 33), (35, 42)):
        for j in range(x, y + 1):
            p1.append(format_printusing(img_2260, [C_s[j], I_arr[j, 1], I_arr[j, 2]]))
        p1.append("")

    p2: List[str] = []
    p2.append(" " * 21 + "DATA FORM FOR WEEKLY COMPARATIVE REPORT")
    p2.append("")
    p2.append(" " * 36 + "Page 2")
    p2.append("")
    p2.append("Item")
    p2.append("Number       Item                                     Run          To Date")
    p2.append("------       --------------------------------        -----        ---------")
    p2.append(format_printusing(img_2290, [C_s[43], A2_s[1], A2_s[3]]))
    p2.append(format_printusing(img_2290, [C_s[44], A2_s[2], "XXXXXXXX"]))

    for j in range(45, 52):
        p2.append(format_printusing(img_2260, [C_s[j], I_arr[j, 1], I_arr[j, 2]]))
    p2.append("")
    for j in range(52, 55):
        p2.append(format_printusing(img_2260, [C_s[j], I_arr[j, 1], I_arr[j, 2]]))
    p2.append(format_printusing(img_2280, [C_s[55], I_arr[55, 1], I_arr[55, 2]]))
    for j in range(56, 59):
        p2.append(format_printusing(img_2260, [C_s[j], I_arr[j, 1], I_arr[j, 2]]))
    p2.append("")
    for j in range(59, 62):
        p2.append(format_printusing(img_2260, [C_s[j], I_arr[j, 1], I_arr[j, 2]]))
    for j in range(63, 68):
        p2.append(format_printusing(img_2260, [C_s[j], I_arr[j, 1], I_arr[j, 2]]))
    p2.append("")
    for j in range(68, 77):
        p2.append(format_printusing(img_2280, [C_s[j], I_arr[j, 1], I_arr[j, 2]]))
    p2.append("")
    p2.append(format_printusing(img_2280, [C_s[77], I_arr[77, 1], I_arr[77, 2]]))
    for j in range(79, 82):
        p2.append(format_printusing(img_2260, [C_s[j], I_arr[j, 1], I_arr[j, 2]]))
    p2.append("")
    p2.append(format_printusing(img_2290, [C_s[82], "        ", "XXXXXXXX"]))

    return [p1, p2]


def render_mrcustpr(
    B_name: str,
    A1_s: str,
    J_s: OneBasedArray1D,
    H_s: OneBasedArray1D,
    I_s: OneBasedArray1D,
    H_num: OneBasedArray1D,
) -> List[List[str]]:
    """Renders the 2-page Customized File printout (MRCUSTPR)."""
    I_s[1] = "D" if H_num[1] == 1 else "W"
    for j in range(2, 24):
        I_s[j] = "N" if H_num[j] == 0 else "Y"
    I_s[24] = "N" if H_num[27] == 0 else "Y"

    b_labels = [
        "FACTORY NAME ON REPORT",
        "GREGORIAN DATE CROP STARTED",
        *[f"LOST TIME CATEGORY NO. {i}" for i in range(1, 11)],
        *[f"MATERIALS AND SUPPLIES CATEGORY NO. {i}" for i in range(1, 13)],
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
        "JULIAN DATE CROP STARTED",
    ]
    img_650 = "%################################################################   ####################"
    img_660 = "%################################################################   ################################################################"

    p1: List[str] = []
    p1.append(" " * 34 + "CUSTOM PARAMETERS")
    p1.append("")
    p1.append(format_printusing(img_660, [b_labels[0], B_name.strip()]))
    p1.append(format_printusing(img_650, [b_labels[1], A1_s.strip()]))
    p1.append("")
    p1.append("LOST TIME CATEGORIES")
    p1.append("--------------------")
    p1.append("")
    for j in range(1, 11):
        p1.append(format_printusing(img_650, [b_labels[j + 1], J_s[j]]))
    p1.append("")
    p1.append("MATERIALS AND SUPPLIES CATEGORIES")
    p1.append("---------------------------------")
    p1.append("")
    for j in range(1, 13):
        p1.append(format_printusing(img_650, [b_labels[j + 11], H_s[j]]))
    p1.append("")
    for j in (1, 2):
        p1.append(format_printusing(img_650, [b_labels[j + 23], H_s[j + 12]]))

    p2: List[str] = []
    p2.append("SUPPRESSION OF DATA INPUT FOR ITEMS NOT REPORTED")
    p2.append("------------------------------------------------")
    p2.append("")
    for j in range(1, 25):
        p2.append(format_printusing(img_650, [b_labels[j + 25], I_s[j]]))
    p2.append("")
    p2.append("PRINTER AND DATA DISK SELECTIONS")
    p2.append("--------------------------------")
    p2.append("")
    p2.append(f"PRINTER SELECTED (0 = SYSTEM, 1 = TERMINAL) IS NO. {int(round(H_num[36]))}")
    p2.append(
        f"DATA DISK SELECTED (0=SAME AS PROGRAM,1=310,2=D11,3=D12,4=D13,5=D14,6=D20,7=D21,8=D22,9=D23,10=D24,11=D25) IS NO. {int(round(H_num[37]))}"
    )
    return [p1, p2]


def render_mrdatafm(
    B_name: str,
    J_s: OneBasedArray1D,
    H_s: OneBasedArray1D,
    H_num: OneBasedArray1D,
) -> List[List[str]]:
    """Renders the 4-page Blank Daily Report Data Input Form (MRDATAFM)."""
    C_s = OneBasedArray1D(110, "")
    C_s[1] = "Crop Day Number"
    C_s[2] = "Lbs TRS Purchased"
    for j in range(1, 11):
        C_s[j + 2] = J_s[j]
    C_s[13] = "Total Hours Available"
    for j in range(1, 13):
        C_s[j + 13] = H_s[j]

    fixed = {
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
        64: "B Magma Brix" if H_num[22] == 1 else "C Cyclone Brix",
        65: "B Magma Pol" if H_num[22] == 1 else "C Cyclone Pol",
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
    }
    for k, v in fixed.items():
        C_s[k] = v

    b_trim = B_name.strip()
    center_b = " " * max(0, int(40 - len(b_trim) / 2)) + b_trim

    def fmt_item(idx: Any, label: str, suppressed: bool = False) -> str:
        idx_str = f"{idx:3d}" if isinstance(idx, int) else str(idx).rjust(3)
        if suppressed:
            return f"{idx_str}     {label.ljust(40)}      XXXXXXXXXX"
        return f"{idx_str}     {label.ljust(40)}"

    p1: List[str] = [
        center_b,
        "",
        " " * 25 + "DAILY REPORT DATA INPUT FORM" + " " * 16 + "Page 1",
        "",
        "",
        fmt_item("   ", "Report Date", False),
        fmt_item(1, C_s[1], True),
        fmt_item(2, C_s[2], False),
        "",
    ]
    for j in range(3, 14):
        p1.append(fmt_item(j, C_s[j], False))
    p1.append("")
    for j in range(14, 26):
        p1.append(fmt_item(j, C_s[j], False))
    p1.append("")
    p1.append(fmt_item(26, C_s[26], False))
    p1.append(fmt_item(27, C_s[27], False))
    p1.append(fmt_item(28, C_s[28], H_num[2] == 0))
    p1.append(fmt_item(29, C_s[29], H_num[3] == 0))
    p1.append("")
    p1.append(fmt_item(30, C_s[30], False))
    p1.append(fmt_item(31, C_s[31], False))
    p1.append(fmt_item(32, C_s[32], H_num[4] == 0))
    p1.append(fmt_item(33, C_s[33], H_num[5] == 0))
    p1.append("")
    p1.append(fmt_item(34, C_s[34], False))
    p1.append(fmt_item(35, C_s[35], False))
    p1.append("")
    p1.append(fmt_item(36, C_s[36], False))
    p1.append(fmt_item(37, C_s[37], False))
    p1.append(fmt_item(38, C_s[38], H_num[6] == 0))
    p1.append(fmt_item(39, C_s[39], H_num[7] == 0))

    p2: List[str] = [
        center_b,
        "",
        " " * 22 + "DAILY REPORT DATA INPUT FORM (Cont'd)" + " " * 10 + "Page 2",
        "",
        "",
        fmt_item(40, C_s[40], H_num[18] == 0),
        fmt_item(41, C_s[41], H_num[18] == 0),
        "",
        fmt_item(42, C_s[42], False),
        fmt_item(43, C_s[43], False),
        fmt_item(44, C_s[44], H_num[8] == 0),
        fmt_item(45, C_s[45], H_num[9] == 0),
        "",
        fmt_item(46, C_s[46], False),
        fmt_item(47, C_s[47], False),
        "",
        fmt_item(48, C_s[48], H_num[19] == 0),
        fmt_item(49, C_s[49], H_num[19] == 0),
        "",
        fmt_item(50, C_s[50], False),
        fmt_item(51, C_s[51], False),
        "",
        fmt_item(52, C_s[52], False),
        fmt_item(53, C_s[53], False),
        "",
        fmt_item(54, C_s[54], False),
        fmt_item(55, C_s[55], False),
        "",
        fmt_item(56, C_s[56], H_num[19] == 0),
        fmt_item(57, C_s[57], H_num[19] == 0),
        "",
        fmt_item(58, C_s[58], False),
        fmt_item(59, C_s[59], False),
        "",
        fmt_item(60, C_s[60], False),
        fmt_item(61, C_s[61], False),
        "",
        fmt_item(62, C_s[62], False),
        fmt_item(63, C_s[63], False),
        "",
        fmt_item(64, C_s[64], H_num[20] == 0),
        fmt_item(65, C_s[65], H_num[20] == 0),
        "",
        fmt_item(66, C_s[66], False),
        fmt_item(67, C_s[67], H_num[19] == 0),
        fmt_item(68, C_s[68], False),
        fmt_item(69, C_s[69], False),
        "",
        fmt_item(70, C_s[70], False),
        fmt_item(71, C_s[71], False),
        fmt_item(72, C_s[72], H_num[10] == 0),
        fmt_item(73, C_s[73], H_num[11] == 0),
    ]

    p3: List[str] = [
        center_b,
        "",
        " " * 22 + "DAILY REPORT DATA INPUT FORM (Cont'd)" + " " * 10 + "Page 3",
        "",
        fmt_item(74, C_s[74], False),
        fmt_item(75, C_s[75], False),
        fmt_item(76, C_s[76], H_num[12] == 0),
        fmt_item(77, C_s[77], H_num[13] == 0),
        fmt_item(78, C_s[78], H_num[14] == 0),
        "",
        fmt_item(79, C_s[79], False),
        fmt_item(80, C_s[80], False),
        fmt_item(81, C_s[81], H_num[15] == 0),
        fmt_item(82, C_s[82], H_num[16] == 0),
        fmt_item(83, C_s[83], H_num[17] == 0),
        "",
        fmt_item(84, C_s[84], False),
        fmt_item(85, C_s[85], H_num[21] == 0),
        "",
        fmt_item(86, C_s[86], False),
        fmt_item(87, C_s[87], False),
        "",
        fmt_item(88, C_s[88], False),
        "",
    ]
    for j in range(91, 97):
        p3.append(fmt_item(j, C_s[j], False))
    p3.append("")
    for j in (97, 98):
        p3.append(fmt_item(j, C_s[j], False))
    p3.append("")
    for j in range(99, 102):
        p3.append(fmt_item(j, C_s[j], False))
    p3.append("")
    p3.append(fmt_item(102, C_s[102], False))
    p3.append("")
    for j in (103, 104):
        p3.append(fmt_item(j, C_s[j], False))
    p3.append("")
    for j in (105, 106):
        p3.append(fmt_item(j, C_s[j], False))
    p3.append("")
    for j in (107, 108):
        p3.append(fmt_item(j, C_s[j], False))
    p3.append("")
    p3.append(fmt_item(109, C_s[109], True))
    p3.append("")
    p3.append(fmt_item(246, C_s[110], H_num[27] == 0))
    p3.append("")
    for wh in range(1, 5):
        p3.append(fmt_item(250 + wh, f"Lbs Sugar in W/H #{wh}", False))

    p4: List[str] = [
        "REMARKS - LINE 1A:    ------------------------------------------------------------",
        "REMARKS - LINE 1B:    ------------------------------------------------------------",
        "REMARKS - LINE 2A:    ------------------------------------------------------------",
        "REMARKS - LINE 2B:    ------------------------------------------------------------",
        "REMARKS - LINE 3A:    ------------------------------------------------------------",
        "REMARKS - LINE 3B:    ------------------------------------------------------------",
    ]
    return [p1, p2, p3, p4]


def render_mrstokfm(B_name: str) -> List[List[str]]:
    """Renders the 2-page Blank Stock Calculation Data Form (MRSTOKFM)."""
    b_trim = B_name.strip()
    center_b = " " * max(0, int(40 - len(b_trim) / 2)) + b_trim
    streams = [
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
    ]
    pages: List[List[str]] = []
    for unit_lbl in ("Gallons", "Cu. Ft."):
        p: List[str] = [
            center_b,
            "",
            " " * 22 + "DATA FORM FOR STOCK CALCULATIONS",
            "",
            "        Date",
            "",
        ]
        idx = 1
        for st in streams:
            p.append(f"{idx:2d}      {st}, {unit_lbl}")
            p.append(f"{idx+1:2d}      {st}, Brix")
            p.append(f"{idx+2:2d}      {st}, Pol")
            idx += 3
        p.append("")
        p.append("40      Final Molasses Purity for Run")
        p.append("41      Sugar Purity for Run")
        pages.append(p)
    return pages


def render_mrdatapr(
    B_name: str,
    report_date: str,
    X_arr: List[float],
    B1_s: OneBasedArray1D,
    J_s: OneBasedArray1D,
    H_s: OneBasedArray1D,
    H_num: OneBasedArray1D,
    include_todate_workup: bool = False,
) -> List[List[str]]:
    """
    Renders Menu Item 3 (Print Data for Daily Report - MRDATAPR)
    and Menu Item 4 (Print Todate Data File on Disk - MRDATAP2).
    """
    b_trim = B_name.strip()
    center_b = " " * max(0, int(40 - len(b_trim) / 2)) + b_trim
    img_item = "%###   ######################################## -###,###,###,###,###.####"
    img_item4 = "%####  ######################################## -###,###,###,###,###.####"

    def x_val(idx_1based: int) -> float:
        if 1 <= idx_1based <= len(X_arr):
            return float(X_arr[idx_1based - 1])
        return 0.0

    # Fixed labels for X(26..108) and X(134..248) from MRDATAPR & MRDATAP2
    k_labels: Dict[int, str] = {
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
        64: "B Magma Brix" if H_num[22] == 1 else "C Cyclone Brix",
        65: "B Magma Pol" if H_num[22] == 1 else "C Cyclone Pol",
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
    }

    pages: List[List[str]] = []
    if not include_todate_workup:
        p1: List[str] = [
            center_b,
            "",
            " " * 30 + "DAILY REPORT DATA" + " " * 26 + "Page 1",
            "",
            f"      Report Date                                                       {report_date}",
            "",
        ]
        for j in (1, 2):
            p1.append(format_printusing(img_item, [j, k_labels[j], x_val(j)]))
        p1.append("")
        for j in range(3, 13):
            p1.append(format_printusing(img_item, [j, J_s[j - 2], x_val(j)]))
        p1.append(format_printusing(img_item, [13, "Total Hours Available", x_val(13)]))
        p1.append("")
        for j in range(14, 26):
            p1.append(format_printusing(img_item, [j, H_s[j - 13], x_val(j)]))
        p1.append("")
        for rng in ((26, 29), (30, 33), (34, 35), (36, 39)):
            for j in range(rng[0], rng[1] + 1):
                p1.append(format_printusing(img_item, [j, k_labels[j], x_val(j)]))
            p1.append("")
        pages.append(p1)

        p2: List[str] = [
            " " * 26 + "DAILY REPORT DATA (Cont'd)" + " " * 21 + "Page 2",
            "",
        ]
        for rng in (
            (40, 41),
            (42, 45),
            (46, 47),
            (48, 49),
            (50, 51),
            (52, 53),
            (54, 55),
            (56, 57),
            (58, 59),
            (60, 61),
            (62, 63),
            (64, 65),
            (66, 69),
            (70, 73),
        ):
            for j in range(rng[0], rng[1] + 1):
                p2.append(format_printusing(img_item, [j, k_labels[j], x_val(j)]))
            p2.append("")
        pages.append(p2)

        p3: List[str] = [
            " " * 26 + "DAILY REPORT DATA (Cont'd)" + " " * 21 + "Page 3",
            "",
        ]
        for rng in (
            (74, 78),
            (79, 83),
            (84, 85),
            (86, 87),
            (88, 88),
            (91, 96),
            (97, 98),
            (99, 101),
            (102, 102),
            (103, 104),
            (105, 106),
            (107, 108),
        ):
            for j in range(rng[0], rng[1] + 1):
                p3.append(format_printusing(img_item, [j, k_labels[j], x_val(j)]))
            p3.append("")
        p3.append(format_printusing(img_item, [109, k_labels[109], x_val(109)]))
        p3.append(format_printusing(img_item, [246, k_labels[246], x_val(246)]))
        for wh in range(251, 255):
            p3.append(format_printusing(img_item, [wh, k_labels[wh], x_val(wh)]))
        p3.append("")
        for r_idx, r_lbl in enumerate(("1A", "1B", "2A", "2B", "3A", "3B"), start=1):
            p3.append(f"REMARKS - LINE {r_lbl}   {B1_s[r_idx].rstrip()}")
        pages.append(p3)
        return pages

    # Item 4: Print Todate Data File on Disk (MRDATAP2 lines 2920-3860)
    td_labels: Dict[int, str] = {
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
        147: "B Magma Brix and Pol" if H_num[22] == 1 else "C Cyclone Brix and Pol",
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
        168: "B Magma Brix" if H_num[22] == 1 else "C Cyclone Brix",
        169: "B Magma Pol" if H_num[22] == 1 else "C Cyclone Pol",
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
    }

    tp1: List[str] = [
        center_b,
        "",
        " " * 25 + "DAILY REPORT TODATE RESULTS" + " " * 21 + "Page 1",
        "",
        f"      Report Date                                                       {report_date}",
        "",
        "Lost Time",
        "---------",
        "",
    ]
    for j in range(110, 120):
        tp1.append(format_printusing(img_item4, [j, J_s[j - 109], x_val(j)]))
    tp1.append(format_printusing(img_item4, [120, "Total Hours Lost", x_val(120)]))
    tp1.append(format_printusing(img_item4, [121, "Total Hours Available", x_val(121)]))
    tp1.append("")
    tp1.append("Chemicals and Supplies")
    tp1.append("----------------------")
    tp1.append("")
    for j in range(122, 134):
        tp1.append(format_printusing(img_item4, [j, H_s[j - 121], x_val(j)]))
    tp1.append("")
    tp1.append("Weighting Factors")
    tp1.append("-----------------")
    tp1.append("")
    for j in range(134, 148):
        tp1.append(format_printusing(img_item4, [j, td_labels[j], x_val(j)]))
    pages.append(tp1)

    tp2: List[str] = [
        " " * 21 + "DAILY REPORT TODATE RESULTS (Cont'd)" + " " * 16 + "Page 2",
        "",
        "Weight x Analysis",
        "-----------------",
        "",
    ]
    for j in range(148, 170):
        tp2.append(format_printusing(img_item4, [j, td_labels[j], x_val(j)]))
    pages.append(tp2)

    tp3: List[str] = [
        " " * 21 + "DAILY REPORT TODATE RESULTS (Cont'd)" + " " * 16 + "Page 3",
        "",
        "Cu. Ft. x Analysis",
        "------------------",
        "",
    ]
    for j in range(170, 188):
        tp3.append(format_printusing(img_item4, [j, td_labels[j], x_val(j)]))
    tp3.append("")
    tp3.append("Tons Account")
    tp3.append("------------")
    tp3.append("")
    for j in range(188, 204):
        tp3.append(format_printusing(img_item4, [j, td_labels[j], x_val(j)]))
    pages.append(tp3)

    tp4: List[str] = [
        " " * 21 + "DAILY REPORT TODATE RESULTS (Cont'd)" + " " * 16 + "Page 4",
        "",
    ]
    for j in range(204, 246):
        if j in td_labels:
            tp4.append(format_printusing(img_item4, [j, td_labels[j], x_val(j)]))
    tp4.append(format_printusing(img_item4, [247, td_labels[247], x_val(247)]))
    pages.append(tp4)

    return pages


def calculate_and_render_stock(
    B_name: str,
    stock_date: str,
    unit_mode: str,
    inputs_41: List[float],
    H_num: OneBasedArray1D,
) -> Tuple[List[str], Dict[str, float]]:
    """
    Executes MRSTOCKC (unit_mode == 'CF') or MRSTOCKG (unit_mode == 'G')
    given 41 input values (13 streams x 3 [vol, brix, pol] + FM purity + Sugar purity).
    Returns (132-col report lines, summary dict with Lbs Sugar/Molasses Brix/Pol in stock).
    """
    E_st = OneBasedArray2D(18, 12, 0.0)
    names = [
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
    ]
    for idx_s in range(13):
        E_st[idx_s + 1, 1] = inputs_41[idx_s * 3]
        E_st[idx_s + 1, 2] = inputs_41[idx_s * 3 + 1]
        E_st[idx_s + 1, 3] = inputs_41[idx_s * 3 + 2]
    E_st[15, 1] = inputs_41[39]
    E_st[16, 1] = inputs_41[40]

    is_cf = unit_mode.upper() == "CF"

    for j in range(1, 14):
        if E_st[j, 2] != 0:
            E_st[j, 4] = safe_div(E_st[j, 3] * 100.0, E_st[j, 2])
            dens = brix_density_poly_4(E_st[j, 2])
            E_st[j, 5] = dens if is_cf else (dens / 7.48)
            E_st[j, 6] = E_st[j, 1] * E_st[j, 5] / 2000.0
            E_st[j, 7] = E_st[j, 6] * E_st[j, 2] / 100.0
            E_st[j, 8] = E_st[j, 6] * E_st[j, 3] / 100.0

    for col in range(1, 9):
        E_st[14, col] = sum(E_st[r, col] for r in range(1, 14))

    E_st[14, 2] = safe_div(E_st[14, 7] * 100.0, E_st[14, 6])
    E_st[14, 3] = safe_div(E_st[14, 8] * 100.0, E_st[14, 6])
    E_st[14, 4] = safe_div(E_st[14, 3] * 100.0, E_st[14, 2])
    E_st[14, 5] = safe_div(E_st[14, 6] * 2000.0, E_st[14, 1])

    E_st[17, 1] = safe_div(
        E_st[14, 7] * (E_st[14, 4] - E_st[15, 1]), E_st[16, 1] - E_st[15, 1]
    )
    E_st[17, 2] = E_st[17, 1] * E_st[16, 1] / 100.0
    E_st[18, 1] = E_st[14, 7] - E_st[17, 1]
    E_st[18, 2] = E_st[14, 8] - E_st[17, 2]
    E_st[17, 3] = E_st[17, 2] * 2000.0 / 0.96

    k1 = brix_density_poly_4(H_num[30]) * H_num[30] / 748.0
    E_st[18, 3] = safe_div(E_st[18, 1] * 2000.0, k1)

    b_trim = B_name.strip()
    lines: List[str] = []
    lines.append(" " * max(0, int(66 - len(b_trim) / 2)) + b_trim)
    lines.append("")
    lines.append(" " * 56 + "STOCK CALCULATIONS")
    lines.append("")
    lines.append(f"Date: {stock_date}")
    lines.append("--------------")
    lines.append("")

    if is_cf:
        lines.append(
            "Material in Stock   Cu. Ft. Measured   Brix     Pol   Purity   Pounds per Cu. Ft.   Tons Material   Tons Brix    Tons Pol"
        )
        lines.append(
            "-----------------   ----------------  -----   -----   ------   ------------------   -------------   ---------    --------"
        )
        img_row = "%#################   -###,###,###.## -###.## -###.##  -###.##           -#,###.###  -##,###,###.### -#,###,###.### -###,###.###"
    else:
        lines.append(
            "Material in Stock   Gallons Measured   Brix     Pol   Purity   Pounds per Gallon    Tons Material   Tons Brix    Tons Pol"
        )
        lines.append(
            "-----------------   ----------------  -----   -----   ------   -----------------    -------------   ---------    --------"
        )
        img_row = "%#################    -##,###,###.## -###.## -###.##  -###.##           -#,###.###       -#,###.###    -#,###.###   -#,###.###"

    for j in range(1, 14):
        lines.append(
            format_printusing(
                img_row,
                [
                    names[j - 1],
                    E_st[j, 1],
                    E_st[j, 2],
                    E_st[j, 3],
                    E_st[j, 4],
                    E_st[j, 5],
                    E_st[j, 6],
                    E_st[j, 7],
                    E_st[j, 8],
                ],
            )
        )
    sep_st = (
        "-------------             ----------  -----   -----   ------               ------        --------     -------     -------"
    )
    lines.append(sep_st)
    j = 14
    lines.append(
        format_printusing(
            img_row,
            [
                names[j - 1],
                E_st[j, 1],
                E_st[j, 2],
                E_st[j, 3],
                E_st[j, 4],
                E_st[j, 5],
                E_st[j, 6],
                E_st[j, 7],
                E_st[j, 8],
            ],
        )
    )
    lines.append(sep_st)
    lines.append("")
    lines.append("")
    lines.append("Assumptions")
    lines.append("-----------")
    lines.append("")
    img_assump = "%################################      -###.##"
    for j in (15, 16):
        lines.append(format_printusing(img_assump, [names[j - 1], E_st[j, 1]]))
    lines.append("")
    lines.append("")
    lines.append("                                  SUGAR AND MOLASSES IN PROCESS")
    lines.append("                                  -----------------------------")
    lines.append("")
    lines.append("                                    Lbs Brix            Lbs Pol")
    lines.append("                                    --------            -------")

    img_1290 = "%########################    -###,###,###,###   -###,###,###,###        (Lbs. 96 Sugar in Stock = -##,###,###.##)"
    img_1320 = "%########################    -###,###,###,###   -###,###,###,###        (Final Molasses in Stock - Gals. @ ##.## Brix =-#,###,###.##)"
    img_1350 = "%TOTAL                       -###,###,###,###   -###,###,###,###"

    lines.append(
        format_printusing(
            img_1290, [names[16], E_st[17, 1] * 2000.0, E_st[17, 2] * 2000.0, E_st[17, 3]]
        )
    )
    lines.append("")
    lines.append(
        format_printusing(
            img_1320,
            [
                names[17],
                E_st[18, 1] * 2000.0,
                E_st[18, 2] * 2000.0,
                H_num[30],
                E_st[18, 3],
            ],
        )
    )
    lines.append("                                   ---------           --------")
    lines.append(format_printusing(img_1350, [E_st[14, 7] * 2000.0, E_st[14, 8] * 2000.0]))
    lines.append("                                   ---------           --------")

    summary = {
        "sugar_lbs_brix": E_st[17, 1] * 2000.0,
        "sugar_lbs_pol": E_st[17, 2] * 2000.0,
        "sugar_lbs_96": E_st[17, 3],
        "molasses_lbs_brix": E_st[18, 1] * 2000.0,
        "molasses_lbs_pol": E_st[18, 2] * 2000.0,
        "molasses_gals_at_brix": E_st[18, 3],
    }
    return lines, summary



# ==============================================================================
# Historical Presets & Oct 2015 St. Mary Sugar Co-op Dataset
# ==============================================================================

def get_st_mary_oct2015_params() -> Dict[str, Any]:
    """Returns the MRPARAMS dictionary for St. Mary Sugar Cooperative, Inc. (Oct 2015)."""
    j_list = [
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
    ]
    h_str_list = [
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
    ]
    i_str_list = [
        "W",  # 1: Averaged by Cane Weighting (W)
        "Y",  # 2: Crusher Juice Glucose
        "N",  # 3: Crusher Juice pH
        "Y",  # 4: Mixed Juice Glucose
        "N",  # 5: Mixed Juice pH
        "Y",  # 6: Clarified Juice Glucose
        "Y",  # 7: Clarified Juice pH
        "N",  # 8: Syrup Glucose
        "Y",  # 9: Syrup pH
        "Y",  # 10: Sugar Made Starch (Glu/Dex)
        "N",  # 11: Sugar Made Dextran (Ash/Str)
        "Y",  # 12: Final Molasses Made Glucose
        "Y",  # 13: Final Molasses Made Ash
        "Y",  # 14: Final Molasses Made Clerget
        "N",  # 15: Final Molasses Shipped Glucose
        "N",  # 16: Final Molasses Shipped Ash
        "N",  # 17: Final Molasses Shipped Clerget
        "Y",  # 18: Filtrate Juice Brix and Pol
        "N",  # 19: Top-Off A Strikes Brix and Pol
        "Y",  # 20: Either B Magma or C Cyclones
        "N",  # 21: Filter Cake Moistures
        "Y",  # 22: B Magma (Y) or C Cyclone (N)
        "N",  # 23: Expanded Print Capability
        "Y",  # 24: Metered Imbibition Water
        *["" for _ in range(6)],
    ]
    h_num = [0.0] * 37
    h_num[0] = 0.0  # H(1): 0 = Cane Weighting
    for idx in range(2, 24):
        h_num[idx - 1] = 0.0 if i_str_list[idx - 1] == "N" else 1.0
    h_num[24] = 15279.0  # H(25): Julian date for 10/06/15
    h_num[25] = 6.0      # H(26): Last day number
    h_num[26] = 1.0      # H(27): Metered imbibition flag
    h_num[28] = 1262.0   # H(29): Total Roll Surface of All Mill Rolls
    h_num[29] = 79.50    # H(30): Brix Desired for Molasses M&E
    h_num[35] = 0.0      # H(36): Printer Selection Code (0 = System 215)
    h_num[36] = 3.0      # H(37): Disk Selection Code (3 = D12)
    return {
        "B$": "ST. MARY SUGAR COOPERATIVE, INC.",
        "A1$": "10/06/15",
        "J$": j_list,
        "H$": h_str_list,
        "I$": i_str_list,
        "H": h_num,
    }


def get_st_mary_oct2015_daily_inputs() -> List[Dict[str, Any]]:
    """
    Returns the 6 days of raw daily inputs (10/06/15 to 10/11/15) reconstructed
    from `Program scanned Outputs.pdf`.
    """
    return [
        {
            "day": 1,
            "date": "10/06/15",
            "julian": 15279,
            "inputs": {
                2: 1806422.36,
                13: 17.50,
                14: 666.0,
                16: 110.0,
                21: 10838.0,
                26: 19.50,
                27: 16.90,
                30: 15.10,
                31: 12.92,
                34: 2.60,
                35: 1.98,
                36: 14.70,
                37: 12.98,
                39: 6.05,
                40: 19.28,
                41: 16.67,
                42: 14.70,
                66: 9987.0,
                68: 1604.0,
                70: 0.00,
                71: 99.00,
                84: 2.30,
                86: 2.23,
                87: 50.00,
                88: 8336.79,
                91: 6436.79,
                92: 6472.585,
                93: 1935.48,
                94: 300.00,
                95: 275596.0,
                99: 13.65,
                100: 16.54,
                101: 18.06,
                102: 0.00,
                103: 86.0,
                104: 70.0,
                105: 827113.0,
                106: 818842.0,
                107: 237564.0,
                108: 78396.0,
                246: 0.0,
            },
            "remarks": [
                "SUGAR DETECTED IN INJECTION WATER AT 8.63 POL",
                "SUGAR IN STOCK BASED ON ASSUMPTIONS, MISSING LAB DATA",
                "FILTER CAKE AMOUNT ASSUMED BASED ON PREV REPORTS",
                "SUGAR MADE PURITY ASSUMED AT 99, NO LAB DATA",
                "",
                "",
            ],
        },
        {
            "day": 2,
            "date": "10/07/15",
            "julian": 15280,
            "inputs": {
                2: 2112997.66,
                13: 24.00,
                15: 24.0,
                16: 551.0,
                21: 12449.0,
                25: 17.0,
                26: 19.30,
                27: 16.53,
                28: 0.83,
                30: 15.83,
                31: 13.50,
                32: 0.57,
                34: 2.75,
                35: 2.04,
                36: 15.40,
                37: 13.23,
                38: 0.39,
                39: 6.04,
                40: 19.28,
                41: 16.67,
                42: 44.00,
                43: 38.30,
                45: 5.84,
                46: 91.25,
                47: 79.08,
                50: 90.60,
                51: 69.75,
                54: 80.80,
                55: 60.86,
                58: 79.60,
                59: 49.32,
                66: 33823.0,
                68: 5213.0,
                70: 0.67,
                71: 98.10,
                72: 0.80,
                84: 5.19,
                86: 2.50,
                87: 47.47,
                88: 9583.31,
                91: 10976.70,
                92: 12976.53,
                93: 5180.25,
                94: 400.00,
                95: 1653526.0,
                99: 16.68,
                100: 13.79,
                101: 18.52,
                102: 0.00,
                103: 94.0,
                104: 66.0,
                105: 1252930.0,
                106: 1240401.0,
                107: 522519.0,
                108: 172436.0,
                246: 1909.95,
            },
            "remarks": [
                "NO LAB DATA FOR C MASSECUITE",
                "",
                "",
                "",
                "",
                "",
            ],
        },
        {
            "day": 3,
            "date": "10/08/15",
            "julian": 15281,
            "inputs": {
                2: 2511930.50,
                13: 24.00,
                15: 24.0,
                16: 881.0,
                21: 14671.0,
                25: 17.0,
                26: 20.00,
                27: 17.37,
                28: 0.82,
                30: 16.60,
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
                50: 92.20,
                51: 69.06,
                52: 92.60,
                53: 53.91,
                54: 80.05,
                55: 60.55,
                58: 82.45,
                59: 46.72,
                60: 92.20,
                61: 58.08,
                62: 93.40,
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
                84: 5.10,
                86: 2.51,
                87: 49.89,
                88: 11285.44,
                91: 11530.44,
                92: 10569.27,
                93: 2547.27,
                94: 400.00,
                95: 2324038.0,
                96: 12431.0,
                99: 13.88,
                100: 16.74,
                101: 18.57,
                102: 0.00,
                103: 94.0,
                104: 52.0,
                105: 1303447.0,
                106: 1289239.0,
                107: 834292.0,
                108: 275333.0,
                246: 2179.25,
            },
            "remarks": [
                "RAW COLOR 2264",
                "",
                "",
                "",
                "",
                "",
            ],
        },
        {
            "day": 4,
            "date": "10/09/15",
            "julian": 15282,
            "inputs": {
                2: 2925200.47,
                13: 24.00,
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
                36: 15.70,
                37: 13.76,
                38: 0.60,
                39: 6.49,
                42: 62.30,
                43: 53.69,
                45: 6.09,
                46: 91.87,
                47: 81.06,
                50: 93.20,
                51: 71.25,
                52: 92.60,
                53: 53.91,
                54: 79.72,
                55: 61.38,
                58: 80.64,
                59: 48.62,
                60: 90.67,
                61: 63.24,
                62: 93.90,
                63: 81.66,
                64: 93.90,
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
                94: 400.00,
                95: 2395498.0,
                96: 124310.0,
                99: 14.11,
                100: 16.89,
                101: 18.44,
                102: 0.00,
                103: 94.0,
                104: 68.0,
                105: 1835856.0,
                106: 1825953.0,
                107: 1179482.0,
                108: 389408.0,
                246: 2109.97,
            },
            "remarks": ["", "", "", "", "", ""],
        },
        {
            "day": 5,
            "date": "10/10/15",
            "julian": 15283,
            "inputs": {
                2: 2479568.42,
                13: 24.00,
                15: 240.0,
                16: 660.0,
                21: 14043.0,
                25: 17.0,
                26: 19.63,
                27: 16.97,
                28: 0.82,
                30: 15.99,
                31: 14.04,
                32: 0.00,
                34: 3.50,
                35: 2.74,
                36: 15.53,
                37: 13.81,
                38: 0.53,
                39: 7.01,
                40: 19.28,
                41: 16.67,
                42: 60.70,
                43: 53.15,
                45: 6.78,
                46: 92.51,
                47: 82.53,
                50: 93.53,
                51: 71.97,
                52: 95.78,
                53: 56.50,
                54: 80.90,
                55: 62.92,
                58: 81.25,
                59: 46.92,
                60: 91.90,
                61: 65.68,
                62: 94.47,
                63: 83.49,
                64: 94.20,
                65: 86.01,
                66: 50935.0,
                68: 23395.0,
                69: 10227.0,
                70: 0.35,
                71: 98.81,
                72: 1.30,
                74: 69.00,
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
                94: 350.00,
                95: 2614862.0,
                96: 80801.70,
                99: 14.24,
                100: 17.01,
                101: 18.10,
                102: 0.00,
                103: 82.0,
                104: 58.0,
                105: 1734092.0,
                106: 1719252.0,
                107: 1175831.0,
                108: 388202.0,
                246: 2139.27,
            },
            "remarks": [
                "RAW COLOR 2251",
                "MOIST .35",
                "SAFETY FACTOR .22",
                "SPECIAL COLOR 3875",
                "SUGAR DETECTED IN INJECTION WATER 8 POL",
                "",
            ],
        },
        {
            "day": 6,
            "date": "10/11/15",
            "julian": 15284,
            "inputs": {
                2: 2849001.62,
                13: 24.00,
                15: 240.0,
                16: 660.0,
                21: 16213.0,
                25: 17.0,
                26: 19.43,
                27: 16.93,
                28: 0.64,
                30: 15.30,
                31: 13.26,
                32: 0.44,
                34: 4.38,
                35: 3.45,
                36: 16.20,
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
                54: 78.00,
                55: 59.79,
                58: 76.63,
                59: 45.41,
                60: 91.20,
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
                87: 49.00,
                88: 12471.96,
                91: 11271.96,
                92: 11419.09,
                93: 3451.78,
                94: 400.00,
                95: 2513672.0,
                96: 74586.18,
                99: 14.17,
                100: 16.91,
                101: 18.22,
                102: 0.00,
                103: 86.0,
                104: 56.0,
                105: 1914562.0,
                106: 1898016.0,
                107: 1062831.0,
                108: 350926.0,
                246: 2074.04,
            },
            "remarks": [
                "RAW COLOR 2175   ",
                "RAW COLOR BIG PILE 2116",
                "RAW COLOR OUT OF PROD 2341",
                "",
                "",
                "",
            ],
        },
    ]



# ==============================================================================
# Virtual Disk & Interactive Session State Machine (MRSTART + All 17 Options)
# ==============================================================================

DISK_CODE_MAP = {
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
}


class MFRSession:
    """
    Manages the COMMON block, virtual disk files, 80-column CRT terminal buffer,
    top-of-screen status rows (AT(1,0), AT(2,0), AT(3,0)), and 132-column line printer pages.
    """

    def __init__(self, data_root: Path = DATA_ROOT):
        self.data_root = data_root
        self.data_root.mkdir(parents=True, exist_ok=True)

        # COMMON block variables
        self.B_str: str = "ST. MARY SUGAR COOPERATIVE, INC."
        self.B1_str = OneBasedArray1D(6, " ")
        self.A1_str: str = "10/06/15"
        self.A2_str = OneBasedArray1D(3, " ")
        self.A = OneBasedArray2D(258, 3, 0.0)
        self.J_str = OneBasedArray1D(10, " ")
        self.H_str = OneBasedArray1D(20, " ")
        self.I_str = OneBasedArray1D(30, " ")
        self.H_num = OneBasedArray1D(37, 0.0)
        self.B = OneBasedArray2D(28, 4, 0.0)
        self.C = OneBasedArray2D(8, 7, 0.0)
        self.D = OneBasedArray2D(10, 6, 0.0)
        self.E = OneBasedArray2D(18, 12, 0.0)
        self.F = OneBasedArray2D(8, 10, 0.0)
        self.G = OneBasedArray2D(12, 8, 0.0)

        # Terminal & Printer State
        self.crt_lines: List[str] = []
        self.top_bar_row1: str = ""  # AT(1,0) prompt / date verification
        self.top_bar_row3: str = ""  # AT(3,0) RE-ENTER error banner
        self.current_prompt: str = ""
        self.beep_flag: bool = False
        self.strict_wang_mode: bool = False  # If True, empty Enter in MRDATACO triggers RE-ENTER

        # Printer pages: list of {"title": str, "pages": List[List[str]]}
        self.printer_jobs: List[Dict[str, Any]] = []

        # Interactive State Machine
        self.state: str = "MENU"
        self.ctx: Dict[str, Any] = {}

        # Initialize disk if needed
        if not (self.data_root / "MRPARAMS.json").exists():
            self.seed_st_mary_oct2015()
        else:
            self.load_mrparams()
            self.show_main_menu()

    # --------------------------------------------------------------------------
    # Disk Persistence Helpers
    # --------------------------------------------------------------------------

    def get_disk_name(self, code: Optional[int] = None) -> str:
        c = int(round(self.H_num[37])) if code is None else int(code)
        return DISK_CODE_MAP.get(c, "D12")

    def get_disk_dir(self, code: Optional[int] = None) -> Path:
        d = self.data_root / self.get_disk_name(code)
        d.mkdir(parents=True, exist_ok=True)
        return d

    def load_mrparams(self) -> None:
        p_file = self.data_root / "MRPARAMS.json"
        if not p_file.exists():
            return
        with open(p_file, "r", encoding="utf-8") as f:
            obj = json.load(f)
        self.B_str = obj.get("B$", "ST. MARY SUGAR COOPERATIVE, INC.")
        self.A1_str = obj.get("A1$", "10/06/15")
        self.J_str.from_list(obj.get("J$", []))
        self.H_str.from_list(obj.get("H$", []))
        self.I_str.from_list(obj.get("I$", []))
        self.H_num.from_list(obj.get("H", []))

    def save_mrparams(self) -> None:
        p_file = self.data_root / "MRPARAMS.json"
        obj = {
            "B$": self.B_str,
            "A1$": self.A1_str,
            "J$": self.J_str.to_list(),
            "H$": self.H_str.to_list(),
            "I$": self.I_str.to_list(),
            "H": self.H_num.to_list(),
        }
        with open(p_file, "w", encoding="utf-8") as f:
            json.dump(obj, f, indent=2)

    def day_file_path(self, day_num: int, disk_code: Optional[int] = None) -> Path:
        return self.get_disk_dir(disk_code) / f"{int(round(day_num)):03d}.json"

    def day_file_exists(self, day_num: int, disk_code: Optional[int] = None) -> bool:
        return self.day_file_path(day_num, disk_code).exists()

    def save_day_file(
        self,
        day_num: int,
        a1_date: str,
        x_arr: List[float],
        b1_remarks: List[str],
        disk_code: Optional[int] = None,
    ) -> None:
        p = self.day_file_path(day_num, disk_code)
        with open(p, "w", encoding="utf-8") as f:
            json.dump(
                {
                    "day": int(round(day_num)),
                    "A1$": a1_date,
                    "X": [float(v) for v in x_arr[:258]],
                    "B1$": [str(s) for s in b1_remarks[:6]],
                },
                f,
                indent=2,
            )

    def load_day_file(
        self, day_num: int, disk_code: Optional[int] = None
    ) -> Tuple[str, List[float], List[str]]:
        p = self.day_file_path(day_num, disk_code)
        with open(p, "r", encoding="utf-8") as f:
            obj = json.load(f)
        a1 = obj.get("A1$", "  /  /  ")
        x_list = obj.get("X", [0.0] * 258)
        if len(x_list) < 258:
            x_list = x_list + [0.0] * (258 - len(x_list))
        b1_list = obj.get("B1$", [" "] * 6)
        if len(b1_list) < 6:
            b1_list = b1_list + [" "] * (6 - len(b1_list))
        return a1, x_list, b1_list

    def list_disk_files(self, disk_code: Optional[int] = None) -> List[Dict[str, Any]]:
        d = self.get_disk_dir(disk_code)
        out = []
        for p in sorted(d.glob("*.json")):
            try:
                with open(p, "r", encoding="utf-8") as f:
                    meta = json.load(f)
                out.append(
                    {
                        "name": p.stem,
                        "date": meta.get("A1$", ""),
                        "crop_day": int(round(meta.get("X", [0])[0])) if meta.get("X") else 0,
                    }
                )
            except Exception:
                out.append({"name": p.stem, "date": "", "crop_day": 0})
        return out

    # --------------------------------------------------------------------------
    # Seeding Demo Data (St. Mary Oct 2015 / Raceland PLATTER1.BS2)
    # --------------------------------------------------------------------------

    def seed_st_mary_oct2015(self) -> None:
        """Populates MRPARAMS and files 000..006 on D12 (and backup D13) for St. Mary Sugar Co-op."""
        params = get_st_mary_oct2015_params()
        with open(self.data_root / "MRPARAMS.json", "w", encoding="utf-8") as f:
            json.dump(params, f, indent=2)
        self.load_mrparams()

        # Clear D12
        d12 = self.get_disk_dir(3)
        for p in d12.glob("*.json"):
            p.unlink()

        # Create file "000" (day before crop started: 10/05/15, Julian 15278)
        x0 = [0.0] * 258
        x0[0] = 0.0
        x0[242] = 15278.0  # X(243)
        self.save_day_file(0, "10/05/15", x0, [" "] * 6, disk_code=3)

        # Run MRDATAWU for Days 1..6 sequentially
        days_data = get_st_mary_oct2015_daily_inputs()
        for d_info in days_data:
            day_num = d_info["day"]
            dt_str = d_info["date"]
            jul = d_info["julian"]
            _, prev_x, _ = self.load_day_file(day_num - 1, disk_code=3)

            self.A.clear()
            for j in range(1, 259):
                self.A[j, 3] = prev_x[j - 1]
            self.A[1, 1] = float(day_num)
            self.A[243, 1] = float(jul)
            for k_idx, val in d_info["inputs"].items():
                self.A[int(k_idx), 1] = float(val)

            run_workup_on_A(self.A, self.H_num, is_correction=False)
            x_new = [self.A[j, 2] for j in range(1, 259)]
            self.save_day_file(day_num, dt_str, x_new, d_info["remarks"], disk_code=3)

        # Also copy to D13 backup
        d13 = self.get_disk_dir(4)
        for p in d13.glob("*.json"):
            p.unlink()
        for p in d12.glob("*.json"):
            shutil.copy2(p, d13 / p.name)

        self.show_main_menu()

    def seed_raceland_platter(self) -> None:
        """Loads the Raceland Raw Sugar, L.L.C. MRPARAMS extracted from PLATTER1.BS2."""
        platter_params_path = ROOT_DIR / "extracted_basic" / "MRPARAMS_platter.json"
        if platter_params_path.exists():
            # Fix alignment of B$ and A1$ from raw MRPARAMS extraction
            j_list = [
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
            ]
            h_str_list = [
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
            ]
            i_str_list = [
                "W", "N", "Y", "N", "Y", "N", "Y", "N", "Y", "Y", "Y", "N",
                "N", "N", "N", "N", "N", "Y", "N", "Y", "N", "Y", "N", "Y",
                "", "", "", "", "", "",
            ]
            h_num = [0.0] * 37
            h_num[0] = 0.0
            for idx in range(2, 24):
                h_num[idx - 1] = 0.0 if i_str_list[idx - 1] == "N" else 1.0
            h_num[24] = 22265.0
            h_num[26] = 1.0
            h_num[28] = 1644.0
            h_num[29] = 79.50
            h_num[35] = 0.0
            h_num[36] = 3.0
            obj = {
                "B$": "RACELAND RAW SUGAR, L.L.C.",
                "A1$": "09/22/22",
                "J$": j_list,
                "H$": h_str_list,
                "I$": i_str_list,
                "H": h_num,
            }
            with open(self.data_root / "MRPARAMS.json", "w", encoding="utf-8") as f:
                json.dump(obj, f, indent=2)
            self.load_mrparams()
            d12 = self.get_disk_dir(3)
            for p in d12.glob("*.json"):
                p.unlink()
            self.show_main_menu()

    # --------------------------------------------------------------------------
    # CRT Screen & Menu Helpers (MRSTART lines 0060-0530)
    # --------------------------------------------------------------------------

    def clear_crt(self) -> None:
        self.crt_lines = []
        self.top_bar_row1 = ""
        self.top_bar_row3 = ""

    def print_crt(self, text: str = "") -> None:
        for line in text.split("\n"):
            self.crt_lines.append(line)

    def add_printer_job(self, title: str, pages: List[List[str]]) -> None:
        import datetime
        job_id = len(self.printer_jobs) + 1
        ts = datetime.datetime.now().strftime("%H:%M:%S")
        self.printer_jobs.insert(0, {"id": job_id, "timestamp": ts, "title": title, "pages": pages})

    def show_main_menu(self) -> None:
        """Executes MRSTART lines 0060-0380."""
        self.A.clear()
        for j in range(1, 36):
            self.H_num[j] = 0.0
        self.load_mrparams()
        self.clear_crt()
        b_trim = self.B_str.strip()
        self.print_crt(" " * 26 + "MANUFACTURING REPORT MENU")
        self.print_crt(" " * 33 + "VERSION 2.1")
        self.print_crt(" " * max(0, int(40 - len(b_trim) / 2)) + b_trim)
        self.print_crt("")
        self.print_crt(" 1.   Input Data for Daily Report")
        self.print_crt(" 2.   Correct Data for Daily Report")
        self.print_crt(" 3.   Print Data for Daily Report")
        self.print_crt(" 4.   Print Todate Data File on Disk")
        self.print_crt(" 5.   Print Daily Report")
        self.print_crt(" 6.   Print Weekly Report")
        self.print_crt(" 7.   Perform Stock in Process Calculations")
        self.print_crt(" 8.   Help Routine for Daily Report")
        self.print_crt(" 9.   End of Crop Correction Routine")
        self.print_crt("10.   Customize Program")
        self.print_crt("11.   Print Customized File")
        self.print_crt("12.   Print up Data Forms")
        self.print_crt("13.   Print Weekly Comparative Report Form")
        self.print_crt("14.   Back-up Data to Hard Disk (D13)")
        self.print_crt("16.   END")
        self.print_crt("17.   Delete Data Files at Start of Crop")
        self.print_crt("")
        self.current_prompt = "WHICH ITEM NUMBER DO YOU WANT"
        self.state = "MENU"
        self.ctx = {}

    def _ask_date(self, prompt_text: str, next_state: str) -> None:
        """Initiates DEFFN'220(P$) date entry & confirmation."""
        self.top_bar_row1 = prompt_text
        self.top_bar_row3 = ""
        self.current_prompt = prompt_text
        self.ctx["date_prompt"] = prompt_text
        self.ctx["date_next_state"] = next_state
        self.state = "DATE_ENTRY"

    def _trigger_reenter(self, msg: str = "RE-ENTER") -> None:
        self.beep_flag = True
        self.top_bar_row3 = msg
        self.print_crt(f"*** {msg} ***")


    # --------------------------------------------------------------------------
    # Main Input Dispatcher
    # --------------------------------------------------------------------------

    def handle_input(self, raw_input: str) -> Dict[str, Any]:
        """Processes a single line of user terminal input and advances the state machine."""
        self.beep_flag = False
        self.top_bar_row3 = ""
        val_str = raw_input.strip()
        self.print_crt(f"{self.current_prompt}? {raw_input}")

        if self.state == "MENU":
            self._handle_menu_choice(val_str)
        elif self.state == "DATE_ENTRY":
            self._handle_date_entry(val_str)
        elif self.state == "DATE_CONFIRM":
            self._handle_date_confirm(val_str)
        elif self.state == "WAIT_RETURN_MENU":
            self.show_main_menu()
        elif self.state == "ITEM1_ALREADY_ENTERED":
            self._handle_item1_already_entered(val_str)
        elif self.state == "ITEM1_NO_DATA_START_CROP":
            self._handle_item1_start_crop_yn(val_str)
        elif self.state == "MRDATA_INPUT":
            self._handle_mrdata_step(raw_input)
        elif self.state == "MRDATACO_INPUT":
            self._handle_mrdataco_step(raw_input)
        elif self.state == "REPORT_CHECK_PAGE_YN":
            self._handle_report_check_yn(val_str)
        elif self.state == "DAILY_REPORT_COPIES":
            self._handle_daily_report_copies(val_str)
        elif self.state == "WEEKLY_REPORT_NUM":
            self._handle_weekly_report_num(val_str)
        elif self.state == "WEEKLY_REPORT_COPIES":
            self._handle_weekly_report_copies(val_str)
        elif self.state == "WEEKLY_REPORT_OK":
            self._handle_weekly_report_ok(val_str)
        elif self.state == "WEEKLY_REMARKS":
            self._handle_weekly_remarks(raw_input)
        elif self.state == "MRSTOCK_UNIT":
            self._handle_mrstock_unit(val_str)
        elif self.state == "MRSTOCK_INPUT":
            self._handle_mrstock_step(val_str)
        elif self.state == "MRSTOCK_OK":
            self._handle_mrstock_ok(val_str)
        elif self.state == "MRHELP_MODE":
            self._handle_mrhelp_mode(val_str)
        elif self.state == "MRHELPC_INPUT":
            self._handle_mrhelpc_step(val_str)
        elif self.state == "MRHELPS_INPUT":
            self._handle_mrhelps_step(val_str)
        elif self.state == "MRHELP_OK":
            self._handle_mrhelp_ok(val_str)
        elif self.state == "MRENCROP_INPUT":
            self._handle_mrencrop_step(raw_input)
        elif self.state == "MRCUSTOM_INPUT":
            self._handle_mrcustom_step(raw_input)
        elif self.state == "MRBLANFM_CHOICE":
            self._handle_mrblanfm_choice(val_str)
        elif self.state == "ITEM17_CONFIRM":
            self._handle_item17_confirm(val_str)
        elif self.state == "HALTED":
            self.show_main_menu()

        return self.get_status_payload()

    def get_status_payload(self) -> Dict[str, Any]:
        return {
            "state": self.state,
            "crt_lines": self.crt_lines[-200:],
            "top_bar_row1": self.top_bar_row1,
            "top_bar_row3": self.top_bar_row3,
            "current_prompt": self.current_prompt,
            "beep": self.beep_flag,
            "strict_wang_mode": self.strict_wang_mode,
            "factory_name": self.B_str.strip(),
            "crop_start_date": self.A1_str.strip(),
            "active_disk": self.get_disk_name(),
            "disk_files": self.list_disk_files(),
            "printer_jobs": self.printer_jobs,
        }

    # --------------------------------------------------------------------------
    # Menu Choice & Date Subroutines
    # --------------------------------------------------------------------------

    def _handle_menu_choice(self, val_str: str) -> None:
        try:
            x = int(float(val_str))
        except ValueError:
            self._trigger_reenter()
            self.show_main_menu()
            return

        if x == 1:
            # Item 1 - Daily Report Input (lines 0550-0600)
            self.clear_crt()
            self.print_crt("DAILY DATA INPUT ROUTINE")
            if not self.day_file_exists(0):
                self.current_prompt = "NO DATA FILES ON DISK - DO YOU WANT TO START THE CROP (Y OR N)"
                self.state = "ITEM1_NO_DATA_START_CROP"
            else:
                self._ask_date("REPORT DATE (MM/DD/YY)?", "ITEM1_AFTER_DATE")
        elif x == 2:
            self.clear_crt()
            self.print_crt("CORRECT DAILY REPORT DATA ROUTINE")
            self._ask_date("ENTER DATE OF REPORT TO BE CORRECTED (MM/DD/YY)?", "ITEM2_AFTER_DATE")
        elif x in (3, 4):
            self.clear_crt()
            self.print_crt("PRINT DAILY REPORT DATA ROUTINE")
            self.ctx["menu_x"] = x
            self._ask_date("DATE OF REPORT DATA TO BE PRINTED (MM/DD/YY)?", "ITEM34_AFTER_DATE")
        elif x in (5, 6):
            self.ctx["menu_x"] = x
            self.H_num[34] = 0.0
            self.H_num[35] = 0.0
            self.A2_str[3] = self.A1_str
            self.current_prompt = "DO YOU WANT REPORT CHECKING PAGE PRINTED (Y OR N)"
            self.state = "REPORT_CHECK_PAGE_YN"
        elif x == 7:
            self.clear_crt()
            self._ask_date("DATE OF STOCK REPORT (MM/DD/YY)?", "ITEM7_AFTER_DATE")
        elif x == 8:
            self.clear_crt()
            self.print_crt("HELP ROUTINE")
            self.print_crt("")
            self.print_crt("1. Core Sampler Factory Help (MRHELPC)")
            self.print_crt("2. Standard Ton Factory Help (MRHELPS)")
            self.current_prompt = "SELECT HELP ROUTINE (1 OR 2, RETURN=1)"
            self.state = "MRHELP_MODE"
        elif x == 9:
            self.clear_crt()
            self.print_crt("END OF CROP CORRECTION ROUTINE")
            self._ask_date("DATE OF LAST CROP DAY (MM/DD/YY)?", "ITEM9_AFTER_DATE")
        elif x == 10:
            self.clear_crt()
            self.print_crt("CUSTOMIZE ROUTINE")
            self._start_mrcustom()
        elif x == 11:
            self.clear_crt()
            self.print_crt("PRINT CUSTOMIZED FILE")
            pages = render_mrcustpr(
                self.B_str, self.A1_str, self.J_str, self.H_str, self.I_str, self.H_num
            )
            self.add_printer_job("CUSTOM PARAMETERS (MRCUSTPR)", pages)
            self.show_main_menu()
        elif x == 12:
            self.clear_crt()
            self.print_crt("1    DAILY REPORT DATA FORMS")
            self.print_crt("2    STOCK REPORT DATA FORMS")
            self.print_crt("")
            self.current_prompt = "WHICH FORMS DO YOU WANT PRINTED"
            self.state = "MRBLANFM_CHOICE"
        elif x == 13:
            self.ctx["menu_x"] = 6
            self.H_num[34] = 1.0
            self.H_num[35] = 0.0
            self.A2_str[3] = self.A1_str
            self.current_prompt = "DO YOU WANT REPORT CHECKING PAGE PRINTED (Y OR N)"
            self.state = "REPORT_CHECK_PAGE_YN"
        elif x == 14:
            # Back-up Data to Hard Disk (D13)
            d12 = self.get_disk_dir(3)
            d13 = self.get_disk_dir(4)
            for p in d13.glob("*.json"):
                p.unlink()
            for p in d12.glob("*.json"):
                shutil.copy2(p, d13 / p.name)
            self.show_main_menu()
            self.top_bar_row1 = "BACK-UP COMPLETED: COPIED D12 TO HARD DISK (D13)"
        elif x == 15:
            self.H_num[37] = 4.0
            self.save_mrparams()
            self.show_main_menu()
        elif x == 16:
            self.clear_crt()
            self.print_crt("$END - PROGRAM TERMINATED")
            self.current_prompt = "KEY RETURN TO RESTART MRSTART"
            self.state = "HALTED"
        elif x == 17:
            self.current_prompt = "DO YOU WANT TO DELETE ALL DATA FILES TO START CROP (Y OR N)"
            self.state = "ITEM17_CONFIRM"
        else:
            self.show_main_menu()

    def _handle_date_entry(self, val_str: str) -> None:
        parsed = wang_parse_mmddyy(val_str)
        if parsed is None:
            self._trigger_reenter("INVALID DATE (MM/DD/YY) - RE-ENTER")
            return
        _, _, _, fmt_date, julian = parsed
        fmt_norm, julian_norm = wang_julian_to_mmddyy(julian)
        self.ctx["u9_str"] = fmt_norm
        self.ctx["u9_num"] = julian_norm
        self.top_bar_row1 = f"IS DATE OK?   (Y/N)   {fmt_norm}   {julian_norm}"
        self.current_prompt = f"IS DATE OK? (Y/N) {fmt_norm} ({julian_norm})"
        self.state = "DATE_CONFIRM"

    def _handle_date_confirm(self, val_str: str) -> None:
        ans = val_str.upper()
        if ans == "N":
            self._ask_date(self.ctx["date_prompt"], self.ctx["date_next_state"])
            return
        if ans != "Y":
            self._trigger_reenter("ENTER Y OR N")
            return
        self.top_bar_row1 = ""
        u9_str = self.ctx["u9_str"]
        u9_num = self.ctx["u9_num"]
        next_st = self.ctx["date_next_state"]

        if next_st == "ITEM1_AFTER_DATE":
            self.A2_str[2] = u9_str
            u3 = wang_julian_diff(self.H_num[25], u9_num)
            self.H_num[27] = float(u9_num)
            self.H_num[26] = float(u3)
            # Check if H(26)+1 already exists on disk (lines 0660-0690)
            if self.day_file_exists(u3 + 1):
                self.current_prompt = "REPORT DATA ALREADY ENTERED - DO YOU WANT TO CORRECT IT? (Y OR N)"
                self.state = "ITEM1_ALREADY_ENTERED"
            elif self.day_file_exists(u3):
                self._start_mrdata()
            else:
                self.current_prompt = "MUST DO PREVIOUS DAY FIRST (KEY RETURN TO CONTINUE)"
                self.state = "WAIT_RETURN_MENU"

        elif next_st == "ITEM1_START_CROP_DATE":
            # Lines 0850-1120: Initialize crop start date in MRPARAMS and create "000"
            self.load_mrparams()
            self.A1_str = u9_str
            self.H_num[25] = float(u9_num)
            self.H_num[26] = 0.0
            self.A2_str[2] = u9_str
            self.save_mrparams()

            prev_dt, prev_jul = wang_julian_to_mmddyy(u9_num - 1)
            x0 = [0.0] * 258
            x0[0] = 0.0
            x0[242] = float(prev_jul)
            self.save_day_file(0, prev_dt, x0, [" "] * 6)
            self.H_num[27] = self.H_num[25]
            self._start_mrdata()

        elif next_st == "ITEM2_AFTER_DATE":
            u3 = wang_julian_diff(self.H_num[25], u9_num)
            if u3 < 0 or not self.day_file_exists(u3 + 1):
                self.current_prompt = "THIS REPORT NOT ON FILE - KEY RETURN TO CONTINUE"
                self.state = "WAIT_RETURN_MENU"
            else:
                self.H_num[26] = float(u3 + 1)
                self._start_mrdataco()

        elif next_st == "ITEM34_AFTER_DATE":
            u3 = wang_julian_diff(self.H_num[25], u9_num)
            day_idx = u3 + 1
            if u3 < 0 or not self.day_file_exists(day_idx):
                self.current_prompt = "THIS REPORT NOT ON FILE - KEY RETURN TO CONTINUE"
                self.state = "WAIT_RETURN_MENU"
            else:
                self.H_num[28] = float(self.ctx.get("menu_x", 3))
                self.H_num[26] = float(day_idx)
                a1_dt, x_arr, b1_rem = self.load_day_file(day_idx)
                b1_obj = OneBasedArray1D(6, " ")
                b1_obj.from_list(b1_rem)
                is_todate = int(round(self.H_num[28])) == 4
                pages = render_mrdatapr(
                    self.B_str, a1_dt, x_arr, b1_obj, self.J_str, self.H_str, self.H_num, include_todate_workup=is_todate
                )
                title = f"{'TODATE FILE' if is_todate else 'DAILY REPORT DATA'} - {a1_dt} (Day {day_idx})"
                self.add_printer_job(title, pages)
                self.show_main_menu()

        elif next_st == "ITEM5_AFTER_DATE":
            self.ctx["daily_rep_u9_str"] = u9_str
            self.ctx["daily_rep_u9_num"] = u9_num
            self.current_prompt = "NUMBER OF REPORT COPIES REQUIRED"
            self.state = "DAILY_REPORT_COPIES"

        elif next_st == "ITEM6_LAST_DAY":
            u3 = wang_julian_diff(self.H_num[25], u9_num)
            self.H_num[26] = float(u3 + 1)
            self.A2_str[2] = u9_str
            self._ask_date("FIRST DAY INCLUDED IN THIS WEEKLY REPORT (MM/DD/YY)?", "ITEM6_FIRST_DAY")

        elif next_st == "ITEM6_FIRST_DAY":
            self.A2_str[1] = u9_str
            u3 = wang_julian_diff(self.H_num[25], u9_num)
            self.H_num[27] = float(u3)
            self.current_prompt = "NUMBER OF THIS WEEKLY REPORT"
            self.state = "WEEKLY_REPORT_NUM"

        elif next_st == "ITEM7_AFTER_DATE":
            self.A1_str = u9_str
            self.ctx["stock_date"] = u9_str
            self.clear_crt()
            self.print_crt("STOCK CALCULATIONS")
            self.print_crt("")
            self.current_prompt = "WILL MATERIALS IN PROCESS BE REPORTED IN GALLONS OR CUBIC FEET (G OR CF)"
            self.state = "MRSTOCK_UNIT"

        elif next_st == "ITEM9_AFTER_DATE":
            u3 = wang_julian_diff(self.H_num[25], u9_num)
            self.H_num[26] = float(u3)
            if self.day_file_exists(u3 + 2):
                self.current_prompt = "THIS IS NOT LAST CROP DAY, KEY RETURN TO CONTINUE"
                self.state = "WAIT_RETURN_MENU"
            elif not self.day_file_exists(u3 + 1):
                self.current_prompt = "THIS REPORT NOT ON FILE - KEY RETURN TO CONTINUE"
                self.state = "WAIT_RETURN_MENU"
            else:
                self._start_mrencrop()

    # --------------------------------------------------------------------------
    # Item 1: MRDATA (Daily Input) & MRDATAWU
    # --------------------------------------------------------------------------

    def _handle_item1_already_entered(self, val_str: str) -> None:
        ans = val_str.upper()
        if ans == "Y":
            u3 = wang_julian_diff(self.H_num[25], self.ctx["u9_num"])
            self.H_num[26] = float(u3 + 1)
            self._start_mrdataco()
        elif ans == "N":
            self.show_main_menu()
        else:
            self._trigger_reenter("ENTER Y OR N")

    def _handle_item1_start_crop_yn(self, val_str: str) -> None:
        ans = val_str.upper()
        if ans == "N":
            self.show_main_menu()
        elif ans == "Y":
            self._ask_date("DATE THAT CROP STARTED (MM/DD/YY)?", "ITEM1_START_CROP_DATE")
        else:
            self._trigger_reenter("ENTER Y OR N")

    def _start_mrdata(self) -> None:
        """Initializes MRDATA sequential input (lines 0030-0190)."""
        self.A.clear()
        prev_day = int(round(self.H_num[26]))
        self.A[1, 1] = float(prev_day + 1)
        self.A[243, 1] = self.H_num[27]
        _, prev_x, _ = self.load_day_file(prev_day)
        for j in range(1, 259):
            self.A[j, 3] = prev_x[j - 1]
        for j in range(1, 7):
            self.B1_str[j] = " "

        self.clear_crt()
        self.print_crt(f"DAILY DATA INPUT - CROP DAY {int(round(self.A[1, 1]))} ({self.A2_str[2]})")
        prompts = get_daily_input_prompts(self.J_str, self.H_str, self.H_num)
        self.ctx["mrdata_prompts"] = prompts
        self.ctx["mrdata_idx"] = 0
        self.ctx["mrdata_remark_idx"] = 0
        self._prompt_next_mrdata()

    def _prompt_next_mrdata(self) -> None:
        prompts = self.ctx["mrdata_prompts"]
        idx = self.ctx["mrdata_idx"]
        if idx < len(prompts):
            _, label, pre_hdr = prompts[idx]
            if pre_hdr:
                self.print_crt(pre_hdr)
            self.current_prompt = label
            self.state = "MRDATA_INPUT"
        else:
            rem_idx = self.ctx["mrdata_remark_idx"]
            rem_labels = ["1A", "1B", "2A", "2B", "3A", "3B"]
            if rem_idx < 6:
                self.current_prompt = f"REMARKS - LINE {rem_labels[rem_idx]}"
                self.state = "MRDATA_INPUT"
            else:
                # Chain to MRDATAWU (lines 0010-1740)
                run_workup_on_A(self.A, self.H_num, is_correction=False)
                day_num = int(round(self.A[1, 2]))
                x_new = [self.A[j, 2] for j in range(1, 259)]
                self.save_day_file(day_num, self.A2_str[2], x_new, self.B1_str.to_list())
                self.show_main_menu()
                self.top_bar_row1 = f"SAVED DAILY REPORT NO. {day_num} ({self.A2_str[2]}) TO DISK {self.get_disk_name()}"

    def _handle_mrdata_step(self, raw_input: str) -> None:
        prompts = self.ctx["mrdata_prompts"]
        idx = self.ctx["mrdata_idx"]
        if idx < len(prompts):
            item_no, _, _ = prompts[idx]
            val_s = raw_input.strip()
            if val_s == "" and not self.strict_wang_mode:
                val = 0.0
            else:
                try:
                    val = float(val_s)
                except ValueError:
                    self._trigger_reenter("NUMERIC INPUT REQUIRED - RE-ENTER")
                    return
            self.A[item_no, 1] = val
            self.ctx["mrdata_idx"] += 1
            self._prompt_next_mrdata()
        else:
            rem_idx = self.ctx["mrdata_remark_idx"]
            self.B1_str[rem_idx + 1] = raw_input[:60]
            self.ctx["mrdata_remark_idx"] += 1
            self._prompt_next_mrdata()

    # --------------------------------------------------------------------------
    # Item 2: MRDATACO (Correct Data) & MRDACOWU (Cascading Recalculation)
    # --------------------------------------------------------------------------

    def _start_mrdataco(self) -> None:
        """Initializes MRDATACO (lines 0030-0260)."""
        self.A.clear()
        target_day = int(round(self.H_num[26]))
        _, prev_x, _ = self.load_day_file(target_day - 1)
        for j in range(1, 259):
            self.A[j, 3] = prev_x[j - 1]
        a1_dt, cur_x, cur_b1 = self.load_day_file(target_day)
        self.A1_str = a1_dt
        for j in range(1, 259):
            self.A[j, 1] = cur_x[j - 1]
        self.B1_str.from_list(cur_b1)

        self.clear_crt()
        self.print_crt("DATA CORRECTION ROUTINE")
        self.print_crt(f"FOR CROP DAY  {int(round(self.A[1, 1]))}")
        self.print_crt(f"REPORT FOR DAY {self.A1_str}")
        self.print_crt("")

        prompts = get_daily_input_prompts(self.J_str, self.H_str, self.H_num)
        self.ctx["mrdataco_prompts"] = prompts
        self.ctx["mrdataco_idx"] = 0
        self.ctx["mrdataco_remark_idx"] = 0
        self._prompt_next_mrdataco()

    def _prompt_next_mrdataco(self) -> None:
        prompts = self.ctx["mrdataco_prompts"]
        idx = self.ctx["mrdataco_idx"]
        if idx < len(prompts):
            item_no, label, pre_hdr = prompts[idx]
            if pre_hdr:
                self.print_crt(pre_hdr)
            cur_val = self.A[item_no, 1]
            self.print_crt(f"{label}  {cur_val:g}")
            self.current_prompt = label
            self.state = "MRDATACO_INPUT"
        else:
            rem_idx = self.ctx["mrdataco_remark_idx"]
            rem_labels = ["1A", "1B", "2A", "2B", "3A", "3B"]
            if rem_idx < 6:
                cur_rem = self.B1_str[rem_idx + 1].rstrip()
                self.print_crt(f"CURRENT REMARKS - LINE {rem_labels[rem_idx]}: {cur_rem}")
                self.current_prompt = f"REMARKS - LINE {rem_labels[rem_idx]}"
                self.state = "MRDATACO_INPUT"
            else:
                self._run_mrdacowu_cascade()

    def _handle_mrdataco_step(self, raw_input: str) -> None:
        prompts = self.ctx["mrdataco_prompts"]
        idx = self.ctx["mrdataco_idx"]
        if idx < len(prompts):
            item_no, _, _ = prompts[idx]
            val_s = raw_input.strip()
            if val_s == "":
                if self.strict_wang_mode:
                    self._trigger_reenter("STRICT WANG BASIC MODE: MUST TYPE VALUE")
                    return
                # Convenient mode: keep existing value
                val = self.A[item_no, 1]
            else:
                try:
                    val = float(val_s)
                except ValueError:
                    self._trigger_reenter("NUMERIC INPUT REQUIRED - RE-ENTER")
                    return
            self.A[item_no, 1] = val
            self.print_crt("")
            self.ctx["mrdataco_idx"] += 1
            self._prompt_next_mrdataco()
        else:
            rem_idx = self.ctx["mrdataco_remark_idx"]
            if raw_input != "" or self.strict_wang_mode:
                self.B1_str[rem_idx + 1] = raw_input[:60]
            self.ctx["mrdataco_remark_idx"] += 1
            self._prompt_next_mrdataco()

    def _run_mrdacowu_cascade(self) -> None:
        """
        Executes MRDACOWU (lines 0010-1910):
        Recalculates target day H(26) and cascades To-Date updates forward through all subsequent days on disk.
        """
        cascaded_days = []
        while True:
            run_workup_on_A(self.A, self.H_num, is_correction=True)
            day_num = int(round(self.A[1, 2]))
            x_new = [self.A[j, 2] for j in range(1, 259)]
            self.save_day_file(day_num, self.A1_str, x_new, self.B1_str.to_list())
            cascaded_days.append((day_num, self.A1_str))

            for j in range(1, 259):
                self.A[j, 3] = self.A[j, 2]

            self.H_num[26] += 1.0
            next_day = int(round(self.H_num[26]))
            if not self.day_file_exists(next_day):
                break
            a1_next, x_next, b1_next = self.load_day_file(next_day)
            self.A1_str = a1_next
            self.B1_str.from_list(b1_next)
            for j in range(1, 110):
                self.A[j, 1] = x_next[j - 1]
            for j in (243, 246, 251, 252, 253, 254):
                self.A[j, 1] = x_next[j - 1]

        self.show_main_menu()
        for d_no, d_dt in cascaded_days:
            self.print_crt(f"CORRECTED TODATE FIGURES ON REPORT NO. {d_no} FOR {d_dt}")
        self.top_bar_row1 = f"CASCADE COMPLETE: UPDATED {len(cascaded_days)} CROP DAY FILE(S)"

    # --------------------------------------------------------------------------
    # Items 5, 6, 13: Daily Report, Weekly Report, Weekly Comparative Form
    # --------------------------------------------------------------------------

    def _handle_report_check_yn(self, val_str: str) -> None:
        ans = val_str.upper()
        if ans == "Y":
            self.H_num[35] = 1.0
        elif ans == "N":
            self.H_num[35] = 0.0
        else:
            self._trigger_reenter("ENTER Y OR N")
            return

        if int(round(self.ctx.get("menu_x", 5))) == 6:
            self.clear_crt()
            self.print_crt("PRINT WEEKLY REPORT ROUTINE")
            self._ask_date("LAST DAY INCLUDED IN THIS WEEKLY REPORT (MM/DD/YY)?", "ITEM6_LAST_DAY")
        else:
            self.clear_crt()
            self.print_crt("PRINT DAILY REPORT ROUTINE")
            self._ask_date("REPORT FOR CROP DAY (MM/DD/YY)?", "ITEM5_AFTER_DATE")

    def _handle_daily_report_copies(self, val_str: str) -> None:
        try:
            copies = max(1, int(float(val_str)))
        except ValueError:
            self._trigger_reenter("ENTER NUMBER OF COPIES")
            return
        self.H_num[32] = float(copies)
        u9_str = self.ctx["daily_rep_u9_str"]
        u9_num = self.ctx["daily_rep_u9_num"]
        self.A2_str[2] = u9_str
        u3 = wang_julian_diff(self.H_num[25], u9_num)
        self.H_num[26] = float(u3 + 1)
        self.H_num[27] = float(u3)
        if u3 < 0 or not self.day_file_exists(u3 + 1):
            self.current_prompt = "THIS REPORT NOT ON FILE - KEY RETURN TO CONTINUE"
            self.state = "WAIT_RETURN_MENU"
            return
        self.H_num[28] = 0.0
        self._execute_report_generation()

    def _handle_weekly_report_num(self, val_str: str) -> None:
        try:
            rep_no = int(float(val_str))
        except ValueError:
            self._trigger_reenter("ENTER WEEKLY REPORT NUMBER")
            return
        self.H_num[31] = float(rep_no)
        if int(round(self.H_num[34])) == 1:
            self.current_prompt = "IS THIS OKAY (Y OR N)"
            self.state = "WEEKLY_REPORT_OK"
        else:
            self.current_prompt = "NUMBER OF REPORT COPIES REQUIRED"
            self.state = "WEEKLY_REPORT_COPIES"

    def _handle_weekly_report_copies(self, val_str: str) -> None:
        try:
            copies = max(1, int(float(val_str)))
        except ValueError:
            self._trigger_reenter("ENTER NUMBER OF COPIES")
            return
        self.H_num[32] = float(copies)
        self.current_prompt = "IS THIS OKAY (Y OR N)"
        self.state = "WEEKLY_REPORT_OK"

    def _handle_weekly_report_ok(self, val_str: str) -> None:
        ans = val_str.upper()
        if ans == "N":
            self.clear_crt()
            self.print_crt("PRINT WEEKLY REPORT ROUTINE")
            self._ask_date("LAST DAY INCLUDED IN THIS WEEKLY REPORT (MM/DD/YY)?", "ITEM6_LAST_DAY")
            return
        if ans != "Y":
            self._trigger_reenter("ENTER Y OR N")
            return

        end_day = int(round(self.H_num[26]))
        base_day = int(round(self.H_num[27]))
        if end_day < 1 or base_day < 0 or not self.day_file_exists(end_day) or not self.day_file_exists(base_day):
            self.current_prompt = "THIS REPORT NOT ON FILE - KEY RETURN TO CONTINUE"
            self.state = "WAIT_RETURN_MENU"
            return

        self.H_num[28] = 1.0
        if int(round(self.H_num[34])) == 0:
            # Weekly report prompts for 6 lines of remarks in MRREPOPR lines 0150-0230
            for j in range(1, 7):
                self.B1_str[j] = " "
            self.ctx["weekly_rem_idx"] = 0
            self.current_prompt = "REMARKS: LINE 1A"
            self.state = "WEEKLY_REMARKS"
        else:
            self._execute_report_generation()

    def _handle_weekly_remarks(self, raw_input: str) -> None:
        idx = self.ctx["weekly_rem_idx"]
        self.B1_str[idx + 1] = raw_input[:60]
        idx += 1
        self.ctx["weekly_rem_idx"] = idx
        rem_labels = ["1A", "1B", "2A", "2B", "3A", "3B"]
        if idx < 6:
            self.current_prompt = f"REMARKS: LINE {rem_labels[idx]}"
        else:
            self._execute_report_generation()

    def _execute_report_generation(self) -> None:
        """Runs MRCALC and chains to MRREPOPR -> MRREPOP2 (-> MRREPOCK) or MRCOMPPR."""
        end_day = int(round(self.H_num[26]))
        base_day = int(round(self.H_num[27]))

        _, x_end, b1_end = self.load_day_file(end_day)
        _, x_base, _ = self.load_day_file(base_day)

        self.A.clear()
        for j in range(1, 259):
            self.A[j, 2] = x_end[j - 1]
            self.A[j, 3] = x_base[j - 1]

        if int(round(self.H_num[28])) == 0:
            self.B1_str.from_list(b1_end)

        # Load range of day files for Max/Min temperature scan (MRCALC lines 2770-2940)
        day_files_range = []
        start_scan = max(1, base_day if base_day > 0 else 1)
        for d_idx in range(start_scan, end_day + 1):
            if self.day_file_exists(d_idx):
                _, x_d, _ = self.load_day_file(d_idx)
                day_files_range.append(x_d)

        # Preserve H(27) across MRCALC
        saved_h27 = self.H_num[27]
        run_mrcalc(
            self.A, self.B, self.C, self.D, self.E, self.F, self.G, self.H_num, day_files_range
        )
        self.H_num[27] = saved_h27

        if int(round(self.H_num[34])) == 1:
            pages = render_mrcomppr(
                self.B_str, self.A2_str, self.A, self.B, self.D, self.E, self.F, self.G, self.H_num
            )
            title = f"WEEKLY COMPARATIVE REPORT FORM - {self.A2_str[1]} to {self.A2_str[2]}"
            self.add_printer_job(title, pages)
            self.show_main_menu()
            self.top_bar_row1 = f"PRINTED {title} TO LINE PRINTER (215)"
            return

        p1 = render_mrrepopr_page1(
            self.B_str, self.A2_str, self.A, self.B, self.C, self.D, self.H_num
        )
        p2 = render_mrrepop2_page2(
            self.B_str,
            self.B1_str,
            self.A2_str,
            self.A,
            self.E,
            self.F,
            self.G,
            self.J_str,
            self.H_str,
            self.H_num,
        )
        pages = [p1, p2]
        if int(round(self.H_num[35])) == 1:
            p3 = render_mrrepock_page3(
                self.B_str, self.A2_str, self.A, self.B, self.C, self.D, self.E, self.F, self.H_num
            )
            pages.append(p3)

        if int(round(self.H_num[28])) == 1:
            title = f"WEEKLY MANUFACTURING REPORT NO. {int(round(self.H_num[31]))} ({self.A2_str[1]} to {self.A2_str[2]})"
        else:
            title = f"DAILY MANUFACTURING REPORT NO. {int(round(self.A[1, 2]))} ({self.A2_str[2]})"

        self.add_printer_job(title, pages)
        self.show_main_menu()
        self.top_bar_row1 = f"PRINTED {title} ({len(pages)} PAGES) TO LINE PRINTER (215)"

    # --------------------------------------------------------------------------
    # Item 7: Stock in Process Calculations (MRSTOCK -> MRSTOCKG / MRSTOCKC)
    # --------------------------------------------------------------------------

    def _handle_mrstock_unit(self, val_str: str) -> None:
        ans = val_str.upper()
        if ans not in ("G", "CF"):
            self._trigger_reenter("ENTER G OR CF")
            return
        self.ctx["stock_unit"] = ans
        unit_word = "GALLONS" if ans == "G" else "CU. FT."
        streams = [
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
        ]
        prompts: List[Tuple[int, str]] = []
        idx = 1
        for st in streams:
            if st == "B MAGMA":
                # Lines 0560-0580 in MRSTOCKC / 0462-0466 in MRSTOCKG are REM'd out
                idx += 3
                continue
            prompts.append((idx, f"{idx:2d}   {st}, {unit_word}"))
            prompts.append((idx + 1, f"{idx+1:2d}   {st}, BRIX"))
            prompts.append((idx + 2, f"{idx+2:2d}   {st}, POL"))
            idx += 3
        prompts.append((40, "40   FINAL MOLASSES PURITY FOR RUN"))
        prompts.append((41, "41   SUGAR PURITY FOR RUN"))

        self.ctx["stock_prompts"] = prompts
        self.ctx["stock_vals"] = [0.0] * 41
        self.ctx["stock_idx"] = 0
        self.current_prompt = prompts[0][1]
        self.state = "MRSTOCK_INPUT"

    def _handle_mrstock_step(self, val_str: str) -> None:
        prompts = self.ctx["stock_prompts"]
        idx = self.ctx["stock_idx"]
        item_no, _ = prompts[idx]
        if val_str == "" and not self.strict_wang_mode:
            v = 0.0
        else:
            try:
                v = float(val_str)
            except ValueError:
                self._trigger_reenter("NUMERIC INPUT REQUIRED - RE-ENTER")
                return
        self.ctx["stock_vals"][item_no - 1] = v
        idx += 1
        self.ctx["stock_idx"] = idx
        if idx < len(prompts):
            self.current_prompt = prompts[idx][1]
        else:
            lines, summary = calculate_and_render_stock(
                self.B_str,
                self.ctx.get("stock_date", self.A1_str),
                self.ctx["stock_unit"],
                self.ctx["stock_vals"],
                self.H_num,
            )
            title = f"STOCK CALCULATIONS ({self.ctx['stock_unit']}) - {self.ctx.get('stock_date', self.A1_str)}"
            self.add_printer_job(title, [lines])
            self.print_crt("")
            self.print_crt(f"SUGAR IN STOCK:    {summary['sugar_lbs_brix']:,.0f} Lbs Brix | {summary['sugar_lbs_pol']:,.0f} Lbs Pol")
            self.print_crt(f"MOLASSES IN STOCK: {summary['molasses_lbs_brix']:,.0f} Lbs Brix | {summary['molasses_lbs_pol']:,.0f} Lbs Pol")
            self.current_prompt = "IS DATA OKAY (Y OR N)"
            self.state = "MRSTOCK_OK"

    def _handle_mrstock_ok(self, val_str: str) -> None:
        ans = val_str.upper()
        if ans == "Y":
            self.show_main_menu()
        elif ans == "N":
            self._handle_mrstock_unit(self.ctx["stock_unit"])
        else:
            self._trigger_reenter("ENTER Y OR N")

    # --------------------------------------------------------------------------
    # Item 8: Help Routine for Daily Report (MRHELPC & MRHELPS)
    # --------------------------------------------------------------------------

    def _handle_mrhelp_mode(self, val_str: str) -> None:
        if val_str in ("", "1"):
            prompts = [
                "TOTAL LBS TRS PURCHASED",
                "LIQUIDATION FACTOR",
                "POL % MIXED JUICE",
                "BRIX % MIXED JUICE",
                "BOILING HOUSE EFFICIENCY",
                "TONS CANE GROUND TODAY",
                "TONS CANE PURCHASED TODAY",
                "FIBER % BAGASSE",
                "FIBER % CANE DESIRED",
            ]
            self.ctx["help_prompts"] = prompts
            self.ctx["help_vals"] = []
            self.ctx["help_mode"] = "C"
            self.current_prompt = prompts[0]
            self.state = "MRHELPC_INPUT"
        elif val_str == "2":
            prompts = [
                "TONS CANE GROUND",
                "MIXED JUICE BRIX",
                "NORMAL JUICE BRIX",
                "DESIRED NORMAL JUICE EXTRACTION",
                "FIBER % BAGASSE",
                "DESIRED FIBER % CANE",
            ]
            self.ctx["help_prompts"] = prompts
            self.ctx["help_vals"] = []
            self.ctx["help_mode"] = "S"
            self.current_prompt = prompts[0]
            self.state = "MRHELPS_INPUT"
        else:
            self._trigger_reenter("ENTER 1 OR 2")

    def _handle_mrhelpc_step(self, val_str: str) -> None:
        try:
            v = float(val_str)
        except ValueError:
            self._trigger_reenter("NUMERIC INPUT REQUIRED")
            return
        self.ctx["help_vals"].append(v)
        prompts = self.ctx["help_prompts"]
        if len(self.ctx["help_vals"]) < len(prompts):
            self.current_prompt = prompts[len(self.ctx["help_vals"])]
        else:
            a, b, c, d, e, f, g, h, i = self.ctx["help_vals"]
            denom = c * (1.4 - 0.4 * safe_div(d, c)) * e * g
            m = safe_div(a * b * 0.048 * f, denom)
            b1 = safe_div(f * i, h)
            i1 = m + b1 - f
            self.print_crt("")
            self.print_crt(f"TONS MIXED JUICE=  {m:.4f}")
            self.print_crt(f"TONS IMBIBITION=   {i1:.4f}")
            self.print_crt("")
            self.current_prompt = "IS THIS OKAY (Y OR N)"
            self.state = "MRHELP_OK"

    def _handle_mrhelps_step(self, val_str: str) -> None:
        try:
            v = float(val_str)
        except ValueError:
            self._trigger_reenter("NUMERIC INPUT REQUIRED")
            return
        self.ctx["help_vals"].append(v)
        prompts = self.ctx["help_prompts"]
        if len(self.ctx["help_vals"]) < len(prompts):
            self.current_prompt = prompts[len(self.ctx["help_vals"])]
        else:
            c, m, n, e, b, f = self.ctx["help_vals"]
            d = safe_div((n - m) * 100.0, m)
            j = e + d
            m1 = c * j / 100.0
            a = safe_div(f * c, b)
            i = m1 + a - c
            self.print_crt("")
            self.print_crt(f"TONS MIXED JUICE=  {m1:.4f}")
            self.print_crt(f"TONS IMBIBITION=   {i:.4f}")
            self.print_crt("")
            self.current_prompt = "IS THIS OKAY (Y OR N)"
            self.state = "MRHELP_OK"

    def _handle_mrhelp_ok(self, val_str: str) -> None:
        ans = val_str.upper()
        if ans == "Y":
            self.show_main_menu()
        elif ans == "N":
            mode = "1" if self.ctx.get("help_mode") == "C" else "2"
            self._handle_mrhelp_mode(mode)
        else:
            self._trigger_reenter("ENTER Y OR N")

    # --------------------------------------------------------------------------
    # Item 9: End of Crop Correction Routine (MRENCROP -> MRDACOWU)
    # --------------------------------------------------------------------------

    def _start_mrencrop(self) -> None:
        """Initializes MRENCROP (lines 0060-0600)."""
        prev_day = int(round(self.H_num[26]))
        last_day = prev_day + 1
        _, x_prev, _ = self.load_day_file(prev_day)
        a1_last, x_last, b1_last = self.load_day_file(last_day)
        self.A1_str = a1_last
        self.B1_str.from_list(b1_last)

        self.A.clear()
        for j in range(1, 259):
            self.A[j, 2] = x_prev[j - 1]
            self.A[j, 3] = x_last[j - 1]
        self.H_num[26] = float(last_day)

        b_vals = [0.0] * 19
        b_vals[1] = self.A[204, 3] * 2000.0
        b_vals[2] = safe_div((self.A[204, 3] - self.A[205, 3]) * 100.0, self.A[204, 3])
        b_vals[3] = safe_div(self.A[206, 3] * 100.0, self.A[204, 3])
        b_vals[4] = safe_div(self.A[207, 3] * 100.0, self.A[204, 3])
        b_vals[5] = safe_div(self.A[208, 3] * 100.0, self.A[204, 3])
        b_vals[6] = self.A[211, 3]
        b_vals[7] = safe_div(self.A[213, 3] * 100.0, self.A[212, 3])
        b_vals[8] = safe_div(self.A[214, 3] * 100.0, self.A[212, 3])
        b_vals[9] = safe_div(self.A[215, 3] * 100.0, self.A[212, 3])
        b_vals[10] = safe_div(self.A[216, 3] * 100.0, self.A[212, 3])
        b_vals[11] = safe_div(self.A[217, 3] * 100.0, self.A[212, 3])
        b_vals[12] = self.A[220, 3]
        b_vals[13] = safe_div(self.A[222, 3] * 100.0, self.A[221, 3])
        b_vals[14] = safe_div(self.A[223, 3] * 100.0, self.A[221, 3])
        b_vals[15] = safe_div(self.A[224, 3] * 100.0, self.A[221, 3])
        b_vals[16] = safe_div(self.A[225, 3] * 100.0, self.A[221, 3])
        b_vals[17] = safe_div(self.A[226, 3] * 100.0, self.A[221, 3])
        b_vals[18] = self.A[242, 3]

        enc_prompts = [
            (1, "TODATE LBS SUGAR MADE"),
            (2, "TODATE MOISTURE % SUGAR"),
            (3, "TODATE POL % SUGAR"),
            (4, "TODATE STARCH % SUGAR"),
            (5, "TODATE GRAIN SUGAR"),
            (18, "TODATE LBS SUGAR SHIPPED"),
            (6, "TODATE GALLONS FINAL MOLASSES MADE"),
            (7, "TODATE BRIX OF FINAL MOLASSES MADE"),
            (8, "TODATE POL OF FINAL MOLASSES MADE"),
            (9, "TODATE GLUCOSE % FINAL MOLASSES MADE"),
            (10, "TODATE ASH % FINAL MOLASSES MADE"),
            (11, "TODATE CLERGET OF FINAL MOLASSES MADE"),
            (12, "TODATE GALLONS OF FINAL MOLASSES SHIPPED"),
            (13, "TODATE BRIX OF FINAL MOLASSES SHIPPED"),
            (14, "TODATE POL OF FINAL MOLASSES SHIPPED"),
            (15, "TODATE GLUCOSE % FINAL MOLASSES SHIPPED"),
            (16, "TODATE ASH % FINAL MOLASSES SHIPPED"),
            (17, "TODATE CLERGET % FINAL MOLASSES SHIPPED"),
        ]
        self.print_crt("")
        self.print_crt(f"REPORT FOR DAY {self.A1_str}")
        self.print_crt(f"FOR CROP DAY {int(round(self.A[1, 3]))}")
        self.print_crt("")

        self.ctx["enc_b"] = b_vals
        self.ctx["enc_prompts"] = enc_prompts
        self.ctx["enc_idx"] = 0
        b_idx, lbl = enc_prompts[0]
        self.print_crt(f"{lbl}  {b_vals[b_idx]:g}")
        self.current_prompt = f"CORRECT {lbl}"
        self.state = "MRENCROP_INPUT"

    def _handle_mrencrop_step(self, raw_input: str) -> None:
        enc_prompts = self.ctx["enc_prompts"]
        idx = self.ctx["enc_idx"]
        b_idx, _ = enc_prompts[idx]
        val_s = raw_input.strip()
        if val_s == "" and not self.strict_wang_mode:
            v = self.ctx["enc_b"][b_idx]
        else:
            try:
                v = float(val_s)
            except ValueError:
                self._trigger_reenter("NUMERIC INPUT REQUIRED")
                return
        self.ctx["enc_b"][b_idx] = v
        idx += 1
        self.ctx["enc_idx"] = idx
        if idx < len(enc_prompts):
            next_b_idx, next_lbl = enc_prompts[idx]
            self.print_crt("")
            self.print_crt(f"{next_lbl}  {self.ctx['enc_b'][next_b_idx]:g}")
            self.current_prompt = f"CORRECT {next_lbl}"
        else:
            # Execute MRENCROP lines 0960-1580
            bv = self.ctx["enc_b"]
            self.A[204, 1] = bv[1] / 2000.0
            self.A[205, 1] = (100.0 - bv[2]) / 100.0 * self.A[204, 1]
            self.A[206, 1] = bv[3] / 100.0 * self.A[204, 1]
            self.A[207, 1] = bv[4] / 100.0 * self.A[204, 1]
            self.A[208, 1] = bv[5] / 100.0 * self.A[204, 1]
            self.A[211, 1] = bv[6]
            k = bv[7]
            k1 = brix_density_poly_5(k) / 7.48
            self.A[212, 1] = self.A[211, 1] * k1 / 2000.0
            self.A[213, 1] = self.A[212, 1] * k / 100.0
            self.A[214, 1] = self.A[212, 1] * bv[8] / 100.0
            self.A[215, 1] = self.A[212, 1] * bv[9] / 100.0
            self.A[216, 1] = self.A[212, 1] * bv[10] / 100.0
            self.A[217, 1] = self.A[212, 1] * bv[11] / 100.0
            self.A[220, 1] = bv[12]
            k_s = bv[13]
            k1_s = brix_density_poly_5(k_s) / 7.48
            self.A[221, 1] = self.A[220, 1] * k1_s / 2000.0
            self.A[222, 1] = self.A[221, 1] * k_s / 100.0
            self.A[223, 1] = self.A[221, 1] * bv[14] / 100.0
            self.A[224, 1] = self.A[221, 1] * bv[15] / 100.0
            self.A[225, 1] = self.A[221, 1] * bv[16] / 100.0
            self.A[226, 1] = self.A[221, 1] * bv[17] / 100.0
            self.A[242, 1] = bv[18]

            self.A[95, 1] = (self.A[204, 1] - self.A[204, 2]) * 2000.0
            d_sug = self.A[204, 1] - self.A[204, 2]
            self.A[70, 1] = safe_div(
                (self.A[204, 1] - self.A[205, 1] - self.A[204, 2] + self.A[205, 2]) * 100.0, d_sug
            )
            self.A[71, 1] = safe_div((self.A[206, 1] - self.A[206, 2]) * 100.0, d_sug)
            self.A[72, 1] = safe_div((self.A[207, 1] - self.A[207, 2]) * 100.0, d_sug)
            self.A[73, 1] = safe_div((self.A[208, 1] - self.A[208, 2]) * 100.0, d_sug)

            self.A[96, 1] = self.A[211, 1] - self.A[211, 2]
            self.A[97, 1] = self.A[242, 1] - self.A[242, 2]
            self.A[98, 1] = self.A[220, 1] - self.A[220, 2]

            d_fm = self.A[212, 1] - self.A[212, 2]
            for offset_i in range(5):
                self.A[74 + offset_i, 1] = safe_div(
                    (self.A[213 + offset_i, 1] - self.A[213 + offset_i, 2]) * 100.0, d_fm
                )
            d_fms = self.A[221, 1] - self.A[221, 2]
            for offset_i in range(5):
                self.A[79 + offset_i, 1] = safe_div(
                    (self.A[222 + offset_i, 1] - self.A[222 + offset_i, 2]) * 100.0, d_fms
                )

            for rng in ((70, 83), (95, 98), (204, 208), (211, 217), (220, 226), (242, 242)):
                for j in range(rng[0], rng[1] + 1):
                    self.A[j, 3] = self.A[j, 1]

            for j in range(1, 259):
                self.A[j, 1] = self.A[j, 3]
                self.A[j, 3] = self.A[j, 2]

            self._run_mrdacowu_cascade()

    # --------------------------------------------------------------------------
    # Item 10: Customize Program (MRCUSTOM)
    # --------------------------------------------------------------------------

    def _start_mrcustom(self) -> None:
        self.load_mrparams()
        steps = [("B$", "FACTORY NAME ON REPORT", self.B_str.strip())]
        for j in range(1, 11):
            steps.append((f"J$_{j}", f"LOST TIME CATEGORY NO. {j}", self.J_str[j].strip()))
        self.H_str[1] = "Gas, M. Cu. Ft."
        for j in range(2, 13):
            steps.append((f"H$_{j}", f"MATERIALS AND SUPPLIES CATEGORY NO. {j}", self.H_str[j].strip()))
        steps.append(("H$_13", "TOTAL ROLL SURFACE OF ALL MILL ROLLS", self.H_str[13].strip()))
        steps.append(("H$_14", "BRIX DESIRED FOR REPORTING FINAL MOLASSES M&E/TON CANE", self.H_str[14].strip()))

        i_questions = [
            (1, "WILL ANALYSES BE AVERAGED BY CROP DAY (D) OR CANE WEIGHTING (W)"),
            (2, "WILL CRUSHER JUICE GLUCOSE BE REPORTED (Y OR N)"),
            (3, "WILL CRUSHER JUICE pH BE REPORTED (Y OR N)"),
            (4, "WILL MIXED JUICE GLUCOSE BE REPORTED (Y OR N)"),
            (5, "WILL MIXED JUICE pH BE REPORTED (Y OR N)"),
            (6, "WILL CLARIFIED JUICE GLUCOSE BE REPORTED (Y OR N)"),
            (7, "WILL CLARIFIED JUICE pH BE REPORTED (Y OR N)"),
            (8, "WILL SYRUP GLUCOSE BE REPORTED (Y OR N)"),
            (9, "WILL SYRUP pH BE REPORTED (Y OR N)"),
            (10, "WILL SUGAR MADE STARCH BE REPORTED (Y OR N)"),
            (11, "WILL SUGAR MADE DEXTRAN BE REPORTED (Y OR N)"),
            (12, "WILL FINAL MOLASSES MADE GLUCOSE BE REPORTED (Y OR N)"),
            (13, "WILL FINAL MOLASSES MADE ASH BE REPORTED (Y OR N)"),
            (14, "WILL FINAL MOLASSES MADE CLERGET BE REPORTED (Y OR N)"),
            (15, "WILL FINAL MOLASSES SHIPPED GLUCOSE BE REPORTED (Y OR N)"),
            (16, "WILL FINAL MOLASSES SHIPPED ASH BE REPORTED (Y OR N)"),
            (17, "WILL FINAL MOLASSES SHIPPED CLERGET BE REPORTED (Y OR N)"),
            (18, "WILL FILTRATE JUICE BRIX AND POL BE REPORTED (Y OR N)"),
            (19, "WILL TOP-OFF A STRIKES BRIX AND POL BE REPORTED (Y OR N)"),
            (20, "WILL EITHER B MAGMA OR C CYCLONES BE REPORTED (Y OR N)"),
            (21, "WILL FILTER CAKE MOISTURES BE REPORTED (Y OR N)"),
            (22, "WILL B MAGMA (Y) OR C CYCLONE (N) ANALYSES BE REPORTED"),
            (23, "DOES REPORT PRINTER HAVE EXPANDED PRINT CAPABILITY (Y OR N)"),
            (24, "WILL METERED IMBIBITION WATER BE REPORTED (Y OR N)"),
        ]
        for idx_q, q_text in i_questions:
            steps.append((f"I$_{idx_q}", q_text, self.I_str[idx_q].strip()))

        steps.append(("H_36", "PRINTER SELECTION CODE: 0 = SYSTEM (215), 1 = TERMINAL (204)", str(int(round(self.H_num[36])))))
        steps.append(("H_37", "CODE FOR DATA DISK (0=SAME, 1=310, 2=D11, 3=D12, 4=D13, ETC.)", str(int(round(self.H_num[37])))))

        self.ctx["cust_steps"] = steps
        self.ctx["cust_idx"] = 0
        _, lbl, cur = steps[0]
        self.print_crt(f"[Current: {cur}]")
        self.current_prompt = lbl
        self.state = "MRCUSTOM_INPUT"

    def _handle_mrcustom_step(self, raw_input: str) -> None:
        steps = self.ctx["cust_steps"]
        idx = self.ctx["cust_idx"]
        key, _, cur_default = steps[idx]
        val_s = raw_input.strip()
        if val_s == "":
            val_s = cur_default

        if key == "B$":
            self.B_str = val_s[:64]
        elif key.startswith("J$_"):
            j_idx = int(key.split("_")[1])
            self.J_str[j_idx] = val_s[:16]
        elif key.startswith("H$_"):
            h_idx = int(key.split("_")[1])
            if h_idx in (13, 14):
                try:
                    num_v = float(val_s)
                except ValueError:
                    self._trigger_reenter("NOT NUMERIC, ENTER AGAIN")
                    return
                self.H_str[h_idx] = val_s[:20]
                self.H_num[16 + h_idx] = num_v  # H(29) or H(30)
            else:
                self.H_str[h_idx] = val_s[:20]
        elif key.startswith("I$_"):
            i_idx = int(key.split("_")[1])
            self.I_str[i_idx] = val_s.upper()[:16]
        elif key == "H_36":
            try:
                self.H_num[36] = float(int(val_s))
            except ValueError:
                self._trigger_reenter("ENTER 0 OR 1")
                return
        elif key == "H_37":
            try:
                self.H_num[37] = float(int(val_s))
            except ValueError:
                self._trigger_reenter("ENTER DISK CODE 0..11")
                return

        idx += 1
        self.ctx["cust_idx"] = idx
        if idx < len(steps):
            _, next_lbl, next_cur = steps[idx]
            self.print_crt(f"[Current: {next_cur}]")
            self.current_prompt = next_lbl
        else:
            # Update H(1..23) and H(27) from I$(1..24) (MRCUSTOM lines 0760-0800)
            self.H_num[1] = 1.0 if self.I_str[1].strip().upper() == "D" else 0.0
            for j in range(2, 24):
                self.H_num[j] = 0.0 if self.I_str[j].strip().upper() == "N" else 1.0
            self.H_num[27] = 0.0 if self.I_str[24].strip().upper() == "N" else 1.0
            self.save_mrparams()
            self.show_main_menu()
            self.top_bar_row1 = "SAVED CUSTOMIZED PARAMETERS TO MRPARAMS"

    # --------------------------------------------------------------------------
    # Item 12: Print Blank Data Forms (MRBLANFM) & Item 17: Scratch Disk
    # --------------------------------------------------------------------------

    def _handle_mrblanfm_choice(self, val_str: str) -> None:
        if val_str == "1":
            pages = render_mrdatafm(self.B_str, self.J_str, self.H_str, self.H_num)
            self.add_printer_job("BLANK DAILY REPORT DATA INPUT FORMS (MRDATAFM)", pages)
            self.show_main_menu()
            self.top_bar_row1 = "PRINTED DAILY REPORT DATA INPUT FORMS TO LINE PRINTER (215)"
        elif val_str == "2":
            pages = render_mrstokfm(self.B_str)
            self.add_printer_job("BLANK STOCK REPORT DATA FORMS (MRSTOKFM)", pages)
            self.show_main_menu()
            self.top_bar_row1 = "PRINTED STOCK REPORT DATA FORMS TO LINE PRINTER (215)"
        else:
            self._trigger_reenter("ENTER 1 OR 2")

    def _handle_item17_confirm(self, val_str: str) -> None:
        ans = val_str.upper()
        if ans == "Y":
            d = self.get_disk_dir()
            for p in d.glob("*.json"):
                p.unlink()
            self.show_main_menu()
            self.top_bar_row1 = f"SCRATCHED ALL DATA FILES ON DISK {self.get_disk_name()}"
        elif ans == "N":
            self.show_main_menu()
        else:
            self._trigger_reenter("ENTER Y OR N")
